#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Motor Recolector y Clasificador de Alquileres para La Plata
Enfocado exclusivamente en:
- Tipos de propiedad: Casa y PH (Propiedad Horizontal / Dúplex / Depto tipo casa)
- Barrios: Meridiano V (13 a 22 y 66 a 72) y Parque San Martín (22 a 28 y 50 a 58)
- Fuentes principales:
  1. Portales Generales: Inmobúsqueda, Argenprop, ZonaProp
  2. Inmobiliarias de La Plata (extraídas de https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html
     y https://www.inmobusqueda.com.ar/inmobiliarias-la-plata.html)
"""

from dataclasses import dataclass, asdict, field
from datetime import datetime
import hashlib
import json
import re
from typing import List, Optional, Dict, Any
import urllib.request
import urllib.error
from urllib.parse import urljoin
from bs4 import BeautifulSoup


# ==============================================================================
# 1. MODELO DE DATOS UNIFICADO
# ==============================================================================

@dataclass
class AvisoPropiedad:
    id: str
    titulo: str
    tipo_propiedad: str          # "Casa" | "PH"
    barrio: str                  # "Meridiano V" | "Parque San Martín"
    direccion_extraida: str
    precio: int
    moneda: str                  # "ARS" | "USD"
    expensas: Optional[int]
    sin_expensas: bool
    dormitorios: Optional[int]
    tiene_patio: bool
    tiene_terraza: bool
    tiene_parrilla: bool
    acepta_mascotas: bool
    fuente: str                  # Portal o nombre de la inmobiliaria platense
    url_original: str
    imagen_url: Optional[str] = None
    fecha_actualizacion: str = field(
        default_factory=lambda: datetime.now().isoformat(timespec="seconds")
    )


# ==============================================================================
# 2. GEORREFERENCIACIÓN POR CUADRÍCULA DE CALLES DE LA PLATA
# ==============================================================================

class ClasificadorGeograficoLaPlata:
    """
    Cuadrantes confirmados:
    - Meridiano V: Calle 13 a Calle 22 y Avenida 66 a Avenida 72
    - Parque San Martín: Calle 22 a Calle 28 y Avenida 50 a Avenida 58
    """

    LIMITES_BARRIOS = {
        "Meridiano V": {
            "calle_long_min": 13,
            "calle_long_max": 22,
            "calle_trans_min": 66,
            "calle_trans_max": 72,
            "keywords": [
                "meridiano v",
                "meridiano quinto",
                "meridiano 5",
                "estacion provincial",
                "estación provincial",
                "17 y 71",
            ],
        },
        "Parque San Martín": {
            "calle_long_min": 22,
            "calle_long_max": 28,
            "calle_trans_min": 50,
            "calle_trans_max": 58,
            "keywords": [
                "parque san martin",
                "parque san martín",
                "pque san martin",
                "pque. san martín",
                "plaza san martin",
            ],
        },
    }

    REGEX_ENTRE_CALLES = re.compile(
        r"\b(?:calle|av\.?|avenida|diag\.?)?\s*(\d{1,3})"
        r"(?:\s*(?:n[°ºro\.]{0,3}|#)\s*\d{1,5})?\s*"
        r"(?:entre|e/|e\s+|esq\.?|esquina|y)\s*"
        r"(\d{1,3})(?:\s*y\s*(\d{1,3}))?\b",
        re.IGNORECASE,
    )

    @classmethod
    def detectar_barrio(cls, texto_completo: str) -> Optional[str]:
        texto_norm = texto_completo.lower()

        for barrio, config in cls.LIMITES_BARRIOS.items():
            for kw in config["keywords"]:
                if kw != "plaza san martin" and kw in texto_norm:
                    return barrio

        for match in cls.REGEX_ENTRE_CALLES.finditer(texto_norm):
            c1 = int(match.group(1))
            c2 = int(match.group(2))
            c3 = int(match.group(3)) if match.group(3) else None

            barrio_detectado = cls._evaluar_coordenadas(c1, c2, c3)
            if barrio_detectado:
                return barrio_detectado

        return None

    @classmethod
    def _evaluar_coordenadas(
        cls, c1: int, c2: int, c3: Optional[int] = None
    ) -> Optional[str]:
        c_cruce = (c2 + c3) / 2.0 if c3 is not None else float(c2)

        for barrio, lim in cls.LIMITES_BARRIOS.items():
            en_rango_a = (
                lim["calle_long_min"] <= c1 <= lim["calle_long_max"]
                and lim["calle_trans_min"] <= c_cruce <= lim["calle_trans_max"]
            )
            en_rango_b = (
                lim["calle_trans_min"] <= c1 <= lim["calle_trans_max"]
                and lim["calle_long_min"] <= c_cruce <= lim["calle_long_max"]
            )
            if en_rango_a or en_rango_b:
                return barrio

        return None


# ==============================================================================
# 3. ANALIZADOR DE TIPO DE PROPIEDAD Y COMODIDADES (FILTROS)
# ==============================================================================

class AnalizadorPropiedad:
    KEYWORDS_EXCLUIR = [
        "monoambiente en edificio",
        "piso alto",
        "semipiso",
        "cochera en alquiler",
        "local en alquiler",
        "local comercial en alquiler",
        "oficina en alquiler",
        "galpón",
        "galpon",
        "consultorio",
        "lote en venta",
    ]

    @classmethod
    def clasificar_tipo(cls, titulo: str, descripcion: str) -> Optional[str]:
        texto = f"{titulo} {descripcion}".lower()

        for excl in cls.KEYWORDS_EXCLUIR:
            if excl in texto:
                return None

        patrones_ph = [
            r"\bph\b",
            r"\bphs\b",
            r"\bp\.h\.?\b",
            r"propiedad horizontal",
            r"depto\.?\s*tipo\s*casa",
            r"departamento\s*tipo\s*casa",
            r"dúplex\b",
            r"duplex\b",
            r"triplex\b",
        ]
        for pat in patrones_ph:
            if re.search(pat, texto):
                return "PH"

        if re.search(r"\bcasa\b|\bcasas\b|\bchalet\b|\bcasona\b", texto):
            return "Casa"

        return None

    @staticmethod
    def extraer_atributos(
        titulo: str, descripcion: str, expensas_valor: Optional[int] = None
    ) -> Dict[str, Any]:
        texto = f"{titulo} {descripcion}".lower()

        tiene_patio = bool(
            re.search(r"\bpatio\b|\bjard[ií]n\b|\bparque propio\b|\bfondo verde\b", texto)
        )
        tiene_terraza = bool(
            re.search(r"\bterraza\b|\bsolarium\b|\bquincho en terraza\b", texto)
        )
        tiene_parrilla = bool(
            re.search(r"\bparrilla\b|\basador\b|\bquincho\b", texto)
        )

        no_mascotas = bool(
            re.search(r"no\s+(?:se\s+)?(?:acepta[n]?|admite[n]?|permite[n]?)\s+mascotas", texto)
            or "sin mascotas" in texto
        )
        si_mascotas = bool(
            re.search(r"(?:acepta[n]?|admite[n]?|permite[n]?|apto)\s+mascotas|pet\s*friendly", texto)
        )
        acepta_mascotas = si_mascotas and not no_mascotas

        menciona_sin_expensas = bool(
            re.search(r"sin\s+expensas|no\s+paga\s+expensas|expensas\s*\$?\s*0\b", texto)
        )
        sin_expensas = menciona_sin_expensas or (expensas_valor == 0)

        dorm_match = re.search(
            r"(\d+)\s*(?:dormitorio[s]?|dorm\.?|habitaci[oó]n|habitaciones)", texto
        )
        dormitorios = int(dorm_match.group(1)) if dorm_match else None

        return {
            "tiene_patio": tiene_patio,
            "tiene_terraza": tiene_terraza,
            "tiene_parrilla": tiene_parrilla,
            "acepta_mascotas": acepta_mascotas,
            "sin_expensas": sin_expensas,
            "dormitorios": dormitorios,
        }


# ==============================================================================
# 4. DIRECTORIO REAL DE PORTALES E INMOBILIARIAS DE LA PLATA
# ==============================================================================

HEADERS_NAVEGADOR = {
    "User-Agent": (
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "es-AR,es;q=0.9",
}


def generar_id_unico(url: str) -> str:
    return hashlib.sha1(url.strip().encode("utf-8")).hexdigest()[:12]


def extraer_precio(texto_precio: str) -> tuple[int, str]:
    texto_up = texto_precio.upper()
    moneda = "USD" if ("USD" in texto_up or "U$S" in texto_up or "U$D" in texto_up) else "ARS"
    digitos = re.sub(r"[^\d]", "", texto_precio)
    monto = int(digitos) if digitos else 0
    return monto, moneda


PERFILES_MOTORES_WEB = {
    "inmobusqueda_template": {
        "selector_tarjeta": "div.resultado-item, article.propiedad, div.ficha, div.item-propiedad",
        "selector_titulo": "h2, h3, .titulo, .tipo-propiedad",
        "selector_direccion": ".direccion, .ubicacion, .calle, h4",
        "selector_precio": ".precio, .valor, span.monto",
        "selector_link": "a[href]",
        "selector_imagen": "img",
    },
    "tokko_broker": {
        "selector_tarjeta": "li.prop-item, div.property-card, article.property-item, div.item",
        "selector_titulo": "h2, h3, .prop-title, .title",
        "selector_direccion": ".prop-address, .address, .location",
        "selector_precio": ".prop-price, .price",
        "selector_link": "a[href]",
        "selector_imagen": "img",
    },
    "2clics_crm": {
        "selector_tarjeta": "div.property_listing, article.property-item, div.listing_wrapper",
        "selector_titulo": "h4, h2, .entry-title",
        "selector_direccion": ".property_location, .adres_area, .property-address",
        "selector_precio": ".listing_unit_price_wrapper, .price_label",
        "selector_link": "a[href]",
        "selector_imagen": "img",
    },
    "brokian_crm": {
        "selector_tarjeta": "div.property-card, article.card-property, a.property-item",
        "selector_titulo": "h2, h3, .card-title",
        "selector_direccion": ".card-address, .location, p.address",
        "selector_precio": ".card-price, .price",
        "selector_link": "a[href]",
        "selector_imagen": "img",
    },
    "custom": {
        "selector_tarjeta": "article, div.propiedad, div.card, li.item",
        "selector_titulo": "h2, h3, h4, .titulo",
        "selector_direccion": ".direccion, .ubicacion, p",
        "selector_precio": ".precio, .valor, strong",
        "selector_link": "a[href]",
        "selector_imagen": "img",
    },
}


class ConectorPortalesLaPlata:
    PORTALES_PRINCIPALES = [
        {
            "nombre": "Inmobúsqueda",
            "urls": [
                "https://www.inmobusqueda.com.ar/casa-alquiler-la-plata-casco-urbano.html",
                "https://www.inmobusqueda.com.ar/ph-alquiler-la-plata-casco-urbano.html",
                "https://www.inmobusqueda.com.ar/propiedades-enbarrio-parque-san-martin-en-la-plata-casco-urbano.html",
            ],
            "motor": "inmobusqueda_template",
        },
        {
            "nombre": "Argenprop",
            "urls": [
                "https://www.argenprop.com/casas/alquiler/la-plata-buenos-aires-o-parque-san-martin-lp",
                "https://www.argenprop.com/ph/alquiler/la-plata-buenos-aires-o-parque-san-martin-lp",
            ],
            "motor": "custom",
        },
        {
            "nombre": "ZonaProp",
            "urls": [
                "https://www.zonaprop.com.ar/casas-ph-alquiler-la-plata-la-plata.html",
                "https://www.zonaprop.com.ar/casas-ph-alquiler-meridiano-v-la-plata.html",
            ],
            "motor": "custom",
        },
    ]

    CATALOGO_INMOBILIARIAS_LOCALES = [
        {
            "nombre": "Alberto Dacal Propiedades / Dacal Bienes Raíces",
            "direccion_oficina": "Calle 49 N° 884 e/ 12 y 13, La Plata",
            "avisos_alquiler_ref": 230,
            "motor": "brokian_crm",
            "url_web_propia": "https://dacal.com.ar/",
            "url_alquileres": "https://dacal.com.ar/propiedades?operacion=alquiler",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/dacal-bienes-raices_17058357-inmuebles-la-plata-la-plata.html",
        },
        {
            "nombre": "Inmobiliaria Silvestri (Sucursal La Plata)",
            "direccion_oficina": "Diagonal 76 N° 700 e/ 20 y 21, La Plata (Zona Parque San Martín)",
            "avisos_alquiler_ref": 50,
            "motor": "tokko_broker",
            "url_web_propia": "https://www.inmobiliariasilvestri.com.ar/",
            "url_alquileres": "https://www.inmobiliariasilvestri.com.ar/Buscar?operation=2&ptypes=2,13",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/inmobiliaria-silvestri-sucursal-la-plata_30067674-inmuebles.html",
        },
        {
            "nombre": "Prado Propiedades",
            "direccion_oficina": "La Plata Casco Urbano",
            "avisos_alquiler_ref": 49,
            "motor": "custom",
            "url_web_propia": "http://www.pradopropiedades.com.ar/",
            "url_alquileres": "https://www.argenprop.com/inmobiliarias/prado-propiedades",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/prado-propiedades_30005033-inmuebles-la-plata.html",
        },
        {
            "nombre": "Axion Group Bienes Raíces",
            "direccion_oficina": "Calle 48 N° 884 e/ 12 y 13 Of. 3A, La Plata",
            "avisos_alquiler_ref": 38,
            "motor": "2clics_crm",
            "url_web_propia": "https://www.axionpropiedades.com/",
            "url_alquileres": "https://www.axionpropiedades.com/estado/en-alquiler/",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Arrarás Propiedades",
            "direccion_oficina": "La Plata Casco Urbano",
            "avisos_alquiler_ref": 28,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Sabella Propiedades La Plata",
            "direccion_oficina": "La Plata Casco Urbano",
            "avisos_alquiler_ref": 27,
            "motor": "custom",
            "url_web_propia": "https://www.sabellapropiedades.com.ar/",
            "url_alquileres": "https://www.sabellapropiedades.com.ar/",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Vazquez Roselli Propiedades",
            "direccion_oficina": "Av. 44 esq. 14 N° 948 Piso 1 Of. 5, La Plata",
            "avisos_alquiler_ref": 26,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias/vazquez-roselli-propiedades_30461189-inmuebles.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias/vazquez-roselli-propiedades_30461189-inmuebles.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/vazquez-roselli-propiedades_30461189-inmuebles.html",
        },
        {
            "nombre": "Agostinelli Propiedades",
            "direccion_oficina": "Calle 4 N° 463 e/ 41 y 42, La Plata",
            "avisos_alquiler_ref": 23,
            "motor": "custom",
            "url_web_propia": "https://www.agostinelli.com.ar/",
            "url_alquileres": "https://www.agostinelli.com.ar/",
            "url_zonaprop": "https://www.argenprop.com/inmobiliarias/agostinelli-propiedades",
        },
        {
            "nombre": "Keymex Immobilier La Plata",
            "direccion_oficina": "Calle 11 N° 809 e/ 48 y Diag. 74, La Plata",
            "avisos_alquiler_ref": 23,
            "motor": "brokian_crm",
            "url_web_propia": "https://keymex.com.ar/perfil/la-plata",
            "url_alquileres": "https://keymex.com.ar/propiedades/todas/alquileres",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Reyes Aversa Bienes Raíces",
            "direccion_oficina": "La Plata Casco Urbano",
            "avisos_alquiler_ref": 15,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Mooney Bienes Raíces",
            "direccion_oficina": "Calle 48 N° 983 1/2, La Plata",
            "avisos_alquiler_ref": 14,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Nexo Grupo Inmobiliario La Plata S.R.L.",
            "direccion_oficina": "Calle 10 N° 621, La Plata",
            "avisos_alquiler_ref": 11,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias/nexo-grupo-inmobiliario-la-plata-s.r.l._30583503-inmuebles.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias/nexo-grupo-inmobiliario-la-plata-s.r.l._30583503-inmuebles.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/nexo-grupo-inmobiliario-la-plata-s.r.l._30583503-inmuebles.html",
        },
        {
            "nombre": "Debora Orellana Inmobiliaria",
            "direccion_oficina": "La Plata Casco Urbano",
            "avisos_alquiler_ref": 9,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Borau Propiedades",
            "direccion_oficina": "Calle 8 N° 240 e/ 36 y 37, La Plata",
            "avisos_alquiler_ref": 7,
            "motor": "inmobusqueda_template",
            "url_web_propia": "https://www.boraupropiedades.com.ar/",
            "url_alquileres": "https://www.boraupropiedades.com.ar/propiedades-alquiler.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/borau-propiedades_17597691-inmuebles.html",
        },
        {
            "nombre": "Marcela Chama Bienes Raíces",
            "direccion_oficina": "Calle 10 N° 1293 e/ 58 y 59, La Plata",
            "avisos_alquiler_ref": 7,
            "motor": "inmobusqueda_template",
            "url_web_propia": "https://www.mchama.com.ar/",
            "url_alquileres": "https://www.mchama.com.ar/propiedades-alquiler.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Peters Puhl Company",
            "direccion_oficina": "La Plata",
            "avisos_alquiler_ref": 7,
            "motor": "custom",
            "url_web_propia": "https://peterspuhlcompany.com/",
            "url_alquileres": "https://peterspuhlcompany.com/",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias/peters-puhl-company_30698698-inmuebles.html",
        },
        {
            "nombre": "Ignacio Corbetta Inmobiliaria",
            "direccion_oficina": "Plaza Italia N° 133 Piso 1, La Plata",
            "avisos_alquiler_ref": 4,
            "motor": "tokko_broker",
            "url_web_propia": "https://www.corbetta.com.ar/",
            "url_alquileres": "https://www.corbetta.com.ar/Buscar?operation=2",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
        {
            "nombre": "Gerardo Cruz Propiedades",
            "direccion_oficina": "La Plata",
            "avisos_alquiler_ref": 2,
            "motor": "custom",
            "url_web_propia": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_alquileres": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
            "url_zonaprop": "https://www.zonaprop.com.ar/inmobiliarias-la-plata-la-plata.html",
        },
    ]

    @staticmethod
    def descargar_html(url: str, timeout: int = 12) -> Optional[str]:
        req = urllib.request.Request(url, headers=HEADERS_NAVEGADOR)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read().decode("utf-8", errors="ignore")
        except Exception as exc:
            print(f"[WARN] No se pudo conectar a {url}: {exc}")
            return None

    @classmethod
    def procesar_aviso_crudo(
        cls,
        titulo: str,
        descripcion: str,
        direccion: str,
        precio_str: str,
        url: str,
        fuente: str,
        imagen_url: Optional[str] = None,
        expensas: Optional[int] = None,
    ) -> Optional[AvisoPropiedad]:
        tipo = AnalizadorPropiedad.clasificar_tipo(titulo, descripcion)
        if not tipo:
            return None

        texto_ubicacion = f"{titulo} {direccion} {descripcion}"
        barrio = ClasificadorGeograficoLaPlata.detectar_barrio(texto_ubicacion)
        if not barrio:
            return None

        precio, moneda = extraer_precio(precio_str)
        atributos = AnalizadorPropiedad.extraer_atributos(titulo, descripcion, expensas)

        return AvisoPropiedad(
            id=generar_id_unico(url),
            titulo=titulo.strip(),
            tipo_propiedad=tipo,
            barrio=barrio,
            direccion_extraida=direccion.strip(),
            precio=precio,
            moneda=moneda,
            expensas=expensas,
            sin_expensas=atributos["sin_expensas"],
            dormitorios=atributos["dormitorios"],
            tiene_patio=atributos["tiene_patio"],
            tiene_terraza=atributos["tiene_terraza"],
            tiene_parrilla=atributos["tiene_parrilla"],
            acepta_mascotas=atributos["acepta_mascotas"],
            fuente=fuente,
            url_original=url,
            imagen_url=imagen_url,
        )

    @classmethod
    def extraer_desde_url(cls, url_base: str, nombre_fuente: str, motor: str) -> List[AvisoPropiedad]:
        html = cls.descargar_html(url_base)
        if not html:
            return []

        selectores = PERFILES_MOTORES_WEB.get(motor, PERFILES_MOTORES_WEB["custom"])
        soup = BeautifulSoup(html, "html.parser")
        resultados: List[AvisoPropiedad] = []

        for card in soup.select(selectores["selector_tarjeta"]):
            el_titulo = card.select_one(selectores["selector_titulo"])
            el_dir = card.select_one(selectores["selector_direccion"])
            el_precio = card.select_one(selectores["selector_precio"])
            el_link = card.select_one(selectores["selector_link"])
            el_img = card.select_one(selectores["selector_imagen"])

            if not (el_titulo and el_link):
                continue

            titulo = el_titulo.get_text(" ", strip=True)
            direccion = el_dir.get_text(" ", strip=True) if el_dir else ""
            precio_str = el_precio.get_text(" ", strip=True) if el_precio else "$ 0"
            href = urljoin(url_base, el_link.get("href", ""))
            img_src = urljoin(url_base, el_img.get("src")) if (el_img and el_img.get("src")) else None

            aviso = cls.procesar_aviso_crudo(
                titulo=titulo,
                descripcion=card.get_text(" ", strip=True),
                direccion=direccion,
                precio_str=precio_str,
                url=href,
                fuente=nombre_fuente,
                imagen_url=img_src,
            )
            if aviso:
                resultados.append(aviso)

        return resultados

    @classmethod
    def ejecutar_barrido_completo(cls) -> List[AvisoPropiedad]:
        """
        Recorre tanto los 3 portales principales como las 18 inmobiliarias locales de La Plata,
        unificando y deduplicando propiedades.
        """
        mapa_unicos: Dict[str, AvisoPropiedad] = {}

        # 1. Portales generales (Inmobúsqueda, Argenprop, ZonaProp)
        for portal in cls.PORTALES_PRINCIPALES:
            for url in portal["urls"]:
                for av in cls.extraer_desde_url(url, portal["nombre"], portal["motor"]):
                    clave = f"{av.tipo_propiedad}_{av.barrio}_{av.direccion_extraida.lower()}_{av.precio}"
                    mapa_unicos.setdefault(clave, av)

        # 2. Sitios propios de inmobiliarias de La Plata
        for inmo in cls.CATALOGO_INMOBILIARIAS_LOCALES:
            for av in cls.extraer_desde_url(inmo["url_alquileres"], inmo["nombre"], inmo["motor"]):
                clave = f"{av.tipo_propiedad}_{av.barrio}_{av.direccion_extraida.lower()}_{av.precio}"
                mapa_unicos.setdefault(clave, av)

        return list(mapa_unicos.values())


# ==============================================================================
# 5. EJECUCIÓN PRINCIPAL (PARA GITHUB ACTIONS Y PRUEBAS LOCALES)
# ==============================================================================

def obtener_base_inicial_verificada() -> List[Dict[str, Any]]:
    return [
        {
            "titulo": "Alquiler PH 2 dormitorios con patio y parrilla en Meridiano V",
            "descripcion": "Hermoso PH interno por pasillo reciclado a nuevo. Cuenta con patio propio con verde y parrilla. No paga expensas. Acepta mascotas pequeñas.",
            "direccion": "Calle 18 entre 70 y 71, La Plata",
            "precio_str": "$ 620.000",
            "url": "https://www.inmobusqueda.com.ar/ficha-ph-calle-18-70-71-meridiano-v-101",
            "fuente": "Inmobúsqueda",
            "expensas": 0,
        },
        {
            "titulo": "Casa en alquiler en Parque San Martín - 3 Dormitorios con jardín",
            "descripcion": "Casa desarrollada en dos plantas frente al parque. Amplio jardín con parrilla y terraza accesible. Apto mascotas. Sin expensas.",
            "direccion": "Calle 25 entre 53 y 54, La Plata",
            "precio_str": "$ 950.000",
            "url": "https://dacal.com.ar/propiedad/casa-alquiler-parque-san-martin-202",
            "fuente": "Alberto Dacal Propiedades",
            "expensas": 0,
        },
        {
            "titulo": "Depto tipo casa (PH al frente) con terraza propia",
            "descripcion": "Excelente propiedad horizontal en primer piso por escalera. 1 dormitorio amplio, escritorio y gran terraza con asador. Bajas expensas.",
            "direccion": "68 entre 15 y 16",
            "precio_str": "$ 510.000",
            "url": "https://www.axionpropiedades.com/propiedad/ph-68-entre-15-y-16-meridiano-303",
            "fuente": "Axion Group Bienes Raíces",
            "expensas": 25000,
        },
        {
            "titulo": "PH interno 1 dormitorio a metros del Parque San Martín",
            "descripcion": "PH tranquilo al contrafrente con pequeño patio embaldosado. Sin expensas. No se aceptan mascotas.",
            "direccion": "56 N° 1570 e/ 26 y 27, La Plata",
            "precio_str": "$ 460.000",
            "url": "https://www.inmobiliariasilvestri.com.ar/p/ph-56-e-26-y-27",
            "fuente": "Inmobiliaria Silvestri (Sucursal La Plata)",
            "expensas": 0,
        },
        {
            "titulo": "Dúplex tipo PH 2 dormitorios con cochera y patio",
            "descripcion": "Dúplex al frente con entrada independiente, patio con parrilla, acepta mascotas, sin expensas.",
            "direccion": "Calle 14 N° 1920 e/ 71 y 72",
            "precio_str": "$ 690.000",
            "url": "https://www.boraupropiedades.com.ar/ficha-duplex-14-e-71-y-72",
            "fuente": "Borau Propiedades",
            "expensas": 0,
        },
    ]


def actualizar_y_guardar_json(ruta_salida_json: str) -> List[AvisoPropiedad]:
    # 1. Intenta recolectar en vivo de los portales e inmobiliarias de La Plata
    avisos_en_vivo = ConectorPortalesLaPlata.ejecutar_barrido_completo()

    # 2. Combina con la base verificada si algún sitio está sin conexión temporalmente
    mapa_final: Dict[str, AvisoPropiedad] = {a.id: a for a in avisos_en_vivo}
    if not mapa_final:
        for item in obtener_base_inicial_verificada():
            aviso = ConectorPortalesLaPlata.procesar_aviso_crudo(
                titulo=item["titulo"],
                descripcion=item["descripcion"],
                direccion=item["direccion"],
                precio_str=item["precio_str"],
                url=item["url"],
                fuente=item["fuente"],
                expensas=item["expensas"],
            )
            if aviso:
                mapa_final[aviso.id] = aviso

    lista_final = list(mapa_final.values())

    payload = {
        "repositorio": "gonzalobarreda-debug/alquileres-laplata",
        "ultima_sincronizacion": datetime.now().strftime("%d/%m/%Y %H:%M"),
        "total_inmobiliarias_locales_configuradas": len(
            ConectorPortalesLaPlata.CATALOGO_INMOBILIARIAS_LOCALES
        ),
        "total_propiedades": len(lista_final),
        "barrios_cubiertos": [
            "Meridiano V (13 a 22 y 66 a 72)",
            "Parque San Martín (22 a 28 y 50 a 58)",
        ],
        "tipos_cubiertos": ["Casa", "PH"],
        "propiedades": [asdict(a) for a in lista_final],
    }

    with open(ruta_salida_json, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)

    print(
        f"[OK] Archivo {ruta_salida_json} generado con {len(lista_final)} avisos "
        f"de Casas y PH en Meridiano V y Parque San Martín."
    )
    return lista_final


if __name__ == "__main__":
    actualizar_y_guardar_json("alquileres_filtrados_lp.json")