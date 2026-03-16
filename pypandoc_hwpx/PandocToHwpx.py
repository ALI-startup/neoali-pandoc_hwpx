import copy
import re
import sys
import os
import io
import shutil
import zipfile
import json
import xml.sax.saxutils as saxutils
import xml.etree.ElementTree as ET
import pypandoc
from PIL import Image
from html.parser import HTMLParser

class HTMLStyleExtractor(HTMLParser):
    """Extract inline styles from HTML elements"""
    def __init__(self):
        super().__init__()
        self.style_stack = []
        self.text_segments = []
        self.para_styles = []

    def handle_starttag(self, tag, attrs):
        style_dict = {}
        for attr, value in attrs:
            if attr == 'style':
                for style_part in value.split(';'):
                    if ':' in style_part:
                        key, val = style_part.split(':', 1)
                        key = key.strip().lower()
                        val = val.strip()
                        style_dict[key] = val
        if tag == 'p':
            self.para_styles.append(style_dict.copy())
        if tag == 'strong' or tag == 'b':
            style_dict['font-weight'] = 'bold'
        elif tag == 'em' or tag == 'i':
            style_dict['font-style'] = 'italic'
        elif tag == 'u':
            style_dict['text-decoration'] = 'underline'
        self.style_stack.append((tag, style_dict))

    def handle_endtag(self, tag):
        if self.style_stack and self.style_stack[-1][0] == tag:
            self.style_stack.pop()

    def handle_data(self, data):
        if data.strip():
            combined_style = {}
            for tag, style in self.style_stack:
                combined_style.update(style)
            self.text_segments.append((data, combined_style.copy()))


class HTMLParagraphStyleExtractor(HTMLParser):
    """Extract paragraph-level styles from HTML before Pandoc processing"""
    def __init__(self):
        super().__init__()
        self.para_styles = {}
        self.current_para_content = []
        self.current_para_styles = {}
        self.in_paragraph = False

    def handle_starttag(self, tag, attrs):
        if tag == 'p':
            self.in_paragraph = True
            self.current_para_content = []
            attrs_dict = dict(attrs)
            self.current_para_styles = {}
            if 'style' in attrs_dict:
                for style_part in attrs_dict['style'].split(';'):
                    if ':' in style_part:
                        key, val = style_part.split(':', 1)
                        key = key.strip().lower()
                        val = val.strip()
                        if key == 'padding-left':
                            self.current_para_styles['padding-left'] = val
                        elif key == 'margin-left':
                            self.current_para_styles['margin-left'] = val
                        elif key == 'text-indent':
                            self.current_para_styles['text-indent'] = val

    def handle_endtag(self, tag):
        if tag == 'p' and self.in_paragraph:
            content_text = ''.join(self.current_para_content).strip()
            if content_text and self.current_para_styles:
                self.para_styles[content_text[:100]] = self.current_para_styles.copy()
            self.in_paragraph = False
            self.current_para_content = []
            self.current_para_styles = {}

    def handle_data(self, data):
        if self.in_paragraph:
            self.current_para_content.append(data)


class PandocToHwpx:
    def __init__(self, json_ast=None, header_xml_content=None, html_content=None):
        self.ast = json_ast
        self.output = []
        self.header_xml_content = header_xml_content
        self.html_content = html_content

        self.html_para_styles = {}
        if html_content:
            self._extract_html_para_styles(html_content)

        self.STYLE_MAP = {'Normal': 0, 'Header1': 1, 'Header2': 2, 'Header3': 3,
                          'Header4': 4, 'Header5': 5, 'Header6': 6}
        self.dynamic_style_map = {}
        self.normal_style_id = 0
        self.normal_para_pr_id = 1

        self.header_tree = None
        self.header_root = None
        self.namespaces = {
            'hh': 'http://www.hancom.co.kr/hwpml/2011/head',
            'hp': 'http://www.hancom.co.kr/hwpml/2011/paragraph',
            'hc': 'http://www.hancom.co.kr/hwpml/2011/core',
            'hs': 'http://www.hancom.co.kr/hwpml/2011/section'
        }
        self.char_pr_cache = {}
        self.max_char_pr_id = 0
        self.max_para_pr_id = 0
        self.max_border_fill_id = 0
        self.para_pr_cache = {}
        self.images = []
        self.table_border_fill_id = None

        self.title = None
        self._extract_metadata()

        if self.header_xml_content:
            self._parse_styles_and_init_xml(self.header_xml_content)

    # ------------------------------------------------------------------ helpers

    def _extract_html_para_styles(self, html_content):
        try:
            extractor = HTMLParagraphStyleExtractor()
            extractor.feed(html_content)
            self.html_para_styles = extractor.para_styles
        except Exception as e:
            print(f"[Warn] Failed to extract HTML paragraph styles: {e}", file=sys.stderr)

    def _extract_metadata(self):
        if not self.ast:
            return
        meta = self.ast.get('meta', {})
        if 'title' in meta:
            t_obj = meta['title']
            if t_obj.get('t') == 'MetaInlines':
                self.title = self._get_plain_text(t_obj.get('c', []))
            elif t_obj.get('t') == 'MetaString':
                self.title = t_obj.get('c', "")

    def _get_plain_text(self, inlines):
        if not isinstance(inlines, list):
            return ""
        text = []
        for item in inlines:
            t = item.get('t')
            c = item.get('c')
            if t == 'Str':
                text.append(c)
            elif t == 'Space':
                text.append(" ")
            elif t in ['Strong', 'Emph', 'Underline', 'Strikeout',
                       'Superscript', 'Subscript', 'SmallCaps']:
                text.append(self._get_plain_text(c))
            elif t == 'Span':
                text.append(self._get_plain_text(c[1]))
            elif t == 'Link':
                text.append(self._get_plain_text(c[1]))
            elif t == 'Image':
                text.append(self._get_plain_text(c[1]))
            elif t == 'Code':
                text.append(c[1])
            elif t == 'Quoted':
                text.append('"' + self._get_plain_text(c[1]) + '"')
            elif t in ('LineBreak', 'SoftBreak'):
                text.append("\n")
        return "".join(text)

    def _convert_color_to_hwp(self, color):
        if not color:
            return '#000000'
        color_map = {
            'red': '#FF0000', 'green': '#008000', 'blue': '#0000FF',
            'black': '#000000', 'white': '#FFFFFF', 'yellow': '#FFFF00',
            'cyan': '#00FFFF', 'magenta': '#FF00FF', 'orange': '#FFA500',
            'purple': '#800080', 'pink': '#FFC0CB', 'brown': '#A52A2A',
            'gray': '#808080', 'grey': '#808080', 'lime': '#00FF00',
            'navy': '#000080', 'teal': '#008080', 'silver': '#C0C0C0',
            'maroon': '#800000', 'olive': '#808000',
        }
        color = color.lower().strip()
        if color in color_map:
            return color_map[color]
        if color.startswith('#'):
            if len(color) == 7:
                return color.upper()
            elif len(color) == 4:
                r, g, b = color[1], color[2], color[3]
                return f'#{r}{r}{g}{g}{b}{b}'.upper()
        if color.startswith('rgb'):
            match = re.search(r'rgb\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', color)
            if match:
                r, g, b = int(match.group(1)), int(match.group(2)), int(match.group(3))
                return f'#{r:02X}{g:02X}{b:02X}'
        return '#000000'

    def _convert_size_to_hwp(self, size_str):
        if not size_str:
            return None
        size_str = size_str.lower().strip()
        if size_str.endswith('pt'):
            try:
                return int(float(size_str[:-2]))
            except:
                return None
        if size_str.endswith('px'):
            try:
                return int(float(size_str[:-2]) * 72 / 96)
            except:
                return None
        try:
            return int(float(size_str))
        except:
            return None

    def _extract_style_from_attr(self, attr):
        styles = {}
        if len(attr) < 3:
            return styles
        for cls in attr[1]:
            cls_lower = cls.lower()
            if 'bold' in cls_lower or 'strong' in cls_lower:
                styles['bold'] = True
            if 'italic' in cls_lower or 'emph' in cls_lower:
                styles['italic'] = True
            if 'underline' in cls_lower:
                styles['underline'] = True
        for key, val in attr[2]:
            if key.lower() == 'style':
                for part in val.split(';'):
                    if ':' in part:
                        sk, sv = part.split(':', 1)
                        sk, sv = sk.strip().lower(), sv.strip()
                        if sk == 'color':
                            styles['color'] = self._convert_color_to_hwp(sv)
                        elif sk == 'font-size':
                            styles['font-size'] = self._convert_size_to_hwp(sv)
                        elif sk == 'font-weight' and 'bold' in sv.lower():
                            styles['bold'] = True
                        elif sk == 'font-style' and 'italic' in sv.lower():
                            styles['italic'] = True
                        elif sk == 'text-decoration':
                            if 'underline' in sv.lower():
                                styles['underline'] = True
                            if 'line-through' in sv.lower():
                                styles['strikeout'] = True
                        elif sk == 'padding-left':
                            styles['padding-left'] = self._convert_size_to_hwp(sv)
                        elif sk == 'margin-left':
                            styles['margin-left'] = self._convert_size_to_hwp(sv)
                        elif sk == 'text-indent':
                            styles['text-indent'] = self._convert_size_to_hwp(sv)
        return styles

    def _parse_styles_and_init_xml(self, header_xml_content):
        try:
            for prefix, uri in self.namespaces.items():
                ET.register_namespace(prefix, uri)
            self.header_tree = ET.ElementTree(ET.fromstring(header_xml_content))
            self.header_root = self.header_tree.getroot()

            for cp in self.header_root.findall('.//hh:charPr', self.namespaces):
                cid = int(cp.get('id', 0))
                if cid > self.max_char_pr_id:
                    self.max_char_pr_id = cid
            for pp in self.header_root.findall('.//hh:paraPr', self.namespaces):
                pid = int(pp.get('id', 0))
                if pid > self.max_para_pr_id:
                    self.max_para_pr_id = pid
            for bf in self.header_root.findall('.//hh:borderFill', self.namespaces):
                bid = int(bf.get('id', 0))
                if bid > self.max_border_fill_id:
                    self.max_border_fill_id = bid

            for style in self.header_root.findall('.//hh:style', self.namespaces):
                name = style.get('name', '')
                sid = int(style.get('id', 0))
                if name in ('Normal', '바탕글'):
                    self.normal_style_id = sid
                    self.normal_para_pr_id = int(style.get('paraPrIDRef', 1))
                self.dynamic_style_map[name] = sid
        except Exception as e:
            print(f"[Warn] Failed to parse header.xml: {e}", file=sys.stderr)

    # ------------------------------------------------------------------ charPr

    def _get_or_create_char_pr(self, base_char_pr_id=0, active_formats=None,
                                color=None, font_size=None):
        if active_formats is None:
            active_formats = set()
        base_char_pr_id = str(base_char_pr_id)
        cache_key = (base_char_pr_id, frozenset(active_formats), color, font_size)
        if cache_key in self.char_pr_cache:
            return self.char_pr_cache[cache_key]
        if not active_formats and not color and not font_size:
            return base_char_pr_id
        if self.header_root is None:
            return base_char_pr_id

        base_node = self.header_root.find(
            f'.//hh:charPr[@id="{base_char_pr_id}"]', self.namespaces)
        if base_node is None:
            base_node = self.header_root.find('.//hh:charPr[@id="0"]', self.namespaces)
        if base_node is None:
            return base_char_pr_id

        new_node = copy.deepcopy(base_node)
        self.max_char_pr_id += 1
        new_id = str(self.max_char_pr_id)
        new_node.set('id', new_id)

        if color:
            new_node.set('textColor', color)
            ul = new_node.find('hh:underline', self.namespaces)
            if ul is not None:
                ul.set('color', color)
        if font_size:
            new_node.set('height', str(font_size * 100))
        if 'BOLD' in active_formats:
            if new_node.find('hh:bold', self.namespaces) is None:
                ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}bold')
        if 'ITALIC' in active_formats:
            if new_node.find('hh:italic', self.namespaces) is None:
                ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}italic')
        if 'UNDERLINE' in active_formats:
            ul = new_node.find('hh:underline', self.namespaces)
            if ul is None:
                ul = ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}underline')
            ul.set('type', 'BOTTOM')
            ul.set('shape', 'SOLID')
            ul.set('color', color if color else '#000000')
        if 'STRIKEOUT' in active_formats:
            st = new_node.find('hh:strikeout', self.namespaces)
            if st is None:
                st = ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}strikeout')
            st.set('shape', 'CONTINUOUS')
            st.set('color', color if color else '#000000')
        if 'SUPERSCRIPT' in active_formats:
            sub = new_node.find('hh:subscript', self.namespaces)
            if sub is not None:
                new_node.remove(sub)
            if new_node.find('hh:supscript', self.namespaces) is None:
                ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}supscript')
        elif 'SUBSCRIPT' in active_formats:
            sup = new_node.find('hh:supscript', self.namespaces)
            if sup is not None:
                new_node.remove(sup)
            if new_node.find('hh:subscript', self.namespaces) is None:
                ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}subscript')

        char_props = self.header_root.find('.//hh:charProperties', self.namespaces)
        if char_props is not None:
            char_props.append(new_node)
        self.char_pr_cache[cache_key] = new_id
        return new_id

    # ------------------------------------------------------------------ paraPr

    def _get_or_create_para_pr(self, padding_left=0, text_indent=0):
        left_margin = int(padding_left * 100) if padding_left else 0
        indent_val = int(text_indent * 100) if text_indent else 0
        cache_key = (left_margin, indent_val)
        if cache_key in self.para_pr_cache:
            return self.para_pr_cache[cache_key]
        if left_margin == 0 and indent_val == 0:
            return str(self.normal_para_pr_id)
        if self.header_root is None:
            return str(self.normal_para_pr_id)

        base_node = self.header_root.find(
            f'.//hh:paraPr[@id="{self.normal_para_pr_id}"]', self.namespaces)
        if base_node is None:
            base_node = self.header_root.find('.//hh:paraPr[@id="0"]', self.namespaces)
        if base_node is None:
            return str(self.normal_para_pr_id)

        new_node = copy.deepcopy(base_node)
        self.max_para_pr_id += 1
        new_id = str(self.max_para_pr_id)
        new_node.set('id', new_id)

        HP = 'http://www.hancom.co.kr/hwpml/2011/paragraph'
        HH = 'http://www.hancom.co.kr/hwpml/2011/head'
        HC = 'http://www.hancom.co.kr/hwpml/2011/core'

        switch_elem = new_node.find('hp:switch', self.namespaces)
        if switch_elem is None:
            switch_elem = ET.SubElement(new_node, f'{{{HP}}}switch')

        for container, make_if_missing in [
            (switch_elem.find('hp:case', self.namespaces), True),
            (switch_elem.find('hp:default', self.namespaces), True),
        ]:
            pass  # handled below

        # case
        case_elem = switch_elem.find('hp:case', self.namespaces)
        if case_elem is None:
            case_elem = ET.SubElement(switch_elem, f'{{{HP}}}case')
            case_elem.set(f'{{{HP}}}required-namespace',
                          'http://www.hancom.co.kr/hwpml/2016/HwpUnitChar')
        margin_elem = case_elem.find('hh:margin', self.namespaces)
        if margin_elem is None:
            margin_elem = ET.SubElement(case_elem, f'{{{HH}}}margin')
        for tag, val in [('hc:intent', indent_val), ('hc:left', left_margin)]:
            elem = margin_elem.find(tag, self.namespaces)
            if elem is None:
                elem = ET.SubElement(margin_elem,
                                     f'{{{HC}}}{tag.split(":")[1]}')
            elem.set('value', str(val))
            elem.set('unit', 'HWPUNIT')

        # default
        default_elem = switch_elem.find('hp:default', self.namespaces)
        if default_elem is None:
            default_elem = ET.SubElement(switch_elem, f'{{{HP}}}default')
        def_margin = default_elem.find('hh:margin', self.namespaces)
        if def_margin is None:
            def_margin = ET.SubElement(default_elem, f'{{{HH}}}margin')
        for tag, val in [('hc:intent', indent_val), ('hc:left', left_margin)]:
            elem = def_margin.find(tag, self.namespaces)
            if elem is None:
                elem = ET.SubElement(def_margin,
                                     f'{{{HC}}}{tag.split(":")[1]}')
            elem.set('value', str(val))
            elem.set('unit', 'HWPUNIT')

        para_props = self.header_root.find('.//hh:paraProperties', self.namespaces)
        if para_props is not None:
            para_props.append(new_node)
        self.para_pr_cache[cache_key] = new_id
        return new_id

    # 1 HWPUNIT ≈ 1/7200 inch; 3600 ≈ 0.5 inch / ~1.27 cm
    LIST_INDENT_HWPUNIT = 3600

    def _get_para_pr_for_list_depth(self, depth):
        """Return paraPrIDRef with left-margin for the given list depth level."""
        left_margin = (depth + 1) * self.LIST_INDENT_HWPUNIT
        cache_key = (left_margin, 0)
        if cache_key in self.para_pr_cache:
            return self.para_pr_cache[cache_key]
        new_id = self._create_para_pr_with_margin(left_margin)
        self.para_pr_cache[cache_key] = new_id
        return new_id

    def _get_left_margin_from_para_pr(self, para_pr_id):
        """Return the left-margin HWPUNIT value stored in the given paraPrIDRef."""
        # Fast path via cache
        for cache_key, pid in self.para_pr_cache.items():
            if not isinstance(cache_key, tuple) or len(cache_key) != 2:
                continue
            left_margin, _indent = cache_key
            if pid == str(para_pr_id):
                return left_margin
        # Slow path via XML
        if self.header_root is None:
            return 0
        node = self.header_root.find(f'.//hh:paraPr[@id="{para_pr_id}"]', self.namespaces)
        if node is None:
            return 0
        for path in ('hp:switch/hp:default/hh:margin/hc:left',
                     'hp:switch/hp:case/hh:margin/hc:left',
                     'hh:margin/hc:left'):
            elem = node.find(path, self.namespaces)
            if elem is not None:
                try:
                    return int(elem.get('value', 0))
                except (TypeError, ValueError):
                    pass
        return 0

    def _create_para_pr_with_margin(self, left_margin_hwpunit):
        """Clone the base paraPr and set left-margin to left_margin_hwpunit."""
        if self.header_root is None:
            return str(self.normal_para_pr_id)

        base_node = self.header_root.find(
            f'.//hh:paraPr[@id="{self.normal_para_pr_id}"]', self.namespaces)
        if base_node is None:
            base_node = self.header_root.find('.//hh:paraPr[@id="0"]', self.namespaces)
        if base_node is None:
            return str(self.normal_para_pr_id)

        new_node = copy.deepcopy(base_node)
        self.max_para_pr_id += 1
        new_id = str(self.max_para_pr_id)
        new_node.set('id', new_id)

        HP = 'http://www.hancom.co.kr/hwpml/2011/paragraph'
        HH = 'http://www.hancom.co.kr/hwpml/2011/head'
        HC = 'http://www.hancom.co.kr/hwpml/2011/core'

        def _set_margin(parent_elem):
            margin = parent_elem.find('hh:margin', self.namespaces)
            if margin is None:
                margin = ET.SubElement(parent_elem, f'{{{HH}}}margin')
            left = margin.find('hc:left', self.namespaces)
            if left is None:
                left = ET.SubElement(margin, f'{{{HC}}}left')
            left.set('value', str(left_margin_hwpunit))
            left.set('unit', 'HWPUNIT')
            indent = margin.find('hc:intent', self.namespaces)
            if indent is None:
                indent = ET.SubElement(margin, f'{{{HC}}}intent')
            indent.set('value', '0')
            indent.set('unit', 'HWPUNIT')

        switch_elem = new_node.find('hp:switch', self.namespaces)
        if switch_elem is None:
            switch_elem = ET.SubElement(new_node, f'{{{HP}}}switch')

        default_elem = switch_elem.find('hp:default', self.namespaces)
        if default_elem is None:
            default_elem = ET.SubElement(switch_elem, f'{{{HP}}}default')
        _set_margin(default_elem)

        case_elem = switch_elem.find('hp:case', self.namespaces)
        if case_elem is None:
            case_elem = ET.SubElement(switch_elem, f'{{{HP}}}case')
            case_elem.set(f'{{{HP}}}required-namespace',
                          'http://www.hancom.co.kr/hwpml/2016/HwpUnitChar')
        _set_margin(case_elem)

        para_props = self.header_root.find('.//hh:paraProperties', self.namespaces)
        if para_props is not None:
            para_props.append(new_node)
        return new_id

    # ------------------------------------------------------------------ utils

    def _escape_text(self, text):
        return saxutils.escape(text)

    def _create_para_start(self, style_id=0, para_pr_id=1, column_break=0, merged=0):
        return (f'<hp:p paraPrIDRef="{para_pr_id}" styleIDRef="{style_id}" '
                f'pageBreak="0" columnBreak="{column_break}" merged="{merged}">')

    def _create_run_start(self, char_pr_id=0):
        return f'<hp:run charPrIDRef="{char_pr_id}">'

    def _create_text_run(self, text, char_pr_id=0):
        return f'{self._create_run_start(char_pr_id)}<hp:t>{self._escape_text(text)}</hp:t></hp:run>'

    # ------------------------------------------------------------------ table

    def _handle_table(self, content, para_pr_id=None):
        """Convert a Pandoc Table AST node to HWPX XML.

        para_pr_id: when supplied (e.g. from a list), the wrapping paragraph
        uses that paraPr so indentation matches the surrounding list text.
        Table width is reduced by the same indent so it stays within the column.
        horzOffset is always 0 — the paraPr left-margin already handles position.
        """
        table_head = content[3]
        table_bodies = content[4]
        table_foot = content[5]

        all_rows = []
        for row in table_head[1]:
            all_rows.append(row)
        for body in table_bodies:
            for row in body[2]:
                all_rows.append(row)
            for row in body[3]:
                all_rows.append(row)
        for row in table_foot[1]:
            all_rows.append(row)

        if not all_rows:
            return ""

        cell_grid = {}
        max_row = 0
        max_col = 0
        for row_idx, row in enumerate(all_rows):
            curr_col = 0
            for cell in row[1]:
                while (row_idx, curr_col) in cell_grid:
                    curr_col += 1
                rowspan = cell[2]
                colspan = cell[3]
                for r in range(rowspan):
                    for c in range(colspan):
                        cell_grid[(row_idx + r, curr_col + c)] = {
                            'origin_row': row_idx,
                            'origin_col': curr_col,
                            'rowspan': rowspan,
                            'colspan': colspan,
                            'blocks': cell[4]
                        }
                max_row = max(max_row, row_idx + rowspan - 1)
                max_col = max(max_col, curr_col + colspan - 1)
                curr_col += colspan

        row_cnt = max_row + 1
        col_cnt = max_col + 1
        TOTAL_TABLE_WIDTH = 45000

        import time, random
        tbl_id = str(int(time.time() * 1000) % 100000000 + random.randint(0, 10000))

        effective_para_pr_id = para_pr_id if para_pr_id is not None else self.normal_para_pr_id

        xml_parts = []
        xml_parts.append(self._create_para_start(
            style_id=self.normal_style_id, para_pr_id=effective_para_pr_id))
        xml_parts.append(self._create_run_start(char_pr_id=0))

        if self.table_border_fill_id is None:
            self._ensure_table_border_fill()

        # Width shrinks by the left-margin so table stays within the column.
        para_left_margin = self._get_left_margin_from_para_pr(effective_para_pr_id)
        effective_width = TOTAL_TABLE_WIDTH - para_left_margin
        col_widths = [int(effective_width / col_cnt) for _ in range(col_cnt)]

        xml_parts.append(
            f'<hp:tbl id="{tbl_id}" zOrder="0" numberingType="TABLE" '
            f'textWrap="TOP_AND_BOTTOM" textFlow="BOTH_SIDES" lock="0" '
            f'dropcapstyle="None" pageBreak="CELL" repeatHeader="1" '
            f'rowCnt="{row_cnt}" colCnt="{col_cnt}" cellSpacing="0" '
            f'borderFillIDRef="{self.table_border_fill_id}" noAdjust="0">')
        xml_parts.append(
            f'<hp:sz width="{effective_width}" widthRelTo="ABSOLUTE" '
            f'height="{row_cnt * 1000}" heightRelTo="ABSOLUTE" protect="0"/>')
        xml_parts.append(
            '<hp:pos treatAsChar="0" affectLSpacing="0" flowWithText="1" '
            'allowOverlap="0" holdAnchorAndSO="0" vertRelTo="PARA" '
            'horzRelTo="PARA" vertAlign="TOP" horzAlign="LEFT" '
            'vertOffset="0" horzOffset="0"/>')
        xml_parts.append('<hp:outMargin left="0" right="0" top="0" bottom="1417"/>')
        xml_parts.append('<hp:inMargin left="510" right="510" top="141" bottom="141"/>')

        processed_cells = set()
        for row_idx in range(row_cnt):
            xml_parts.append('<hp:tr>')
            for col_idx in range(col_cnt):
                if (row_idx, col_idx) not in cell_grid:
                    continue
                ci = cell_grid[(row_idx, col_idx)]
                if ci['origin_row'] != row_idx or ci['origin_col'] != col_idx:
                    continue
                cell_key = (row_idx, col_idx)
                if cell_key in processed_cells:
                    continue
                processed_cells.add(cell_key)

                rowspan = ci['rowspan']
                colspan = ci['colspan']
                cell_width = sum(col_widths[col_idx:col_idx + colspan])
                sublist_id = str(
                    int(time.time() * 100000) % 1000000000 + random.randint(0, 100000))

                cell_xml = self._process_blocks_for_table_cell(ci['blocks'])
                if not cell_xml.strip():
                    cell_xml = (
                        self._create_para_start(
                            style_id=self.normal_style_id, para_pr_id=self.normal_para_pr_id)
                        + '<hp:run charPrIDRef="0"><hp:t></hp:t></hp:run></hp:p>')

                xml_parts.append(
                    f'<hp:tc name="" header="0" hasMargin="0" protect="0" '
                    f'editable="0" dirty="0" borderFillIDRef="{self.table_border_fill_id}">')
                xml_parts.append(
                    f'<hp:subList id="{sublist_id}" textDirection="HORIZONTAL" '
                    f'lineWrap="BREAK" vertAlign="TOP" linkListIDRef="0" '
                    f'linkListNextIDRef="0" textWidth="0" textHeight="0" '
                    f'hasTextRef="0" hasNumRef="0">')
                xml_parts.append(cell_xml)
                xml_parts.append('</hp:subList>')
                xml_parts.append(f'<hp:cellAddr colAddr="{col_idx}" rowAddr="{row_idx}"/>')
                xml_parts.append(f'<hp:cellSpan colSpan="{colspan}" rowSpan="{rowspan}"/>')
                xml_parts.append(f'<hp:cellSz width="{cell_width}" height="1000"/>')
                xml_parts.append('<hp:cellMargin left="510" right="510" top="141" bottom="141"/>')
                xml_parts.append('</hp:tc>')
            xml_parts.append('</hp:tr>')

        xml_parts.append('</hp:tbl>')
        xml_parts.append('</hp:run>')
        xml_parts.append('</hp:p>')
        return "".join(xml_parts)

    def _ensure_table_border_fill(self):
        if self.table_border_fill_id is not None:
            return self.table_border_fill_id
        self.max_border_fill_id += 1
        self.table_border_fill_id = self.max_border_fill_id
        if self.header_root is None:
            return self.table_border_fill_id
        bf_xml = (
            f'<hh:borderFill xmlns:hh="http://www.hancom.co.kr/hwpml/2011/head" '
            f'xmlns:hc="http://www.hancom.co.kr/hwpml/2011/core" '
            f'id="{self.table_border_fill_id}" threeD="0" shadow="0" slash="NONE" '
            f'backSlash="NONE" crookedSlash="0" counterstrike="0">'
            f'<hh:leftBorder type="SOLID" width="0.12 mm" color="#000000"/>'
            f'<hh:rightBorder type="SOLID" width="0.12 mm" color="#000000"/>'
            f'<hh:topBorder type="SOLID" width="0.12 mm" color="#000000"/>'
            f'<hh:bottomBorder type="SOLID" width="0.12 mm" color="#000000"/>'
            f'<hh:diagonal type="NONE" crooked="0"/>'
            f'<hc:fill><hc:fillColorPattern type="NONE" foreColor="#FFFFFF" '
            f'backColor="#FFFFFF"/></hc:fill></hh:borderFill>'
        )
        bf_elem = ET.fromstring(bf_xml)
        bfc = self.header_root.find('.//hh:borderFills', self.namespaces)
        if bfc is None:
            bfc = ET.SubElement(
                self.header_root, '{http://www.hancom.co.kr/hwpml/2011/head}borderFills')
        bfc.append(bf_elem)
        return self.table_border_fill_id

    # ------------------------------------------------------------------ table cell

    def _process_blocks_for_table_cell(self, blocks):
        result = []
        for block in blocks:
            if not isinstance(block, dict):
                continue
            bt = block.get('t')
            bc = block.get('c')
            if bt == 'Para':
                result.append(self._handle_para_in_table(bc))
            elif bt == 'Plain':
                result.append(self._handle_plain_in_table(bc))
            elif bt == 'Header':
                result.append(self._handle_header(bc))
            elif bt == 'BulletList':
                result.append(self._handle_bullet_list(bc))
            elif bt == 'OrderedList':
                result.append(self._handle_ordered_list(bc))
            elif bt == 'Table':
                xml = self._handle_table(bc)
                if xml:
                    result.append(xml)
            elif bt == 'HorizontalRule':
                result.append(self._handle_horizontal_rule())
            elif bt == 'BlockQuote':
                result.append(self._handle_block_quote(bc))
        return "\n".join(result)

    def _handle_para_in_table(self, content):
        segments = self._split_by_linebreak(content)
        result = []
        for seg in segments:
            if seg:
                xml = self._create_para_start(
                    style_id=self.normal_style_id, para_pr_id=self.normal_para_pr_id)
                xml += self._process_inlines(seg) + '</hp:p>'
                result.append(xml)
        if not result:
            result.append(
                self._create_para_start(
                    style_id=self.normal_style_id, para_pr_id=self.normal_para_pr_id)
                + '<hp:run charPrIDRef="0"><hp:t></hp:t></hp:run></hp:p>')
        return "\n".join(result)

    def _handle_plain_in_table(self, content):
        return self._handle_para_in_table(content)

    def _split_by_linebreak(self, inlines):
        segments = []
        current = []
        for inline in inlines:
            if inline.get('t') == 'LineBreak':
                segments.append(current)
                current = []
            else:
                current.append(inline)
        if current:
            segments.append(current)
        return segments

    # ------------------------------------------------------------------ paragraphs

    def _handle_para(self, content, para_styles=None):
        if para_styles is None and self.html_para_styles:
            para_text = self._get_plain_text(content)[:100]
            if para_text in self.html_para_styles:
                hs = self.html_para_styles[para_text]
                para_styles = {
                    k: self._convert_size_to_hwp(v)
                    for k, v in hs.items()
                }
        padding_left = 0
        text_indent = 0
        if para_styles:
            padding_left = para_styles.get('padding-left', 0) or para_styles.get('margin-left', 0)
            text_indent = para_styles.get('text-indent', 0)
        para_pr_id = self._get_or_create_para_pr(padding_left, text_indent)
        return (self._create_para_start(style_id=self.normal_style_id, para_pr_id=para_pr_id)
                + self._process_inlines(content) + '</hp:p>')

    def _handle_plain(self, content, para_styles=None):
        return self._handle_para(content, para_styles)

    def _handle_header(self, content):
        level = content[0]
        inlines = content[2]
        style = min(level, 6)
        return (self._create_para_start(style_id=style)
                + self._process_inlines(inlines) + '</hp:p>')

    # ------------------------------------------------------------------ lists

    def _handle_bullet_list(self, list_data, depth=0):
        """Handle bullet lists with indentation and all block types per item."""
        items = list_data if isinstance(list_data, list) else []
        result = []
        para_pr_id = self._get_para_pr_for_list_depth(depth)

        for item in items:
            if not isinstance(item, list):
                continue
            has_text_block = False
            for block in item:
                bt = block.get('t')
                bc = block.get('c')

                if bt in ('Plain', 'Para'):
                    result.append(self._create_para_start(
                        style_id=self.normal_style_id, para_pr_id=para_pr_id))
                    if not has_text_block:
                        result.append('<hp:run charPrIDRef="0"><hp:t>• </hp:t></hp:run>')
                        has_text_block = True
                    result.append(self._process_inlines(bc))
                    result.append('</hp:p>')
                elif bt == 'BulletList':
                    result.append(self._handle_bullet_list(bc, depth + 1))
                elif bt == 'OrderedList':
                    result.append(self._handle_ordered_list(bc, depth + 1))
                elif bt == 'Header':
                    result.append(self._handle_header(bc))
                elif bt == 'HorizontalRule':
                    result.append(self._handle_horizontal_rule())
                elif bt == 'BlockQuote':
                    result.append(self._handle_block_quote(bc, para_pr_id=para_pr_id))
                elif bt == 'Table':
                    xml = self._handle_table(bc, para_pr_id=para_pr_id)
                    if xml:
                        result.append(xml)
                elif bt == 'Div':
                    div_blocks = bc[1] if (bc and len(bc) > 1) else []
                    result.append(self._process_blocks_in_list(div_blocks, depth))
                elif bt == 'RawBlock':
                    xml = self._handle_raw_block_in_list(bc, para_pr_id=para_pr_id)
                    if xml:
                        result.append(xml)
                elif bt == 'CodeBlock':
                    result.append(self._handle_code_block(bc))

        return "\n".join(result)

    def _handle_ordered_list(self, list_data, depth=0):
        """Handle ordered lists with indentation and all block types per item."""
        items = list_data[1] if len(list_data) > 1 else []
        result = []
        para_pr_id = self._get_para_pr_for_list_depth(depth)

        for idx, item in enumerate(items, 1):
            if not isinstance(item, list):
                continue
            has_text_block = False
            for block in item:
                bt = block.get('t')
                bc = block.get('c')

                if bt in ('Plain', 'Para'):
                    result.append(self._create_para_start(
                        style_id=self.normal_style_id, para_pr_id=para_pr_id))
                    if not has_text_block:
                        result.append(
                            f'<hp:run charPrIDRef="0"><hp:t>{idx}. </hp:t></hp:run>')
                        has_text_block = True
                    result.append(self._process_inlines(bc))
                    result.append('</hp:p>')
                elif bt == 'BulletList':
                    result.append(self._handle_bullet_list(bc, depth + 1))
                elif bt == 'OrderedList':
                    result.append(self._handle_ordered_list(bc, depth + 1))
                elif bt == 'Header':
                    result.append(self._handle_header(bc))
                elif bt == 'HorizontalRule':
                    result.append(self._handle_horizontal_rule())
                elif bt == 'BlockQuote':
                    result.append(self._handle_block_quote(bc, para_pr_id=para_pr_id))
                elif bt == 'Table':
                    xml = self._handle_table(bc, para_pr_id=para_pr_id)
                    if xml:
                        result.append(xml)
                elif bt == 'Div':
                    div_blocks = bc[1] if (bc and len(bc) > 1) else []
                    result.append(self._process_blocks_in_list(div_blocks, depth))
                elif bt == 'RawBlock':
                    xml = self._handle_raw_block_in_list(bc, para_pr_id=para_pr_id)
                    if xml:
                        result.append(xml)
                elif bt == 'CodeBlock':
                    result.append(self._handle_code_block(bc))

        return "\n".join(result)

    def _process_blocks_in_list(self, blocks, depth=0):
        """Process blocks inside a list item (e.g. wrapped in a Div).

        Para/Plain blocks use depth-appropriate indentation.
        Tables pass para_pr_id so they are also correctly indented.
        """
        result = []
        para_pr_id = self._get_para_pr_for_list_depth(depth)

        for block in blocks:
            if not isinstance(block, dict):
                continue
            bt = block.get('t')
            bc = block.get('c')

            if bt in ('Para', 'Plain'):
                xml = (self._create_para_start(
                            style_id=self.normal_style_id, para_pr_id=para_pr_id)
                       + self._process_inlines(bc) + '</hp:p>')
                result.append(xml)
            elif bt == 'Header':
                result.append(self._handle_header(bc))
            elif bt == 'HorizontalRule':
                result.append(self._handle_horizontal_rule())
            elif bt == 'BlockQuote':
                result.append(self._handle_block_quote(bc, para_pr_id=para_pr_id))
            elif bt == 'Table':
                xml = self._handle_table(bc, para_pr_id=para_pr_id)
                if xml:
                    result.append(xml)
            elif bt == 'BulletList':
                result.append(self._handle_bullet_list(bc, depth + 1))
            elif bt == 'OrderedList':
                result.append(self._handle_ordered_list(bc, depth + 1))
            elif bt == 'Div':
                inner = bc[1] if (bc and len(bc) > 1) else []
                result.append(self._process_blocks_in_list(inner, depth))
            elif bt == 'RawBlock':
                xml = self._handle_raw_block_in_list(bc, para_pr_id=para_pr_id)
                if xml:
                    result.append(xml)
            elif bt == 'CodeBlock':
                result.append(self._handle_code_block(bc))

        return "\n".join(result)

    # ------------------------------------------------------------------ raw / code

    def _handle_raw_block_in_list(self, content, para_pr_id=None):
        if not content or len(content) < 2:
            return ""
        raw_format, raw_html = content[0], content[1]
        if raw_format not in ('html', 'HTML'):
            return ""
        if '<table' not in raw_html.lower():
            return ""
        try:
            return self._convert_raw_html_table(raw_html, para_pr_id=para_pr_id)
        except Exception as e:
            print(f"[Warn] Failed to convert raw HTML table: {e}", file=sys.stderr)
            return ""

    def _convert_raw_html_table(self, html_str, para_pr_id=None):
        """Parse a raw HTML <table> and emit HWPX XML reusing _handle_table logic."""
        from html.parser import HTMLParser as _HP

        class _TP(_HP):
            def __init__(self):
                super().__init__()
                self.rows = []
                self._row = None
                self._cell = None
                self._buf = []
                self._depth = 0

            def handle_starttag(self, tag, attrs):
                ad = dict(attrs)
                if tag == 'table':
                    self._depth += 1
                    return
                if self._depth != 1:
                    return
                if tag == 'tr':
                    self._row = []
                elif tag in ('td', 'th'):
                    self._buf = []
                    self._cell = {
                        'is_header': tag == 'th',
                        'colspan': int(ad.get('colspan', 1)),
                        'rowspan': int(ad.get('rowspan', 1)),
                        'text': ''
                    }

            def handle_endtag(self, tag):
                if tag == 'table':
                    self._depth -= 1
                    return
                if self._depth != 1:
                    return
                if tag in ('td', 'th'):
                    if self._cell is not None:
                        self._cell['text'] = ''.join(self._buf).strip()
                        if self._row is not None:
                            self._row.append(self._cell)
                    self._cell = None
                    self._buf = []
                elif tag == 'tr':
                    if self._row is not None:
                        self.rows.append(self._row)
                    self._row = None

            def handle_data(self, data):
                if self._cell is not None and self._depth == 1:
                    self._buf.append(data)

        parser = _TP()
        parser.feed(html_str)
        rows = parser.rows
        if not rows:
            return ""

        cell_grid = {}
        max_row = max_col = 0
        for row_idx, row in enumerate(rows):
            curr_col = 0
            for cell in row:
                while (row_idx, curr_col) in cell_grid:
                    curr_col += 1
                colspan = cell['colspan']
                rowspan = cell['rowspan']
                ib = ({'t': 'Para', 'c': [{'t': 'Str', 'c': cell['text']}]}
                      if cell['text'] else {'t': 'Para', 'c': []})
                for r in range(rowspan):
                    for c in range(colspan):
                        cell_grid[(row_idx + r, curr_col + c)] = {
                            'origin_row': row_idx, 'origin_col': curr_col,
                            'rowspan': rowspan, 'colspan': colspan, 'blocks': [ib]
                        }
                max_row = max(max_row, row_idx + rowspan - 1)
                max_col = max(max_col, curr_col + colspan - 1)
                curr_col += colspan

        row_cnt = max_row + 1
        col_cnt = max_col + 1
        TOTAL_TABLE_WIDTH = 45000

        import time, random
        tbl_id = str(int(time.time() * 1000) % 100000000 + random.randint(0, 10000))

        eppid = para_pr_id if para_pr_id is not None else self.normal_para_pr_id
        xml_parts = [
            self._create_para_start(style_id=self.normal_style_id, para_pr_id=eppid),
            self._create_run_start(char_pr_id=0),
        ]

        if self.table_border_fill_id is None:
            self._ensure_table_border_fill()

        plm = self._get_left_margin_from_para_pr(eppid)
        ew = TOTAL_TABLE_WIDTH - plm
        col_widths = [int(ew / col_cnt) for _ in range(col_cnt)]

        xml_parts.append(
            f'<hp:tbl id="{tbl_id}" zOrder="0" numberingType="TABLE" '
            f'textWrap="TOP_AND_BOTTOM" textFlow="BOTH_SIDES" lock="0" '
            f'dropcapstyle="None" pageBreak="CELL" repeatHeader="1" '
            f'rowCnt="{row_cnt}" colCnt="{col_cnt}" cellSpacing="0" '
            f'borderFillIDRef="{self.table_border_fill_id}" noAdjust="0">')
        xml_parts.append(
            f'<hp:sz width="{ew}" widthRelTo="ABSOLUTE" '
            f'height="{row_cnt * 1000}" heightRelTo="ABSOLUTE" protect="0"/>')
        xml_parts.append(
            '<hp:pos treatAsChar="0" affectLSpacing="0" flowWithText="1" '
            'allowOverlap="0" holdAnchorAndSO="0" vertRelTo="PARA" '
            'horzRelTo="PARA" vertAlign="TOP" horzAlign="LEFT" '
            'vertOffset="0" horzOffset="0"/>')
        xml_parts.append('<hp:outMargin left="0" right="0" top="0" bottom="1417"/>')
        xml_parts.append('<hp:inMargin left="510" right="510" top="141" bottom="141"/>')

        processed = set()
        for row_idx in range(row_cnt):
            xml_parts.append('<hp:tr>')
            for col_idx in range(col_cnt):
                if (row_idx, col_idx) not in cell_grid:
                    continue
                ci = cell_grid[(row_idx, col_idx)]
                if ci['origin_row'] != row_idx or ci['origin_col'] != col_idx:
                    continue
                if (row_idx, col_idx) in processed:
                    continue
                processed.add((row_idx, col_idx))
                cw = sum(col_widths[col_idx:col_idx + ci['colspan']])
                sid = str(int(time.time() * 100000) % 1000000000 + random.randint(0, 100000))
                cxml = self._process_blocks_for_table_cell(ci['blocks'])
                if not cxml.strip():
                    cxml = (
                        self._create_para_start(
                            style_id=self.normal_style_id,
                            para_pr_id=self.normal_para_pr_id)
                        + '<hp:run charPrIDRef="0"><hp:t></hp:t></hp:run></hp:p>')
                xml_parts.append(
                    f'<hp:tc name="" header="0" hasMargin="0" protect="0" '
                    f'editable="0" dirty="0" borderFillIDRef="{self.table_border_fill_id}">')
                xml_parts.append(
                    f'<hp:subList id="{sid}" textDirection="HORIZONTAL" lineWrap="BREAK" '
                    f'vertAlign="TOP" linkListIDRef="0" linkListNextIDRef="0" '
                    f'textWidth="0" textHeight="0" hasTextRef="0" hasNumRef="0">')
                xml_parts.append(cxml)
                xml_parts.append('</hp:subList>')
                xml_parts.append(f'<hp:cellAddr colAddr="{col_idx}" rowAddr="{row_idx}"/>')
                xml_parts.append(
                    f'<hp:cellSpan colSpan="{ci["colspan"]}" rowSpan="{ci["rowspan"]}"/>')
                xml_parts.append(f'<hp:cellSz width="{cw}" height="1000"/>')
                xml_parts.append('<hp:cellMargin left="510" right="510" top="141" bottom="141"/>')
                xml_parts.append('</hp:tc>')
            xml_parts.append('</hp:tr>')

        xml_parts += ['</hp:tbl>', '</hp:run>', '</hp:p>']
        return "".join(xml_parts)

    def _handle_code_block(self, content):
        code_text = content[1] if len(content) > 1 else ''
        return (self._create_para_start(
                    style_id=self.normal_style_id, para_pr_id=self.normal_para_pr_id)
                + f'<hp:run charPrIDRef="0"><hp:t>{self._escape_text(code_text)}</hp:t></hp:run>'
                + '</hp:p>')

    # ------------------------------------------------------------------ HR / blockquote

    def _handle_horizontal_rule(self):
        """Render <hr> as an empty paragraph with a bottom border."""
        cache_key = '__horizontal_rule__'
        if cache_key in self.para_pr_cache:
            hr_id = self.para_pr_cache[cache_key]
        else:
            hr_id = self._create_hr_para_pr()
            self.para_pr_cache[cache_key] = hr_id
        return (self._create_para_start(style_id=self.normal_style_id, para_pr_id=hr_id)
                + '<hp:run charPrIDRef="0"><hp:t></hp:t></hp:run></hp:p>')

    def _create_hr_para_pr(self):
        if self.header_root is None:
            return str(self.normal_para_pr_id)
        hr_bf_id = self._ensure_hr_border_fill()
        base_node = self.header_root.find(
            f'.//hh:paraPr[@id="{self.normal_para_pr_id}"]', self.namespaces)
        if base_node is None:
            base_node = self.header_root.find('.//hh:paraPr[@id="0"]', self.namespaces)
        if base_node is None:
            return str(self.normal_para_pr_id)
        new_node = copy.deepcopy(base_node)
        self.max_para_pr_id += 1
        new_id = str(self.max_para_pr_id)
        new_node.set('id', new_id)
        new_node.set('borderFillIDRef', str(hr_bf_id))
        para_props = self.header_root.find('.//hh:paraProperties', self.namespaces)
        if para_props is not None:
            para_props.append(new_node)
        return new_id

    def _ensure_hr_border_fill(self):
        if hasattr(self, '_hr_border_fill_id') and self._hr_border_fill_id is not None:
            return self._hr_border_fill_id
        self.max_border_fill_id += 1
        bf_id = self.max_border_fill_id
        self._hr_border_fill_id = bf_id
        bf_xml = (
            f'<hh:borderFill xmlns:hh="http://www.hancom.co.kr/hwpml/2011/head" '
            f'xmlns:hc="http://www.hancom.co.kr/hwpml/2011/core" '
            f'id="{bf_id}" threeD="0" shadow="0" slash="NONE" backSlash="NONE" '
            f'crookedSlash="0" counterstrike="0">'
            f'<hh:leftBorder type="NONE" width="0.12 mm" color="#000000"/>'
            f'<hh:rightBorder type="NONE" width="0.12 mm" color="#000000"/>'
            f'<hh:topBorder type="NONE" width="0.12 mm" color="#000000"/>'
            f'<hh:bottomBorder type="SOLID" width="0.12 mm" color="#A0A0A0"/>'
            f'<hh:diagonal type="NONE" crooked="0"/>'
            f'<hc:fill><hc:fillColorPattern type="NONE" foreColor="#FFFFFF" '
            f'backColor="#FFFFFF"/></hc:fill></hh:borderFill>'
        )
        bf_elem = ET.fromstring(bf_xml)
        bfc = self.header_root.find('.//hh:borderFills', self.namespaces)
        if bfc is None:
            bfc = ET.SubElement(
                self.header_root, '{http://www.hancom.co.kr/hwpml/2011/head}borderFills')
        bfc.append(bf_elem)
        return bf_id

    def _handle_block_quote(self, content, para_pr_id=None):
        """Render BlockQuote as indented paragraphs (one extra indent level)."""
        BQ_EXTRA = 3600
        base_margin = self._get_left_margin_from_para_pr(para_pr_id) if para_pr_id else 0
        bq_margin = base_margin + BQ_EXTRA
        cache_key = (bq_margin, 0)
        if cache_key in self.para_pr_cache:
            bq_id = self.para_pr_cache[cache_key]
        else:
            bq_id = self._create_para_pr_with_margin(bq_margin)
            self.para_pr_cache[cache_key] = bq_id

        result = []
        for block in (content or []):
            if not isinstance(block, dict):
                continue
            bt = block.get('t')
            bc = block.get('c')
            if bt in ('Para', 'Plain'):
                result.append(
                    self._create_para_start(style_id=self.normal_style_id, para_pr_id=bq_id)
                    + self._process_inlines(bc) + '</hp:p>')
            elif bt == 'Header':
                result.append(self._handle_header(bc))
            elif bt == 'BulletList':
                result.append(self._handle_bullet_list(bc))
            elif bt == 'OrderedList':
                result.append(self._handle_ordered_list(bc))
            elif bt == 'Table':
                result.append(self._handle_table(bc, para_pr_id=bq_id))
            elif bt == 'HorizontalRule':
                result.append(self._handle_horizontal_rule())
            elif bt == 'BlockQuote':
                result.append(self._handle_block_quote(bc, para_pr_id=bq_id))
            elif bt == 'CodeBlock':
                result.append(self._handle_code_block(bc))
        return "\n".join(result)

    # ------------------------------------------------------------------ top-level

    def _process_blocks(self, blocks):
        result = []
        for block in blocks:
            if not isinstance(block, dict):
                continue
            bt = block.get('t')
            bc = block.get('c')

            if bt == 'Para':
                result.append(self._handle_para(bc))
            elif bt == 'Plain':
                result.append(self._handle_plain(bc))
            elif bt == 'Header':
                result.append(self._handle_header(bc))
            elif bt == 'BulletList':
                result.append(self._handle_bullet_list(bc))
            elif bt == 'OrderedList':
                result.append(self._handle_ordered_list(bc))
            elif bt == 'Table':
                xml = self._handle_table(bc)
                if xml:
                    result.append(xml)
            elif bt == 'Div':
                inner = bc[1] if (bc and len(bc) > 1) else []
                result.append(self._process_blocks(inner))
            elif bt == 'CodeBlock':
                result.append(self._handle_code_block(bc))
            elif bt == 'HorizontalRule':
                result.append(self._handle_horizontal_rule())
            elif bt == 'BlockQuote':
                result.append(self._handle_block_quote(bc))
            elif bt == 'RawBlock':
                xml = self._handle_raw_block_in_list(bc)
                if xml:
                    result.append(xml)

        return "\n".join(result)

    def _process_inlines(self, inlines, active_formats=None, base_color=None, base_size=None):
        if active_formats is None:
            active_formats = set()
        result = []
        for inline in inlines:
            it = inline.get('t')
            ic = inline.get('c')

            if it == 'Str':
                cid = self._get_or_create_char_pr(0, active_formats, base_color, base_size)
                result.append(
                    f'<hp:run charPrIDRef="{cid}"><hp:t>{saxutils.escape(ic)}</hp:t></hp:run>')
            elif it == 'Space':
                cid = self._get_or_create_char_pr(0, active_formats, base_color, base_size)
                result.append(f'<hp:run charPrIDRef="{cid}"><hp:t> </hp:t></hp:run>')
            elif it == 'Strong':
                nf = active_formats | {'BOLD'}
                result.append(self._process_inlines(ic, nf, base_color, base_size))
            elif it == 'Emph':
                nf = active_formats | {'ITALIC'}
                result.append(self._process_inlines(ic, nf, base_color, base_size))
            elif it == 'Underline':
                nf = active_formats | {'UNDERLINE'}
                result.append(self._process_inlines(ic, nf, base_color, base_size))
            elif it == 'Strikeout':
                nf = active_formats | {'STRIKEOUT'}
                result.append(self._process_inlines(ic, nf, base_color, base_size))
            elif it == 'Superscript':
                nf = active_formats | {'SUPERSCRIPT'}
                result.append(self._process_inlines(ic, nf, base_color, base_size))
            elif it == 'Subscript':
                nf = active_formats | {'SUBSCRIPT'}
                result.append(self._process_inlines(ic, nf, base_color, base_size))
            elif it == 'Span':
                attr = ic[0]
                span_inlines = ic[1]
                styles = self._extract_style_from_attr(attr)
                nf = active_formats.copy()
                nc, ns = base_color, base_size
                if styles.get('bold'):
                    nf.add('BOLD')
                if styles.get('italic'):
                    nf.add('ITALIC')
                if styles.get('underline'):
                    nf.add('UNDERLINE')
                if styles.get('strikeout'):
                    nf.add('STRIKEOUT')
                if 'color' in styles:
                    nc = styles['color']
                if 'font-size' in styles:
                    ns = styles['font-size']
                result.append(self._process_inlines(span_inlines, nf, nc, ns))
            elif it == 'LineBreak':
                result.append('<hp:lineseg/>')
            elif it == 'SoftBreak':
                cid = self._get_or_create_char_pr(0, active_formats, base_color, base_size)
                result.append(f'<hp:run charPrIDRef="{cid}"><hp:t> </hp:t></hp:run>')
            elif it == 'Code':
                cid = self._get_or_create_char_pr(0, active_formats, base_color, base_size)
                result.append(
                    f'<hp:run charPrIDRef="{cid}"><hp:t>{saxutils.escape(ic[1])}</hp:t></hp:run>')

        return "".join(result)

    # ------------------------------------------------------------------ entry points

    def process(self):
        if not self.ast:
            return ""
        blocks = self.ast.get('blocks', [])
        self.output = [self._process_blocks(blocks)]
        return "\n".join(self.output)

    def get_modified_header_xml(self):
        if self.header_tree is None:
            return self.header_xml_content

        for section, tag in [
            ('.//hh:charProperties', 'hh:charPr'),
            ('.//hh:paraProperties', 'hh:paraPr'),
            ('.//hh:borderFills', 'hh:borderFill'),
        ]:
            container = self.header_root.find(section, self.namespaces)
            if container is not None:
                count = len(container.findall(tag, self.namespaces))
                container.set('itemCnt', str(count))

        return ET.tostring(self.header_root, encoding='unicode', method='xml')

    @staticmethod
    def convert_to_hwpx(input_path, output_path, reference_path):
        """Convert input file to HWPX using a reference template."""
        if os.path.isdir(reference_path):
            with open(os.path.join(reference_path, 'Contents', 'header.xml'),
                      'r', encoding='utf-8') as f:
                header_xml = f.read()
            with open(os.path.join(reference_path, 'Contents', 'section0.xml'),
                      'r', encoding='utf-8') as f:
                section0_xml = f.read()
        else:
            with zipfile.ZipFile(reference_path, 'r') as ref_zip:
                header_xml = ref_zip.read('Contents/header.xml').decode('utf-8')
                section0_xml = ref_zip.read('Contents/section0.xml').decode('utf-8')

        html_content = None
        if input_path.lower().endswith('.html'):
            with open(input_path, 'r', encoding='utf-8') as f:
                html_content = f.read()

        json_str = pypandoc.convert_file(input_path, 'json', format=None)
        ast = json.loads(json_str)

        converter = PandocToHwpx(
            json_ast=ast, header_xml_content=header_xml, html_content=html_content)
        section_content = converter.process()
        modified_header = converter.get_modified_header_xml()

        section_xml = f'''<?xml version="1.0" encoding="utf-8"?>
<hs:sec xmlns:hp="http://www.hancom.co.kr/hwpml/2011/paragraph" xmlns:hs="http://www.hancom.co.kr/hwpml/2011/section">
  <hp:p paraPrIDRef="1" styleIDRef="0" pageBreak="0" columnBreak="0" merged="0">
    <hp:run charPrIDRef="0">
      <hp:secPr id="" textDirection="HORIZONTAL" spaceColumns="1134" tabStop="8000" tabStopVal="4000" tabStopUnit="HWPUNIT" outlineShapeIDRef="1" memoShapeIDRef="1" textVerticalWidthHead="0" masterPageCnt="0">
        <hp:grid lineGrid="0" charGrid="0" wonggojiFormat="0"/>
        <hp:startNum pageStartsOn="BOTH" page="0" pic="0" tbl="0" equation="0"/>
        <hp:visibility hideFirstHeader="0" hideFirstFooter="0" hideFirstMasterPage="0" border="SHOW_ALL" fill="SHOW_ALL" hideFirstPageNum="0" hideFirstEmptyLine="0" showLineNumber="0"/>
        <hp:lineNumberShape restartType="0" countBy="0" distance="0" startNumber="0"/>
        <hp:pagePr landscape="WIDELY" width="59530" height="84190" gutterType="LEFT_ONLY">
          <hp:margin header="4250" footer="2240" gutter="0" left="7200" right="7200" top="4255" bottom="4960"/>
        </hp:pagePr>
        <hp:footNotePr>
          <hp:autoNumFormat type="DIGIT" userChar="" prefixChar="" suffixChar="" supscript="1"/>
          <hp:noteLine length="-1" type="SOLID" width="0.25 mm" color="#000000"/>
          <hp:noteSpacing betweenNotes="283" belowLine="0" aboveLine="1000"/>
          <hp:numbering type="CONTINUOUS" newNum="1"/>
          <hp:placement place="EACH_COLUMN" beneathText="0"/>
        </hp:footNotePr>
        <hp:endNotePr>
          <hp:autoNumFormat type="ROMAN_SMALL" userChar="" prefixChar="" suffixChar="" supscript="1"/>
          <hp:noteLine length="-1" type="SOLID" width="0.12 mm" color="#000000"/>
          <hp:noteSpacing betweenNotes="0" belowLine="0" aboveLine="1000"/>
          <hp:numbering type="CONTINUOUS" newNum="1"/>
          <hp:placement place="END_OF_DOCUMENT" beneathText="0"/>
        </hp:endNotePr>
        <hp:pageBorderFill type="BOTH" borderFillIDRef="1" textBorder="PAPER" headerInside="0" footerInside="0" fillArea="PAPER">
          <hp:offset left="1417" right="1417" top="1417" bottom="1417"/>
        </hp:pageBorderFill>
        <hp:pageBorderFill type="EVEN" borderFillIDRef="1" textBorder="PAPER" headerInside="0" footerInside="0" fillArea="PAPER">
          <hp:offset left="1417" right="1417" top="1417" bottom="1417"/>
        </hp:pageBorderFill>
        <hp:pageBorderFill type="ODD" borderFillIDRef="1" textBorder="PAPER" headerInside="0" footerInside="0" fillArea="PAPER">
          <hp:offset left="1417" right="1417" top="1417" bottom="1417"/>
        </hp:pageBorderFill>
      </hp:secPr>
      <hp:ctrl>
        <hp:colPr id="" type="NEWSPAPER" layout="LEFT" colCount="1" sameSz="1" sameGap="0"/>
      </hp:ctrl>
    </hp:run>
    <hp:run charPrIDRef="0">
      <hp:t/>
    </hp:run>
  </hp:p>
{section_content}
</hs:sec>'''

        skip = {'Contents/header.xml', 'Contents/section0.xml'}
        with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as out_zip:
            if os.path.isdir(reference_path):
                for root, _, files in os.walk(reference_path):
                    for fname in files:
                        abs_path = os.path.join(root, fname)
                        arc_name = os.path.relpath(abs_path, reference_path).replace(os.sep, '/')
                        if arc_name not in skip:
                            with open(abs_path, 'rb') as f:
                                out_zip.writestr(arc_name, f.read())
            else:
                with zipfile.ZipFile(reference_path, 'r') as ref_zip:
                    for item in ref_zip.namelist():
                        if item not in skip:
                            out_zip.writestr(item, ref_zip.read(item))

            out_zip.writestr('Contents/header.xml', modified_header.encode('utf-8'))
            out_zip.writestr('Contents/section0.xml', section_xml.encode('utf-8'))