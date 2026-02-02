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
        self.para_styles = []  # NEW: Track paragraph-level styles
        
    def handle_starttag(self, tag, attrs):
        style_dict = {}
        for attr, value in attrs:
            if attr == 'style':
                # Parse inline CSS
                for style_part in value.split(';'):
                    if ':' in style_part:
                        key, val = style_part.split(':', 1)
                        key = key.strip().lower()
                        val = val.strip()
                        style_dict[key] = val
        
        # NEW: Track paragraph-level styles
        if tag == 'p':
            self.para_styles.append(style_dict.copy())
        
        # Handle semantic tags
        if tag == 'strong' or tag == 'b':
            style_dict['font-weight'] = 'bold'
        elif tag == 'em' or tag == 'i':
            style_dict['font-style'] = 'italic'
        elif tag == 'u':
            style_dict['text-decoration'] = 'underline'
        elif tag == 'span':
            pass  # Span already captured in attrs
            
        self.style_stack.append((tag, style_dict))
    
    def handle_endtag(self, tag):
        if self.style_stack and self.style_stack[-1][0] == tag:
            self.style_stack.pop()
    
    def handle_data(self, data):
        if data.strip():
            # Combine all active styles
            combined_style = {}
            for tag, style in self.style_stack:
                combined_style.update(style)
            self.text_segments.append((data, combined_style.copy()))

class HTMLParagraphStyleExtractor(HTMLParser):
    """Extract paragraph-level styles from HTML before Pandoc processing"""
    def __init__(self):
        super().__init__()
        self.para_styles = {}  # Map content_hash -> styles_dict
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
            # Create a hash from the paragraph content
            content_text = ''.join(self.current_para_content).strip()
            if content_text and self.current_para_styles:
                # Use first 100 chars as key to identify paragraph
                content_key = content_text[:100]
                self.para_styles[content_key] = self.current_para_styles.copy()
            
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
        
        # NEW: Extract paragraph styles from HTML before processing
        self.html_para_styles = {}  # Map para_index -> styles_dict
        if html_content:
            self._extract_html_para_styles(html_content)
        
        # Default Style Mappings (Fallback)
        self.STYLE_MAP = {
            'Normal': 0,
            'Header1': 1,
            'Header2': 2,
            'Header3': 3,
            'Header4': 4,
            'Header5': 5,
            'Header6': 6,
        }
        
        # Dynamic Style Mappings from header.xml
        self.dynamic_style_map = {}
        self.normal_style_id = 0 
        self.normal_para_pr_id = 1
        
        # XML Tree and CharPr Cache
        self.header_tree = None
        self.header_root = None
        self.namespaces = {
            'hh': 'http://www.hancom.co.kr/hwpml/2011/head',
            'hp': 'http://www.hancom.co.kr/hwpml/2011/paragraph',
            'hc': 'http://www.hancom.co.kr/hwpml/2011/core',
            'hs': 'http://www.hancom.co.kr/hwpml/2011/section'
        }
        # cache key: (base_char_pr_id, frozenset(active_formats), color, font_size) -> new_char_pr_id
        self.char_pr_cache = {} 
        self.max_char_pr_id = 0
        self.max_para_pr_id = 0
        self.max_border_fill_id = 0
        
        # NEW: ParaPr cache for indented paragraphs
        self.para_pr_cache = {}  # key: (padding_left, text_indent) -> para_pr_id
        
        self.images = [] # metadata for images
        
        # Table-related attributes (from original)
        self.table_border_fill_id = None

        # Metadata extraction
        self.title = None
        self._extract_metadata()

        if self.header_xml_content:
            self._parse_styles_and_init_xml(self.header_xml_content)

    def _extract_html_para_styles(self, html_content):
        """Extract paragraph styles from HTML before Pandoc processes it"""
        try:
            extractor = HTMLParagraphStyleExtractor()
            extractor.feed(html_content)
            
            # Store content-based styles dictionary
            self.html_para_styles = extractor.para_styles
        except Exception as e:
            print(f"[Warn] Failed to extract HTML paragraph styles: {e}", file=sys.stderr)

    def _extract_metadata(self):
        if not self.ast:
            return
        meta = self.ast.get('meta', {})
        
        # Title
        if 'title' in meta:
             t_obj = meta['title']
             # "title": {"t": "MetaInlines","c": [{"t": "Str","c": "..."}]}
             if t_obj.get('t') == 'MetaInlines':
                 self.title = self._get_plain_text(t_obj.get('c', []))
             elif t_obj.get('t') == 'MetaString': # Sometimes simple string
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
            elif t in ['Strong', 'Emph', 'Underline', 'Strikeout', 'Superscript', 'Subscript', 'SmallCaps']:
                 text.append(self._get_plain_text(c)) # recursive
            elif t == 'Span':
                 # c = [attr, [inlines]]
                 text.append(self._get_plain_text(c[1]))
            elif t == 'Link':
                 # c = [attr, [text], [url, title]]
                 text.append(self._get_plain_text(c[1]))
            elif t == 'Image':
                 # c = [attr, [caption], [url, title]]
                 text.append(self._get_plain_text(c[1]))
            elif t == 'Code':
                 text.append(c[1])
            elif t == 'Quoted':
                 # c = [quoteType, [inlines]]
                 text.append('"' + self._get_plain_text(c[1]) + '"')
        return "".join(text)

    def _convert_color_to_hwp(self, color):
        """Convert CSS color to HWP format (#RRGGBB)"""
        if not color:
            return '#000000'
            
        # Named colors map
        color_map = {
            'red': '#FF0000',
            'green': '#008000',
            'blue': '#0000FF',
            'black': '#000000',
            'white': '#FFFFFF',
            'yellow': '#FFFF00',
            'cyan': '#00FFFF',
            'magenta': '#FF00FF',
            'orange': '#FFA500',
            'purple': '#800080',
            'pink': '#FFC0CB',
            'brown': '#A52A2A',
            'gray': '#808080',
            'grey': '#808080',
            'lime': '#00FF00',
            'navy': '#000080',
            'teal': '#008080',
            'silver': '#C0C0C0',
            'maroon': '#800000',
            'olive': '#808000',
        }
        
        color = color.lower().strip()
        
        # If it's a named color
        if color in color_map:
            return color_map[color]
        
        # If it's already hex
        if color.startswith('#'):
            if len(color) == 7:  # #RRGGBB
                return color.upper()
            elif len(color) == 4:  # #RGB -> #RRGGBB
                r, g, b = color[1], color[2], color[3]
                return f'#{r}{r}{g}{g}{b}{b}'.upper()
        
        # If it's rgb(r, g, b)
        if color.startswith('rgb'):
            import re
            match = re.search(r'rgb\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', color)
            if match:
                r, g, b = int(match.group(1)), int(match.group(2)), int(match.group(3))
                return f'#{r:02X}{g:02X}{b:02X}'
        
        return '#000000'

    def _convert_size_to_hwp(self, size_str):
        """Convert CSS font-size to HWP point size"""
        if not size_str:
            return None
            
        size_str = size_str.lower().strip()
        
        # If it's already in pt
        if size_str.endswith('pt'):
            try:
                return int(float(size_str[:-2]))
            except:
                return None
        
        # If it's in px (assuming 96 DPI)
        if size_str.endswith('px'):
            try:
                px = float(size_str[:-2])
                pt = px * 72 / 96  # Convert px to pt
                return int(pt)
            except:
                return None
        
        # If it's a number without unit, assume pt
        try:
            return int(float(size_str))
        except:
            return None

    def _extract_style_from_attr(self, attr):
        """Extract style information from Pandoc attributes"""
        # attr = [id, [classes], [[key, val], ...]]
        styles = {}
        
        if len(attr) < 3:
            return styles
        
        # Check classes for common formatting
        classes = attr[1]
        for cls in classes:
            cls_lower = cls.lower()
            if 'bold' in cls_lower or 'strong' in cls_lower:
                styles['bold'] = True
            if 'italic' in cls_lower or 'emph' in cls_lower:
                styles['italic'] = True
            if 'underline' in cls_lower:
                styles['underline'] = True
        
        # Check key-value pairs for inline styles
        kv_pairs = attr[2]
        for key, val in kv_pairs:
            key_lower = key.lower()
            if key_lower == 'style':
                # Parse CSS style string
                for style_part in val.split(';'):
                    if ':' in style_part:
                        style_key, style_val = style_part.split(':', 1)
                        style_key = style_key.strip().lower()
                        style_val = style_val.strip()
                        
                        if style_key == 'color':
                            styles['color'] = self._convert_color_to_hwp(style_val)
                        elif style_key == 'font-size':
                            styles['font-size'] = self._convert_size_to_hwp(style_val)
                        elif style_key == 'font-weight':
                            if 'bold' in style_val.lower():
                                styles['bold'] = True
                        elif style_key == 'font-style':
                            if 'italic' in style_val.lower():
                                styles['italic'] = True
                        elif style_key == 'text-decoration':
                            if 'underline' in style_val.lower():
                                styles['underline'] = True
                            if 'line-through' in style_val.lower():
                                styles['strikeout'] = True
                        # NEW: Extract padding/indent for paragraphs
                        elif style_key == 'padding-left':
                            styles['padding-left'] = self._convert_size_to_hwp(style_val)
                        elif style_key == 'margin-left':
                            styles['margin-left'] = self._convert_size_to_hwp(style_val)
                        elif style_key == 'text-indent':
                            styles['text-indent'] = self._convert_size_to_hwp(style_val)
        
        return styles

    def _parse_styles_and_init_xml(self, header_xml_content):
        """Parse header.xml and initialize style mappings with XML tree"""
        try:
            # Register namespaces
            for prefix, uri in self.namespaces.items():
                ET.register_namespace(prefix, uri)
            
            self.header_tree = ET.ElementTree(ET.fromstring(header_xml_content))
            self.header_root = self.header_tree.getroot()
            
            # Find max IDs
            for char_pr in self.header_root.findall('.//hh:charPr', self.namespaces):
                char_id = int(char_pr.get('id', 0))
                if char_id > self.max_char_pr_id:
                    self.max_char_pr_id = char_id
            
            for para_pr in self.header_root.findall('.//hh:paraPr', self.namespaces):
                para_id = int(para_pr.get('id', 0))
                if para_id > self.max_para_pr_id:
                    self.max_para_pr_id = para_id
            
            for border_fill in self.header_root.findall('.//hh:borderFill', self.namespaces):
                bf_id = int(border_fill.get('id', 0))
                if bf_id > self.max_border_fill_id:
                    self.max_border_fill_id = bf_id
            
            # Find Normal style
            styles = self.header_root.findall('.//hh:style', self.namespaces)
            for style in styles:
                style_name = style.get('name', '')
                style_id = int(style.get('id', 0))
                
                if style_name == 'Normal' or style_name == '바탕글':
                    self.normal_style_id = style_id
                    self.normal_para_pr_id = int(style.get('paraPrIDRef', 1))
                
                self.dynamic_style_map[style_name] = style_id
            
        except Exception as e:
            print(f"[Warn] Failed to parse header.xml: {e}", file=sys.stderr)

    def _get_or_create_char_pr(self, base_char_pr_id=0, active_formats=None, color=None, font_size=None):
        """Get or create a charPr with specified formatting - using correct HWPX format"""
        if active_formats is None:
            active_formats = set()
        
        base_char_pr_id = str(base_char_pr_id)
        
        # Create cache key
        cache_key = (base_char_pr_id, frozenset(active_formats), color, font_size)
        
        if cache_key in self.char_pr_cache:
            return self.char_pr_cache[cache_key]
        
        # If no formatting needed, return base
        if not active_formats and not color and not font_size:
            return base_char_pr_id
        
        # Create new charPr
        if self.header_root is None:
            return base_char_pr_id
        
        base_node = self.header_root.find(f'.//hh:charPr[@id="{base_char_pr_id}"]', self.namespaces)
        if base_node is None:
            base_node = self.header_root.find('.//hh:charPr[@id="0"]', self.namespaces)
            if base_node is None:
                return base_char_pr_id
        
        new_node = copy.deepcopy(base_node)
        self.max_char_pr_id += 1
        new_id = str(self.max_char_pr_id)
        new_node.set('id', new_id)
        
        # Apply color as ATTRIBUTE (not child element)
        if color:
            new_node.set('textColor', color)
            
            # Also update underline color if underline exists
            ul = new_node.find('hh:underline', self.namespaces)
            if ul is not None:
                ul.set('color', color)
        
        # Apply font size as ATTRIBUTE (not child element)
        # HWPX height: 1000 = 10pt, so multiply pt by 100
        if font_size:
            new_node.set('height', str(font_size * 100))
        
        # Apply formatting using CHILD ELEMENTS
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
            if color:
                ul.set('color', color)
            else:
                ul.set('color', '#000000')
        
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
        
        # Add to header
        char_props = self.header_root.find('.//hh:charProperties', self.namespaces)
        if char_props is not None:
            char_props.append(new_node)
        
        # Cache and return
        self.char_pr_cache[cache_key] = new_id
        return new_id

    def _get_or_create_para_pr(self, padding_left=0, text_indent=0):
        """NEW: Get or create a paraPr with specified indentation"""
        # Convert pt to HWPUNIT (1pt ≈ 100 HWPUNIT)
        left_margin = int(padding_left * 100) if padding_left else 0
        indent_val = int(text_indent * 100) if text_indent else 0
        
        # Create cache key
        cache_key = (left_margin, indent_val)
        
        if cache_key in self.para_pr_cache:
            return self.para_pr_cache[cache_key]
        
        # If no indentation, return normal
        if left_margin == 0 and indent_val == 0:
            return str(self.normal_para_pr_id)
        
        # Create new paraPr
        if self.header_root is None:
            return str(self.normal_para_pr_id)
        
        # Get base paraPr
        base_node = self.header_root.find(f'.//hh:paraPr[@id="{self.normal_para_pr_id}"]', self.namespaces)
        if base_node is None:
            base_node = self.header_root.find('.//hh:paraPr[@id="0"]', self.namespaces)
            if base_node is None:
                return str(self.normal_para_pr_id)
        
        new_node = copy.deepcopy(base_node)
        self.max_para_pr_id += 1
        new_id = str(self.max_para_pr_id)
        new_node.set('id', new_id)
        
        # Add or modify margin element
        # Look for existing switch/case/margin structure
        switch_elem = new_node.find('hp:switch', self.namespaces)
        if switch_elem is None:
            switch_elem = ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/paragraph}switch')
        
        case_elem = switch_elem.find('hp:case', self.namespaces)
        if case_elem is None:
            case_elem = ET.SubElement(switch_elem, '{http://www.hancom.co.kr/hwpml/2011/paragraph}case')
            case_elem.set('{http://www.hancom.co.kr/hwpml/2011/paragraph}required-namespace', 
                         'http://www.hancom.co.kr/hwpml/2016/HwpUnitChar')
        
        margin_elem = case_elem.find('hh:margin', self.namespaces)
        if margin_elem is None:
            margin_elem = ET.SubElement(case_elem, '{http://www.hancom.co.kr/hwpml/2011/head}margin')
        
        # Set margin values
        # intent = text-indent (negative for hanging indent)
        # left = padding-left/margin-left
        intent_elem = margin_elem.find('hc:intent', self.namespaces)
        if intent_elem is None:
            intent_elem = ET.SubElement(margin_elem, '{http://www.hancom.co.kr/hwpml/2011/core}intent')
        intent_elem.set('value', str(indent_val))
        intent_elem.set('unit', 'HWPUNIT')
        
        left_elem = margin_elem.find('hc:left', self.namespaces)
        if left_elem is None:
            left_elem = ET.SubElement(margin_elem, '{http://www.hancom.co.kr/hwpml/2011/core}left')
        left_elem.set('value', str(left_margin))
        left_elem.set('unit', 'HWPUNIT')
        
        # Also add to default
        default_elem = switch_elem.find('hp:default', self.namespaces)
        if default_elem is None:
            default_elem = ET.SubElement(switch_elem, '{http://www.hancom.co.kr/hwpml/2011/paragraph}default')
        
        default_margin = default_elem.find('hh:margin', self.namespaces)
        if default_margin is None:
            default_margin = ET.SubElement(default_elem, '{http://www.hancom.co.kr/hwpml/2011/head}margin')
        
        default_intent = default_margin.find('hc:intent', self.namespaces)
        if default_intent is None:
            default_intent = ET.SubElement(default_margin, '{http://www.hancom.co.kr/hwpml/2011/core}intent')
        default_intent.set('value', str(indent_val))
        default_intent.set('unit', 'HWPUNIT')
        
        default_left = default_margin.find('hc:left', self.namespaces)
        if default_left is None:
            default_left = ET.SubElement(default_margin, '{http://www.hancom.co.kr/hwpml/2011/core}left')
        default_left.set('value', str(left_margin))
        default_left.set('unit', 'HWPUNIT')
        
        # Add to header
        para_props = self.header_root.find('.//hh:paraProperties', self.namespaces)
        if para_props is not None:
            para_props.append(new_node)
        
        # Cache and return
        self.para_pr_cache[cache_key] = new_id
        return new_id

    def _escape_text(self, text):
        return saxutils.escape(text)

    def _create_para_start(self, style_id=0, para_pr_id=1, column_break=0, merged=0):
        # merged=0 is default
        return f'<hp:p paraPrIDRef="{para_pr_id}" styleIDRef="{style_id}" pageBreak="0" columnBreak="{column_break}" merged="{merged}">'

    def _create_run_start(self, char_pr_id=0):
        return f'<hp:run charPrIDRef="{char_pr_id}">'
    
    def _create_text_run(self, text, char_pr_id=0):
        run_xml = self._create_run_start(char_pr_id)
        run_xml += f'<hp:t>{self._escape_text(text)}</hp:t>'
        run_xml += '</hp:run>'
        return run_xml

    # === ORIGINAL TABLE HANDLING FROM org_PandocToHwpx.py ===
    def _handle_table(self, content):
        """Handle table from Pandoc AST - ORIGINAL LOGIC"""
        # content = [attr, caption, specs, table_head, table_body, table_foot]
        # Pandoc JSON structure for Table is complex and changes between versions.
        # Assuming standard Pandoc JSON (recent):
        # [attr, caption, specs, table_head, table_body, table_foot]
        
        # attr: [id, [classes], [[key, val]]]
        # caption: [short_caption, blocks]
        # specs: [[align, col_width], ...]
        # table_head: [attr, [row, ...]]
        # table_body: [ [attr, row_head_columns, [row, ...], [row, ...]] ] (List of bodies)
        # table_foot: [attr, [row, ...]]
        
        # Row: [attr, [cell, ...]]
        # Cell: [attr, align, rowspan, colspan, [blocks]]
        
        specs = content[2]
        table_head = content[3]
        table_bodies = content[4] 
        table_foot = content[5]
        
        # 1. Flatten Rows
        # Collect all rows from head, bodies, foot to determine total row count and structure
        all_rows = []
        
        # Head Rows
        head_rows = table_head[1] # list of rows
        for row in head_rows:
            all_rows.append(row)
            
            # Body Rows (Bodies is a list of bodies)
        for body in table_bodies:
            # body = [attr, row_head_columns, intermediate_headers, main_rows]
            
            # Intermediate Headers (if any)
            inter_headers = body[2]
            for row in inter_headers:
                 all_rows.append(row)
            
            # Main Rows
            main_rows = body[3]
            for row in main_rows:
                 all_rows.append(row)
        
        # Foot Rows
        foot_rows = table_foot[1]
        for row in foot_rows:
            all_rows.append(row)
            
        if not all_rows:
            return ""

        row_cnt = len(all_rows)
        col_cnt = len(specs)
        
        # 2. Calculate Widths
        # Total Page Width approx 45000 - margins. Let's assume 30000-40000 range.
        # Sample uses total ~45000.
        TOTAL_TABLE_WIDTH = 45000
        col_widths = []
        
        for spec in specs:
            # spec = [align, width_info]
            # width_info is specific format (e.g. {"t": "ColWidthDefault"}) or explicit float
            # If float, it's relative?
            # Let's simplify: split evenly if unknown
            col_widths.append(int(TOTAL_TABLE_WIDTH / col_cnt))
            
        # 3. Generate Table XML
        import time
        import random
        tbl_id = str(int(time.time() * 1000) % 100000000 + random.randint(0, 10000))
        
        xml_parts = []
        
        # Table Start
        # We need to wrap table in a Run/Para structure? 
        # Yes, Table is an inline character-like object in HWPX (like image).
        # <hp:p><hp:run><hp:tbl ...>...</hp:tbl></hp:run></hp:p>
        
        # Para Start
        xml_parts.append(self._create_para_start(style_id=self.normal_style_id, para_pr_id=self.normal_para_pr_id))
        xml_parts.append(self._create_run_start(char_pr_id=0)) # Table run charPr=0 usually
        
        # Ensure table borderFill exists
        if self.table_border_fill_id is None:
            self._ensure_table_border_fill()
        
        # Table properties
        xml_parts.append(f'<hp:tbl id="{tbl_id}" zOrder="0" numberingType="TABLE" textWrap="TOP_AND_BOTTOM" textFlow="BOTH_SIDES" lock="0" dropcapstyle="None" pageBreak="CELL" repeatHeader="1" rowCnt="{row_cnt}" colCnt="{col_cnt}" cellSpacing="0" borderFillIDRef="{self.table_border_fill_id}" noAdjust="0">')
        
        # Dimensions
        xml_parts.append(f'<hp:sz width="{TOTAL_TABLE_WIDTH}" widthRelTo="ABSOLUTE" height="{row_cnt * 1000}" heightRelTo="ABSOLUTE" protect="0"/>')
        xml_parts.append('<hp:pos treatAsChar="0" affectLSpacing="0" flowWithText="1" allowOverlap="0" holdAnchorAndSO="0" vertRelTo="PARA" horzRelTo="COLUMN" vertAlign="TOP" horzAlign="LEFT" vertOffset="0" horzOffset="0"/>')
        xml_parts.append('<hp:outMargin left="0" right="0" top="0" bottom="1417"/>')
        xml_parts.append('<hp:inMargin left="510" right="510" top="141" bottom="141"/>')
        
        # 4. Generate Rows
        occupied_cells = set() # (row, col)
        curr_row_addr = 0
        
        for row in all_rows:
            # Row = [attr, [cell, ...]]
            cells = row[1]
            
            xml_parts.append('<hp:tr>')
            
            curr_col_addr = 0
            for cell in cells:
                # Find next free column by skipping occupied cells
                while (curr_row_addr, curr_col_addr) in occupied_cells:
                    curr_col_addr += 1
                
                actual_col = curr_col_addr
                
                # Cell = [attr, align, rowspan, colspan, [blocks]]
                # Pandoc cell structure: [attr, align, rowspan, colspan, blocks]
                rowspan = cell[2]
                colspan = cell[3]
                cell_blocks = cell[4]
                
                # Mark occupied cells for this span
                for r in range(rowspan):
                    for c in range(colspan):
                        occupied_cells.add((curr_row_addr + r, actual_col + c))

                # Calculate cell width based on colspan
                # Sum widths of columns covered
                cell_width = 0
                for i in range(colspan):
                    if actual_col + i < len(col_widths):
                        cell_width += col_widths[actual_col + i]
                    else:
                        cell_width += int(TOTAL_TABLE_WIDTH / col_cnt)

                sublist_id = str(int(time.time() * 100000) % 1000000000 + random.randint(0, 100000))
                
                cell_content_xml = self._process_blocks(cell_blocks)
                
                # TC Start
                xml_parts.append(f'<hp:tc name="" header="0" hasMargin="0" protect="0" editable="0" dirty="0" borderFillIDRef="{self.table_border_fill_id}">')
                
                # SubList
                xml_parts.append(f'<hp:subList id="{sublist_id}" textDirection="HORIZONTAL" lineWrap="BREAK" vertAlign="TOP" linkListIDRef="0" linkListNextIDRef="0" textWidth="0" textHeight="0" hasTextRef="0" hasNumRef="0">')
                xml_parts.append(cell_content_xml)
                xml_parts.append('</hp:subList>')
                
                # Cell Address & Span
                xml_parts.append(f'<hp:cellAddr colAddr="{actual_col}" rowAddr="{curr_row_addr}"/>')
                xml_parts.append(f'<hp:cellSpan colSpan="{colspan}" rowSpan="{rowspan}"/>')
                xml_parts.append(f'<hp:cellSz width="{cell_width}" height="1000"/>')
                xml_parts.append('<hp:cellMargin left="510" right="510" top="141" bottom="141"/>')
                
                xml_parts.append('</hp:tc>')
                
                # Advance current column by the span of this cell in the current row
                curr_col_addr += colspan
                
            xml_parts.append('</hp:tr>')
            curr_row_addr += 1
            
        xml_parts.append('</hp:tbl>')
        xml_parts.append('</hp:run>')
        xml_parts.append('</hp:p>')
        
        return "".join(xml_parts)

    def _ensure_table_border_fill(self):
        """Ensure a borderFill for tables exists in header.xml"""
        if self.table_border_fill_id is not None:
            return self.table_border_fill_id
        
        # Create new borderFill ID
        self.max_border_fill_id += 1
        self.table_border_fill_id = self.max_border_fill_id
        
        # Create borderFill element
        border_fill_xml = f'''<hh:borderFill xmlns:hh="http://www.hancom.co.kr/hwpml/2011/head" xmlns:hc="http://www.hancom.co.kr/hwpml/2011/core" id="{self.table_border_fill_id}" threeD="0" shadow="0" slash="NONE" backSlash="NONE" crookedSlash="0" counterstrike="0">
    <hh:leftBorder type="SOLID" width="0.12 mm" color="#000000"/>
    <hh:rightBorder type="SOLID" width="0.12 mm" color="#000000"/>
    <hh:topBorder type="SOLID" width="0.12 mm" color="#000000"/>
    <hh:bottomBorder type="SOLID" width="0.12 mm" color="#000000"/>
    <hh:diagonal type="NONE" crooked="0"/>
    <hc:fill>
      <hc:fillColorPattern type="NONE" foreColor="#FFFFFF" backColor="#FFFFFF"/>
    </hc:fill>
</hh:borderFill>'''
        
        bf_elem = ET.fromstring(border_fill_xml)
        bf_container = self.header_root.find('.//hh:borderFills', self.namespaces)
        if bf_container is None:
            bf_container = ET.SubElement(self.header_root, '{http://www.hancom.co.kr/hwpml/2011/head}borderFills')
        bf_container.append(bf_elem)
        
        return self.table_border_fill_id
    # === END ORIGINAL TABLE HANDLING ===

    def _handle_para(self, content, para_styles=None):
        """Handle paragraph with style preservation - UPDATED to support indentation"""
        # NEW: Get paragraph styles from pre-extracted HTML styles based on content
        if para_styles is None and self.html_para_styles:
            # Extract text content from this paragraph to match against HTML
            para_text = self._get_plain_text(content)[:100]  # First 100 chars
            
            if para_text in self.html_para_styles:
                html_styles = self.html_para_styles[para_text]
                para_styles = {}
                
                if 'padding-left' in html_styles:
                    para_styles['padding-left'] = self._convert_size_to_hwp(html_styles['padding-left'])
                if 'margin-left' in html_styles:
                    para_styles['margin-left'] = self._convert_size_to_hwp(html_styles['margin-left'])
                if 'text-indent' in html_styles:
                    para_styles['text-indent'] = self._convert_size_to_hwp(html_styles['text-indent'])
        
        # Check for paragraph-level indentation styles
        padding_left = 0
        text_indent = 0
        
        if para_styles:
            padding_left = para_styles.get('padding-left', 0) or para_styles.get('margin-left', 0)
            text_indent = para_styles.get('text-indent', 0)
        
        # Get or create paraPr with indentation
        para_pr_id = self._get_or_create_para_pr(padding_left, text_indent)
        
        xml = self._create_para_start(style_id=self.normal_style_id, para_pr_id=para_pr_id) 
        xml += self._process_inlines(content) 
        xml += '</hp:p>'
        return xml

    def _handle_plain(self, content, para_styles=None):
        """Handle plain text with style preservation - UPDATED to support indentation"""
        # NEW: Get paragraph styles from pre-extracted HTML styles based on content
        if para_styles is None and self.html_para_styles:
            # Extract text content from this paragraph to match against HTML
            para_text = self._get_plain_text(content)[:100]  # First 100 chars
            
            if para_text in self.html_para_styles:
                html_styles = self.html_para_styles[para_text]
                para_styles = {}
                
                if 'padding-left' in html_styles:
                    para_styles['padding-left'] = self._convert_size_to_hwp(html_styles['padding-left'])
                if 'margin-left' in html_styles:
                    para_styles['margin-left'] = self._convert_size_to_hwp(html_styles['margin-left'])
                if 'text-indent' in html_styles:
                    para_styles['text-indent'] = self._convert_size_to_hwp(html_styles['text-indent'])
        
        # Check for paragraph-level indentation styles
        padding_left = 0
        text_indent = 0
        
        if para_styles:
            padding_left = para_styles.get('padding-left', 0) or para_styles.get('margin-left', 0)
            text_indent = para_styles.get('text-indent', 0)
        
        # Get or create paraPr with indentation
        para_pr_id = self._get_or_create_para_pr(padding_left, text_indent)
        
        xml = self._create_para_start(style_id=self.normal_style_id, para_pr_id=para_pr_id)
        xml += self._process_inlines(content)
        xml += '</hp:p>'
        return xml

    def _handle_header(self, content):
        """Handle headers"""
        level = content[0]
        inlines = content[2]
        header_style = min(level, 6)  # Max header level 6
        
        xml = self._create_para_start(style_id=header_style)
        xml += self._process_inlines(inlines)
        xml += '</hp:p>'
        return xml

    def _handle_bullet_list(self, list_data):
        """Handle bullet lists"""
        items = list_data if isinstance(list_data, list) else []
        result = []
        
        for item in items:
            if isinstance(item, list):
                for block in item:
                    block_type = block.get('t')
                    content = block.get('c')
                    
                    if block_type == 'Plain' or block_type == 'Para':
                        result.append(self._create_para_start())
                        result.append('<hp:run charPrIDRef="0"><hp:t>• </hp:t></hp:run>')
                        result.append(self._process_inlines(content))
                        result.append('</hp:p>')
        return "\n".join(result)

    def _handle_ordered_list(self, list_data):
        """Handle ordered lists"""
        # list_data = [list_attributes, items]
        items = list_data[1] if len(list_data) > 1 else []
        result = []
        
        for idx, item in enumerate(items, 1):
            # Each item is a list of blocks
            if isinstance(item, list):
                for block in item:
                    block_type = block.get('t')
                    content = block.get('c')
                    
                    if block_type == 'Plain' or block_type == 'Para':
                        result.append(self._create_para_start())
                        result.append(f'<hp:run charPrIDRef="0"><hp:t>{idx}. </hp:t></hp:run>')
                        result.append(self._process_inlines(content))
                        result.append('</hp:p>')
        return "\n".join(result)

    def _process_blocks(self, blocks):
        """Process Pandoc block elements"""
        result = []
        for block in blocks:
            if not isinstance(block, dict):
                continue
                
            block_type = block.get('t')
            content = block.get('c')
            
            if block_type == 'Para':
                result.append(self._handle_para(content))
                
            elif block_type == 'Plain':
                result.append(self._handle_plain(content))
                
            elif block_type == 'Header':
                result.append(self._handle_header(content))
                
            elif block_type == 'BulletList':
                result.append(self._handle_bullet_list(content))
                
            elif block_type == 'OrderedList':
                result.append(self._handle_ordered_list(content))
                
            elif block_type == 'Table':
                table_xml = self._handle_table(content)
                if table_xml:
                    result.append(table_xml)
                
        return "\n".join(result)

    def _process_inlines(self, inlines, active_formats=None, base_color=None, base_size=None):
        """Process inline elements with style preservation"""
        if active_formats is None:
            active_formats = set()
        
        result = []
        
        for inline in inlines:
            inline_type = inline.get('t')
            content = inline.get('c')
            
            if inline_type == 'Str':
                char_pr_id = self._get_or_create_char_pr(
                    base_char_pr_id=0,
                    active_formats=active_formats,
                    color=base_color,
                    font_size=base_size
                )
                text = saxutils.escape(content)
                result.append(f'<hp:run charPrIDRef="{char_pr_id}"><hp:t>{text}</hp:t></hp:run>')
                
            elif inline_type == 'Space':
                char_pr_id = self._get_or_create_char_pr(
                    base_char_pr_id=0,
                    active_formats=active_formats,
                    color=base_color,
                    font_size=base_size
                )
                result.append(f'<hp:run charPrIDRef="{char_pr_id}"><hp:t> </hp:t></hp:run>')
                
            elif inline_type == 'Strong':
                new_formats = active_formats.copy()
                new_formats.add('BOLD')
                result.append(self._process_inlines(content, new_formats, base_color, base_size))
                
            elif inline_type == 'Emph':
                new_formats = active_formats.copy()
                new_formats.add('ITALIC')
                result.append(self._process_inlines(content, new_formats, base_color, base_size))
                
            elif inline_type == 'Underline':
                new_formats = active_formats.copy()
                new_formats.add('UNDERLINE')
                result.append(self._process_inlines(content, new_formats, base_color, base_size))
                
            elif inline_type == 'Strikeout':
                new_formats = active_formats.copy()
                new_formats.add('STRIKEOUT')
                result.append(self._process_inlines(content, new_formats, base_color, base_size))
                
            elif inline_type == 'Superscript':
                new_formats = active_formats.copy()
                new_formats.add('SUPERSCRIPT')
                result.append(self._process_inlines(content, new_formats, base_color, base_size))
                
            elif inline_type == 'Subscript':
                new_formats = active_formats.copy()
                new_formats.add('SUBSCRIPT')
                result.append(self._process_inlines(content, new_formats, base_color, base_size))
                
            elif inline_type == 'Span':
                # Extract styles from span attributes
                attr = content[0]
                span_inlines = content[1]
                styles = self._extract_style_from_attr(attr)
                
                new_formats = active_formats.copy()
                new_color = base_color
                new_size = base_size
                
                if styles.get('bold'):
                    new_formats.add('BOLD')
                if styles.get('italic'):
                    new_formats.add('ITALIC')
                if styles.get('underline'):
                    new_formats.add('UNDERLINE')
                if styles.get('strikeout'):
                    new_formats.add('STRIKEOUT')
                if 'color' in styles:
                    new_color = styles['color']
                if 'font-size' in styles:
                    new_size = styles['font-size']
                    
                result.append(self._process_inlines(span_inlines, new_formats, new_color, new_size))
                
            elif inline_type == 'LineBreak':
                result.append('<hp:lineseg/>')
                
        return "".join(result)

    def process(self):
        """Main processing method"""
        if not self.ast:
            return ""
        
        blocks = self.ast.get('blocks', [])
        self.output = [self._process_blocks(blocks)]
        return "\n".join(self.output)

    def get_modified_header_xml(self):
        """Return the modified header.xml content"""
        if self.header_tree is None:
            return self.header_xml_content
        
        # Update itemCnt for charProperties
        char_props = self.header_root.find('.//hh:charProperties', self.namespaces)
        if char_props is not None:
            char_count = len(char_props.findall('hh:charPr', self.namespaces))
            char_props.set('itemCnt', str(char_count))
        
        # Update itemCnt for paraProperties
        para_props = self.header_root.find('.//hh:paraProperties', self.namespaces)
        if para_props is not None:
            para_count = len(para_props.findall('hh:paraPr', self.namespaces))
            para_props.set('itemCnt', str(para_count))
        
        # Update itemCnt for borderFills
        border_fills = self.header_root.find('.//hh:borderFills', self.namespaces)
        if border_fills is not None:
            border_fill_count = len(border_fills.findall('hh:borderFill', self.namespaces))
            border_fills.set('itemCnt', str(border_fill_count))
        
        return ET.tostring(self.header_root, encoding='unicode', method='xml')

    @staticmethod
    def convert_to_hwpx(input_path, output_path, reference_path):
        """Convert input file to HWPX format using reference template"""
        # Read reference HWPX
        with zipfile.ZipFile(reference_path, 'r') as ref_zip:
            header_xml = ref_zip.read('Contents/header.xml').decode('utf-8')
            section0_xml = ref_zip.read('Contents/section0.xml').decode('utf-8')
        
        # Read input file content if it's HTML
        html_content = None
        if input_path.lower().endswith('.html'):
            with open(input_path, 'r', encoding='utf-8') as f:
                html_content = f.read()
        
        # Convert to JSON AST using pypandoc
        json_str = pypandoc.convert_file(input_path, 'json', format=None)
        ast = json.loads(json_str)
        
        # Process with style preservation
        converter = PandocToHwpx(json_ast=ast, header_xml_content=header_xml, html_content=html_content)
        section_content = converter.process()
        modified_header = converter.get_modified_header_xml()
        
        # Create section XML
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
        
        # Create output HWPX
        with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as out_zip:
            # Copy all files from reference except header.xml and section0.xml
            with zipfile.ZipFile(reference_path, 'r') as ref_zip:
                for item in ref_zip.namelist():
                    if item not in ['Contents/header.xml', 'Contents/section0.xml']:
                        out_zip.writestr(item, ref_zip.read(item))
            
            # Write modified files
            out_zip.writestr('Contents/header.xml', modified_header.encode('utf-8'))
            out_zip.writestr('Contents/section0.xml', section_xml.encode('utf-8'))