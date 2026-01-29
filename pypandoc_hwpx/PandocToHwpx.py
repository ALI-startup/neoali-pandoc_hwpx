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

class PandocToHwpx:
    def __init__(self, json_ast=None, header_xml_content=None, html_content=None):
        self.ast = json_ast
        self.output = []
        self.header_xml_content = header_xml_content
        self.html_content = html_content
        
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
        # cache key: (base_char_pr_id, frozenset(active_formats), color) -> new_char_pr_id
        self.char_pr_cache = {} 
        self.max_char_pr_id = 0
        self.max_para_pr_id = 0
        
        self.images = [] # metadata for images

        # Metadata extraction
        self.title = None
        self._extract_metadata()

        if self.header_xml_content:
            self._parse_styles_and_init_xml(self.header_xml_content)

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
            # Ensure proper format
            if len(color) == 4:  # #RGB -> #RRGGBB
                return f'#{color[1]}{color[1]}{color[2]}{color[2]}{color[3]}{color[3]}'.upper()
            return color.upper()
        
        # If it's rgb(r, g, b) or rgba(r, g, b, a)
        if color.startswith('rgb'):
            match = re.search(r'rgba?\((\d+),\s*(\d+),\s*(\d+)', color)
            if match:
                r, g, b = match.groups()
                return f'#{int(r):02X}{int(g):02X}{int(b):02X}'
        
        # Default fallback
        return '#000000'

    def _pt_to_hwp_units(self, pt_str):
        """Convert point size to HWP units (1pt = 100 units)"""
        try:
            # Handle both "11pt" and "11"
            pt_str = str(pt_str).lower().replace('pt', '').strip()
            pt = float(pt_str)
            return int(pt * 100)
        except:
            return 1000  # Default 10pt

    def _extract_style_from_attr(self, attr):
        """Extract style properties from Pandoc attr [id, [classes], [[key, val]]]"""
        if not attr or len(attr) < 3:
            return {}
        
        styles = {}
        attr_dict = dict(attr[2])  # Convert list of [key, val] to dict
        
        # Parse style attribute if present
        if 'style' in attr_dict:
            style_str = attr_dict['style']
            # Parse CSS-like styles: "color: #FF0000; background-color: #00FF00"
            for style_part in style_str.split(';'):
                if ':' in style_part:
                    key, value = style_part.split(':', 1)
                    key = key.strip().lower()
                    value = value.strip()
                    
                    if key == 'color':
                        styles['color'] = value
                    elif key == 'background-color' or key == 'background':
                        styles['background'] = value
                    elif key == 'font-weight':
                        if 'bold' in value.lower() or value == '700' or value == '800' or value == '900':
                            styles['bold'] = True
                    elif key == 'font-style':
                        if 'italic' in value.lower():
                            styles['italic'] = True
                    elif key == 'text-decoration':
                        if 'underline' in value.lower():
                            styles['underline'] = True
                        if 'line-through' in value.lower():
                            styles['strikeout'] = True
                    elif key == 'font-size':
                        styles['font-size'] = value
        
        return styles

    def _parse_styles_and_init_xml(self, header_xml_content):
        """Parse header.xml to extract style mappings and prepare for modifications"""
        # Parse XML
        self.header_tree = ET.ElementTree(ET.fromstring(header_xml_content))
        self.header_root = self.header_tree.getroot()
        
        # Extract existing styles
        styles = self.header_root.findall('.//hh:style', self.namespaces)
        for style in styles:
            style_id = int(style.get('id', 0))
            eng_name = style.get('engName', '')
            name = style.get('name', '')
            
            # Map English names to IDs
            if eng_name:
                self.dynamic_style_map[eng_name] = style_id
            if name == '바탕글' or eng_name == 'Normal':
                self.normal_style_id = style_id
                para_pr_ref = style.get('paraPrIDRef')
                if para_pr_ref:
                    self.normal_para_pr_id = int(para_pr_ref)
        
        # Find max charPr ID
        char_props = self.header_root.findall('.//hh:charPr', self.namespaces)
        for cp in char_props:
            cp_id = int(cp.get('id', 0))
            if cp_id > self.max_char_pr_id:
                self.max_char_pr_id = cp_id
        
        # Find max paraPr ID
        para_props = self.header_root.findall('.//hh:paraPr', self.namespaces)
        for pp in para_props:
            pp_id = int(pp.get('id', 0))
            if pp_id > self.max_para_pr_id:
                self.max_para_pr_id = pp_id

    def _get_or_create_char_pr(self, base_char_pr_id=0, active_formats=None, color=None, font_size=None):
        """Get or create a character property with the specified formatting"""
        if active_formats is None:
            active_formats = set()
        
        # Create cache key
        cache_key = (base_char_pr_id, frozenset(active_formats), color, font_size)
        
        # Return cached ID if exists
        if cache_key in self.char_pr_cache:
            return self.char_pr_cache[cache_key]
        
        # Find base charPr node
        base_node = self.header_root.find(f'.//hh:charPr[@id="{base_char_pr_id}"]', self.namespaces)
        if base_node is None:
            return base_char_pr_id
        
        # Create new charPr node
        new_node = copy.deepcopy(base_node)
        self.max_char_pr_id += 1
        new_id = str(self.max_char_pr_id)
        new_node.set('id', new_id)
        
        # Apply color
        if color:
            hwp_color = self._convert_color_to_hwp(color)
            new_node.set('textColor', hwp_color)
        
        # Apply font size
        if font_size:
            hwp_size = self._pt_to_hwp_units(font_size)
            new_node.set('height', str(hwp_size))
        
        # Apply formatting
        if 'BOLD' in active_formats:
            if new_node.find('hh:bold', self.namespaces) is None:
                ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}bold')
        
        if 'ITALIC' in active_formats:
            if new_node.find('hh:italic', self.namespaces) is None:
                ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}italic')
        
        if 'UNDERLINE' in active_formats:
            underline = new_node.find('hh:underline', self.namespaces)
            if underline is not None:
                underline.set('type', 'SOLID')
            else:
                ul = ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}underline')
                ul.set('type', 'SOLID')
                ul.set('shape', 'SOLID')
                ul.set('color', '#000000')
        
        if 'STRIKEOUT' in active_formats:
            strikeout = new_node.find('hh:strikeout', self.namespaces)
            if strikeout is not None:
                strikeout.set('shape', 'SOLID')
            else:
                so = ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}strikeout')
                so.set('shape', 'SOLID')
                so.set('color', '#000000')
        
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
        
        # Update cache
        self.char_pr_cache[cache_key] = new_id
        
        return new_id

    # --- LIST HANDLING ---
    
    ORDERED_NUM_XML = """
    <hh:numbering id="{id}" start="1" xmlns:hh="http://www.hancom.co.kr/hwpml/2011/head">
      <hh:paraHead start="1" level="1" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">^1.</hh:paraHead>
      <hh:paraHead start="1" level="2" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="LATIN_CAPITAL" charPrIDRef="4294967295" checkable="0">^2.</hh:paraHead>
      <hh:paraHead start="1" level="3" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="ROMAN_SMALL" charPrIDRef="4294967295" checkable="0">^3.</hh:paraHead>
      <hh:paraHead start="1" level="4" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">^4.</hh:paraHead>
      <hh:paraHead start="1" level="5" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="LATIN_CAPITAL" charPrIDRef="4294967295" checkable="0">^5.</hh:paraHead>
      <hh:paraHead start="1" level="6" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="ROMAN_SMALL" charPrIDRef="4294967295" checkable="0">^6.</hh:paraHead>
      <hh:paraHead start="1" level="7" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">^7.</hh:paraHead>
    </hh:numbering>
    """

    BULLET_NUM_XML = """
    <hh:numbering id="{id}" start="1" xmlns:hh="http://www.hancom.co.kr/hwpml/2011/head">
      <hh:paraHead start="1" level="1" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">●</hh:paraHead>
      <hh:paraHead start="1" level="2" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">○</hh:paraHead>
      <hh:paraHead start="1" level="3" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">■</hh:paraHead>
      <hh:paraHead start="1" level="4" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">●</hh:paraHead>
      <hh:paraHead start="1" level="5" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">○</hh:paraHead>
      <hh:paraHead start="1" level="6" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">■</hh:paraHead>
      <hh:paraHead start="1" level="7" align="LEFT" useInstWidth="1" autoIndent="0" widthAdjust="0" textOffsetType="PERCENT" textOffset="50" numFormat="DIGIT" charPrIDRef="4294967295" checkable="0">●</hh:paraHead>
    </hh:numbering>
    """

    def _init_numbering_structure(self, root):
        numberings_node = root.find('.//hh:numberings', self.namespaces)
        if numberings_node is None:
            numberings_node = ET.SubElement(root, '{http://www.hancom.co.kr/hwpml/2011/head}numberings')
    
    def _create_numbering(self, type='ORDERED', start_num=1):
        root = self.header_root
        max_num_id = 0
        for num in root.findall('.//hh:numbering', self.namespaces):
            nid = int(num.get('id', 0))
            if nid > max_num_id:
                max_num_id = nid
        
        new_id = str(max_num_id + 1)
        
        if type == 'ORDERED':
            template = self.ORDERED_NUM_XML
        else:
            template = self.BULLET_NUM_XML
        
        xml_str = template.format(id=new_id).strip()
        new_node = ET.fromstring(xml_str)
        
        new_node.set('start', str(start_num))
        
        numberings_node = root.find('.//hh:numberings', self.namespaces)
        if numberings_node is None:
             self._init_numbering_structure(root)
             numberings_node = root.find('.//hh:numberings', self.namespaces)
             
        numberings_node.append(new_node)
        return new_id

    def _get_list_para_pr(self, num_id, level):
        base_id = self.normal_para_pr_id
        base_node = self.header_root.find(f'.//hh:paraPr[@id="{base_id}"]', self.namespaces)
        if base_node is None:
            return base_id 
            
        new_node = copy.deepcopy(base_node)
        self.max_para_pr_id += 1
        new_id = str(self.max_para_pr_id)
        new_node.set('id', new_id)
        
        heading = new_node.find('hh:heading', self.namespaces)
        if heading is None:
            heading = ET.SubElement(new_node, '{http://www.hancom.co.kr/hwpml/2011/head}heading')
        heading.set('type', 'NUMBER')
        heading.set('idRef', str(num_id))
        heading.set('level', str(level))
        
        indent_per_level = 2000
        current_indent = (level) * indent_per_level 
        
        for margin_node in new_node.findall('.//hc:left', self.namespaces):
            original_val = int(margin_node.get('value', 0))
            new_val = original_val + current_indent
            margin_node.set('value', str(new_val))
            
        hanging_val = 2000
        for intent_node in new_node.findall('.//hc:intent', self.namespaces):
            intent_node.set('value', str(-hanging_val))
            
        for left_node in new_node.findall('.//hc:left', self.namespaces):
            val = (level + 1) * hanging_val
            left_node.set('value', str(val))

        para_props = self.header_root.find('.//hh:paraProperties', self.namespaces)
        if para_props is not None:
            para_props.append(new_node)
            
        return new_id

    def _handle_bullet_list(self, content, level=0):
        num_id = self._create_numbering('BULLET')
        
        results = []
        for item_blocks in content:
            for i, block in enumerate(item_blocks):
                b_type = block.get('t')
                b_content = block.get('c')
                
                list_para_pr = self._get_list_para_pr(num_id, level)
                
                if b_type == 'Para' or b_type == 'Plain':
                     xml = self._create_para_start(style_id=self.normal_style_id, para_pr_id=list_para_pr)
                     xml += self._process_inlines(b_content)
                     xml += '</hp:p>'
                     results.append(xml)
                elif b_type == 'BulletList':
                    results.append(self._handle_bullet_list(b_content, level=level+1))
                elif b_type == 'OrderedList':
                    results.append(self._handle_ordered_list(b_content, level=level+1))
                else:
                    results.append(self._process_blocks([block]))

        return "\n".join(results)

    def _handle_ordered_list(self, content, level=0):
        attrs = content[0]
        start_num = attrs[0]
        items = content[1]
        
        num_id = self._create_numbering('ORDERED', start_num=start_num)
        
        results = []
        for item_blocks in items:
            for block in item_blocks:
                b_type = block.get('t')
                b_content = block.get('c')
                
                list_para_pr = self._get_list_para_pr(num_id, level)

                if b_type == 'Para' or b_type == 'Plain':
                     xml = self._create_para_start(style_id=self.normal_style_id, para_pr_id=list_para_pr)
                     xml += self._process_inlines(b_content)
                     xml += '</hp:p>'
                     results.append(xml)
                elif b_type == 'BulletList':
                     results.append(self._handle_bullet_list(b_content, level=level+1))
                elif b_type == 'OrderedList':
                     results.append(self._handle_ordered_list(b_content, level=level+1))
                else:
                     results.append(self._process_blocks([block]))

        return "\n".join(results)

    def _create_para_start(self, style_id=0, para_pr_id=None):
        """Create opening tag for a paragraph"""
        if para_pr_id is None:
            para_pr_id = self.normal_para_pr_id
        return f'<hp:p paraPrIDRef="{para_pr_id}" styleIDRef="{style_id}" pageBreak="0" columnBreak="0" merged="0">'

    def _process_blocks(self, blocks):
        """Process Pandoc block elements"""
        result = []
        for block in blocks:
            block_type = block.get('t')
            content = block.get('c')
            
            if block_type == 'Para' or block_type == 'Plain':
                result.append(self._create_para_start())
                result.append(self._process_inlines(content))
                result.append('</hp:p>')
                
            elif block_type == 'Header':
                level = content[0]
                inlines = content[2]
                header_style = min(level, 6)  # Max header level 6
                result.append(self._create_para_start(style_id=header_style))
                result.append(self._process_inlines(inlines))
                result.append('</hp:p>')
                
            elif block_type == 'BulletList':
                result.append(self._handle_bullet_list(content))
                
            elif block_type == 'OrderedList':
                result.append(self._handle_ordered_list(content))
                
            elif block_type == 'Table':
                result.append(self._process_table(content))
                
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

    def _process_table(self, table_content):
        """Process table - simplified version"""
        # This is a placeholder - full table implementation would be complex
        result = ['<hp:p paraPrIDRef="1" styleIDRef="0" pageBreak="0" columnBreak="0" merged="0">']
        result.append('<hp:run charPrIDRef="0"><hp:t>[Table content]</hp:t></hp:run>')
        result.append('</hp:p>')
        return "\n".join(result)

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
        
        return ET.tostring(self.header_root, encoding='unicode', method='xml')

    @staticmethod
    def convert_to_hwpx(input_file, output_file, reference_hwpx):
        """Convert input file to HWPX format using reference template"""
        # Read reference HWPX
        with zipfile.ZipFile(reference_hwpx, 'r') as ref_zip:
            header_xml = ref_zip.read('Contents/header.xml').decode('utf-8')
            section0_xml = ref_zip.read('Contents/section0.xml').decode('utf-8')
        
        # Read input file content if it's HTML
        html_content = None
        if input_file.lower().endswith('.html'):
            with open(input_file, 'r', encoding='utf-8') as f:
                html_content = f.read()
        
        # Convert to JSON AST using pypandoc
        json_str = pypandoc.convert_file(input_file, 'json', format=None)
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
          <hp:noteLine length="-1" type="SOLID" width="0.25 mm" color="#000000"/>
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
        with zipfile.ZipFile(output_file, 'w', zipfile.ZIP_DEFLATED) as out_zip:
            # Copy all files from reference except header.xml and section0.xml
            with zipfile.ZipFile(reference_hwpx, 'r') as ref_zip:
                for item in ref_zip.namelist():
                    if item not in ['Contents/header.xml', 'Contents/section0.xml']:
                        out_zip.writestr(item, ref_zip.read(item))
            
            # Write modified files
            out_zip.writestr('Contents/header.xml', modified_header.encode('utf-8'))
            out_zip.writestr('Contents/section0.xml', section_xml.encode('utf-8'))