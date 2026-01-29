#!/usr/bin/env python3
# python convert.py output.html output.hwpx pypandoc_hwpx/blank.hwpx
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from pypandoc_hwpx.PandocToHwpx import PandocToHwpx

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print("Usage: python convert.py <input_file> <output_file> <reference_hwpx>")
        print("\nExample:")
        print("  python convert.py input.html output.hwpx template.hwpx")
        print("  python convert.py input.md output.hwpx template.hwpx")
        print("  python convert.py input.docx output.hwpx template.hwpx")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2]
    reference_file = sys.argv[3]
    
    try:
        PandocToHwpx.convert_to_hwpx(input_file, output_file, reference_file)
        print(f"\n✓ Conversion successful!")
        print(f"  Input:  {input_file}")
        print(f"  Output: {output_file}")
    except Exception as e:
        print(f"\n✗ Conversion failed: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)