# pypandoc-hwpx (Fork)

This repository is a **fork of**  
https://github.com/msjang/pypandoc-hwpx.git

## Overview

This fork addresses several limitations in the original `pypandoc-hwpx` project and improves the quality of HWPX conversion.

### Fixes & Improvements

- ✅ Correct handling of **text color**
- ✅ Improved **font preservation**
- ✅ Fixed **table rendering issues**

These enhancements make the generated HWPX files more faithful to the original source documents.

## Usage

Run the conversion script as follows:

```bash
python convert.py output.html output.hwpx pypandoc_hwpx/blank.hwpx
