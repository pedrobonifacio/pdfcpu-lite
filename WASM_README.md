# WASM-Compatible PDF Optimization Library

This PDF library has been modified for full WASM compatibility by removing all `os` package dependencies.

## ✅ What Works in WASM Mode

### Core PDF Optimization
- ✅ **Duplicate object removal** - Removes redundant PDF objects
- ✅ **Compression optimization** - Optimizes stream compression  
- ✅ **XRef table optimization** - Optimizes cross-reference tables
- ✅ **Stream compression** - Compresses content streams
- ✅ **Metadata optimization** - Optimizes PDF metadata
- ✅ **Content stream optimization** - Optimizes page content
- ✅ **Image optimization** - Optimizes embedded images

### In-Memory Operations
- ✅ **Byte-to-byte processing** - Input: `[]byte`, Output: `[]byte`
- ✅ **io.Writer compatibility** - Works with `bytes.Buffer`
- ✅ **io.ReadSeeker compatibility** - Works with `bytes.Reader`

## Usage Example

```go
package main

import (
    "bytes"
    api "github.com/pedrobonifacio/pdfcpu-lite"
)

func optimizePDF(inputPDF []byte) ([]byte, error) {
    // Simple optimization
    return api.Optimize(inputPDF, nil)
}

func advancedOptimization(inputPDF []byte) ([]byte, error) {
    // Advanced: Read, validate, and optimize
    ctx, err := api.ReadValidateAndOptimize(bytes.NewReader(inputPDF), nil)
    if err != nil {
        return nil, err
    }
    
    // Write to buffer
    var output bytes.Buffer
    err = api.WriteContextF(ctx, &output)
    if err != nil {
        return nil, err
    }
    
    return output.Bytes(), nil
}
```

## ❌ Disabled for WASM Compatibility

- **Font installation from file system** - `InstallTrueTypeFont()`
- **Font collection installation** - `InstallTrueTypeCollection()`
- **Font file reading** - `ReadFont()`
- **Font subsetting** - Requires file system access

## Alternative: In-Memory Font Operations

If you need font operations, use the in-memory alternative:

```go
// ✅ This works in WASM mode
err := api.InstallFontFromBytes(fontDir, fontName, fontBytes)
```

## Building for WASM

```bash
# Standard build
go build -o pdfcpu-lite

# WASM build (when needed)
GOOS=js GOARCH=wasm go build -o pdfcpu.wasm
```

## Changes Made for WASM Compatibility

1. **Removed `*os.File` from `WriteContext` struct**
2. **Eliminated file operations in `CoreWriteContext`**  
3. **Updated `setFileSizeOfWrittenFile` to use write offset**
4. **Disabled file-based font functions with clear error messages**
5. **All operations now work through `io.Writer`/`io.Reader` interfaces**

The core PDF optimization functionality remains fully intact and functional!
