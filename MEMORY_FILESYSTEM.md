# Using Afero Memory Filesystem with pdfcpu

This guide explains how to use Afero's memory filesystem with pdfcpu for in-memory PDF operations without touching the actual filesystem.

## Overview

pdfcpu now supports using [Afero](https://github.com/spf13/afero) as an abstraction layer for file operations. This enables you to:

- Process PDFs entirely in memory
- Run tests without filesystem side effects
- Create isolated PDF processing environments
- Build applications that don't require disk access

## Latest Updates

**✅ COMPLETED FEATURES:**
- ✅ Afero dependency integration (`github.com/spf13/afero v1.14.0`)
- ✅ FileSystem abstraction layer with OS and Memory implementations
- ✅ Configuration model extension with `FileSystem` field
- ✅ Enhanced file I/O functions (`WriteReaderFS`, `WriteImageFS`, `WriteFS`, `CopyFileFS`)
- ✅ High-level `MemoryPDFProcessor` wrapper class
- ✅ **NEW: Filesystem-aware reading** (`ReadFileFS`, `ReadFileWithContextFS`)
- ✅ **NEW: Filesystem-aware writing** (`WriteContextFS`)
- ✅ Comprehensive testing suite with memory filesystem scenarios
- ✅ Complete documentation and examples
- ✅ **NEW: Advanced demos** showing complex memory operations

**🔧 API EXTENSIONS:**
The integration now includes filesystem-aware versions of core pdfcpu functions:
- `ReadFileFS()` - Read PDFs from memory filesystem
- `ReadFileWithContextFS()` - Context-aware reading from memory filesystem  
- `WriteContextFS()` - Write PDF contexts to memory filesystem
- `WriteFS()` - Generic file writing to memory filesystem
- `CopyFileFS()` - File copying within memory filesystem
- `WriteReaderFS()` - Stream writing to memory filesystem
- `WriteImageFS()` - Image extraction to memory filesystem

## Quick Start

### Method 1: Using MemoryPDFProcessor (Easiest)

```go
package main

import (
    "fmt"
    "github.com/pdfcpu/pdfcpu/pkg/pdfcpu"
)

func main() {
    // Create a memory-based PDF processor
    mp := pdfcpu.NewMemoryPDFProcessor()
    
    // Write some content to memory
    mp.WriteFile("test.txt", []byte("Hello Memory!"))
    
    // Check if file exists
    if mp.FileExists("test.txt") {
        fmt.Println("File exists in memory!")
    }
    
    // Read the file back
    data, _ := mp.ReadFile("test.txt")
    fmt.Printf("Content: %s\n", string(data))
    
    // List all files in memory
    files, _ := mp.ListFiles()
    fmt.Printf("Files: %v\n", files)
}
```

### Method 2: Using Configuration (More Control)

```go
package main

import (
    "github.com/pdfcpu/pdfcpu/pkg/pdfcpu/model"
    "github.com/spf13/afero"
)

func main() {
    // Create configuration with memory filesystem
    conf := model.NewDefaultConfiguration()
    conf.SetMemoryFileSystem()
    
    // Or set it directly:
    // conf.FileSystem = afero.NewMemMapFs()
    
    // Get the filesystem for direct operations
    fs := conf.GetFileSystem()
    
    // Use standard Afero operations
    afero.WriteFile(fs, "example.txt", []byte("Direct Afero!"), 0644)
    
    exists, _ := afero.Exists(fs, "example.txt")
    fmt.Printf("File exists: %v\n", exists)
}
```

### Method 3: Direct Afero Usage

```go
package main

import (
    "github.com/spf13/afero"
    "github.com/pdfcpu/pdfcpu/pkg/pdfcpu/model"
)

func main() {
    // Create memory filesystem directly
    memFs := afero.NewMemMapFs()
    
    // Configure pdfcpu to use it
    conf := model.NewDefaultConfiguration()
    conf.FileSystem = memFs
    
    // Now all pdfcpu operations using this config will use memory filesystem
    // (Future API enhancements will leverage this automatically)
}
```

## PDF Operations in Memory

### Creating PDFs in Memory

```go
package main

import (
    "bytes"
    "github.com/pdfcpu/pdfcpu/pkg/api"
    "github.com/pdfcpu/pdfcpu/pkg/pdfcpu"
)

func main() {
    mp := pdfcpu.NewMemoryPDFProcessor()
    
    // Create PDF content in JSON format
    jsonContent := `{
        "pages": [
            {
                "content": {
                    "text": [
                        {
                            "value": "Hello Memory PDF!",
                            "x": 100,
                            "y": 700,
                            "fontname": "Helvetica",
                            "fontsize": 12
                        }
                    ]
                }
            }
        ]
    }`
    
    // Write JSON to memory
    mp.WriteFile("content.json", []byte(jsonContent))
    
    // Get reader for API
    jsonReader, _ := mp.GetReader("content.json")
    
    // Create PDF in memory
    var pdfBuffer bytes.Buffer
    api.Create(nil, jsonReader, &pdfBuffer, mp.GetConfiguration())
    
    // Store PDF in memory filesystem
    mp.WriteReader("output.pdf", &pdfBuffer)
    
    // Verify PDF was created
    pdfData, _ := mp.ReadFile("output.pdf")
    fmt.Printf("Created PDF of %d bytes in memory\n", len(pdfData))
}
```

## Advanced Usage

### Copying Between Memory and OS Filesystem

```go
// Copy from OS to memory
mp := pdfcpu.NewMemoryPDFProcessor()
err := mp.CopyFromOS("/path/to/input.pdf", "memory-input.pdf")

// Process in memory...

// Copy result back to OS
err = mp.CopyToOS("memory-output.pdf", "/path/to/output.pdf")
```

### Working with Multiple Memory Filesystems

```go
// Create separate memory environments
mp1 := pdfcpu.NewMemoryPDFProcessor()
mp2 := pdfcpu.NewMemoryPDFProcessor()

// Each has its own isolated filesystem
mp1.WriteFile("test.txt", []byte("Environment 1"))
mp2.WriteFile("test.txt", []byte("Environment 2"))

// They don't interfere with each other
data1, _ := mp1.ReadFile("test.txt") // "Environment 1"
data2, _ := mp2.ReadFile("test.txt") // "Environment 2"
```

### Integration with Existing pdfcpu APIs

The memory filesystem integrates with pdfcpu's configuration system. Future enhancements will make APIs automatically respect the configured filesystem, but you can already start using it for preparation:

```go
conf := model.NewDefaultConfiguration()
conf.SetMemoryFileSystem()

// Pass this configuration to pdfcpu APIs
// As APIs are enhanced, they'll automatically use the memory filesystem
```

## Advanced Usage

### Filesystem-Aware PDF Operations

With the latest updates, you can now use filesystem-aware versions of core pdfcpu functions:

```go
package main

import (
    "context"
    "github.com/pdfcpu/pdfcpu/pkg/pdfcpu"
    "github.com/pdfcpu/pdfcpu/pkg/pdfcpu/model"
    "github.com/spf13/afero"
)

func advancedMemoryOperations() {
    // Create memory filesystem and configuration
    memFs := afero.NewMemMapFs()
    conf := model.NewDefaultConfiguration()
    conf.FileSystem = memFs
    
    // Write sample PDF content to memory (in practice, this would be real PDF data)
    afero.WriteFile(memFs, "input.pdf", []byte("PDF_CONTENT"), 0644)
    
    // Read PDF from memory filesystem
    ctx, err := pdfcpu.ReadFileFS("input.pdf", conf)
    if err != nil {
        // Handle error
        return
    }
    
    // Process the PDF context (modify, optimize, etc.)
    // ... your PDF processing logic here ...
    
    // Write the result back to memory filesystem
    ctx.Write.DirName = ""
    ctx.Write.FileName = "output.pdf"
    err = pdfcpu.WriteContextFS(ctx)
    if err != nil {
        // Handle error
        return
    }
    
    // The processed PDF is now in memory at "output.pdf"
    // You can read it back or transfer to OS filesystem as needed
}
```

### Multi-PDF Memory Processing

Process multiple PDFs entirely in memory:

```go
func processMultiplePDFs() {
    mp := pdfcpu.NewMemoryPDFProcessor()
    
    // Load multiple PDFs into memory
    documents := []string{"doc1.pdf", "doc2.pdf", "doc3.pdf"}
    for _, doc := range documents {
        // In practice, load actual PDF content
        mp.WriteFile(doc, []byte("PDF_CONTENT_"+doc))
    }
    
    // Process each document in memory
    files, _ := mp.ListFiles()
    for _, file := range files {
        if strings.HasSuffix(file, ".pdf") {
            // Read, process, and write back processed version
            content, _ := mp.ReadFile(file)
            processedContent := processPDF(content) // Your processing logic
            processedName := strings.Replace(file, ".pdf", "_processed.pdf", 1)
            mp.WriteFile(processedName, processedContent)
        }
    }
    
    // All processing done in memory - no filesystem touched
}
```

## Benefits

1. **No Filesystem Dependencies**: Perfect for serverless environments or containers with read-only filesystems
2. **Faster Tests**: No I/O overhead during testing
3. **Isolation**: Each memory filesystem is completely isolated
4. **Security**: Sensitive PDFs never touch disk
5. **Cleaner Code**: No need to manage temporary files
6. **Complete Control**: Full PDF processing pipelines in memory

## Examples

- **Basic Demo**: `examples/memory_demo.go` - Shows basic memory filesystem usage
- **Advanced Demo**: `examples/advanced/advanced_memory_demo.go` - Complex in-memory operations

Run the examples:
```bash
go run examples/memory_demo.go
go run examples/advanced/advanced_memory_demo.go
```

## Current Status

✅ **Fully Implemented:**
- Memory filesystem abstraction layer
- Configuration integration with FileSystem field  
- Core file I/O operations (read, write, copy)
- PDF reading and writing with memory filesystem
- Image extraction to memory filesystem
- High-level MemoryPDFProcessor wrapper
- Comprehensive test coverage

🔧 **Partially Implemented:**
- Some APIs still use OS filesystem by default
- Font loading still OS-based (can be extended)
- Command-line tools don't use memory filesystem yet

🚀 **Future Enhancements:**
- Extend all pdfcpu APIs to automatically detect and use configured filesystem
- Command-line interface with memory filesystem options
- Plugin system for custom filesystem implementations

## Testing

Run the memory filesystem tests:

```bash
go test -v ./pkg/pdfcpu -run TestMemory
```

## Contributing

This is a low-friction integration that maintains backward compatibility. All existing code continues to work unchanged, while new code can opt into memory filesystem usage.

To contribute:
1. Identify file operations that could use the filesystem abstraction
2. Add filesystem-aware variants of functions
3. Update APIs to optionally use configured filesystems
4. Maintain backward compatibility
