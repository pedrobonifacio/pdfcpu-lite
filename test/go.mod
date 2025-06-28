module test

go 1.23.0

toolchain go1.24.2

replace github.com/pedrobonifacio/pdfcpu-lite => ../

require github.com/pedrobonifacio/pdfcpu-lite v0.0.0-00010101000000-000000000000

require (
	github.com/hhrutter/lzw v1.0.0 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	golang.org/x/image v0.28.0 // indirect
	golang.org/x/text v0.26.0 // indirect
)
