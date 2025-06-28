package main

import (
	"fmt"
	"io/ioutil"
	"os"

	api "github.com/pedrobonifacio/pdfcpu-lite"
)

func main() {
	fmt.Println("Testing PDF optimization...")

	if _, err := os.Stat("test.pdf"); err != nil {
		fmt.Println("❌ test.pdf not found")
		return
	}

	inputPDF, err := ioutil.ReadFile("test.pdf")
	if err != nil {
		fmt.Printf("❌ Failed to read test.pdf: %v\n", err)
		return
	}

	optimizedPDF, err := api.Optimize(inputPDF, nil)
	if err != nil {
		fmt.Printf("❌ Optimization failed: %v\n", err)
		return
	}

	fmt.Printf("✅ Original: %d bytes\n", len(inputPDF))
	fmt.Printf("✅ Optimized: %d bytes\n", len(optimizedPDF))

	if len(optimizedPDF) < len(inputPDF) {
		reduction := float64(len(inputPDF)-len(optimizedPDF)) / float64(len(inputPDF)) * 100
		fmt.Printf("✅ Reduced by %.1f%%\n", reduction)
	}
}
