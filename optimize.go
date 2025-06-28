/*
	Copyright 2020 The pdfcpu Authors.

	Licensed under the Apache License, Version 2.0 (the "License");
	you may not use this file except in compliance with the License.
	You may obtain a copy of the License at

		http://www.apache.org/licenses/LICENSE-2.0

	Unless required by applicable law or agreed to in writing, software
	distributed under the License is distributed on an "AS IS" BASIS,
	WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
	See the License for the specific language governing permissions and
	limitations under the License.
*/

package api

import (
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/md5"
	"crypto/rand"
	"crypto/rc4"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/binary"
	"encoding/hex"
	"encoding/xml"
	"fmt"
	"io"
	"math"
	"math/big"
	randMath "math/rand"
	"net"
	"net/http"
	"net/url"
	"path/filepath"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode/utf16"

	"github.com/pkg/errors"
	"golang.org/x/text/secure/precis"
	"golang.org/x/text/unicode/norm"
)

func ApplyBox(boxName string, b *Box, d Dict, parent *Rectangle) *Rectangle {
	if b.Rect != nil {
		if d != nil {
			d.Update(boxName, b.Rect.Array())
		}
		return b.Rect
	}

	if b.Dim != nil {
		return boxByDim(boxName, b, d, parent)
	}

	mLeft, mRight, mTop, mBot := b.MLeft, b.MRight, b.MTop, b.MBot
	if b.MLeft != 0 && -1 < b.MLeft && b.MLeft < 1 {
		// Margins relative to media box
		mLeft *= parent.Width()
		mRight *= parent.Width()
		mBot *= parent.Height()
		mTop *= parent.Height()
	}
	xmin := parent.LL.X + mLeft
	ymin := parent.LL.Y + mBot
	xmax := parent.UR.X - mRight
	ymax := parent.UR.Y - mTop
	r := NewRectangle(xmin, ymin, xmax, ymax)
	if d != nil {
		d.Update(boxName, r.Array())
	}
	if boxName == "CropBox" {
		ensureCropBoxWithinMediaBox(xmin, xmax, ymin, ymax, d, parent)
	}
	return r
}

type boxes struct {
	mediaBox, cropBox, trimBox, bleedBox, artBox *Rectangle
}

func applyBoxDefinitions(d Dict, pb *PageBoundaries, b *boxes) {
	parentBox := b.mediaBox
	if pb.Media != nil {
		// fmt.Println("add mb")
		b.mediaBox = ApplyBox("MediaBox", pb.Media, d, parentBox)
	}

	if pb.Crop != nil {
		// fmt.Println("add cb")
		b.cropBox = ApplyBox("CropBox", pb.Crop, d, parentBox)
	}

	if b.cropBox != nil {
		parentBox = b.cropBox
	}
	if pb.Trim != nil && pb.Trim.RefBox == "" {
		// fmt.Println("add tb")
		b.trimBox = ApplyBox("TrimBox", pb.Trim, d, parentBox)
	}

	if pb.Bleed != nil && pb.Bleed.RefBox == "" {
		// fmt.Println("add bb")
		b.bleedBox = ApplyBox("BleedBox", pb.Bleed, d, parentBox)
	}

	if pb.Art != nil && pb.Art.RefBox == "" {
		// fmt.Println("add ab")
		b.artBox = ApplyBox("ArtBox", pb.Art, d, parentBox)
	}
}

func updateTrimBox(d Dict, trimBox *Box, b *boxes) {
	var r *Rectangle
	switch trimBox.RefBox {
	case "media":
		r = b.mediaBox
	case "crop":
		r = b.cropBox
	case "bleed":
		r = b.bleedBox
		if r == nil {
			r = b.cropBox
		}
	case "art":
		r = b.artBox
		if r == nil {
			r = b.cropBox
		}
	}
	d.Update("TrimBox", r.Array())
	b.trimBox = r
}

func updateBleedBox(d Dict, bleedBox *Box, b *boxes) {
	var r *Rectangle
	switch bleedBox.RefBox {
	case "media":
		r = b.mediaBox
	case "crop":
		r = b.cropBox
	case "trim":
		r = b.trimBox
		if r == nil {
			r = b.cropBox
		}
	case "art":
		r = b.artBox
		if r == nil {
			r = b.cropBox
		}
	}
	d.Update("BleedBox", r.Array())
	b.bleedBox = r
}

func updateArtBox(d Dict, artBox *Box, b *boxes) {
	var r *Rectangle
	switch artBox.RefBox {
	case "media":
		r = b.mediaBox
	case "crop":
		r = b.cropBox
	case "trim":
		r = b.trimBox
		if r == nil {
			r = b.cropBox
		}
	case "bleed":
		r = b.bleedBox
		if r == nil {
			r = b.cropBox
		}
	}
	d.Update("ArtBox", r.Array())
	b.artBox = r
}

func applyBoxAssignments(d Dict, pb *PageBoundaries, b *boxes) {
	if pb.Trim != nil && pb.Trim.RefBox != "" {
		updateTrimBox(d, pb.Trim, b)
	}

	if pb.Bleed != nil && pb.Bleed.RefBox != "" {
		updateBleedBox(d, pb.Bleed, b)
	}

	if pb.Art != nil && pb.Art.RefBox != "" {
		updateArtBox(d, pb.Art, b)
	}
}

// AddPageBoundaries adds page boundaries specified by pb for selected pages.
func (ctx *Context) AddPageBoundaries(selectedPages IntSet, pb *PageBoundaries) error {
	for k, v := range selectedPages {
		if !v {
			continue
		}
		d, _, inhPAttrs, err := ctx.PageDict(k, false)
		if err != nil {
			return err
		}
		mediaBox := inhPAttrs.MediaBox
		cropBox := inhPAttrs.CropBox

		var trimBox *Rectangle
		obj, found := d.Find("TrimBox")
		if found {
			a, err := ctx.DereferenceArray(obj)
			if err != nil {
				return err
			}
			if trimBox, err = rect(ctx.XRefTable, a); err != nil {
				return err
			}
		}

		var bleedBox *Rectangle
		obj, found = d.Find("BleedBox")
		if found {
			a, err := ctx.DereferenceArray(obj)
			if err != nil {
				return err
			}
			if bleedBox, err = rect(ctx.XRefTable, a); err != nil {
				return err
			}
		}

		var artBox *Rectangle
		obj, found = d.Find("ArtBox")
		if found {
			a, err := ctx.DereferenceArray(obj)
			if err != nil {
				return err
			}
			if artBox, err = rect(ctx.XRefTable, a); err != nil {
				return err
			}
		}

		boxes := &boxes{mediaBox: mediaBox, cropBox: cropBox, trimBox: trimBox, bleedBox: bleedBox, artBox: artBox}
		applyBoxDefinitions(d, pb, boxes)
		applyBoxAssignments(d, pb, boxes)
	}
	return nil
}

// Crop sets crop box for selected pages to b.
func (ctx *Context) Crop(selectedPages IntSet, b *Box) error {
	for k, v := range selectedPages {
		if !v {
			continue
		}
		d, _, inhPAttrs, err := ctx.PageDict(k, false)
		if err != nil {
			return err
		}
		ApplyBox("CropBox", b, d, inhPAttrs.MediaBox)
	}
	return nil
}

func (xRefTable *XRefTable) collectPageBoundariesForPage(d Dict, pb []PageBoundaries, inhMediaBox, inhCropBox *Rectangle, rot, p int) error {
	if inhMediaBox != nil {
		pb[p].Media = &Box{Rect: inhMediaBox, Inherited: true}
	}
	r, err := xRefTable.resolvePageBoundary(d, "MediaBox")
	if err != nil {
		return err
	}
	if r != nil {
		pb[p].Media = &Box{Rect: r, Inherited: false}
	}
	if pb[p].Media == nil {
		return errors.New("pdfcpu: collectMediaBoxesForPageTree: mediaBox is nil")
	}

	if inhCropBox != nil {
		pb[p].Crop = &Box{Rect: inhCropBox, Inherited: true}
	}
	r, err = xRefTable.resolvePageBoundary(d, "CropBox")
	if err != nil {
		return err
	}
	if r != nil {
		pb[p].Crop = &Box{Rect: r, Inherited: false}
	}

	r, err = xRefTable.resolvePageBoundary(d, "TrimBox")
	if err != nil {
		return err
	}
	if r != nil {
		pb[p].Trim = &Box{Rect: r}
	}

	r, err = xRefTable.resolvePageBoundary(d, "BleedBox")
	if err != nil {
		return err
	}
	if r != nil {
		pb[p].Bleed = &Box{Rect: r}
	}

	r, err = xRefTable.resolvePageBoundary(d, "ArtBox")
	if err != nil {
		return err
	}
	if r != nil {
		pb[p].Art = &Box{Rect: r}
	}

	pb[p].Rot = rot

	return nil
}

func (xRefTable *XRefTable) collectMediaBoxAndCropBox(d Dict, inhMediaBox, inhCropBox **Rectangle) error {
	obj, found := d.Find("MediaBox")
	if found {
		a, err := xRefTable.DereferenceArray(obj)
		if err != nil {
			return err
		}
		if *inhMediaBox, err = rect(xRefTable, a); err != nil {
			return err
		}
		*inhCropBox = nil
	}

	obj, found = d.Find("CropBox")
	if found {
		a, err := xRefTable.DereferenceArray(obj)
		if err != nil {
			return err
		}
		if *inhCropBox, err = rect(xRefTable, a); err != nil {
			return err
		}
	}
	return nil
}

func (xRefTable *XRefTable) collectPageBoundariesForPageTreeKids(
	kids Array,
	inhMediaBox, inhCropBox **Rectangle,
	pb []PageBoundaries,
	r int,
	p *int,
	selectedPages IntSet,
) error {
	// Iterate over page tree.
	for _, o := range kids {

		if o == nil {
			continue
		}

		// Dereference next page node dict.
		indRef, ok := o.(IndirectRef)
		if !ok {
			return errors.Errorf("pdfcpu: collectPageBoundariesForPageTreeKids: corrupt page node dict")
		}

		pageNodeDict, err := xRefTable.DereferenceDict(indRef)
		if err != nil {
			return err
		}

		switch *pageNodeDict.Type() {

		case "Pages":
			if err = xRefTable.collectPageBoundariesForPageTree(&indRef, inhMediaBox, inhCropBox, pb, r, p, selectedPages); err != nil {
				return err
			}

		case "Page":
			collect := len(selectedPages) == 0
			if !collect {
				_, collect = selectedPages[(*p)+1]
			}
			if collect {
				if err = xRefTable.collectPageBoundariesForPageTree(&indRef, inhMediaBox, inhCropBox, pb, r, p, selectedPages); err != nil {
					return err
				}
			}
			*p++
		}

	}

	return nil
}

func (xRefTable *XRefTable) collectPageBoundariesForPageTree(
	root *IndirectRef,
	inhMediaBox, inhCropBox **Rectangle,
	pb []PageBoundaries,
	r int,
	p *int,
	selectedPages IntSet,
) error {
	d, err := xRefTable.DereferenceDict(*root)
	if err != nil {
		return err
	}

	if obj, found := d.Find("Rotate"); found {
		if obj, err = xRefTable.Dereference(obj); err != nil {
			return err
		}

		switch obj := obj.(type) {
		case Integer:
			r = obj.Value()
		case Float:
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.Errorf("pdfcpu: dereferenceNumber: wrong type <%v>", obj)
			}

			r = int(math.Round(obj.Value()))
		default:
			return errors.Errorf("pdfcpu: dereferenceNumber: wrong type <%v>", obj)
		}
	}

	if err := xRefTable.collectMediaBoxAndCropBox(d, inhMediaBox, inhCropBox); err != nil {
		return err
	}

	o, _ := d.Find("Kids")
	o, _ = xRefTable.Dereference(o)
	if o == nil {
		return xRefTable.collectPageBoundariesForPage(d, pb, *inhMediaBox, *inhCropBox, r, *p)
	}

	kids, ok := o.(Array)
	if !ok {
		return errors.New("pdfcpu: validatePagesDict: corrupt \"Kids\" entry")
	}

	return xRefTable.collectPageBoundariesForPageTreeKids(kids, inhMediaBox, inhCropBox, pb, r, p, selectedPages)
}

// PageBoundaries returns a sorted slice with page boundaries
// for all pages sorted ascending by page number.
func (xRefTable *XRefTable) PageBoundaries(selectedPages IntSet) ([]PageBoundaries, error) {
	// if err := xRefTable.EnsurePageCount(); err != nil {
	// 	return nil, err
	// }

	// Get an indirect reference to the page tree root dict.
	root, err := xRefTable.Pages()
	if err != nil {
		return nil, err
	}

	i := 0
	mb := &Rectangle{}
	cb := &Rectangle{}
	pbs := make([]PageBoundaries, xRefTable.PageCount)
	if err := xRefTable.collectPageBoundariesForPageTree(root, &mb, &cb, pbs, 0, &i, selectedPages); err != nil {
		return nil, err
	}
	return pbs, nil
}

// PageDims returns a sorted slice with effective media box dimensions
// for all pages sorted ascending by page number.
func (xRefTable *XRefTable) PageDims() ([]Dim, error) {
	pbs, err := xRefTable.PageBoundaries(nil)
	if err != nil {
		return nil, err
	}

	dims := make([]Dim, len(pbs))
	for i, pb := range pbs {
		d := pb.MediaBox().Dimensions()
		if pb.Rot%180 != 0 {
			d.Width, d.Height = d.Height, d.Width
		}
		dims[i] = d
	}

	return dims, nil
}

func (xRefTable *XRefTable) EmptyPage(parentIndRef *IndirectRef, mediaBox *Rectangle) (*IndirectRef, error) {
	sd, _ := xRefTable.NewStreamDictForBuf(nil)

	if err := sd.Encode(); err != nil {
		return nil, err
	}

	contentsIndRef, err := xRefTable.IndRefForNewObject(*sd)
	if err != nil {
		return nil, err
	}

	pageDict := Dict(
		map[string]Object{
			"Type":      NameType("Page"),
			"Parent":    *parentIndRef,
			"Resources": NewDict(),
			"MediaBox":  mediaBox.Array(),
			"Contents":  *contentsIndRef,
		},
	)

	return xRefTable.IndRefForNewObject(pageDict)
}

func (xRefTable *XRefTable) pageMediaBox(d Dict) (*Rectangle, error) {
	o, found := d.Find("MediaBox")
	if !found {
		return nil, errors.Errorf("pdfcpu: pageMediaBox: missing mediaBox")
	}

	a, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return nil, err
	}

	return rect(xRefTable, a)
}

func (xRefTable *XRefTable) emptyPage(parent *IndirectRef, d Dict, dim *Dim, pAttrs *InheritedPageAttrs) (*IndirectRef, error) {
	if dim != nil {
		return xRefTable.EmptyPage(parent, RectForDim(dim.Width, dim.Height))
	}

	mediaBox, err := pAttrs.MediaBox, error(nil)
	if mediaBox == nil {
		mediaBox, err = xRefTable.pageMediaBox(d)
		if err != nil {
			return nil, err
		}
	}

	// TODO cache empty page
	return xRefTable.EmptyPage(parent, mediaBox)
}

func (xRefTable *XRefTable) insertBlankPages(
	parent *IndirectRef,
	pAttrs *InheritedPageAttrs,
	p *int, selectedPages IntSet,
	dim *Dim,
	before bool,
) (int, error) {
	d, err := xRefTable.DereferenceDict(*parent)
	if err != nil {
		return 0, err
	}

	consolidateRes := false
	if err = xRefTable.checkInheritedPageAttrs(d, pAttrs, consolidateRes); err != nil {
		return 0, err
	}

	kids := d.ArrayEntry("Kids")
	if kids == nil {
		return 0, nil
	}

	i := 0
	a := Array{}

	for _, o := range kids {

		if o == nil {
			continue
		}

		// Dereference next page node dict.
		ir, ok := o.(IndirectRef)
		if !ok {
			return 0, errors.Errorf("pdfcpu: insertBlankPages: corrupt page node dict")
		}

		pageNodeDict, err := xRefTable.DereferenceDict(ir)
		if err != nil {
			return 0, err
		}

		switch *pageNodeDict.Type() {

		case "Pages":
			// Recurse over sub pagetree.
			j, err := xRefTable.insertBlankPages(&ir, pAttrs, p, selectedPages, dim, before)
			if err != nil {
				return 0, err
			}
			a = append(a, ir)
			i += j

		case "Page":
			*p++
			if !before {
				a = append(a, ir)
				i++
			}
			if selectedPages[*p] {
				// Insert empty page.
				indRef, err := xRefTable.emptyPage(parent, pageNodeDict, dim, pAttrs)
				if err != nil {
					return 0, err
				}
				a = append(a, *indRef)
				i++
				xRefTable.SetValid(*indRef)
			}
			if before {
				a = append(a, ir)
				i++
			}
		}

	}

	d.Update("Kids", a)
	d.Update("Count", Integer(i))

	return i, nil
}

// InsertBlankPages inserts a blank page before or after each selected page.
func (xRefTable *XRefTable) InsertBlankPages(pages IntSet, dim *Dim, before bool) error {
	root, err := xRefTable.Pages()
	if err != nil {
		return err
	}

	var inhPAttrs InheritedPageAttrs
	p := 0

	_, err = xRefTable.insertBlankPages(root, &inhPAttrs, &p, pages, dim, before)

	return err
}

// OptimizationContext represents the context for the optimization of a PDF file.
type OptimizationContext struct {
	// Font section
	PageFonts         []IntSet            // For each page a registry of font object numbers.
	FontObjects       map[int]*FontObject // FontObject lookup table by font object number.
	FormFontObjects   map[int]*FontObject // FormFontObject lookup table by font object number.
	Fonts             map[string][]int    // All font object numbers registered for a font name.
	DuplicateFonts    map[int]Dict        // Registry of duplicate font dicts.
	DuplicateFontObjs IntSet              // The set of objects that represents the union of the object graphs of all duplicate font dicts.

	// Image section
	PageImages         []IntSet                      // For each page a registry of image object numbers.
	ImageObjects       map[int]*ImageObject          // ImageObject lookup table by image object number.
	DuplicateImages    map[int]*DuplicateImageObject // Registry of duplicate image dicts.
	DuplicateImageObjs IntSet                        // The set of objects that represents the union of the object graphs of all duplicate image dicts.

	ContentStreamCache map[int]*StreamDict
	FormStreamCache    map[int]*StreamDict

	DuplicateInfoObjects IntSet // Possible result of manual info dict modification.
	NonReferencedObjs    []int  // Objects that are not referenced.

	Cache     map[int]bool // For visited objects during optimization.
	NullObjNr *int         // objNr of a regular null object, to be used for fixing references to free objects.
}

// ReadContext represents the context for reading a PDF file.
type ReadContextType struct {
	FileName            string        // Input PDF-File.
	FileSize            int64         // Input file size.
	RS                  io.ReadSeeker // Input read seeker.
	EolCount            int           // 1 or 2 characters used for eol.
	BinaryTotalSize     int64         // total stream data
	BinaryImageSize     int64         // total image stream data
	BinaryFontSize      int64         // total font stream data (fontfiles)
	BinaryImageDuplSize int64         // total obsolet image stream data after optimization
	BinaryFontDuplSize  int64         // total obsolet font stream data after optimization
	Linearized          bool          // File is linearized.
	Hybrid              bool          // File is a hybrid PDF file.
	UsingObjectStreams  bool          // File is using object streams.
	ObjectStreams       IntSet        // All object numbers of any object streams found which need to be decoded.
	UsingXRefStreams    bool          // File is using xref streams.
	XRefStreams         IntSet        // All object numbers of any xref streams found.
}

// IsObjectStreamObject returns true if object i is a an object stream.
// All compressed objects are object streams.
func (rc *ReadContextType) IsObjectStreamObject(i int) bool {
	return rc.ObjectStreams[i]
}

// ObjectStreamsString returns a formatted string and the number of object stream objects.
func (rc *ReadContextType) ObjectStreamsString() (int, string) {
	var objs []int
	for k := range rc.ObjectStreams {
		if rc.ObjectStreams[k] {
			objs = append(objs, k)
		}
	}
	sort.Ints(objs)

	var objStreams []string
	for _, i := range objs {
		objStreams = append(objStreams, fmt.Sprintf("%d", i))
	}

	return len(objStreams), strings.Join(objStreams, ",")
}

// ReadFileSize returns the size of the input file, if there is one.
func (rc *ReadContextType) ReadFileSize() int {
	if rc == nil {
		return 0
	}
	return int(rc.FileSize)
}

// WriteContext represents the context for writing a PDF file.
type WriteContext struct {
	// The PDF-File which gets generated.
	*bufio.Writer                     // A writer associated with the underlying io.Writer.
	FileSize            int64         // The size of the written file (calculated from Writer).
	DirName             string        // The output directory.
	FileName            string        // The output file name.
	SelectedPages       IntSet        // For split, trim and extract.
	BinaryTotalSize     int64         // total stream data, counts 100% all stream data written.
	BinaryImageSize     int64         // total image stream data written = Read.BinaryImageSize.
	BinaryFontSize      int64         // total font stream data (fontfiles) = copy of Read.BinaryFontSize.
	Table               map[int]int64 // object write offsets
	Offset              int64         // current write offset
	OffsetSigByteRange  int64         // write offset of signature dict value for "ByteRange"
	OffsetSigContents   int64         // write offset of signature dict value for "Contents"
	WriteToObjectStream bool          // if true start to embed objects into object streams and obey ObjectStreamMaxObjects.
	CurrentObjStream    *int          // if not nil, any new non-stream-object gets added to the object stream with this object number.
	Eol                 string        // end of line char sequence
	Increment           bool          // Write context as PDF increment.
	ObjNrs              []int         // Increment candidate object numbers.
	OffsetPrevXRef      *int64        // Increment trailer entry "Prev".
}

type Context struct {
	*Configuration
	*XRefTable
	Read         *ReadContextType
	Optimize     *OptimizationContext
	Write        *WriteContext
	WritingPages bool // true, when writing page dicts.
	Dest         bool // true when writing a destination within a page.
}

// Zip in ctx's pages: for each page weave in the corresponding ctx page as long as there is one.
func (xRefTable *XRefTable) InsertPages(parent *IndirectRef, p *int, ctx *Context) (int, error) {
	d, err := xRefTable.DereferenceDict(*parent)
	if err != nil {
		return 0, err
	}

	kids := d.ArrayEntry("Kids")
	if kids == nil {
		return 0, nil
	}

	i := 0
	a := Array{}

	for _, o := range kids {

		if o == nil {
			continue
		}

		// Dereference next page node dict.
		ir, ok := o.(IndirectRef)
		if !ok {
			return 0, errors.Errorf("pdfcpu: InsertPagesIntoPageTree: corrupt page node dict")
		}

		pageNodeDict, err := xRefTable.DereferenceDict(ir)
		if err != nil {
			return 0, err
		}

		switch *pageNodeDict.Type() {

		case "Pages":
			// Recurse over sub pagetree.
			j, err := xRefTable.InsertPages(&ir, p, ctx)
			if err != nil {
				return 0, err
			}
			a = append(a, ir)
			i += j

		case "Page":
			*p++
			a = append(a, ir)
			i++
			if *p <= ctx.PageCount {
				// append indRef for ctx page i after this page
				d1, indRef1, inhPAttrs, err := ctx.PageDict(*p, false)
				if err != nil {
					return 0, err
				}
				d1["Parent"] = *parent
				if _, found := d1["Rotate"]; !found {
					d1["Rotate"] = Integer(inhPAttrs.Rotate)
				}
				if _, found := d1["MediaBox"]; !found {
					d1["MediaBox"] = inhPAttrs.MediaBox.Array()
				}
				a = append(a, *indRef1)
				i++
			}

		}

	}

	d.Update("Kids", a)
	d.Update("Count", Integer(i))

	return i, nil
}

func (xRefTable *XRefTable) AppendPages(rootPageIndRef *IndirectRef, fromPageNr int, ctx *Context) (int, error) {
	// Create an intermediary page node containing kids array with indRefs For all ctx Pages fromPageNr - end

	rootPageDict, err := xRefTable.DereferenceDict(*rootPageIndRef)
	if err != nil {
		return 0, err
	}

	// Ensure page root with pages.
	d := NewDict()
	d.InsertName("Type", "Pages")

	indRef, err := xRefTable.IndRefForNewObject(d)
	if err != nil {
		return 0, err
	}

	rootPageDict["Parent"] = *indRef

	kids := Array{*rootPageIndRef}

	count := ctx.PageCount - fromPageNr + 1

	d1 := Dict(
		map[string]Object{
			"Type":   NameType("Pages"),
			"Parent": *indRef,
			"Count":  Integer(count),
		},
	)

	indRef1, err := xRefTable.IndRefForNewObject(d1)
	if err != nil {
		return 0, err
	}

	kids1 := Array{}

	for i := fromPageNr; i <= ctx.PageCount; i++ {
		d, indRef2, inhPAttrs, err := ctx.PageDict(i, false)
		if err != nil {
			return 0, err
		}
		d["Parent"] = *indRef1
		if _, found := d["Rotate"]; !found {
			d["Rotate"] = Integer(inhPAttrs.Rotate)
		}
		if _, found := d["MediaBox"]; !found {
			d["MediaBox"] = inhPAttrs.MediaBox.Array()
		}
		kids1 = append(kids1, *indRef2)
	}
	d1["Kids"] = kids1

	d["Kids"] = append(kids, *indRef1)

	pageCount := *rootPageDict.IntEntry("Count") + count
	d["Count"] = Integer(pageCount)

	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return 0, err
	}

	rootDict["Pages"] = *indRef

	return pageCount, nil
}

// StreamDictIndRef creates a new stream dict for bb.
func (xRefTable *XRefTable) StreamDictIndRef(bb []byte) (*IndirectRef, error) {
	sd, _ := xRefTable.NewStreamDictForBuf(bb)
	if err := sd.Encode(); err != nil {
		return nil, err
	}
	return xRefTable.IndRefForNewObject(*sd)
}

func (xRefTable *XRefTable) insertContent(pageDict Dict, bb []byte) error {
	sd, _ := xRefTable.NewStreamDictForBuf(bb)
	if err := sd.Encode(); err != nil {
		return err
	}

	indRef, err := xRefTable.IndRefForNewObject(*sd)
	if err != nil {
		return err
	}

	pageDict.Insert("Contents", *indRef)

	return nil
}

func appendToContentStream(sd *StreamDict, bb []byte) error {
	err := sd.Decode()
	if err == ErrUnsupportedFilter {
		// if log.InfoEnabled() {
		// 	log.Info.Println("unsupported filter: unable to patch content with watermark.")
		// }
		return nil
	}
	if err != nil {
		return err
	}

	sd.Content = append(sd.Content, ' ')
	sd.Content = append(sd.Content, bb...)
	return sd.Encode()
}

// AppendContent appends bb to pageDict's content stream.
func (xRefTable *XRefTable) AppendContent(pageDict Dict, bb []byte) error {
	obj, found := pageDict.Find("Contents")
	if !found {
		return xRefTable.insertContent(pageDict, bb)
	}

	var entry *XRefTableEntry
	var objNr int

	indRef, ok := obj.(IndirectRef)
	if ok {
		objNr = indRef.ObjectNumber.Value()
		genNr := indRef.GenerationNumber.Value()
		entry, _ = xRefTable.FindTableEntry(objNr, genNr)
		obj = entry.Object
	}

	switch o := obj.(type) {

	case StreamDict:
		if err := appendToContentStream(&o, bb); err != nil {
			return err
		}
		entry.Object = o

	case Array:
		// Get stream dict for last array element.
		o1 := o[len(o)-1]
		indRef, _ = o1.(IndirectRef)
		objNr = indRef.ObjectNumber.Value()
		genNr := indRef.GenerationNumber.Value()
		entry, _ = xRefTable.FindTableEntry(objNr, genNr)
		sd, _ := (entry.Object).(StreamDict)
		if err := appendToContentStream(&sd, bb); err != nil {
			return err
		}
		entry.Object = sd

	default:
		return errors.Errorf("pdfcpu: corrupt page \"Content\"")
	}

	return nil
}

func (xRefTable *XRefTable) HasUsedGIDs(fontName string) bool {
	usedGIDs, ok := xRefTable.UsedGIDs[fontName]
	return ok && len(usedGIDs) > 0
}

func (xRefTable *XRefTable) NameRef(nameType string) NameMap {
	nm, ok := xRefTable.NameRefs[nameType]
	if !ok {
		nm = NameMap{}
		xRefTable.NameRefs[nameType] = nm
		return nm
	}
	return nm
}

func (xRefTable *XRefTable) RemoveSignature() {
	if xRefTable.SignatureExist || xRefTable.AppendOnly {
		// TODO enable incremental writing
		// if log.CLIEnabled() {
		// 	log.CLI.Println("removing signature...")
		// }
		// root -> Perms -> UR3 -> = Sig dict
		d1 := xRefTable.RootDict
		delete(d1, "Perms")
		d2 := xRefTable.Form
		delete(d2, "SigFlags")
		delete(d2, "XFA")
		if xRefTable.Version() == V20 {
			// deprecated in PDF 2.0
			delete(d2, "NeedAppearances")
		}
		d1["AcroForm"] = d2
		delete(d1, "Extensions")
	}
}

func (xRefTable *XRefTable) BindPrinterPreferences(vp *ViewerPreferences, d Dict) {
	if vp.PrintArea != nil {
		d.InsertName("PrintArea", vp.PrintArea.String())
	}
	if vp.PrintClip != nil {
		d.InsertName("PrintClip", vp.PrintClip.String())
	}
	if vp.PrintScaling != nil {
		d.InsertName("PrintScaling", vp.PrintScaling.String())
	}
	if vp.Duplex != nil {
		d.InsertName("Duplex", vp.Duplex.String())
	}
	if vp.PickTrayByPDFSize != nil {
		d.InsertBool("PickTrayByPDFSize", *vp.PickTrayByPDFSize)
	}
	if len(vp.PrintPageRange) > 0 {
		d.Insert("PrintPageRange", vp.PrintPageRange)
	}
	if vp.NumCopies != nil {
		d.Insert("NumCopies", *vp.NumCopies)
	}
	if len(vp.Enforce) > 0 {
		d.Insert("Enforce", vp.Enforce)
	}
}

func (xRefTable *XRefTable) BindViewerPreferences() {
	vp := xRefTable.ViewerPref
	d := NewDict()

	if vp.HideToolbar != nil {
		d.InsertBool("HideToolbar", *vp.HideToolbar)
	}
	if vp.HideMenubar != nil {
		d.InsertBool("HideMenubar", *vp.HideMenubar)
	}
	if vp.HideWindowUI != nil {
		d.InsertBool("HideWindowUI", *vp.HideWindowUI)
	}
	if vp.FitWindow != nil {
		d.InsertBool("FitWindow", *vp.FitWindow)
	}
	if vp.CenterWindow != nil {
		d.InsertBool("CenterWindow", *vp.CenterWindow)
	}
	if vp.DisplayDocTitle != nil {
		d.InsertBool("DisplayDocTitle", *vp.DisplayDocTitle)
	}
	if vp.NonFullScreenPageMode != nil {
		pm := PageMode(*vp.NonFullScreenPageMode)
		d.InsertName("NonFullScreenPageMode", pm.String())
	}
	if vp.Direction != nil {
		d.InsertName("Direction", vp.Direction.String())
	}
	if vp.ViewArea != nil {
		d.InsertName("ViewArea", vp.ViewArea.String())
	}
	if vp.ViewClip != nil {
		d.InsertName("ViewClip", vp.ViewClip.String())
	}

	xRefTable.BindPrinterPreferences(vp, d)

	xRefTable.RootDict["ViewerPreferences"] = d
}

// RectForArray returns a new rectangle for given Array.
func (xRefTable *XRefTable) RectForArray(a Array) (*Rectangle, error) {
	llx, err := xRefTable.DereferenceNumber(a[0])
	if err != nil {
		return nil, err
	}

	lly, err := xRefTable.DereferenceNumber(a[1])
	if err != nil {
		return nil, err
	}

	urx, err := xRefTable.DereferenceNumber(a[2])
	if err != nil {
		return nil, err
	}

	ury, err := xRefTable.DereferenceNumber(a[3])
	if err != nil {
		return nil, err
	}

	return NewRectangle(llx, lly, urx, ury), nil
}

// HandleLeaf processes a leaf node.
func (n *Node) HandleLeaf(xRefTable *XRefTable, k string, v Object, m NameMap, nameRefDictKeys []string) error {
	// A leaf node contains up to maxEntries names.
	// Any number of entries greater than maxEntries will be delegated to kid nodes.

	// fmt.Printf("HandleLeaf: %s %v\n\n", k, v)

	if len(n.Names) == 0 {
		n.Names = append(n.Names, entry{k, v})
		n.Kmin, n.Kmax = k, k
		return nil
	}

	if keyLess(k, n.Kmin) {
		// Prepend (k,v).
		n.Kmin = k
		n.Names = append(n.Names, entry{})
		copy(n.Names[1:], n.Names[0:])
		n.Names[0] = entry{k, v}
	} else if keyLess(n.Kmax, k) {
		// Append (k,v).
		n.Kmax = k
		n.Names = append(n.Names, entry{k, v})
	} else {
		// Insert (k,v) while ensuring unique k.
		ok, err := n.insertUniqueIntoLeaf(k, v, m, nameRefDictKeys)
		if err != nil {
			return err
		}
		if ok {
			return nil
		}
	}

	// if len was already > maxEntries we know we are dealing with somebody elses name tree.
	// In that case we do not know the branching strategy and therefore just add to Names and do not create kids.
	// If len is within maxEntries we do not create kids either way.
	if len(n.Names) != maxEntries+1 {
		return nil
	}

	// turn leaf into intermediate node with 2 kids/leafs (binary tree)
	c := maxEntries + 1
	k1 := &Node{Names: make([]entry, c/2, maxEntries)}
	copy(k1.Names, n.Names[:c/2])
	k1.Kmin = n.Names[0].k
	k1.Kmax = n.Names[c/2-1].k

	k2 := &Node{Names: make([]entry, len(n.Names)-c/2, maxEntries)}
	copy(k2.Names, n.Names[c/2:])
	k2.Kmin = n.Names[c/2].k
	k2.Kmax = n.Names[c-1].k

	n.Kids = []*Node{k1, k2}
	n.Names = nil

	return nil
}

// Add adds an entry to a name tree.
func (n *Node) Add(xRefTable *XRefTable, k string, v Object, m NameMap, nameRefDictKeys []string) error {
	// fmt.Printf("Add: %s %v\n", k, v)

	// The values associated with the keys may be objects of any type.
	// Stream objects shall be specified by indirect object references.
	// Dictionary, array, and string objects should be specified by indirect object references.
	// Other PDF objects (null, number, boolean and name) should be specified as direct objects.

	if n.Names == nil {
		n.Names = make([]entry, 0, maxEntries)
	}

	if n.leaf() {
		return n.HandleLeaf(xRefTable, k, v, m, nameRefDictKeys)
	}

	if keyLess(k, n.Kmin) {
		n.Kmin = k
	} else if keyLess(n.Kmax, k) {
		n.Kmax = k
	}

	// For intermediary nodes we delegate to the corresponding subtree.
	for _, a := range n.Kids {
		if keyLess(k, a.Kmin) || a.withinLimits(k) {
			return a.Add(xRefTable, k, v, m, nameRefDictKeys)
		}
	}

	// Insert k into last (right most) subtree.
	last := n.Kids[len(n.Kids)-1]
	return last.Add(xRefTable, k, v, m, nameRefDictKeys)
}

// AddTree adds a name tree to a name tree.
func (n *Node) AddTree(xRefTable *XRefTable, tree *Node, m NameMap, nameRefDictKeys []string) error {
	if !tree.leaf() {
		for _, v := range tree.Kids {
			if err := n.AddTree(xRefTable, v, m, nameRefDictKeys); err != nil {
				return err
			}
		}
		return nil
	}

	for _, e := range tree.Names {
		if err := n.Add(xRefTable, e.k, e.v, m, nameRefDictKeys); err != nil {
			return err
		}
	}

	return nil
}

func (n *Node) removeFromNames(xRefTable *XRefTable, k string) (ok bool, err error) {
	for i, v := range n.Names {

		if v.k < k {
			continue
		}

		if v.k == k {

			if xRefTable != nil {
				// Remove object graph of value.
				// if log.DebugEnabled() {
				// 	log.Debug.Println("removeFromNames: deleting object graph of v")
				// }
				if err := xRefTable.DeleteObjectGraph(v.v); err != nil {
					return false, err
				}
			}

			n.Names = append(n.Names[:i], n.Names[i+1:]...)
			return true, nil
		}

	}

	return false, nil
}

func (n *Node) removeSingleFromParent(xRefTable *XRefTable) error {
	if xRefTable != nil {
		// Remove object graph of value.
		// if log.DebugEnabled() {
		// 	log.Debug.Println("removeFromLeaf: deleting object graph of v")
		// }
		if err := xRefTable.DeleteObjectGraph(n.Names[0].v); err != nil {
			return err
		}
	}
	n.Kmin, n.Kmax = "", ""
	n.Names = nil
	return nil
}

func (n *Node) removeFromLeaf(xRefTable *XRefTable, k string) (empty, ok bool, err error) {
	if keyLess(k, n.Kmin) || keyLess(n.Kmax, k) {
		return false, false, nil
	}

	// kmin < k < kmax

	// If sole entry gets deleted, remove this node from parent.
	if len(n.Names) == 1 {
		if err := n.removeSingleFromParent(xRefTable); err != nil {
			return false, false, err
		}
		return true, true, nil
	}

	if k == n.Kmin {

		if xRefTable != nil {
			// Remove object graph of value.
			// if log.DebugEnabled() {
			// 	log.Debug.Println("removeFromLeaf: deleting object graph of v")
			// }
			if err := xRefTable.DeleteObjectGraph(n.Names[0].v); err != nil {
				return false, false, err
			}
		}

		n.Names = n.Names[1:]
		n.Kmin = n.Names[0].k
		return false, true, nil
	}

	if k == n.Kmax {

		if xRefTable != nil {
			// Remove object graph of value.
			// if log.DebugEnabled() {
			// 	log.Debug.Println("removeFromLeaf: deleting object graph of v")
			// }
			if err := xRefTable.DeleteObjectGraph(n.Names[len(n.Names)-1].v); err != nil {
				return false, false, err
			}
		}

		n.Names = n.Names[:len(n.Names)-1]
		n.Kmax = n.Names[len(n.Names)-1].k
		return false, true, nil
	}

	if ok, err = n.removeFromNames(xRefTable, k); err != nil {
		return false, false, err
	}

	return false, ok, nil
}

func (n *Node) removeKid(xRefTable *XRefTable, kid *Node, i int) (bool, error) {
	if xRefTable != nil {
		if err := xRefTable.DeleteObject(kid.D); err != nil {
			return false, err
		}
	}

	if i == 0 {
		// Remove first kid.
		// if log.DebugEnabled() {
		// 	log.Debug.Println("removeFromKids: remove first kid.")
		// }
		n.Kids = n.Kids[1:]
	} else if i == len(n.Kids)-1 {
		// if log.DebugEnabled() {
		// 	log.Debug.Println("removeFromKids: remove last kid.")
		// }
		// Remove last kid.
		n.Kids = n.Kids[:len(n.Kids)-1]
	} else {
		// Remove kid from the middle.
		// if log.DebugEnabled() {
		// 	log.Debug.Println("removeFromKids: remove kid form the middle.")
		// }
		n.Kids = append(n.Kids[:i], n.Kids[i+1:]...)
	}

	if len(n.Kids) == 1 {

		// If a single kid remains we can merge it with its parent.
		// By doing this we get rid of a redundant intermediary node.
		// if log.DebugEnabled() {
		// 	log.Debug.Println("removeFromKids: only 1 kid")
		// }

		if xRefTable != nil {
			if err := xRefTable.DeleteObject(n.D); err != nil {
				return false, err
			}
		}

		*n = *n.Kids[0]

		// if log.DebugEnabled() {
		// 	log.Debug.Printf("removeFromKids: new n = %s\n", n)
		// }

		return true, nil
	}

	return false, nil
}

func (n *Node) removeFromKids(xRefTable *XRefTable, k string) (ok bool, err error) {
	// Locate the kid to recurse into, then remove k from that subtree.
	for i, kid := range n.Kids {

		if !kid.withinLimits(k) {
			continue
		}

		empty, ok, err := kid.Remove(xRefTable, k)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}

		if empty {

			// This kid is now empty and needs to be removed.

			noKids, err := n.removeKid(xRefTable, kid, i)
			if err != nil {
				return false, err
			}
			if noKids {
				return true, nil
			}

		}

		// Update kMin, kMax for n.
		n.Kmin = n.Kids[0].Kmin
		n.Kmax = n.Kids[len(n.Kids)-1].Kmax

		return true, nil
	}

	return false, nil
}

// Remove removes an entry from a name tree.
// empty returns true if this node is an empty leaf node after removal.
// ok returns true if removal was successful.
func (n *Node) Remove(xRefTable *XRefTable, k string) (empty, ok bool, err error) {
	if n.leaf() {
		return n.removeFromLeaf(xRefTable, k)
	}

	if ok, err = n.removeFromKids(xRefTable, k); err != nil {
		return false, false, err
	}

	return false, ok, nil
}

// Process traverses the nametree applying a handler to each entry (key-value pair).
func (n *Node) Process(xRefTable *XRefTable, handler func(*XRefTable, string, *Object) error) error {
	if !n.leaf() {
		for _, v := range n.Kids {
			if err := v.Process(xRefTable, handler); err != nil {
				return err
			}
		}
		return nil
	}

	for k, e := range n.Names {
		if err := handler(xRefTable, e.k, &e.v); err != nil {
			return err
		}
		n.Names[k] = e
	}

	return nil
}

// KeyList returns a sorted list of all keys.
func (n Node) KeyList() ([]string, error) {
	list := []string{}

	keys := func(xRefTable *XRefTable, k string, v *Object) error {
		list = append(list, fmt.Sprintf("%s %v", k, *v))
		return nil
	}

	if err := n.Process(nil, keys); err != nil {
		return nil, err
	}

	return list, nil
}

func (n Node) String() string {
	a := []string{}

	if n.leaf() {
		a = append(a, "[")
		for _, n := range n.Names {
			a = append(a, fmt.Sprintf("(%s,%s)", n.k, n.v))
		}
		a = append(a, fmt.Sprintf("{%s,%s}]", n.Kmin, n.Kmax))
		return strings.Join(a, "")
	}

	a = append(a, fmt.Sprintf("{%s,%s}", n.Kmin, n.Kmax))

	for _, v := range n.Kids {
		a = append(a, v.String())
	}

	return strings.Join(a, ",")
}

var (
	ErrWrongPassword         = errors.New("pdfcpu: please provide the correct password")
	ErrCorruptHeader         = errors.New("pdfcpu: no header version available")
	ErrMissingXRefSection    = errors.New("pdfcpu: can't detect last xref section")
	ErrReferenceDoesNotExist = errors.New("pdfcpu: referenced object does not exist")
)

// fillBuffer reads from r until buf is full or read returns an error.
// Unlike io.ReadAtLeast fillBuffer does not return ErrUnexpectedEOF
// if an EOF happens after reading some but not all the bytes.
// Special thanks go to Rene Kaufmann.
func fillBuffer(r io.Reader, buf []byte) (int, error) {
	var n int
	var err error

	for n < len(buf) && err == nil {
		var nn int
		nn, err = r.Read(buf[n:])
		n += nn
	}

	if n > 0 && err == io.EOF {
		return n, nil
	}

	return n, err
}

// Get the file offset of the last XRefSection.
// Go to end of file and search backwards for the first occurrence of startxref {offset} %%EOF
func offsetLastXRefSection(ctx *Context, skip int64) (*int64, error) {
	rs := ctx.Read.RS

	var (
		prevBuf, workBuf []byte
		bufSize          int64 = 512
		offset           int64
	)

	if ctx.Read.FileSize < bufSize {
		bufSize = ctx.Read.FileSize
	}

	for i := 1; offset == 0; i++ {

		_, err := rs.Seek(-int64(i)*bufSize-skip, io.SeekEnd)
		if err != nil {
			return nil, ErrMissingXRefSection
		}

		curBuf := make([]byte, bufSize)

		if _, err = fillBuffer(rs, curBuf); err != nil {
			return nil, err
		}

		workBuf = curBuf
		if prevBuf != nil {
			workBuf = append(curBuf, prevBuf...)
		}

		j := strings.LastIndex(string(workBuf), "startxref")
		if j == -1 {
			prevBuf = curBuf
			continue
		}

		p := workBuf[j+len("startxref")+1:]
		posEOF := strings.Index(string(p), "%%EOF")
		if posEOF == -1 {
			return nil, errors.New("pdfcpu: no matching %%EOF for startxref")
		}

		p = p[:posEOF]
		offset, err = strconv.ParseInt(strings.TrimSpace(string(p)), 10, 64)
		if err != nil {
			return nil, errors.New("pdfcpu: invalid last xref section")
		}
		if offset >= ctx.Read.FileSize {
			offset = 0
		}
	}

	return &offset, nil
}

func scanForVersion(rs io.ReadSeeker, prefix string) ([]byte, int, error) {
	bufSize := 100

	if _, err := rs.Seek(0, io.SeekStart); err != nil {
		return nil, 0, err
	}

	buf := make([]byte, bufSize)
	var curBuf []byte

	off := 0
	found := false
	var buf2 []byte

	for !found {
		n, err := fillBuffer(rs, buf)
		if err != nil {
			return nil, 0, ErrCorruptHeader
		}
		curBuf = buf[:n]
		for {
			i := bytes.IndexByte(curBuf, '%')
			if i < 0 {
				// no match, check next block
				off += len(curBuf)
				break
			}

			// Check all occurrences
			if i < len(curBuf)-18 {
				if !bytes.HasPrefix(curBuf[i:], []byte(prefix)) {
					// No match, keep checking
					off += i + 1
					curBuf = curBuf[i+1:]
					continue
				}
				off += i
				curBuf = curBuf[i:]
				found = true
				break
			}

			// Partial match, need 2nd buffer
			if len(buf2) == 0 {
				buf2 = make([]byte, bufSize)
			}
			n, err := fillBuffer(rs, buf2)
			if err != nil {
				return nil, 0, ErrCorruptHeader
			}
			buf3 := append(curBuf[i:], buf2[:n]...)
			if !bytes.HasPrefix(buf3, []byte(prefix)) {
				// No match, keep checking
				off += len(curBuf)
				curBuf = buf2
				continue
			}
			off += i
			curBuf = buf3
			found = true
			break
		}
	}

	return curBuf, off, nil
}

// Get version from first line of file.
// Beginning with PDF 1.4, the Version entry in the document’s catalog dictionary
// (located via the Root entry in the file’s trailer, as described in 7.5.5, "File Trailer"),
// if present, shall be used instead of the version specified in the Header.
// The header version comes as the first line of the file.
// eolCount is the number of characters used for eol (1 or 2).
func headerVersion(rs io.ReadSeeker) (v *Version, eolCount int, offset int64, err error) {
	prefix := "%PDF-"

	s, off, err := scanForVersion(rs, prefix)
	if err != nil {
		return nil, 0, 0, err
	}

	pdfVersion, err := PDFVersion(string(s[len(prefix) : len(prefix)+3]))
	if err != nil {
		return nil, 0, 0, errors.Wrapf(err, "headerVersion: unknown PDF Header Version")
	}

	s = s[8:]
	s = bytes.TrimLeft(s, "\t\f ")

	// Detect the used eol which should be 1 (0x00, 0x0D) or 2 chars (0x0D0A)long.
	// %PDF-1.x{whiteSpace}{text}{eol} or
	j := bytes.IndexAny(s, "\x0A\x0D")
	if j < 0 {
		return nil, 0, 0, ErrCorruptHeader
	}
	if s[j] == 0x0A {
		eolCount = 1
	} else if s[j] == 0x0D {
		eolCount = 1
		if (len(s) > j+1) && (s[j+1] == 0x0A) {
			eolCount = 2
		}
	}

	return &pdfVersion, eolCount, int64(off), nil
}

func newPositionedReader(rs io.ReadSeeker, offset *int64) (*bufio.Reader, error) {
	if _, err := rs.Seek(*offset, io.SeekStart); err != nil {
		return nil, err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("newPositionedReader: positioned to offset: %d\n", *offset)
	// }

	return bufio.NewReader(rs), nil
}

func scanLineRaw(s *bufio.Scanner) (string, error) {
	if ok := s.Scan(); !ok {
		if s.Err() != nil {
			return "", s.Err()
		}
		return "", errors.New("pdfcpu: scanLineRaw: returning nothing")
	}
	return s.Text(), nil
}

func scanLine(s *bufio.Scanner) (s1 string, err error) {
	for i := 0; i <= 1; i++ {
		s1, err = scanLineRaw(s)
		if err != nil {
			return "", err
		}
		if len(s1) > 0 {
			break
		}
	}

	return s1, nil
}

func decodeSubsection(fields []string, repairOff int) (int64, int, string, error) {
	offset, err := strconv.ParseInt(fields[0], 10, 64)
	if err != nil {
		return 0, 0, "", err
	}
	offset += int64(repairOff)

	generation, err := strconv.Atoi(fields[1])
	if err != nil {
		return 0, 0, "", err
	}

	entryType := fields[2]
	if entryType != "f" && entryType != "n" {
		return 0, 0, "", errors.New("pdfcpu: decodeSubsection: corrupt xref subsection entryType")
	}

	return offset, generation, entryType, nil
}

func createXRefTableEntry(entryType string, objNr int, offset, offExtra int64, generation, incr int) (XRefTableEntry, bool) {
	entry := XRefTableEntry{Offset: &offset, Generation: &generation, Incr: incr}

	if entryType == "n" {

		// in use object

		// if log.ReadEnabled() {
		// 	log.Read.Printf("createXRefTableEntry: Object #%d is in use at offset=%d, generation=%d\n", objNr, offset, generation)
		// }

		if offset == 0 {
			if objNr == 0 {
				entry.Free = true
				return entry, true
			}
			// if log.InfoEnabled() {
			// 	log.Info.Printf("createXRefTableEntry: Skip entry for in use object #%d with offset 0\n", objNr)
			// }
			return entry, false
		}

		*entry.Offset += offExtra

		return entry, true
	}

	// free object

	// if log.ReadEnabled() {
	// 	log.Read.Printf("createXRefTableEntry: Object #%d is unused, next free is object#%d, generation=%d\n", objNr, offset, generation)
	// }

	entry.Free = true

	return entry, true
}

// Read next subsection entry and generate corresponding xref table entry.
func parseXRefTableEntry(xRefTable *XRefTable, s *bufio.Scanner, objNr int, offExtra int64, repairOff, incr int) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefTableEntry: begin")
	// }

	line, err := scanLine(s)
	if err != nil {
		return err
	}

	if xRefTable.Exists(objNr) {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("parseXRefTableEntry: end - Skip entry %d - already assigned\n", objNr)
		// }
		return nil
	}

	fields := strings.Fields(line)
	if len(fields) != 3 ||
		len(fields[0]) != 10 || len(fields[1]) != 5 || len(fields[2]) != 1 {
		return errors.New("pdfcpu: parseXRefTableEntry: corrupt xref subsection header")
	}

	offset, generation, entryType, err := decodeSubsection(fields, repairOff)
	if err != nil {
		return err
	}

	entry, ok := createXRefTableEntry(entryType, objNr, offset, offExtra, generation, incr)
	if !ok {
		return nil
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseXRefTableEntry: Insert new xreftable entry for Object %d\n", objNr)
	// }

	xRefTable.Table[objNr] = &entry

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefTableEntry: end")
	// }

	return nil
}

// Process xRef table subsection and create corresponding xRef table entries.
func parseXRefTableSubSection(xRefTable *XRefTable, s *bufio.Scanner, fields []string, offExtra int64, repairOff, incr int) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefTableSubSection: begin")
	// }

	startObjNumber, err := strconv.Atoi(fields[0])
	if err != nil {
		return err
	}

	objCount, err := strconv.Atoi(fields[1])
	if err != nil {
		return err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("detected xref subsection, startObj=%d length=%d\n", startObjNumber, objCount)
	// }

	// Process all entries of this subsection into xRefTable entries.
	for i := 0; i < objCount; i++ {
		if err = parseXRefTableEntry(xRefTable, s, startObjNumber+i, offExtra, repairOff, incr); err != nil {
			return err
		}
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefTableSubSection: end")
	// }

	return nil
}

func scanTrailerDictStart(s *bufio.Scanner, line *string) error {
	l := *line
	var err error
	for {
		i := strings.Index(l, "<<")
		if i >= 0 {
			*line = l[i:]
			return nil
		}
		l, err = scanLine(s)
		// if log.ReadEnabled() {
		// 	log.Read.Printf("line: <%s>\n", l)
		// }
		if err != nil {
			return err
		}
	}
}

func scanTrailerDictRemainder(s *bufio.Scanner, line string, buf bytes.Buffer) (string, error) {
	var (
		i   int
		err error
	)

	for i = strings.Index(line, "startxref"); i < 0; {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("line: <%s>\n", line)
		// }
		buf.WriteString(line)
		buf.WriteString("\x0a")
		if line, err = scanLine(s); err != nil {
			return "", err
		}
		i = strings.Index(line, "startxref")
	}

	line = line[:i]
	// if log.ReadEnabled() {
	// 	log.Read.Printf("line: <%s>\n", line)
	// }
	buf.WriteString(line[:i])
	buf.WriteString("\x0a")

	return buf.String(), nil
}

func scanTrailer(s *bufio.Scanner, line string) (string, error) {
	var buf bytes.Buffer
	// if log.ReadEnabled() {
	// 	log.Read.Printf("line: <%s>\n", line)
	// }

	if err := scanTrailerDictStart(s, &line); err != nil {
		return "", err
	}

	return scanTrailerDictRemainder(s, line, buf)
}

func parseTrailerSize(xRefTable *XRefTable, d Dict) error {
	i := d.Size()
	if i == nil {
		return errors.New("pdfcpu: parseTrailerSize: missing entry \"Size\"")
	}
	// Not reliable!
	// Patched after all read in.
	xRefTable.Size = i
	return nil
}

func parseTrailerRoot(xRefTable *XRefTable, d Dict) error {
	indRef := d.IndirectRefEntry("Root")
	if indRef == nil {
		return errors.New("pdfcpu: parseTrailerRoot: missing entry \"Root\"")
	}
	xRefTable.Root = indRef
	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseTrailerRoot: Root object: %s\n", *xRefTable.Root)
	// }
	return nil
}

func parseTrailerInfo(xRefTable *XRefTable, d Dict) error {
	indRef := d.IndirectRefEntry("Info")
	if indRef != nil {
		xRefTable.Info = indRef
		// if log.ReadEnabled() {
		// 	log.Read.Printf("parseTrailerInfo: Info object: %s\n", *xRefTable.Info)
		// }
	}
	return nil
}

func parseTrailerID(xRefTable *XRefTable, d Dict) error {
	arr := d.ArrayEntry("ID")
	if arr != nil {
		if len(arr) != 2 {
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.New("pdfcpu: parseTrailerID: invalid entry \"ID\"")
			}
			if len(arr) != 1 {
				return errors.New("pdfcpu: parseTrailerID: invalid entry \"ID\"")
			}
			arr = append(arr, arr[0])
		}
		xRefTable.ID = arr
		// if log.ReadEnabled() {
		// 	log.Read.Printf("parseTrailerID: ID object: %s\n", xRefTable.ID)
		// }
		return nil
	}

	if xRefTable.Encrypt != nil {
		return errors.New("pdfcpu: parseTrailerID: missing entry \"ID\"")
	}

	return nil
}

// Parse trailer dict and return any offset of a previous xref section.
func parseTrailer(xRefTable *XRefTable, d Dict) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("parseTrailer begin")
	// }

	if indRef := d.IndirectRefEntry("Encrypt"); indRef != nil {
		xRefTable.Encrypt = indRef
		// if log.ReadEnabled() {
		// 	log.Read.Printf("parseTrailer: Encrypt object: %s\n", *xRefTable.Encrypt)
		// }
	}

	if xRefTable.Size == nil {
		if err := parseTrailerSize(xRefTable, d); err != nil {
			return err
		}
	}

	if xRefTable.Root == nil {
		if err := parseTrailerRoot(xRefTable, d); err != nil {
			return err
		}
	}

	if xRefTable.Info == nil {
		if err := parseTrailerInfo(xRefTable, d); err != nil {
			return err
		}
	}

	if xRefTable.ID == nil {
		if err := parseTrailerID(xRefTable, d); err != nil {
			return err
		}
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseTrailerf end")
	// }

	return nil
}

func handleAdditionalStreams(trailerDict Dict, xRefTable *XRefTable) {
	arr := trailerDict.ArrayEntry("AdditionalStreams")
	if arr == nil {
		return
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("found AdditionalStreams: %s\n", arr)
	// }

	a := Array{}
	for _, value := range arr {
		if indRef, ok := value.(IndirectRef); ok {
			a = append(a, indRef)
		}
	}

	xRefTable.AdditionalStreams = &a
}

func scanForPreviousXref(ctx *Context, offset *int64) *int64 {
	var (
		prevBuf, workBuf []byte
		bufSize          int64 = 512
		off              int64
		match1           []byte = []byte("startxref")
		match2           []byte = []byte("xref")
	)

	m := match1

	for i := int64(1); ; i++ {
		off = *offset - i*bufSize
		rd, err := newPositionedReader(ctx.Read.RS, &off)
		if err != nil {
			return nil
		}

		curBuf := make([]byte, bufSize)

		n, err := fillBuffer(rd, curBuf)
		if err != nil {
			return nil
		}

		workBuf = curBuf
		if prevBuf != nil {
			workBuf = append(curBuf, prevBuf...)
		}

		j := bytes.LastIndex(workBuf, m)
		if j == -1 {
			if int64(n) < bufSize {
				return nil
			}
			prevBuf = curBuf
			continue
		}

		if bytes.Equal(m, match1) {
			m = match2
			continue
		}

		off += int64(j)
		break
	}

	return &off
}

func offsetPrev(ctx *Context, trailerDict Dict, offCurXRef *int64) *int64 {
	offset := trailerDict.Prev()
	if offset != nil {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("offsetPrev: previous xref table section offset:%d\n", *offset)
		// }
		if *offset == 0 {
			offset = nil
			if offCurXRef != nil {
				if off := scanForPreviousXref(ctx, offCurXRef); off != nil {
					offset = off
				}
			}
		}
	}
	return offset
}

const (
	defaultBufSize = 1024
	maximumBufSize = 1024 * 1024
)

func growBufBy(buf []byte, size int, rd io.Reader) ([]byte, error) {
	b := make([]byte, size)

	if _, err := fillBuffer(rd, b); err != nil {
		return nil, err
	}
	// log.Read.Printf("growBufBy: Read %d bytes\n", n)

	return append(buf, b...), nil
}

// return true if 'stream' follows end of dict: >>{whitespace}stream
func keywordStreamRightAfterEndOfDict(buf string, streamInd int) bool {
	// log.Read.Println("keywordStreamRightAfterEndOfDict: begin")

	// Get a slice of the chunk right in front of 'stream'.
	b := buf[:streamInd]

	// Look for last end of dict marker.
	eod := strings.LastIndex(b, ">>")
	if eod < 0 {
		// No end of dict in buf.
		return false
	}

	// We found the last >>. Return true if after end of dict only whitespace.
	ok := strings.TrimSpace(b[eod:]) == ">>"

	// log.Read.Printf("keywordStreamRightAfterEndOfDict: end, %v\n", ok)

	return ok
}

func lastStreamMarker(streamInd *int, endInd int, line string) {
	if *streamInd > len(line)-len("stream") {
		// No space for another stream marker.
		*streamInd = -1
		return
	}

	// We start searching after this stream marker.
	bufpos := *streamInd + len("stream")

	// Search for next stream marker.
	i := strings.Index(line[bufpos:], "stream")
	if i < 0 {
		// No stream marker within line buffer.
		*streamInd = -1
		return
	}

	// We found the next stream marker.
	*streamInd += len("stream") + i

	if endInd > 0 && *streamInd > endInd {
		// We found a stream marker of another object
		*streamInd = -1
	}
}

func nextStreamOffset(line string, streamInd int) (off int) {
	off = streamInd + len("stream")

	// Skip optional blanks.
	// TODO Should we skip optional whitespace instead?
	for ; line[off] == 0x20; off++ {
	}

	// Skip 0A eol.
	if line[off] == '\n' {
		off++
		return
	}

	// Skip 0D eol.
	if line[off] == '\r' {
		off++
		// Skip 0D0A eol.
		if line[off] == '\n' {
			off++
		}
	}

	return
}

// Provide a PDF file buffer of sufficient size for parsing an object w/o stream.
func buffer(c ContextContext, rd io.Reader) (buf []byte, endInd int, streamInd int, streamOffset int64, err error) {
	// process: # gen obj ... obj dict ... {stream ... data ... endstream} ... endobj
	//                                    streamInd                            endInd
	//                                  -1 if absent                        -1 if absent

	// log.Read.Println("buffer: begin")

	endInd, streamInd = -1, -1
	growSize := defaultBufSize

	for endInd < 0 && streamInd < 0 {
		if err := c.Err(); err != nil {
			return nil, 0, 0, 0, err
		}

		if buf, err = growBufBy(buf, growSize, rd); err != nil {
			return nil, 0, 0, 0, err
		}

		growSize = min(growSize*2, maximumBufSize)
		line := string(buf)

		endInd, streamInd, err = DetectKeywordsWithContext(c, line)
		if err != nil {
			return nil, 0, 0, 0, err
		}

		if endInd > 0 && (streamInd < 0 || streamInd > endInd) {
			// No stream marker in buf detected.
			break
		}

		// For very rare cases where "stream" also occurs within obj dict
		// we need to find the last "stream" marker before a possible end marker.
		for streamInd > 0 && !keywordStreamRightAfterEndOfDict(line, streamInd) {
			lastStreamMarker(&streamInd, endInd, line)
		}

		// if log.ReadEnabled() {
		// 	log.Read.Printf("buffer: endInd=%d streamInd=%d\n", endInd, streamInd)
		// }

		if streamInd > 0 {

			// streamOffset ... the offset where the actual stream data begins.
			//                  is right after the eol after "stream".

			slack := 10 // for optional whitespace + eol (max 2 chars)
			need := streamInd + len("stream") + slack

			if len(line) < need {

				// to prevent buffer overflow.
				if buf, err = growBufBy(buf, need-len(line), rd); err != nil {
					return nil, 0, 0, 0, err
				}

				line = string(buf)
			}

			streamOffset = int64(nextStreamOffset(line, streamInd))
		}
	}

	// log.Read.Printf("buffer: end, returned bufsize=%d streamOffset=%d\n", len(buf), streamOffset)

	return buf, endInd, streamInd, streamOffset, nil
}

// Resolve compressed xRefTableEntry
func decompressXRefTableEntry(xRefTable *XRefTable, objNr int, entry *XRefTableEntry) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("decompressXRefTableEntry: compressed object %d at %d[%d]\n", objNr, *entry.ObjectStream, *entry.ObjectStreamInd)
	// }

	// Resolve xRefTable entry of referenced object stream.
	objectStreamXRefTableEntry, ok := xRefTable.Find(*entry.ObjectStream)
	if !ok {
		return errors.Errorf("decompressXRefTableEntry: problem dereferencing object stream %d, no xref table entry", *entry.ObjectStream)
	}

	// Object of this entry has to be a ObjectStreamDictType.
	sd, ok := objectStreamXRefTableEntry.Object.(ObjectStreamDictType)
	if !ok {
		return errors.Errorf("decompressXRefTableEntry: problem dereferencing object stream %d, no object stream", *entry.ObjectStream)
	}

	// Get indexed object from ObjectStreamDictType.
	o, err := sd.IndexedObject(*entry.ObjectStreamInd)
	if err != nil {
		return errors.Wrapf(err, "decompressXRefTableEntry: problem dereferencing object stream %d", *entry.ObjectStream)
	}

	// Save object to XRefRableEntry.
	g := 0
	entry.Object = o
	entry.Generation = &g
	entry.Compressed = false

	// if log.ReadEnabled() {
	// 	log.Read.Printf("decompressXRefTableEntry: end, Obj %d[%d]:\n<%s>\n", *entry.ObjectStream, *entry.ObjectStreamInd, o)
	// }

	return nil
}

func object(c ContextContext, ctx *Context, offset int64, objNr, genNr int) (o Object, endInd, streamInd int, streamOffset int64, err error) {
	var rd io.Reader

	if rd, err = newPositionedReader(ctx.Read.RS, &offset); err != nil {
		return nil, 0, 0, 0, err
	}

	// log.Read.Printf("object: seeked to offset:%d\n", offset)

	// process: # gen obj ... obj dict ... {stream ... data ... endstream} endobj
	//                                    streamInd                        endInd
	//                                  -1 if absent                    -1 if absent
	var buf []byte
	if buf, endInd, streamInd, streamOffset, err = buffer(c, rd); err != nil {
		return nil, 0, 0, 0, err
	}

	// log.Read.Printf("streamInd:%d(#%x) streamOffset:%d(#%x) endInd:%d(#%x)\n", streamInd, streamInd, streamOffset, streamOffset, endInd, endInd)
	// log.Read.Printf("buflen=%d\n%s", len(buf), hex.Dump(buf))

	line := string(buf)

	var l string

	if endInd < 0 { // && streamInd >= 0, streamdict
		// buf: # gen obj ... obj dict ... stream ... data
		// implies we detected no endobj and a stream starting at streamInd.
		// big stream, we parse object until "stream"
		// if log.ReadEnabled() {
		// 	log.Read.Println("object: big stream, we parse object until stream")
		// }
		l = line[:streamInd]
	} else if streamInd < 0 { // dict
		// buf: # gen obj ... obj dict ... endobj
		// implies we detected endobj and no stream.
		// small object w/o stream, parse until "endobj"
		// if log.ReadEnabled() {
		// 	log.Read.Println("object: small object w/o stream, parse until endobj")
		// }
		l = line[:endInd]
	} else if streamInd < endInd { // streamdict
		// buf: # gen obj ... obj dict ... stream ... data ... endstream endobj
		// implies we detected endobj and stream.
		// small stream within buffer, parse until "stream"
		// if log.ReadEnabled() {
		// 	log.Read.Println("object: small stream within buffer, parse until stream")
		// }
		l = line[:streamInd]
	} else { // dict
		// buf: # gen obj ... obj dict ... endobj # gen obj ... obj dict ... stream
		// small obj w/o stream, parse until "endobj"
		// stream in buf belongs to subsequent object.
		// if log.ReadEnabled() {
		// 	log.Read.Println("object: small obj w/o stream, parse until endobj")
		// }
		l = line[:endInd]
	}

	// Parse object number and object generation.
	var objectNr, generationNr *int
	if objectNr, generationNr, err = ParseObjectAttributes(&l); err != nil {
		return nil, 0, 0, 0, err
	}

	if objNr != *objectNr || genNr != *generationNr {
		// This is suspicious, but ok if two object numbers point to same offset and only one of them is used
		// (compare entry.RefCount) like for cases where the PDF Writer is MS Word 2013.
		// if log.ReadEnabled() {
		// 	log.Read.Printf("object %d: non matching objNr(%d) or generationNumber(%d) tags found.\n", objNr, *objectNr, *generationNr)
		// }
	}

	l = strings.TrimSpace(l)
	if len(l) == 0 {
		// 7.3.9
		// Specifying the null object as the value of a dictionary entry (7.3.7, "Dictionary Objects")
		// shall be equivalent to omitting the entry entirely.
		return nil, endInd, streamInd, streamOffset, err
	}

	o, err = ParseObjectContext(c, &l)

	return o, endInd, streamInd, streamOffset, err
}

func decryptDict(d Dict, objNr, genNr int, key []byte, needAES bool, r int) error {
	isSig := false
	ft := d["FT"]
	if ft == nil {
		ft = d["Type"]
	}
	if ft != nil {
		if ftv, ok := ft.(NameType); ok && (ftv == "Sig" || ftv == "DocTimeStamp") {
			isSig = true
		}
	}
	for k, v := range d {
		if isSig && k == "Contents" {
			continue
		}
		s, err := decryptDeepObject(v, objNr, genNr, key, needAES, r)
		if err != nil {
			return err
		}
		if s != nil {
			d[k] = s
		}
	}
	return nil
}

func decryptKey(objNumber, generation int, key []byte, aes bool) []byte {
	m := md5.New()

	nr := uint32(objNumber)
	b1 := []byte{byte(nr), byte(nr >> 8), byte(nr >> 16)}
	b := append(key, b1...)

	gen := uint16(generation)
	b2 := []byte{byte(gen), byte(gen >> 8)}
	b = append(b, b2...)

	m.Write(b)

	if aes {
		m.Write([]byte("sAlT"))
	}

	dk := m.Sum(nil)

	l := len(key) + 5
	if l < 16 {
		dk = dk[:l]
	}

	return dk
}

func decryptAESBytes(b, key []byte) ([]byte, error) {
	if len(b) < aes.BlockSize {
		return nil, errors.New("pdfcpu: decryptAESBytes: Ciphertext too short")
	}

	if len(b)%aes.BlockSize > 0 {
		return nil, errors.New("pdfcpu: decryptAESBytes: Ciphertext not a multiple of block size")
	}

	cb, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	iv := make([]byte, aes.BlockSize)
	copy(iv, b[:aes.BlockSize])

	data := b[aes.BlockSize:]
	mode := cipher.NewCBCDecrypter(cb, iv)
	mode.CryptBlocks(data, data)

	// Remove padding.
	// Note: For some reason not all AES ciphertexts are padded.
	if len(data) > 0 && data[len(data)-1] <= 0x10 {
		e := len(data) - int(data[len(data)-1])
		data = data[:e]
	}

	return data, nil
}

func applyRC4CipherBytes(b []byte, objNr, genNr int, key []byte, needAES bool) ([]byte, error) {
	c, err := rc4.NewCipher(decryptKey(objNr, genNr, key, needAES))
	if err != nil {
		return nil, err
	}

	c.XORKeyStream(b, b)

	return b, nil
}

// decryptBytes decrypts bb using RC4 or AES.
func decryptBytes(b []byte, objNr, genNr int, encKey []byte, needAES bool, r int) ([]byte, error) {
	if needAES {
		k := encKey
		if r != 5 && r != 6 {
			k = decryptKey(objNr, genNr, encKey, needAES)
		}
		return decryptAESBytes(b, k)
	}

	return applyRC4CipherBytes(b, objNr, genNr, encKey, needAES)
}

func decryptStringLiteral(sl StringLiteral, objNr, genNr int, key []byte, needAES bool, r int) (*StringLiteral, error) {
	if sl.Value() == "" {
		return &sl, nil
	}
	bb, err := Unescape(sl.Value())
	if err != nil {
		return nil, err
	}

	bb, err = decryptBytes(bb, objNr, genNr, key, needAES, r)
	if err != nil {
		return nil, err
	}

	s, err := Escape(string(bb))
	if err != nil {
		return nil, err
	}

	sl = StringLiteral(*s)

	return &sl, nil
}

func decryptHexLiteral(hl HexLiteral, objNr, genNr int, key []byte, needAES bool, r int) (*HexLiteral, error) {
	if hl.Value() == "" {
		return &hl, nil
	}
	bb, err := hl.Bytes()
	if err != nil {
		return nil, err
	}

	bb, err = decryptBytes(bb, objNr, genNr, key, needAES, r)
	if err != nil {
		return nil, err
	}

	hl = NewHexLiteral(bb)

	return &hl, nil
}

func decryptDeepObject(objIn Object, objNr, genNr int, key []byte, needAES bool, r int) (Object, error) {
	_, ok := objIn.(IndirectRef)
	if ok {
		return nil, nil
	}

	switch obj := objIn.(type) {

	case Dict:
		if err := decryptDict(obj, objNr, genNr, key, needAES, r); err != nil {
			return nil, err
		}

	case Array:
		for i, v := range obj {
			s, err := decryptDeepObject(v, objNr, genNr, key, needAES, r)
			if err != nil {
				return nil, err
			}
			if s != nil {
				obj[i] = s
			}
		}

	case StringLiteral:
		sl, err := decryptStringLiteral(obj, objNr, genNr, key, needAES, r)
		if err != nil {
			return nil, err
		}
		return *sl, nil

	case HexLiteral:
		hl, err := decryptHexLiteral(obj, objNr, genNr, key, needAES, r)
		if err != nil {
			return nil, err
		}
		return *hl, nil

	default:

	}

	return nil, nil
}

func dict(ctx *Context, d1 Dict, objNr, genNr, endInd, streamInd int) (d2 Dict, err error) {
	if ctx.EncKey != nil {
		if _, err := decryptDeepObject(d1, objNr, genNr, ctx.EncKey, ctx.AES4Strings, ctx.E.R); err != nil {
			return nil, err
		}
	}

	if endInd >= 0 && (streamInd < 0 || streamInd > endInd) {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("dict: end, #%d\n", objNr)
		// }
		d2 = d1
	}

	return d2, nil
}

func streamDictForObject(c ContextContext, ctx *Context, d Dict, objNr, streamInd int, streamOffset, offset int64) (sd StreamDict, err error) {
	streamLength, streamLengthRef := d.Length()

	if streamInd <= 0 {
		return sd, errors.New("pdfcpu: streamDictForObject: stream object without streamOffset")
	}

	filterPipeline, err := pdfFilterPipeline(c, ctx, d)
	if err != nil {
		return sd, err
	}

	streamOffset += offset

	// We have a stream object.
	sd = NewStreamDict(d, streamOffset, streamLength, streamLengthRef, filterPipeline)

	// if log.ReadEnabled() {
	// 	log.Read.Printf("streamDictForObject: end, Streamobject #%d\n", objNr)
	// }

	return sd, nil
}

func resolveObject(c ContextContext, ctx *Context, obj Object, offset int64, objNr, genNr, endInd, streamInd int, streamOffset int64) (Object, error) {
	switch o := obj.(type) {

	case Dict:
		d, err := dict(ctx, o, objNr, genNr, endInd, streamInd)
		if err != nil || d != nil {
			// Dict
			return d, err
		}
		// StreamDict.
		return streamDictForObject(c, ctx, o, objNr, streamInd, streamOffset, offset)

	case Array:
		if ctx.EncKey != nil {
			if _, err := decryptDeepObject(o, objNr, genNr, ctx.EncKey, ctx.AES4Strings, ctx.E.R); err != nil {
				return nil, err
			}
		}
		return o, nil

	case StringLiteral:
		if ctx.EncKey != nil {
			sl, err := decryptStringLiteral(o, objNr, genNr, ctx.EncKey, ctx.AES4Strings, ctx.E.R)
			if err != nil {
				return nil, err
			}
			return *sl, nil
		}
		return o, nil

	case HexLiteral:
		if ctx.EncKey != nil {
			hl, err := decryptHexLiteral(o, objNr, genNr, ctx.EncKey, ctx.AES4Strings, ctx.E.R)
			if err != nil {
				return nil, err
			}
			return *hl, nil
		}
		return o, nil

	default:
		return o, nil
	}
}

func ParseObjectWithContext(c ContextContext, ctx *Context, offset int64, objNr, genNr int) (Object, error) {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("ParseObject: begin, obj#%d, offset:%d\n", objNr, offset)
	// }

	obj, endInd, streamInd, streamOffset, err := object(c, ctx, offset, objNr, genNr)
	if err != nil {
		if ctx.XRefTable.ValidationMode == ValidationRelaxed {
			if err == io.EOF {
				err = nil
			}
		}
		return nil, err
	}

	return resolveObject(c, ctx, obj, offset, objNr, genNr, endInd, streamInd, streamOffset)
}

func dereferencedObject(c ContextContext, ctx *Context, objNr int) (Object, error) {
	entry, ok := ctx.Find(objNr)
	if !ok {
		return nil, errors.Errorf("pdfcpu: dereferencedObject: unregistered object: %d", objNr)
	}

	if entry.Compressed {
		if err := decompressXRefTableEntry(ctx.XRefTable, objNr, entry); err != nil {
			return nil, err
		}
	}

	if entry.Object == nil {

		// if log.ReadEnabled() {
		// 	log.Read.Printf("dereferencedObject: dereferencing object %d\n", objNr)
		// }

		if entry.Free {
			return nil, ErrReferenceDoesNotExist
		}

		o, err := ParseObjectWithContext(c, ctx, *entry.Offset, objNr, *entry.Generation)
		if err != nil {
			return nil, errors.Wrapf(err, "dereferencedObject: problem dereferencing object %d", objNr)
		}

		if o == nil {
			return nil, errors.New("pdfcpu: dereferencedObject: object is nil")
		}

		entry.Object = o
	} else if l, ok := entry.Object.(LazyObjectStreamObject); ok {
		o, err := l.DecodedObject(c)
		if err != nil {
			return nil, errors.Wrapf(err, "dereferencedObject: problem dereferencing object %d", objNr)
		}

		ProcessRefCounts(ctx.XRefTable, o)
		entry.Object = o
	}

	return entry.Object, nil
}

func dereferencedDict(c ContextContext, ctx *Context, objNr int) (Dict, error) {
	o, err := dereferencedObject(c, ctx, objNr)
	if err != nil {
		return nil, err
	}

	d, ok := o.(Dict)
	if !ok {
		return nil, errors.New("pdfcpu: dereferencedDict: corrupt dict")
	}

	return d, nil
}

func singleFilter(c ContextContext, ctx *Context, filterName string, d Dict) ([]PDFFilter, error) {
	o, found := d.Find("DecodeParms")
	if !found {
		// w/o decode parameters.
		// if log.ReadEnabled() {
		// 	log.Read.Println("singleFilter: end w/o decode parms")
		// }
		return []PDFFilter{{Name: filterName}}, nil
	}

	var err error
	d, ok := o.(Dict)
	if !ok {
		indRef, ok := o.(IndirectRef)
		if !ok {
			return nil, errors.Errorf("singleFilter: corrupt Dict: %s\n", o)
		}
		if d, err = dereferencedDict(c, ctx, indRef.ObjectNumber.Value()); err != nil {
			return nil, err
		}
	}

	// // with decode parameters.
	// if log.ReadEnabled() {
	// 	log.Read.Println("singleFilter: end with decode parms")
	// }

	return []PDFFilter{{Name: filterName, DecodeParms: d}}, nil
}

func filterArraySupportsDecodeParms(filters Array) bool {
	for _, obj := range filters {
		if name, ok := obj.(NameType); ok {
			if SupportsDecodeParms(name.String()) {
				return true
			}
		}
	}
	return false
}

func buildFilterPipeline(c ContextContext, ctx *Context, filterArray, decodeParmsArr Array) ([]PDFFilter, error) {
	var filterPipeline []PDFFilter

	for i, f := range filterArray {

		filterName, ok := f.(NameType)
		if !ok {
			return nil, errors.New("pdfcpu: buildFilterPipeline: filterArray elements corrupt")
		}
		if decodeParmsArr == nil || decodeParmsArr[i] == nil {
			filterPipeline = append(filterPipeline, PDFFilter{Name: filterName.Value(), DecodeParms: nil})
			continue
		}

		dict, ok := decodeParmsArr[i].(Dict)
		if !ok {
			indRef, ok := decodeParmsArr[i].(IndirectRef)
			if !ok {
				return nil, errors.Errorf("buildFilterPipeline: corrupt Dict: %s\n", dict)
			}
			d, err := dereferencedDict(c, ctx, indRef.ObjectNumber.Value())
			if err != nil {
				return nil, err
			}
			dict = d
		}

		filterPipeline = append(filterPipeline, PDFFilter{Name: filterName.String(), DecodeParms: dict})
	}

	return filterPipeline, nil
}

// Return the filter pipeline associated with this stream dict.
func pdfFilterPipeline(c ContextContext, ctx *Context, dict Dict) ([]PDFFilter, error) {
	// if log.ReadEnabled() {
	// 	log.Read.Println("pdfFilterPipeline: begin")
	// }

	var err error

	o, found := dict.Find("Filter")
	if !found {
		// stream is not compressed.
		return nil, nil
	}

	// compressed stream.

	var filterPipeline []PDFFilter

	if indRef, ok := o.(IndirectRef); ok {
		if o, err = dereferencedObject(c, ctx, indRef.ObjectNumber.Value()); err != nil {
			return nil, err
		}
	}

	// fmt.Printf("dereferenced filter obj: %s\n", obj)

	if name, ok := o.(NameType); ok {
		return singleFilter(c, ctx, name.String(), dict)
	}

	// filter pipeline.

	// Array of filternames
	filterArray, ok := o.(Array)
	if !ok {
		return nil, errors.Errorf("pdfFilterPipeline: Expected filterArray corrupt, %v %T", o, o)
	}

	// Optional array of decode parameter dicts.
	var decodeParmsArr Array
	decodeParms, found := dict.Find("DecodeParms")
	if found {
		if filterArraySupportsDecodeParms(filterArray) {
			decodeParmsArr, ok = decodeParms.(Array)
			if ok {
				if len(decodeParmsArr) != len(filterArray) {
					return nil, errors.New("pdfcpu: pdfFilterPipeline: expected decodeParms array corrupt")
				}
			}
		}
	}

	// fmt.Printf("decodeParmsArr: %s\n", decodeParmsArr)

	filterPipeline, err = buildFilterPipeline(c, ctx, filterArray, decodeParmsArr)

	// if log.ReadEnabled() {
	// 	log.Read.Println("pdfFilterPipeline: end")
	// }

	return filterPipeline, err
}

func dereferencedInteger(c ContextContext, ctx *Context, objNr int) (*Integer, error) {
	o, err := dereferencedObject(c, ctx, objNr)
	if err != nil {
		return nil, err
	}

	i, ok := o.(Integer)
	if !ok {
		return nil, errors.New("pdfcpu: dereferencedInteger: corrupt integer")
	}

	return &i, nil
}

// dereference a Integer object representing an int64 value.
func int64Object(c ContextContext, ctx *Context, objNr int) (*int64, error) {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("int64Object begin: %d\n", objNr)
	// }

	i, err := dereferencedInteger(c, ctx, objNr)
	if err != nil {
		return nil, err
	}

	i64 := int64(i.Value())

	// if log.ReadEnabled() {
	// 	log.Read.Printf("int64Object end: %d\n", objNr)
	// }

	return &i64, nil
}

func readStreamContentBlindly(rd io.Reader) (buf []byte, err error) {
	// Weak heuristic for reading in stream data for cases where stream length is unknown.
	// ...data...{eol}endstream{eol}endobj

	growSize := defaultBufSize
	if buf, err = growBufBy(buf, growSize, rd); err != nil {
		return nil, err
	}

	i := bytes.Index(buf, []byte("endstream"))
	if i < 0 {
		for i = -1; i < 0; i = bytes.Index(buf, []byte("endstream")) {
			growSize = min(growSize*2, maximumBufSize)
			buf, err = growBufBy(buf, growSize, rd)
			if err != nil {
				return nil, err
			}
		}
	}

	buf = buf[:i]

	j := 0

	// Cut off trailing eol's.
	for i = len(buf) - 1; i >= 0 && (buf[i] == 0x0A || buf[i] == 0x0D); i-- {
		j++
	}

	if j > 0 {
		buf = buf[:len(buf)-j]
	}

	return buf, nil
}

// Reads and returns a file buffer with length = stream length using provided reader positioned at offset.
func readStreamContent(rd io.Reader, streamLength int) ([]byte, error) {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("readStreamContent: begin streamLength:%d\n", streamLength)
	// }

	if streamLength == 0 {
		// Read until "endstream" then fix "Length".
		return readStreamContentBlindly(rd)
	}

	buf := make([]byte, streamLength)

	for totalCount := 0; totalCount < streamLength; {
		count, err := fillBuffer(rd, buf[totalCount:])
		if err != nil {
			if err != io.EOF {
				return nil, err
			}
			// Weak heuristic to detect the actual end of this stream
			// once we have reached EOF due to incorrect streamLength.
			eob := bytes.Index(buf, []byte("endstream"))
			if eob < 0 {
				return nil, err
			}
			return buf[:eob], nil
		}

		// if log.ReadEnabled() {
		// 	log.Read.Printf("readStreamContent: count=%d, buflen=%d(%X)\n", count, len(buf), len(buf))
		// }
		totalCount += count
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("readStreamContent: end\n")
	// }

	return buf, nil
}

func ensureStreamLength(sd *StreamDict, fixLength bool) {
	l := int64(len(sd.Raw))
	if fixLength || sd.StreamLength == nil || l != *sd.StreamLength {
		sd.StreamLength = &l
		sd.Dict["Length"] = Integer(l)
	}
}

func loadEncodedStreamContent(c ContextContext, ctx *Context, sd *StreamDict, fixLength bool) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("loadEncodedStreamContent: begin\n%v\n", sd)
	// }

	var err error

	if sd.Raw != nil {
		// if log.ReadEnabled() {
		// 	log.Read.Println("loadEncodedStreamContent: end, already in memory.")
		// }
		return nil
	}

	// Read stream content encoded at offset with stream length.

	// Dereference stream length if stream length is an indirect object.
	if !fixLength && sd.StreamLength == nil {
		if sd.StreamLengthObjNr == nil {
			return errors.New("pdfcpu: loadEncodedStreamContent: missing streamLength")
		}
		if sd.StreamLength, err = int64Object(c, ctx, *sd.StreamLengthObjNr); err != nil {
			if err != ErrReferenceDoesNotExist {
				return err
			}
		}
		// if log.ReadEnabled() {
		// 	log.Read.Printf("loadEncodedStreamContent: new indirect streamLength:%d\n", *sd.StreamLength)
		// }
	}

	newOffset := sd.StreamOffset
	rd, err := newPositionedReader(ctx.Read.RS, &newOffset)
	if err != nil {
		return err
	}

	l1 := 0
	if !fixLength && sd.StreamLength != nil {
		l1 = int(*sd.StreamLength)
	}
	rawContent, err := readStreamContent(rd, l1)
	if err != nil {
		return err
	}

	sd.Raw = rawContent

	ensureStreamLength(sd, fixLength)

	// if log.ReadEnabled() {
	// 	log.Read.Printf("loadEncodedStreamContent: end: len(streamDictRaw)=%d\n", len(sd.Raw))
	// }

	return nil
}

func applyRC4Bytes(buf, key []byte) ([]byte, error) {
	c, err := rc4.NewCipher(key)
	if err != nil {
		return nil, err
	}

	var b bytes.Buffer

	r := &cipher.StreamReader{S: c, R: bytes.NewReader(buf)}

	_, err = io.Copy(&b, r)
	if err != nil {
		return nil, err
	}

	return b.Bytes(), nil
}

// decryptStream decrypts a stream buffer using RC4 or AES.
func decryptStream(buf []byte, objNr, genNr int, encKey []byte, needAES bool, r int) ([]byte, error) {
	k := encKey
	if r != 5 && r != 6 {
		k = decryptKey(objNr, genNr, encKey, needAES)
	}

	if needAES {
		return decryptAESBytes(buf, k)
	}

	return applyRC4Bytes(buf, k)
}

// Decodes the raw encoded stream content and saves it to streamDict.Content.
func saveDecodedStreamContent(ctx *Context, sd *StreamDict, objNr, genNr int, decode bool) (err error) {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("saveDecodedStreamContent: begin decode=%t\n", decode)
	// }

	// If the "Identity" crypt filter is used we do not need to decrypt.
	if ctx != nil && ctx.EncKey != nil {
		if len(sd.FilterPipeline) == 1 && sd.FilterPipeline[0].Name == "Crypt" {
			sd.Content = sd.Raw
			return nil
		}
	}

	// Special case: If the length of the encoded data is 0, we do not need to decode anything.
	if len(sd.Raw) == 0 {
		sd.Content = sd.Raw
		return nil
	}

	// ctx gets created after XRefStream parsing.
	// XRefStreams are not encrypted.
	if ctx != nil && ctx.EncKey != nil {
		if sd.Raw, err = decryptStream(sd.Raw, objNr, genNr, ctx.EncKey, ctx.AES4Streams, ctx.E.R); err != nil {
			return err
		}
		ensureStreamLength(sd, true)
	}

	if !decode {
		return nil
	}

	if sd.Image() {
		return nil
	}

	// Actual decoding of stream data.
	err = sd.Decode()
	if err == ErrUnsupportedFilter {
		err = nil
	}
	if err != nil {
		return err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("saveDecodedStreamContent: end")
	// }

	return nil
}

func xRefStreamDict(c ContextContext, ctx *Context, o Object, objNr int, streamOffset int64) (*XRefStreamDict, error) {
	d, ok := o.(Dict)
	if !ok {
		return nil, errors.New("pdfcpu: xRefStreamDict: no dict")
	}

	// Parse attributes for stream object.
	streamLength, streamLengthObjNr := d.Length()
	if streamLength == nil && streamLengthObjNr == nil {
		return nil, errors.New("pdfcpu: xRefStreamDict: no \"Length\" entry")
	}

	filterPipeline, err := pdfFilterPipeline(c, ctx, d)
	if err != nil {
		return nil, err
	}

	// We have a stream object.
	// if log.ReadEnabled() {
	// 	log.Read.Printf("xRefStreamDict: streamobject #%d\n", objNr)
	// }
	sd := NewStreamDict(d, streamOffset, streamLength, streamLengthObjNr, filterPipeline)

	if err = loadEncodedStreamContent(c, ctx, &sd, false); err != nil {
		return nil, err
	}

	// Decode xrefstream content
	if err = saveDecodedStreamContent(nil, &sd, 0, 0, true); err != nil {
		return nil, errors.Wrapf(err, "xRefStreamDict: cannot decode stream for obj#:%d\n", objNr)
	}

	return ParseXRefStreamDict(&sd)
}

func createXRefTableEntryFromXRefStream(entryType int64, objNr int, c2, c3, offExtra int64, objStreams IntSet, incr int) XRefTableEntry {
	var xRefTableEntry XRefTableEntry

	switch entryType {

	case 0x00:
		// free object
		// if log.ReadEnabled() {
		// 	log.Read.Printf("createXRefTableEntryFromXRefStream: Object #%d is unused, next free is object#%d, generation=%d\n", objNr, c2, c3)
		// }
		g := int(c3)

		xRefTableEntry = XRefTableEntry{
			Free:       true,
			Compressed: false,
			Offset:     &c2,
			Generation: &g,
			Incr:       incr,
		}

	case 0x01:
		// in use object
		// if log.ReadEnabled() {
		// 	log.Read.Printf("createXRefTableEntryFromXRefStream: Object #%d is in use at offset=%d, generation=%d\n", objNr, c2, c3)
		// }
		g := int(c3)

		c2 += offExtra

		xRefTableEntry = XRefTableEntry{
			Free:       false,
			Compressed: false,
			Offset:     &c2,
			Generation: &g,
			Incr:       incr,
		}

	case 0x02:
		// compressed object
		// generation always 0.
		// if log.ReadEnabled() {
		// 	log.Read.Printf("createXRefTableEntryFromXRefStream: Object #%d is compressed at obj %5d[%d]\n", objNr, c2, c3)
		// }
		objNumberRef := int(c2)
		objIndex := int(c3)

		xRefTableEntry = XRefTableEntry{
			Free:            false,
			Compressed:      true,
			ObjectStream:    &objNumberRef,
			ObjectStreamInd: &objIndex,
			Incr:            incr,
		}

		objStreams[objNumberRef] = true
	}

	return xRefTableEntry
}

// For each object embedded in this xRefStream create the corresponding xRef table entry.
func extractXRefTableEntriesFromXRefStream(buf []byte, offExtra int64, xsd *XRefStreamDict, ctx *Context, incr int) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("extractXRefTableEntriesFromXRefStream begin")
	// }

	// Note:
	// A value of zero for an element in the W array indicates that the corresponding field shall not be present in the stream,
	// and the default value shall be used, if there is one.
	// If the first element is zero, the type field shall not be present, and shall default to type 1.

	i1 := xsd.W[0]
	i2 := xsd.W[1]
	i3 := xsd.W[2]

	xrefEntryLen := i1 + i2 + i3
	// if log.ReadEnabled() {
	// 	log.Read.Printf("extractXRefTableEntriesFromXRefStream: begin xrefEntryLen = %d\n", xrefEntryLen)
	// }

	if xrefEntryLen != 0 && len(buf)%xrefEntryLen > 0 {
		return errors.New("pdfcpu: extractXRefTableEntriesFromXRefStream: corrupt xrefstream")
	}

	objCount := len(xsd.Objects)
	// if log.ReadEnabled() {
	// 	log.Read.Printf("extractXRefTableEntriesFromXRefStream: objCount:%d %v\n", objCount, xsd.Objects)
	// 	log.Read.Printf("extractXRefTableEntriesFromXRefStream: len(buf):%d objCount*xrefEntryLen:%d\n", len(buf), objCount*xrefEntryLen)
	// }
	if len(buf) < objCount*xrefEntryLen {
		// Sometimes there is an additional xref entry not accounted for by "Index".
		// We ignore such entries and do not treat this as an error.
		return errors.New("pdfcpu: extractXRefTableEntriesFromXRefStream: corrupt xrefstream")
	}

	j := 0

	// bufToInt64 interprets the content of buf as an int64.
	bufToInt64 := func(buf []byte) (i int64) {
		for _, b := range buf {
			i <<= 8
			i |= int64(b)
		}
		return
	}

	for i := 0; i < len(buf) && j < len(xsd.Objects); i += xrefEntryLen {

		objNr := xsd.Objects[j]

		if ctx.XRefTable.Exists(objNr) {
			// if log.ReadEnabled() {
			// 	log.Read.Printf("extractXRefTableEntriesFromXRefStream: Skip entry %d - already assigned\n", objNr)
			// }
			j++
			continue
		}

		var c1 int64
		if i1 == 0 {
			// If the first element is zero, the type field shall not be present,
			// and shall default to type 1.
			c1 = 1
		} else {
			c1 = bufToInt64(buf[i : i+i1])
		}
		c2 := bufToInt64(buf[i+i1 : i+i1+i2])
		c3 := bufToInt64(buf[i+i1+i2 : i+i1+i2+i3])

		entry := createXRefTableEntryFromXRefStream(c1, objNr, c2, c3, offExtra, ctx.Read.ObjectStreams, incr)
		ctx.Table[objNr] = &entry
		j++
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("extractXRefTableEntriesFromXRefStream: end")
	// }

	return nil
}

func processXRefStream(ctx *Context, xsd *XRefStreamDict, objNr *int, offset *int64, offExtra int64, incr int) (prevOffset *int64, err error) {
	// if log.ReadEnabled() {
	// 	log.Read.Println("processXRefStream: begin")
	// }

	if err = parseTrailer(ctx.XRefTable, xsd.Dict); err != nil {
		return nil, err
	}

	// Parse xRefStream and create xRefTable entries for embedded objects.
	if err = extractXRefTableEntriesFromXRefStream(xsd.Content, offExtra, xsd, ctx, incr); err != nil {
		return nil, err
	}

	*offset += offExtra

	if entry, ok := ctx.Table[*objNr]; ok && entry.Offset != nil && *entry.Offset == *offset {
		entry.Object = *xsd
	}

	//////////////////
	// entry :=
	// 	XRefTableEntry{
	// 		Free:       false,
	// 		Offset:     offset,
	// 		Generation: genNr,
	// 		Object:     *xsd}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("processXRefStream: Insert new xRefTable entry for Object %d\n", *objNr)
	// }

	// ctx.Table[*objNr] = &entry
	// ctx.Read.XRefStreams[*objNr] = true
	///////////////////

	prevOffset = xsd.PreviousOffset

	// if log.ReadEnabled() {
	// 	log.Read.Println("processXRefStream: end")
	// }

	return prevOffset, nil
}

// Parse xRef stream and setup xrefTable entries for all embedded objects and the xref stream dict.
func parseXRefStream(c ContextContext, ctx *Context, rd io.Reader, offset *int64, offExtra int64, incr int) (prevOffset *int64, err error) {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseXRefStream: begin at offset %d\n", *offset)
	// }

	buf, endInd, streamInd, streamOffset, err := buffer(c, rd)
	if err != nil {
		return nil, err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseXRefStream: endInd=%[1]d(%[1]x) streamInd=%[2]d(%[2]x)\n", endInd, streamInd)
	// }

	line := string(buf)

	// We expect a stream and therefore "stream" before "endobj" if "endobj" within buffer.
	// There is no guarantee that "endobj" is contained in this buffer for large streams!
	if streamInd < 0 || (endInd > 0 && endInd < streamInd) {
		return nil, errors.New("pdfcpu: parseXRefStream: corrupt pdf file")
	}

	// Init object parse buf.
	l := line[:streamInd]

	objNr, _, err := ParseObjectAttributes(&l)
	if err != nil {
		return nil, err
	}

	// parse this object
	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseXRefStream: xrefstm obj#:%d gen:%d\n", *objNr, *genNr)
	// 	log.Read.Printf("parseXRefStream: dereferencing object %d\n", *objNr)
	// }

	o, err := ParseObjectContext(c, &l)
	if err != nil {
		return nil, errors.Wrapf(err, "parseXRefStream: no object")
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseXRefStream: we have an object: %s\n", o)
	// }

	streamOffset += *offset
	xsd, err := xRefStreamDict(c, ctx, o, *objNr, streamOffset)
	if err != nil {
		return nil, err
	}

	return processXRefStream(ctx, xsd, objNr, offset, offExtra, incr)
}

// Parse an xRefStream for a hybrid PDF file.
func parseHybridXRefStream(c ContextContext, ctx *Context, offset *int64, offExtra int64, incr int) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("parseHybridXRefStream: begin")
	// }

	rd, err := newPositionedReader(ctx.Read.RS, offset)
	if err != nil {
		return err
	}

	if _, err = parseXRefStream(c, ctx, rd, offset, offExtra, incr); err != nil {
		return err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseHybridXRefStream: end")
	// }

	return nil
}

func parseTrailerDict(c ContextContext, ctx *Context, trailerDict Dict, offCurXRef *int64, offExtra int64, incr int) (*int64, error) {
	xRefTable := ctx.XRefTable

	if err := parseTrailer(xRefTable, trailerDict); err != nil {
		return nil, err
	}

	handleAdditionalStreams(trailerDict, xRefTable)

	offset := offsetPrev(ctx, trailerDict, offCurXRef)

	offsetXRefStream := trailerDict.Int64Entry("XRefStm")
	if offsetXRefStream == nil {
		// No cross reference stream.
		if !ctx.Reader15 && xRefTable.Version() >= V14 && !ctx.Read.Hybrid {
			return nil, errors.Errorf("parseTrailerDict: PDF1.4 conformant reader: found incompatible version: %s", xRefTable.VersionString())
		}
		// if log.ReadEnabled() {
		// 	log.Read.Println("parseTrailerDict end")
		// }
		// continue to parse previous xref section, if there is any.
		return offset, nil
	}

	// This file is using cross reference streams.

	if !ctx.Read.Hybrid {
		ctx.Read.Hybrid = true
		ctx.Read.UsingXRefStreams = true
	}

	// 1.5 conformant readers process hidden objects contained
	// in XRefStm before continuing to process any previous XRefSection.
	// Previous XRefSection is expected to have free entries for hidden entries.
	// May appear in XRefSections only.
	if ctx.Reader15 {
		if err := parseHybridXRefStream(c, ctx, offsetXRefStream, offExtra, incr); err != nil {
			return nil, err
		}
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseTrailerDict end")
	// }

	return offset, nil
}

func processTrailer(c ContextContext, ctx *Context, s *bufio.Scanner, line string, offCurXRef *int64, offExtra int64, incr int) (*int64, error) {
	var trailerString string

	if line != "trailer" {
		trailerString = line[7:]
		// if log.ReadEnabled() {
		// 	log.Read.Printf("processTrailer: trailer leftover: <%s>\n", trailerString)
		// }
	} else {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("line (len %d) <%s>\n", len(line), line)
		// }
	}

	trailerString, err := scanTrailer(s, trailerString)
	if err != nil {
		return nil, err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("processTrailer: trailerString: (len:%d) <%s>\n", len(trailerString), trailerString)
	// }

	o, err := ParseObjectContext(c, &trailerString)
	if err != nil {
		return nil, err
	}

	trailerDict, ok := o.(Dict)
	if !ok {
		return nil, errors.New("pdfcpu: processTrailer: corrupt trailer dict")
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("processTrailer: trailerDict:\n%s\n", trailerDict)
	// }

	return parseTrailerDict(c, ctx, trailerDict, offCurXRef, offExtra, incr)
}

// Parse xRef section into corresponding number of xRef table entries.
func parseXRefSection(c ContextContext, ctx *Context, s *bufio.Scanner, fields []string, ssCount *int, offCurXRef *int64, offExtra int64, repairOff, incr int) (*int64, error) {
	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefSection begin")
	// }

	var (
		line string
		err  error
	)

	if len(fields) == 0 {

		line, err = scanLine(s)
		if err != nil {
			return nil, err
		}

		// if log.ReadEnabled() {
		// 	log.Read.Printf("parseXRefSection: <%s>\n", line)
		// }

		fields = strings.Fields(line)
	}

	// Process all sub sections of this xRef section.
	for !strings.HasPrefix(line, "trailer") && len(fields) == 2 {

		if err = parseXRefTableSubSection(ctx.XRefTable, s, fields, offExtra, repairOff, incr); err != nil {
			return nil, err
		}
		*ssCount++

		// trailer or another xref table subsection ?
		if line, err = scanLine(s); err != nil {
			return nil, err
		}

		// if empty line try next line for trailer
		if len(line) == 0 {
			if line, err = scanLine(s); err != nil {
				return nil, err
			}
		}

		fields = strings.Fields(line)
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefSection: All subsections read!")
	// }

	if !strings.HasPrefix(line, "trailer") {
		return nil, errors.Errorf("xrefsection: missing trailer dict, line = <%s>", line)
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseXRefSection: parsing trailer dict..")
	// }

	return processTrailer(c, ctx, s, line, offCurXRef, offExtra, incr)
}

func tryXRefSection(c ContextContext, ctx *Context, rs io.ReadSeeker, offset *int64, offExtra int64, xrefSectionCount *int, incr int) (*int64, error) {
	rd, err := newPositionedReader(rs, offset)
	if err != nil {
		return nil, err
	}

	s := bufio.NewScanner(rd)
	buf := make([]byte, 0, 4096)
	s.Buffer(buf, 1024*1024)
	s.Split(Lines)

	line, err := scanLine(s)
	if err != nil {
		return nil, err
	}
	// if log.ReadEnabled() {
	// 	log.Read.Printf("xref line 1: <%s>\n", line)
	// }
	repairOff := len(line)

	if strings.TrimSpace(line) == "xref" {
		// if log.ReadEnabled() {
		// 	log.Read.Println("tryXRefSection: found xref section")
		// }
		return parseXRefSection(c, ctx, s, nil, xrefSectionCount, offset, offExtra, 0, incr)
	}

	// Repair fix for #823
	if strings.HasPrefix(line, "xref") {
		fields := strings.Fields(line)
		if len(fields) == 3 {
			return parseXRefSection(c, ctx, s, fields[1:], xrefSectionCount, offset, offExtra, 0, incr)
		}
	}

	// Repair fix for #326
	if line, err = scanLine(s); err != nil {
		return nil, err
	}
	// if log.ReadEnabled() {
	// 	log.Read.Printf("xref line 2: <%s>\n", line)
	// }

	i := strings.Index(line, "xref")
	if i >= 0 {
		// if log.ReadEnabled() {
		// 	log.Read.Println("tryXRefSection: found xref section")
		// }
		repairOff += i
		// if log.ReadEnabled() {
		// 	log.Read.Printf("Repair offset: %d\n", repairOff)
		// }
		return parseXRefSection(c, ctx, s, nil, xrefSectionCount, offset, offExtra, repairOff, incr)
	}

	return &zero, nil
}

func loadStreamDict(c ContextContext, ctx *Context, sd *StreamDict, objNr, genNr int, fixLength bool) error {
	// Load encoded stream content for stream dicts into xRefTable entry.
	if err := loadEncodedStreamContent(c, ctx, sd, fixLength); err != nil {
		return errors.Wrapf(err, "dereferenceObject: problem dereferencing stream %d", objNr)
	}

	// Decode stream content.
	if err := saveDecodedStreamContent(ctx, sd, objNr, genNr, ctx.DecodeAllStreams); err != nil {
		return err
	}

	ctx.Read.BinaryTotalSize += *sd.StreamLength

	return nil
}

func parseAndLoad(c ContextContext, ctx *Context, line string, offset *int64, incr int) error {
	l := line
	objNr, generation, err := ParseObjectAttributes(&l)
	if err != nil {
		return err
	}

	entry := XRefTableEntry{
		Free:       false,
		Offset:     offset,
		Generation: generation,
		Incr:       incr,
	}

	if !ctx.XRefTable.Exists(*objNr) {
		ctx.Table[*objNr] = &entry
	}

	o, err := ParseObjectWithContext(c, ctx, *entry.Offset, *objNr, *entry.Generation)
	if err != nil {
		return err
	}

	entry.Object = o

	sd, ok := o.(StreamDict)
	if ok {
		if err = loadStreamDict(c, ctx, &sd, *objNr, *generation, true); err != nil {
			return err
		}
		entry.Object = sd
		*offset = sd.StreamOffset + *sd.StreamLength
		return nil
	}

	if ctx.RootDict == nil {
		if d, ok := o.(Dict); ok {
			if typ := d.Type(); typ != nil {
				if *typ == "Catalog" {
					ctx.RootDict = d
					ctx.Root = NewIndirectRef(*objNr, *generation)
				}
			}
		}
	}

	*offset += int64(len(line) + ctx.Read.EolCount)

	return nil
}

func processObject(c ContextContext, ctx *Context, line string, offset *int64, incr int) (*bufio.Scanner, error) {
	if err := parseAndLoad(c, ctx, line, offset, incr); err != nil {
		return nil, err
	}
	rd, err := newPositionedReader(ctx.Read.RS, offset)
	if err != nil {
		return nil, err
	}
	s := bufio.NewScanner(rd)
	s.Split(Lines)
	return s, nil
}

// bypassXrefSection is a fix for digesting corrupt xref sections.
// It populates the xRefTable by reading in all indirect objects line by line
// and works on the assumption of a single xref section - meaning no incremental updates.
func bypassXrefSection(c ContextContext, ctx *Context, offExtra int64, wasErr error, incr int) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("bypassXRefSection after %v\n", wasErr)
	// }

	var z int64
	g := FreeHeadGeneration
	ctx.Table[0] = &XRefTableEntry{
		Free:       true,
		Offset:     &z,
		Generation: &g,
	}

	rs := ctx.Read.RS
	eolCount := ctx.Read.EolCount
	var offset int64

	rd, err := newPositionedReader(rs, &offset)
	if err != nil {
		return err
	}

	s := bufio.NewScanner(rd)
	s.Split(Lines)

	bb := []byte{}
	var (
		withinXref    bool
		withinTrailer bool
	)

	for {
		line, err := scanLineRaw(s)
		if err != nil {
			break
		}
		if withinXref {
			offset += int64(len(line) + eolCount)
			if withinTrailer {
				bb = append(bb, '\n')
				bb = append(bb, line...)
				i := strings.Index(line, "startxref")
				if i >= 0 {
					_, err = processTrailer(c, ctx, s, string(bb), nil, offExtra, incr)
					return err
				}
				continue
			}
			i := strings.Index(line, "trailer")
			if i >= 0 {
				bb = append(bb, line...)
				withinTrailer = true
			}
			continue
		}
		i := strings.Index(line, "xref")
		if i >= 0 {
			offset += int64(len(line) + eolCount)
			withinXref = true
			continue
		}
		i = strings.Index(line, "obj")
		if i >= 0 {
			if i > 2 && strings.Index(line, "endobj") != i-3 {
				s, err = processObject(c, ctx, line, &offset, incr)
				if err != nil {
					return err
				}
				continue
			}
		}
		offset += int64(len(line) + eolCount)
		continue
	}
	return nil
}

func postProcess(ctx *Context, xrefSectionCount int) {
	// Ensure free object #0 if exactly one xref subsection
	// and in one of the following weird situations:
	if xrefSectionCount == 1 && !ctx.Exists(0) {
		// Fix for #250
		if *ctx.Size == len(ctx.Table)+1 {
			// Create free object 0 from scratch if the free list head is missing.
			g0 := FreeHeadGeneration
			ctx.Table[0] = &XRefTableEntry{Free: true, Offset: &zero, Generation: &g0}
		} else {
			// Create free object 0 by shifting down all objects by one.
			for i := 1; i <= *ctx.Size; i++ {
				ctx.Table[i-1] = ctx.Table[i]
			}
			delete(ctx.Table, *ctx.Size)
		}
	}
}

// Build XRefTable by reading XRef streams or XRef sections.
func buildXRefTableStartingAt(c ContextContext, ctx *Context, offset *int64) error {
	rs := ctx.Read.RS
	hv, eolCount, offExtra, err := headerVersion(rs)
	if err != nil {
		return err
	}
	*offset += offExtra

	ctx.HeaderVersion = hv
	ctx.Read.EolCount = eolCount
	offs := map[int64]bool{}
	xrefSectionCount := 0
	incr := 0

	for offset != nil {

		incr++
		// fmt.Printf("Incr: %d\n", incr)

		if err := c.Err(); err != nil {
			return err
		}

		if offs[*offset] {
			if offset, err = offsetLastXRefSection(ctx, ctx.Read.FileSize-*offset); err != nil {
				return err
			}
			if offs[*offset] {
				return nil
			}
		}

		offs[*offset] = true

		off, err := tryXRefSection(c, ctx, rs, offset, offExtra, &xrefSectionCount, incr)
		if err != nil {
			return err
		}

		if off == nil || *off != 0 {
			offset = off
			continue
		}

		// if log.ReadEnabled() {
		// 	log.Read.Println("buildXRefTableStartingAt: found xref stream")
		// }
		ctx.Read.UsingXRefStreams = true
		rd, err := newPositionedReader(rs, offset)
		if err != nil {
			return err
		}

		if offset, err = parseXRefStream(c, ctx, rd, offset, offExtra, incr); err != nil {
			// Try fix for corrupt single xref section.
			return bypassXrefSection(c, ctx, offExtra, err, incr)
		}

	}

	postProcess(ctx, xrefSectionCount)

	// if log.ReadEnabled() {
	// 	log.Read.Println("buildXRefTableStartingAt: end")
	// }

	return nil
}

// Populate the cross reference table for this PDF file.
// Goto offset of first xref table entry.
// Can be "xref" or indirect object reference eg. "34 0 obj"
// Keep digesting xref sections as long as there is a defined previous xref section
// and build up the xref table along the way.
func readXRefTable(c ContextContext, ctx *Context) (err error) {
	offset, err := offsetLastXRefSection(ctx, 0)
	if err != nil {
		if err != ErrMissingXRefSection {
			return err
		}
		zero := int64(0)
		offset = &zero
	}

	ctx.Write.OffsetPrevXRef = offset

	err = buildXRefTableStartingAt(c, ctx, offset)
	if err == io.EOF {
		return errors.Wrap(err, "readXRefTable: unexpected eof")
	}
	if err != nil {
		return
	}

	// Log list of free objects (not the "free list").
	// log.Read.Printf("freelist: %v\n", ctx.freeObjects())

	// Note: Acrobat 6.0 and later do not use the free list to recycle object numbers - pdfcpu does.
	err = ctx.EnsureValidFreeList()

	// if log.ReadEnabled() {
	// 	log.Read.Println("readXRefTable: end")
	// }

	return err
}

func newOptimizationContext() *OptimizationContext {
	return &OptimizationContext{
		FontObjects:          map[int]*FontObject{},
		FormFontObjects:      map[int]*FontObject{},
		Fonts:                map[string][]int{},
		DuplicateFonts:       map[int]Dict{},
		DuplicateFontObjs:    IntSet{},
		ImageObjects:         map[int]*ImageObject{},
		DuplicateImages:      map[int]*DuplicateImageObject{},
		DuplicateImageObjs:   IntSet{},
		DuplicateInfoObjects: IntSet{},
		ContentStreamCache:   map[int]*StreamDict{},
		FormStreamCache:      map[int]*StreamDict{},
		Cache:                map[int]bool{},
	}
}

func newReadContext(rs io.ReadSeeker) (*ReadContextType, error) {
	rdCtx := &ReadContextType{
		RS:            rs,
		ObjectStreams: IntSet{},
		XRefStreams:   IntSet{},
	}

	fileSize, err := rs.Seek(0, io.SeekEnd)
	if err != nil {
		return nil, err
	}
	rdCtx.FileSize = fileSize

	return rdCtx, nil
}

func NewWriteContext(eol string) *WriteContext {
	return &WriteContext{SelectedPages: IntSet{}, Table: map[int]int64{}, Eol: eol, ObjNrs: []int{}}
}

// NewContext initializes a new Context.
func NewContext(rs io.ReadSeeker, conf *Configuration) (*Context, error) {
	if conf == nil {
		conf = NewDefaultConfiguration()
	}

	rdCtx, err := newReadContext(rs)
	if err != nil {
		return nil, err
	}

	ctx := &Context{
		conf,
		newXRefTable(conf),
		rdCtx,
		newOptimizationContext(),
		NewWriteContext(conf.Eol),
		false,
		false,
	}

	return ctx, nil
}

func handleUnencryptedFile(ctx *Context) error {
	if ctx.Cmd == DECRYPT || ctx.Cmd == SETPERMISSIONS {
		return errors.New("pdfcpu: this file is not encrypted")
	}

	if ctx.Cmd != ENCRYPT {
		return nil
	}

	// Encrypt subcommand found.

	if ctx.OwnerPW == "" {
		return errors.New("pdfcpu: please provide owner password and optional user password")
	}

	return nil
}

func getV(ctx *Context, d Dict, l int) (*int, error) {
	v := d.IntEntry("V")

	if v == nil || (*v != 1 && *v != 2 && *v != 4 && *v != 5) {
		return nil, errors.Errorf("getV: \"V\" must be one of 1,2,4,5")
	}

	if *v == 5 {
		if l != 256 {
			return nil, errors.Errorf("getV: \"V\" 5 invalid length, must be 256, got %d", l)
		}
		if ctx.XRefTable.Version() != V20 && ctx.XRefTable.ValidationMode == ValidationStrict {
			return nil, errors.New("getV: 5 valid for PDF 2.0 only")
		}
	}

	return v, nil
}

func validateCFLength(len int, cfm *string) bool {
	// See table 25 Length

	if cfm != nil {
		if (*cfm == "AESV2" && len != 16) || (*cfm == "AESV3" && len != 32) {
			return false
		}
	}

	// Standard security handler expresses in bytes.
	minBytes, maxBytes := 5, 32
	if len < minBytes {
		return false
	}
	if len <= maxBytes {
		return true
	}

	// Public security handler expresses in bits.
	minBits, maxBits := 40, 256
	if len < minBits || len > maxBits {
		return false
	}

	if len%8 > 0 {
		return false
	}

	return true
}

func supportedCFEntry(d Dict) (bool, error) {
	cfm := d.NameEntry("CFM")
	if cfm != nil && *cfm != "V2" && *cfm != "AESV2" && *cfm != "AESV3" {
		return false, errors.New("pdfcpu: supportedCFEntry: invalid entry \"CFM\"")
	}

	aes := cfm != nil && (*cfm == "AESV2" || *cfm == "AESV3")

	ae := d.NameEntry("AuthEvent")
	if ae != nil && *ae != "DocOpen" {
		return aes, errors.New("pdfcpu: supportedCFEntry: invalid entry \"AuthEvent\"")
	}

	len := d.IntEntry("Length")
	if len == nil {
		return aes, nil
	}

	if !validateCFLength(*len, cfm) {
		s := ""
		if cfm != nil {
			s = *cfm
		}
		return false, errors.Errorf("pdfcpu: supportedCFEntry: invalid entry \"Length\" %d %s", *len, s)
	}

	return aes, nil
}

func checkStmf(ctx *Context, stmf *string, cfDict Dict) error {
	if stmf != nil && *stmf != "Identity" {

		d := cfDict.DictEntry(*stmf)
		if d == nil {
			return errors.Errorf("pdfcpu: checkStmf: entry \"%s\" missing in \"CF\"", *stmf)
		}

		aes, err := supportedCFEntry(d)
		if err != nil {
			return errors.Wrapf(err, "pdfcpu: checkStmv: unsupported \"%s\" entry in \"CF\"", *stmf)
		}
		ctx.AES4Streams = aes
	}

	return nil
}

func checkV(ctx *Context, d Dict, l int) (*int, error) {
	v, err := getV(ctx, d, l)
	if err != nil {
		return nil, err
	}

	// v == 2 implies RC4
	if *v != 4 && *v != 5 {
		return v, nil
	}

	// CF
	cfDict := d.DictEntry("CF")
	if cfDict == nil {
		return nil, errors.Errorf("pdfcpu: checkV: required entry \"CF\" missing.")
	}

	// StmF
	stmf := d.NameEntry("StmF")
	err = checkStmf(ctx, stmf, cfDict)
	if err != nil {
		return nil, err
	}

	// StrF
	strf := d.NameEntry("StrF")
	if strf != nil && *strf != "Identity" {
		d1 := cfDict.DictEntry(*strf)
		if d1 == nil {
			return nil, errors.Errorf("pdfcpu: checkV: entry \"%s\" missing in \"CF\"", *strf)
		}
		aes, err := supportedCFEntry(d1)
		if err != nil {
			return nil, errors.Wrapf(err, "checkV: unsupported \"%s\" entry in \"CF\"", *strf)
		}
		ctx.AES4Strings = aes
	}

	// EFF
	eff := d.NameEntry("EFF")
	if eff != nil && *eff != "Identity" {
		d := cfDict.DictEntry(*eff)
		if d == nil {
			return nil, errors.Errorf("pdfcpu: checkV: entry \"%s\" missing in \"CF\"", *eff)
		}
		aes, err := supportedCFEntry(d)
		if err != nil {
			return nil, errors.Wrapf(err, "checkV: unsupported \"%s\" entry in \"CF\"", *eff)
		}
		ctx.AES4EmbeddedStreams = aes
	}

	return v, nil
}

func length(d Dict) (int, error) {
	l := d.IntEntry("Length")
	if l == nil {
		return 40, nil
	}

	if (*l < 40 || *l > 128 || *l%8 > 0) && *l != 256 {
		return 0, errors.Errorf("pdfcpu: length: \"Length\" %d not supported\n", *l)
	}

	return *l, nil
}

var ErrUnknownEncryption = errors.New("pdfcpu: unknown encryption")

func getR(ctx *Context, d Dict) (int, error) {
	maxR := 5
	if ctx.XRefTable.Version() == V20 || ctx.XRefTable.ValidationMode == ValidationRelaxed {
		maxR = 6
	}

	r := d.IntEntry("R")
	if r == nil || *r < 2 || *r > maxR {
		return 0, ErrUnknownEncryption
	}

	return *r, nil
}

func validateAlgorithm(ctx *Context) (ok bool) {
	k := ctx.EncryptKeyLength

	if ctx.XRefTable.Version() == V20 {
		return ctx.EncryptUsingAES && k == 256
	}

	if ctx.EncryptUsingAES {
		return k == 40 || k == 128 || k == 256
	}

	return k == 40 || k == 128
}

func validateAES256Parameters(d Dict) (oe, ue, perms []byte, err error) {
	// OE
	oe, err = d.StringEntryBytes("OE")
	if err != nil {
		return nil, nil, nil, err
	}
	if len(oe) != 32 {
		return nil, nil, nil, errors.New("pdfcpu: encryption dictionary: 'OE' entry missing or not 32 bytes")
	}

	// UE
	ue, err = d.StringEntryBytes("UE")
	if err != nil {
		return nil, nil, nil, err
	}
	if len(ue) != 32 {
		return nil, nil, nil, errors.New("pdfcpu: encryption dictionary: 'UE' entry missing or not 32 bytes")
	}

	// Perms
	perms, err = d.StringEntryBytes("Perms")
	if err != nil {
		return nil, nil, nil, err
	}
	if len(perms) != 16 {
		return nil, nil, nil, errors.New("pdfcpu: encryption dictionary: 'Perms' entry missing or not 16 bytes")
	}

	return oe, ue, perms, nil
}

func validateOAndU(ctx *Context, d Dict) (o, u []byte, err error) {
	// O
	o, err = d.StringEntryBytes("O")
	if err != nil {
		return nil, nil, err
	}
	if l := len(o); l != 32 && l != 48 {
		if ctx.XRefTable.ValidationMode == ValidationStrict || l < 48 {
			return nil, nil, errors.New("pdfcpu: unsupported encryption: missing or invalid required entry \"O\"")
		}
		o = o[:48] // len(o) > 48, truncate
	}

	// U
	u, err = d.StringEntryBytes("U")
	if err != nil {
		return nil, nil, err
	}
	if l := len(u); l != 32 && l != 48 {
		if ctx.XRefTable.ValidationMode == ValidationStrict || l < 48 {
			return nil, nil, errors.New("pdfcpu: unsupported encryption: missing or invalid required entry \"U\"")
		}
		u = u[:48]
	}

	return o, u, nil
}

// SupportedEncryption returns a pointer to a struct encapsulating used encryption.
func supportedEncryption(ctx *Context, d Dict) (*Enc, error) {
	// Filter
	filter := d.NameEntry("Filter")
	if filter == nil || *filter != "Standard" {
		return nil, errors.New("pdfcpu: unsupported encryption: filter must be \"Standard\"")
	}

	// SubFilter
	if d.NameEntry("SubFilter") != nil {
		return nil, errors.New("pdfcpu: unsupported encryption: \"SubFilter\" not supported")
	}

	// Length
	l, err := length(d)
	if err != nil {
		return nil, err
	}

	// V
	v, err := checkV(ctx, d, l)
	if err != nil {
		return nil, err
	}

	// R
	r, err := getR(ctx, d)
	if err != nil {
		return nil, err
	}

	o, u, err := validateOAndU(ctx, d)
	if err != nil {
		return nil, err
	}

	var oe, ue, perms []byte
	if r == 5 || r == 6 {
		oe, ue, perms, err = validateAES256Parameters(d)
		if err != nil {
			return nil, err
		}
	}

	// P
	p := d.IntEntry("P")
	if p == nil {
		return nil, errors.New("pdfcpu: unsupported encryption: required entry \"P\" missing")
	}

	// EncryptMetadata
	encMeta := true
	emd := d.BooleanEntry("EncryptMetadata")
	if emd != nil {
		encMeta = *emd
	}

	return &Enc{
			O:     o,
			OE:    oe,
			U:     u,
			UE:    ue,
			L:     l,
			P:     *p,
			Perms: perms,
			R:     r,
			V:     *v,
			Emd:   encMeta,
		},
		nil
}

func processInput(input string) ([]byte, error) {
	// Create a new Precis profile for SASLprep
	p := precis.NewIdentifier(
		precis.BidiRule,
		precis.Norm(norm.NFKC),
	)

	output, err := p.String(input)
	if err != nil {
		return nil, err
	}

	return []byte(output), nil
}

func validationSalt(bb []byte) []byte {
	return bb[32:40]
}

func keySalt(bb []byte) []byte {
	return bb[40:48]
}

func decryptOE(ctx *Context, opw []byte) error {
	b := append(opw, keySalt(ctx.E.O)...)
	b = append(b, ctx.E.U...)
	key := sha256.Sum256(b)

	cb, err := aes.NewCipher(key[:])
	if err != nil {
		return err
	}

	iv := make([]byte, 16)
	ctx.EncKey = make([]byte, 32)

	mode := cipher.NewCBCDecrypter(cb, iv)
	mode.CryptBlocks(ctx.EncKey, ctx.E.OE)

	return nil
}

func validateOwnerPasswordAES256(ctx *Context) (ok bool, err error) {
	if len(ctx.OwnerPW) == 0 {
		return false, nil
	}

	opw, err := processInput(ctx.OwnerPW)
	if err != nil {
		return false, err
	}

	if len(opw) > 127 {
		opw = opw[:127]
	}

	// Algorithm 3.2a 3.
	b := append(opw, validationSalt(ctx.E.O)...)
	b = append(b, ctx.E.U...)
	s := sha256.Sum256(b)

	if !bytes.HasPrefix(ctx.E.O, s[:]) {
		return false, nil
	}

	if err := decryptOE(ctx, opw); err != nil {
		return false, err
	}

	return true, nil
}

func hashRev6(input, pw, U []byte) ([]byte, int, error) {
	// 7.6.4.3.4 Algorithm 2.B returns 32 bytes.

	mod3 := new(big.Int).SetUint64(3)

	k0 := sha256.Sum256(input)
	k := k0[:]

	var e []byte
	j := 0

	for ; j < 64 || e[len(e)-1] > byte(j-32); j++ {
		var k1 []byte
		bb := append(pw, k...)
		if len(U) > 0 {
			bb = append(bb, U...)
		}
		for i := 0; i < 64; i++ {
			k1 = append(k1, bb...)
		}

		cb, err := aes.NewCipher(k[:16])
		if err != nil {
			return nil, -1, err
		}

		iv := k[16:32]
		e = make([]byte, len(k1))
		mode := cipher.NewCBCEncrypter(cb, iv)
		mode.CryptBlocks(e, k1)

		num := new(big.Int).SetBytes(e[:16])
		r := (new(big.Int).Mod(num, mod3)).Uint64()

		switch r {
		case 0:
			k0 := sha256.Sum256(e)
			k = k0[:]
		case 1:
			k0 := sha512.Sum384(e)
			k = k0[:]
		case 2:
			k0 := sha512.Sum512(e)
			k = k0[:]
		}

	}

	return k[:32], j, nil
}

func validateOwnerPasswordAES256Rev6(ctx *Context) (ok bool, err error) {
	if len(ctx.OwnerPW) == 0 {
		return false, nil
	}

	// Process PW with SASLPrep profile (RFC 4013) of stringprep (RFC 3454).
	opw, err := processInput(ctx.OwnerPW)
	if err != nil {
		return false, err
	}

	if len(opw) > 127 {
		opw = opw[:127]
	}

	// Algorithm 12
	bb := append(opw, validationSalt(ctx.E.O)...)
	bb = append(bb, ctx.E.U...)
	s, _, err := hashRev6(bb, opw, ctx.E.U)
	if err != nil {
		return false, err
	}

	if !bytes.HasPrefix(ctx.E.O, s[:]) {
		return false, nil
	}

	bb = append(opw, keySalt(ctx.E.O)...)
	bb = append(bb, ctx.E.U...)
	key, _, err := hashRev6(bb, opw, ctx.E.U)
	if err != nil {
		return false, err
	}

	cb, err := aes.NewCipher(key[:])
	if err != nil {
		return false, err
	}

	iv := make([]byte, 16)
	ctx.EncKey = make([]byte, 32)

	mode := cipher.NewCBCDecrypter(cb, iv)
	mode.CryptBlocks(ctx.EncKey, ctx.E.OE)

	return true, nil
}

func validateUserPasswordAES256Rev6(ctx *Context) (bool, error) {
	if len(ctx.E.UE) != 32 {
		return false, errors.New("UE: invalid length")
	}

	upw, err := processInput(ctx.UserPW)
	if err != nil {
		return false, err
	}
	if len(upw) > 127 {
		upw = upw[:127]
	}

	// Validate U prefix
	bb := append([]byte{}, upw...)
	bb = append(bb, validationSalt(ctx.E.U)...)
	s, _, err := hashRev6(bb, upw, nil)
	if err != nil {
		return false, err
	}
	if !bytes.HasPrefix(ctx.E.U, s) {
		return false, nil
	}

	// Derive decryption key
	bb = append([]byte{}, upw...)
	bb = append(bb, keySalt(ctx.E.U)...)
	key, _, err := hashRev6(bb, upw, nil)
	if err != nil {
		return false, err
	}

	block, err := aes.NewCipher(key)
	if err != nil {
		return false, err
	}

	iv := make([]byte, 16)
	encKey := make([]byte, 32)
	cipher.NewCBCDecrypter(block, iv).CryptBlocks(encKey, ctx.E.UE)
	ctx.EncKey = encKey

	return true, nil
}

var padArr = []byte{
	0x28, 0xBF, 0x4E, 0x5E, 0x4E, 0x75, 0x8A, 0x41, 0x64, 0x00, 0x4E, 0x56, 0xFF, 0xFA, 0x01, 0x08,
	0x2E, 0x2E, 0x00, 0xB6, 0xD0, 0x68, 0x3E, 0x80, 0x2F, 0x0C, 0xA9, 0xFE, 0x64, 0x53, 0x69, 0x7A,
}

func key(ownerpw, userpw string, r, l int) (key []byte) {
	// 3a
	pw := []byte(ownerpw)
	if len(pw) == 0 {
		pw = []byte(userpw)
	}
	if len(pw) >= 32 {
		pw = pw[:32]
	} else {
		pw = append(pw, padArr[:32-len(pw)]...)
	}

	// 3b
	h := md5.New()
	h.Write(pw)
	key = h.Sum(nil)

	// 3c
	if r >= 3 {
		for i := 0; i < 50; i++ {
			h.Reset()
			h.Write(key)
			key = h.Sum(nil)
		}
	}

	// 3d
	if r >= 3 {
		key = key[:l/8]
	} else {
		key = key[:5]
	}

	return key
}

func decryptUE(ctx *Context, upw []byte) error {
	key := sha256.Sum256(append(upw, keySalt(ctx.E.U)...))

	cb, err := aes.NewCipher(key[:])
	if err != nil {
		return err
	}

	iv := make([]byte, 16)
	ctx.EncKey = make([]byte, 32)

	mode := cipher.NewCBCDecrypter(cb, iv)
	mode.CryptBlocks(ctx.EncKey, ctx.E.UE)

	return nil
}

func validateUserPasswordAES256(ctx *Context) (ok bool, err error) {
	upw, err := processInput(ctx.UserPW)
	if err != nil {
		return false, err
	}

	if len(upw) > 127 {
		upw = upw[:127]
	}

	// Algorithm 3.2a 4,
	s := sha256.Sum256(append(upw, validationSalt(ctx.E.U)...))

	if !bytes.HasPrefix(ctx.E.U, s[:]) {
		return false, nil
	}

	if err := decryptUE(ctx, upw); err != nil {
		return false, err
	}

	return true, nil
}

func encKey(userpw string, e *Enc) (key []byte) {
	// 2a
	pw := []byte(userpw)
	if len(pw) >= 32 {
		pw = pw[:32]
	} else {
		pw = append(pw, padArr[:32-len(pw)]...)
	}

	// 2b
	h := md5.New()
	h.Write(pw)

	// 2c
	h.Write(e.O)

	// 2d
	q := uint32(e.P)
	h.Write([]byte{byte(q), byte(q >> 8), byte(q >> 16), byte(q >> 24)})

	// 2e
	h.Write(e.ID)

	// 2f
	if e.R == 4 && !e.Emd {
		h.Write([]byte{0xff, 0xff, 0xff, 0xff})
	}

	// 2g
	key = h.Sum(nil)

	// 2h
	if e.R >= 3 {
		for i := 0; i < 50; i++ {
			h.Reset()
			h.Write(key[:e.L/8])
			key = h.Sum(nil)
		}
	}

	// 2i
	if e.R >= 3 {
		key = key[:e.L/8]
	} else {
		key = key[:5]
	}

	return key
}

var nullPad32 = make([]byte, 32)

// U calculates the user password digest.
func u(ctx *Context) (u []byte, key []byte, err error) {
	// The PW string is generated from OS codepage characters by first converting the string to PDFDocEncoding.
	// If input is Unicode, first convert to a codepage encoding , and then to PDFDocEncoding for backward compatibility.
	userpw := ctx.UserPW
	// fmt.Printf("U userpw=ctx.UserPW=%s\n", userpw)

	e := ctx.E

	key = encKey(userpw, e)

	c, err := rc4.NewCipher(key)
	if err != nil {
		return nil, nil, err
	}

	switch e.R {

	case 2:
		// 4b
		u = make([]byte, 32)
		copy(u, padArr)
		c.XORKeyStream(u, u)

	case 3, 4:
		// 5b
		h := md5.New()
		h.Reset()
		h.Write(padArr)

		// 5c
		h.Write(e.ID)
		u = h.Sum(nil)

		// 5ds
		c.XORKeyStream(u, u)

		// 5e
		for i := 1; i <= 19; i++ {
			keynew := make([]byte, len(key))
			copy(keynew, key)

			for j := range keynew {
				keynew[j] ^= byte(i)
			}

			c, err = rc4.NewCipher(keynew)
			if err != nil {
				return nil, nil, err
			}
			c.XORKeyStream(u, u)
		}
	}

	if len(u) < 32 {
		u = append(u, nullPad32[:32-len(u)]...)
	}

	return u, key, nil
}

// validateUserPassword validates the user password aka document open password.
func validateUserPassword(ctx *Context) (ok bool, err error) {
	if ctx.E.R == 5 {
		return validateUserPasswordAES256(ctx)
	}

	if ctx.E.R == 6 {
		return validateUserPasswordAES256Rev6(ctx)
	}

	// Alg.4/5 p63
	// 4a/5a create encryption key using Alg.2 p61

	u, key, err := u(ctx)
	if err != nil {
		return false, err
	}

	ctx.EncKey = key

	switch ctx.E.R {

	case 2:
		ok = bytes.Equal(ctx.E.U, u)

	case 3, 4:
		ok = bytes.HasPrefix(ctx.E.U, u[:16])
	}

	return ok, nil
}

func needsOwnerAndUserPassword(cmd CommandMode) bool {
	return cmd == CHANGEOPW || cmd == CHANGEUPW || cmd == SETPERMISSIONS
}

// ValidateOwnerPassword validates the owner password aka change permissions password.
func validateOwnerPassword(ctx *Context) (ok bool, err error) {
	e := ctx.E

	if e.R == 5 {
		return validateOwnerPasswordAES256(ctx)
	}

	if e.R == 6 {
		return validateOwnerPasswordAES256Rev6(ctx)
	}

	ownerpw := ctx.OwnerPW
	userpw := ctx.UserPW

	// 7a: Alg.3 p62 a-d
	key := key(ownerpw, userpw, e.R, e.L)

	// 7b
	upw := make([]byte, len(e.O))
	copy(upw, e.O)

	var c *rc4.Cipher

	switch e.R {

	case 2:
		c, err = rc4.NewCipher(key)
		if err != nil {
			return
		}
		c.XORKeyStream(upw, upw)

	case 3, 4:
		for i := 19; i >= 0; i-- {

			keynew := make([]byte, len(key))
			copy(keynew, key)

			for j := range keynew {
				keynew[j] ^= byte(i)
			}

			c, err = rc4.NewCipher(keynew)
			if err != nil {
				return false, err
			}

			c.XORKeyStream(upw, upw)
		}
	}

	// Save user pw
	upws := ctx.UserPW

	ctx.UserPW = string(upw)
	ok, err = validateUserPassword(ctx)

	// Restore user pw
	ctx.UserPW = upws

	return ok, err
}

func perms(p int) (list []string) {
	list = append(list, fmt.Sprintf("permission bits: %012b (x%03X)", uint32(p)&0x0F3C, uint32(p)&0x0F3C))
	list = append(list, fmt.Sprintf("Bit  3: %t (print(rev2), print quality(rev>=3))", p&0x0004 > 0))
	list = append(list, fmt.Sprintf("Bit  4: %t (modify other than controlled by bits 6,9,11)", p&0x0008 > 0))
	list = append(list, fmt.Sprintf("Bit  5: %t (extract(rev2), extract other than controlled by bit 10(rev>=3))", p&0x0010 > 0))
	list = append(list, fmt.Sprintf("Bit  6: %t (add or modify annotations)", p&0x0020 > 0))
	list = append(list, fmt.Sprintf("Bit  9: %t (fill in form fields(rev>=3)", p&0x0100 > 0))
	list = append(list, fmt.Sprintf("Bit 10: %t (extract(rev>=3))", p&0x0200 > 0))
	list = append(list, fmt.Sprintf("Bit 11: %t (modify(rev>=3))", p&0x0400 > 0))
	list = append(list, fmt.Sprintf("Bit 12: %t (print high-level(rev>=3))", p&0x0800 > 0))
	return list
}

// PermissionsList returns a list of set permissions.
func PermissionsList(p int) (list []string) {
	if p == 0 {
		return append(list, "Full access")
	}

	return perms(p)
}

// Permissions returns a list of set permissions.
func Permissions(ctx *Context) (list []string) {
	p := 0
	if ctx.E != nil {
		p = ctx.E.P
	}

	return PermissionsList(p)
}

func writePermissions(ctx *Context, d Dict) error {
	// Algorithm 3.10

	if ctx.E.R != 5 && ctx.E.R != 6 {
		return nil
	}

	b := make([]byte, 16)
	binary.LittleEndian.PutUint64(b, uint64(ctx.E.P))

	b[4] = 0xFF
	b[5] = 0xFF
	b[6] = 0xFF
	b[7] = 0xFF

	var c byte = 'F'
	if ctx.E.Emd {
		c = 'T'
	}
	b[8] = c

	b[9] = 'a'
	b[10] = 'd'
	b[11] = 'b'

	cb, err := aes.NewCipher(ctx.EncKey[:])
	if err != nil {
		return err
	}

	cb.Encrypt(ctx.E.Perms, b)
	d.Update("Perms", HexLiteral(hex.EncodeToString(ctx.E.Perms)))

	return nil
}

// Needed permission bits for pdfcpu commands.
var perm = map[CommandMode]struct{ extract, modify int }{
	VALIDATE:                {0, 0},
	LISTINFO:                {0, 0},
	OPTIMIZE:                {0, 0},
	SPLIT:                   {1, 0},
	SPLITBYPAGENR:           {1, 0},
	MERGECREATE:             {0, 0},
	MERGECREATEZIP:          {0, 0},
	MERGEAPPEND:             {0, 0},
	EXTRACTIMAGES:           {1, 0},
	EXTRACTFONTS:            {1, 0},
	EXTRACTPAGES:            {1, 0},
	EXTRACTCONTENT:          {1, 0},
	EXTRACTMETADATA:         {1, 0},
	TRIM:                    {0, 1},
	LISTATTACHMENTS:         {0, 0},
	EXTRACTATTACHMENTS:      {1, 0},
	ADDATTACHMENTS:          {0, 1},
	ADDATTACHMENTSPORTFOLIO: {0, 1},
	REMOVEATTACHMENTS:       {0, 1},
	LISTPERMISSIONS:         {0, 0},
	SETPERMISSIONS:          {0, 0},
	ADDWATERMARKS:           {0, 1},
	REMOVEWATERMARKS:        {0, 1},
	IMPORTIMAGES:            {0, 1},
	INSERTPAGESBEFORE:       {0, 1},
	INSERTPAGESAFTER:        {0, 1},
	REMOVEPAGES:             {0, 1},
	LISTKEYWORDS:            {0, 0},
	ADDKEYWORDS:             {0, 1},
	REMOVEKEYWORDS:          {0, 1},
	LISTPROPERTIES:          {0, 0},
	ADDPROPERTIES:           {0, 1},
	REMOVEPROPERTIES:        {0, 1},
	COLLECT:                 {1, 0},
	CROP:                    {0, 1},
	LISTBOXES:               {0, 0},
	ADDBOXES:                {0, 1},
	REMOVEBOXES:             {0, 1},
	LISTANNOTATIONS:         {0, 1},
	ADDANNOTATIONS:          {0, 1},
	REMOVEANNOTATIONS:       {0, 1},
	ROTATE:                  {0, 1},
	NUP:                     {0, 1},
	BOOKLET:                 {0, 1},
	LISTBOOKMARKS:           {0, 0},
	ADDBOOKMARKS:            {0, 1},
	REMOVEBOOKMARKS:         {0, 1},
	IMPORTBOOKMARKS:         {0, 1},
	EXPORTBOOKMARKS:         {0, 1},
	LISTIMAGES:              {0, 1},
	UPDATEIMAGES:            {0, 1},
	CREATE:                  {0, 0},
	DUMP:                    {0, 1},
	LISTFORMFIELDS:          {0, 0},
	REMOVEFORMFIELDS:        {0, 1},
	LOCKFORMFIELDS:          {0, 1},
	UNLOCKFORMFIELDS:        {0, 1},
	RESETFORMFIELDS:         {0, 1},
	EXPORTFORMFIELDS:        {0, 1},
	FILLFORMFIELDS:          {0, 1},
	LISTPAGELAYOUT:          {0, 1},
	SETPAGELAYOUT:           {0, 1},
	RESETPAGELAYOUT:         {0, 1},
	LISTPAGEMODE:            {0, 1},
	SETPAGEMODE:             {0, 1},
	RESETPAGEMODE:           {0, 1},
	LISTVIEWERPREFERENCES:   {0, 1},
	SETVIEWERPREFERENCES:    {0, 1},
	RESETVIEWERPREFERENCES:  {0, 1},
	ZOOM:                    {0, 1},
}

func maskExtract(mode CommandMode, secHandlerRev int) int {
	p, ok := perm[mode]

	// no permissions defined or don't need extract permission
	if !ok || p.extract == 0 {
		return 0
	}

	// need extract permission

	if secHandlerRev >= 3 {
		return 0x0200 // need bit 10
	}

	return 0x0010 // need bit 5
}

func maskModify(mode CommandMode, secHandlerRev int) int {
	p, ok := perm[mode]

	// no permissions defined or don't need modify permission
	if !ok || p.modify == 0 {
		return 0
	}

	// need modify permission

	if secHandlerRev >= 3 {
		return 0x0400 // need bit 11
	}

	return 0x0008 // need bit 4
}

// HasNeededPermissions returns true if permissions for pdfcpu processing are present.
func hasNeededPermissions(mode CommandMode, enc *Enc) bool {
	// see 7.6.3.2

	m := maskExtract(mode, enc.R)
	if m > 0 {
		if enc.P&m == 0 {
			return false
		}
	}

	m = maskModify(mode, enc.R)
	if m > 0 {
		if enc.P&m == 0 {
			return false
		}
	}

	return true
}

func handlePermissions(ctx *Context) error {
	// AES256 Validate permissions
	ok, err := validatePermissions(ctx)
	if err != nil {
		return err
	}

	if !ok {
		return errors.New("pdfcpu: invalid permissions after upw ok")
	}

	if ctx.OwnerPW == "" && ctx.UserPW == "" {
		return nil
	}

	// Double check minimum permissions for pdfcpu processing.
	if !hasNeededPermissions(ctx.Cmd, ctx.E) {
		return errors.New("pdfcpu: operation restricted via pdfcpu's permission bits setting")
	}

	return nil
}

func setupEncryptionKey(ctx *Context, d Dict) (err error) {
	if ctx.E, err = supportedEncryption(ctx, d); err != nil {
		return err
	}

	if ctx.E.ID, err = ctx.IDFirstElement(); err != nil {
		return err
	}

	var ok bool

	// fmt.Printf("opw: <%s> upw: <%s> \n", ctx.OwnerPW, ctx.UserPW)

	// Validate the owner password aka. permissions/master password.
	if ok, err = validateOwnerPassword(ctx); err != nil {
		return err
	}

	// If the owner password does not match we generally move on if the user password is correct
	// unless we need to insist on a correct owner password due to the specific command in progress.
	if !ok && needsOwnerAndUserPassword(ctx.Cmd) {
		return errors.New("pdfcpu: please provide the owner password with -opw")
	}

	// Generally the owner password, which is also regarded as the master password or set permissions password
	// is sufficient for moving on. A password change is an exception since it requires both current passwords.
	if ok && !needsOwnerAndUserPassword(ctx.Cmd) {
		// AES256 Validate permissions
		if ok, err = validatePermissions(ctx); err != nil {
			return err
		}
		if !ok {
			return errors.New("pdfcpu: invalid permissions after opw ok")
		}
		return nil
	}

	// Validate the user password aka. document open password.
	if ok, err = validateUserPassword(ctx); err != nil {
		return err
	}
	if !ok {
		return ErrWrongPassword
	}

	// fmt.Printf("upw ok: %t\n", ok)

	return handlePermissions(ctx)
}

func checkForEncryption(c ContextContext, ctx *Context) error {
	indRef := ctx.Encrypt
	if indRef == nil {
		// This file is not encrypted.
		return handleUnencryptedFile(ctx)
	}

	// This file is encrypted.
	// if log.ReadEnabled() {
	// 	log.Read.Printf("Encryption: %v\n", indRef)
	// }

	if ctx.Cmd == ENCRYPT {
		// We want to encrypt this file.
		return errors.New("pdfcpu: this file is already encrypted")
	}

	if ctx.Cmd == VALIDATESIGNATURE || ctx.Cmd == ADDSIGNATURE {
		return errors.New("pdfcpu: this file is encrypted")
	}

	// Dereference encryptDict.
	d, err := dereferencedDict(c, ctx, indRef.ObjectNumber.Value())
	if err != nil {
		return err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("%s\n", d)
	// }

	// We need to decrypt this file in order to read it.
	return setupEncryptionKey(ctx, d)
}

// Parse compressed object.
func compressedObject(c ContextContext, s string) (Object, error) {
	// if log.ReadEnabled() {
	// 	log.Read.Println("compressedObject: begin")
	// }

	o, err := ParseObjectContext(c, &s)
	if err != nil {
		return nil, err
	}

	d, ok := o.(Dict)
	if !ok {
		// return trivial Object: Integer, Array, etc.
		// if log.ReadEnabled() {
		// 	log.Read.Println("compressedObject: end, any other than dict")
		// }
		return o, nil
	}

	streamLength, streamLengthRef := d.Length()
	if streamLength == nil && streamLengthRef == nil {
		// return Dict
		// if log.ReadEnabled() {
		// 	log.Read.Println("compressedObject: end, dict")
		// }
		return d, nil
	}

	return nil, errors.New("pdfcpu: compressedObject: stream objects are not to be stored in an object stream")
}

// Parse all objects of an object stream and save them into objectStreamDict.ObjArray.
func parseObjectStream(c ContextContext, osd *ObjectStreamDictType) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("parseObjectStream begin: decoding %d objects.\n", osd.ObjCount)
	// }

	decodedContent := osd.Content
	if decodedContent == nil {
		// The actual content will be decoded lazily, only decode the prolog here.
		var err error
		decodedContent, err = osd.DecodeLength(int64(osd.FirstObjOffset))
		if err != nil {
			return err
		}
	}
	prolog := decodedContent[:osd.FirstObjOffset]

	// The separator used in the prolog shall be white space
	// but some PDF writers use 0x00.
	prolog = bytes.ReplaceAll(prolog, []byte{0x00}, []byte{0x20})

	objs := strings.Fields(string(prolog))
	if len(objs)%2 > 0 {
		return errors.New("pdfcpu: parseObjectStream: corrupt object stream dict")
	}

	// e.g., 10 0 11 25 = 2 Objects: #10 @ offset 0, #11 @ offset 25

	var objArray Array

	var offsetOld int

	for i := 0; i < len(objs); i += 2 {

		if err := c.Err(); err != nil {
			return err
		}

		offset, err := strconv.Atoi(objs[i+1])
		if err != nil {
			return err
		}

		offset += osd.FirstObjOffset

		if i > 0 {
			o := NewLazyObjectStreamObject(osd, offsetOld, offset, compressedObject)
			objArray = append(objArray, o)
		}

		if i == len(objs)-2 {
			o := NewLazyObjectStreamObject(osd, offset, -1, compressedObject)
			objArray = append(objArray, o)
		}

		offsetOld = offset
	}

	osd.ObjArray = objArray

	// if log.ReadEnabled() {
	// 	log.Read.Println("parseObjectStream end")
	// }

	return nil
}

// ObjectStreamDict creates a ObjectStreamDictType out of a StreamDict.
func ObjectStreamDict(sd *StreamDict) (*ObjectStreamDictType, error) {
	if sd.First() == nil {
		return nil, errObjStreamMissingFirst
	}

	if sd.N() == nil {
		return nil, errObjStreamMissingN
	}

	osd := ObjectStreamDictType{
		StreamDict:     *sd,
		ObjCount:       *sd.N(),
		FirstObjOffset: *sd.First(),
		ObjArray:       nil,
	}

	return &osd, nil
}

func decodeObjectStreamObjects(c ContextContext, sd *StreamDict, objNr int) (*ObjectStreamDictType, error) {
	osd, err := ObjectStreamDict(sd)
	if err != nil {
		return nil, errors.Wrapf(err, "decodeObjectStreamObjects: problem dereferencing object stream %d", objNr)
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("decodeObjectStreamObjects: decoding object stream %d:\n", objNr)
	// }

	// Parse all objects of this object stream and save them to ObjectStreamDictType.ObjArray.
	if err = parseObjectStream(c, osd); err != nil {
		return nil, errors.Wrapf(err, "decodeObjectStreamObjects: problem decoding object stream %d\n", objNr)
	}

	if osd.ObjArray == nil {
		return nil, errors.Wrap(err, "decodeObjectStreamObjects: objArray should be set!")
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("decodeObjectStreamObjects: decoded object stream %d:\n", objNr)
	// }

	return osd, nil
}

func decodeObjectStream(c ContextContext, ctx *Context, objNr int) error {
	entry := ctx.Table[objNr]
	if entry == nil {
		return errors.Errorf("decodeObjectStream: missing entry for obj#%d\n", objNr)
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("decodeObjectStream: parsing object stream for obj#%d\n", objNr)
	// }

	// Parse object stream from file.
	o, err := ParseObjectWithContext(c, ctx, *entry.Offset, objNr, *entry.Generation)
	if err != nil || o == nil {
		return errors.New("pdfcpu: decodeObjectStream: corrupt object stream")
	}

	// Ensure StreamDict
	sd, ok := o.(StreamDict)
	if !ok {
		return errors.New("pdfcpu: decodeObjectStream: corrupt object stream")
	}

	// Load encoded stream content to xRefTable.
	if err = loadEncodedStreamContent(c, ctx, &sd, false); err != nil {
		return errors.Wrapf(err, "decodeObjectStream: problem dereferencing object stream %d", objNr)
	}

	// Will only decrypt, the actual stream content is decoded later lazily.
	if err = saveDecodedStreamContent(ctx, &sd, objNr, *entry.Generation, false); err != nil {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("obj %d: %s", objNr, err)
		// }
		return err
	}

	// Ensure decoded objectArray for object stream dicts.
	if !sd.IsObjStm() {
		return errors.New("pdfcpu: decodeObjectStreams: corrupt object stream")
	}

	// We have an object stream.
	// if log.ReadEnabled() {
	// 	log.Read.Printf("decodeObjectStreams: object stream #%d\n", objNr)
	// }

	ctx.Read.UsingObjectStreams = true

	osd, err := decodeObjectStreamObjects(c, &sd, objNr)
	if err != nil {
		return err
	}

	// Save object stream dict to xRefTableEntry.
	entry.Object = *osd

	return nil
}

// Decode all object streams so contained objects are ready to be used.
func decodeObjectStreams(c ContextContext, ctx *Context) error {
	// Note:
	// Entry "Extends" intentionally left out.
	// No object stream collection validation necessary.

	// if log.ReadEnabled() {
	// 	log.Read.Println("decodeObjectStreams: begin")
	// }

	// Get sorted slice of object numbers.
	var keys []int
	for k := range ctx.Read.ObjectStreams {
		keys = append(keys, k)
	}
	sort.Ints(keys)

	for _, objNr := range keys {

		if err := c.Err(); err != nil {
			return err
		}
		if err := decodeObjectStream(c, ctx, objNr); err != nil {
			return err
		}
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("decodeObjectStreams: end")
	// }

	return nil
}

func updateBinaryTotalSize(ctx *Context, o Object) {
	switch o := o.(type) {
	case StreamDict:
		ctx.Read.BinaryTotalSize += *o.StreamLength
	case ObjectStreamDictType:
		ctx.Read.BinaryTotalSize += *o.StreamLength
	case XRefStreamDict:
		ctx.Read.BinaryTotalSize += *o.StreamLength
	}
}

func handleLinearizationParmDict(ctx *Context, obj Object, objNr int) error {
	if ctx.Read.Linearized {
		// Linearization dict already processed.
		return nil
	}

	// handle linearization parm dict.
	if d, ok := obj.(Dict); ok && d.IsLinearizationParmDict() {

		ctx.Read.Linearized = true
		ctx.LinearizationObjs[objNr] = true
		// if log.ReadEnabled() {
		// 	log.Read.Printf("handleLinearizationParmDict: identified linearizationObj #%d\n", objNr)
		// }

		a := d.ArrayEntry("H")

		if a == nil {
			return errors.Errorf("handleLinearizationParmDict: corrupt linearization dict at obj:%d - missing array entry H", objNr)
		}

		if len(a) != 2 && len(a) != 4 {
			return errors.Errorf("handleLinearizationParmDict: corrupt linearization dict at obj:%d - corrupt array entry H, needs length 2 or 4", objNr)
		}

		offset, ok := a[0].(Integer)
		if !ok {
			return errors.Errorf("handleLinearizationParmDict: corrupt linearization dict at obj:%d - corrupt array entry H, needs Integer values", objNr)
		}

		offset64 := int64(offset.Value())
		ctx.OffsetPrimaryHintTable = &offset64

		if len(a) == 4 {

			offset, ok := a[2].(Integer)
			if !ok {
				return errors.Errorf("handleLinearizationParmDict: corrupt linearization dict at obj:%d - corrupt array entry H, needs Integer values", objNr)
			}

			offset64 := int64(offset.Value())
			ctx.OffsetOverflowHintTable = &offset64
		}
	}

	return nil
}

func dereferenceAndLoad(c ContextContext, ctx *Context, objNr int, entry *XRefTableEntry) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("dereferenceAndLoad: dereferencing object %d\n", objNr)
	// }

	// Parse object from ctx: anything goes dict, array, integer, float, streamdict...
	o, err := ParseObjectWithContext(c, ctx, *entry.Offset, objNr, *entry.Generation)
	if err != nil {
		return errors.Wrapf(err, "dereferenceAndLoad: problem dereferencing object %d", objNr)
	}
	if o == nil {
		return nil
	}

	entry.Object = o

	// Linearization dicts are validated and recorded for stats only.
	if err = handleLinearizationParmDict(ctx, o, objNr); err != nil {
		return err
	}

	// Handle stream dicts.

	if _, ok := o.(ObjectStreamDictType); ok {
		return errors.Errorf("dereferenceAndLoad: object stream should already be dereferenced at obj:%d", objNr)
	}

	if _, ok := o.(XRefStreamDict); ok {
		return errors.Errorf("dereferenceAndLoad: xref stream should already be dereferenced at obj:%d", objNr)
	}

	if sd, ok := o.(StreamDict); ok {
		if err = loadStreamDict(c, ctx, &sd, objNr, *entry.Generation, false); err != nil {
			return err
		}
		entry.Object = sd
	}

	// if log.ReadEnabled() {
	// 	log.Read.Printf("dereferenceAndLoad: end obj %d of %d\n<%s>\n", objNr, len(ctx.Table), entry.Object)
	// }

	return nil
}

func dereferenceObject(c ContextContext, ctx *Context, objNr int) error {
	// if log.ReadEnabled() {
	// 	log.Read.Printf("dereferenceObject: begin, dereferencing object %d\n", objNr)
	// }

	if objNr > ctx.MaxObjNr {
		ctx.MaxObjNr = objNr
	}

	entry := ctx.Table[objNr]

	if entry.Free {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("free object %d\n", objNr)
		// }
		return nil
	}

	if entry.Compressed {
		if err := decompressXRefTableEntry(ctx.XRefTable, objNr, entry); err != nil {
			return err
		}
		// log.Read.Printf("dereferenceObject: decompressed entry, Compressed=%v\n%s\n", entry.Compressed, entry.Object)
		return nil
	}

	// entry is in use.
	// if log.ReadEnabled() {
	// 	log.Read.Printf("in use object %d\n", objNr)
	// }

	if entry.Offset == nil || *entry.Offset == 0 {
		// if log.ReadEnabled() {
		// 	log.Read.Printf("dereferenceObject: already decompressed or used object w/o offset -> ignored")
		// }
		return nil
	}

	o := entry.Object

	if o != nil {
		// Already dereferenced.
		// logStream(entry.Object)
		updateBinaryTotalSize(ctx, o)
		// if log.ReadEnabled() {
		// 	log.Read.Printf("dereferenceObject: using cached object %d of %d\n<%s>\n", objNr, ctx.MaxObjNr+1, entry.Object)
		// }
		return nil
	}

	if err := dereferenceAndLoad(c, ctx, objNr, entry); err != nil {
		return err
	}

	// logStream(entry.Object)

	return nil
}

func dereferenceObjectsRaw(c ContextContext, ctx *Context) error {
	xRefTable := ctx.XRefTable
	for objNr := range xRefTable.Table {
		if err := c.Err(); err != nil {
			return err
		}
		if err := dereferenceObject(c, ctx, objNr); err != nil {
			return err
		}
	}

	for objNr := range xRefTable.Table {
		entry := xRefTable.Table[objNr]
		if entry.Free || entry.Compressed {
			continue
		}
		if err := c.Err(); err != nil {
			return err
		}
		ProcessRefCounts(xRefTable, entry.Object)
	}

	return nil
}

// Dereferences all objects including compressed objects from object streams.
func dereferenceObjects(c ContextContext, ctx *Context) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("dereferenceObjects: begin")
	// }

	// var err error

	// if log.StatsEnabled() {
	// 	err = dereferenceObjectsSorted(c, ctx)
	// } else {
	err := dereferenceObjectsRaw(c, ctx)
	// }
	if err != nil {
		return err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("dereferenceObjects: end")
	// }

	return nil
}

// Locate a possible Version entry (since V1.4) in the catalog
// and record this as rootVersion (as opposed to headerVersion).
func identifyRootVersion(xRefTable *XRefTable) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("identifyRootVersion: begin")
	// }

	// Try to get Version from Root.
	rootVersionStr, err := xRefTable.ParseRootVersion()
	if err != nil {
		return err
	}

	if rootVersionStr == nil {
		return nil
	}

	// Validate version and save corresponding constant to xRefTable.
	rootVersion, err := PDFVersion(*rootVersionStr)
	if err != nil {
		return errors.Wrapf(err, "identifyRootVersion: unknown PDF Root version: %s\n", *rootVersionStr)
	}

	xRefTable.RootVersion = &rootVersion

	// since V1.4 the header version may be overridden by a Version entry in the catalog.
	if *xRefTable.HeaderVersion < V14 {
		// if log.InfoEnabled() {
		// 	log.Info.Printf("identifyRootVersion: PDF version is %s - will ignore root version: %s\n", xRefTable.HeaderVersion, *rootVersionStr)
		// }
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("identifyRootVersion: end")
	// }

	return nil
}

// Parse all Objects including stream content from file and save to the corresponding xRefTableEntries.
// This includes processing of object streams and linearization dicts.
func dereferenceXRefTable(c ContextContext, ctx *Context) error {
	// if log.ReadEnabled() {
	// 	log.Read.Println("dereferenceXRefTable: begin")
	// }

	xRefTable := ctx.XRefTable

	// Note for encrypted files:
	// Mandatory provide userpw to open & display file.
	// Access may be restricted (Decode access privileges).
	// Optionally provide ownerpw in order to gain unrestricted access.
	if err := checkForEncryption(c, ctx); err != nil {
		return err
	}
	// fmt.Println("pw authenticated")

	// Prepare decompressed objects.
	if err := decodeObjectStreams(c, ctx); err != nil {
		return err
	}

	// For each xRefTableEntry assign a Object either by parsing from file or pointing to a decompressed object.
	if err := dereferenceObjects(c, ctx); err != nil {
		return err
	}

	// Identify an optional Version entry in the root object/catalog.
	if err := identifyRootVersion(xRefTable); err != nil {
		return err
	}

	// if log.ReadEnabled() {
	// 	log.Read.Println("dereferenceXRefTable: end")
	// }

	return nil
}

// Read takes a readSeeker and generates a PDF model context,
// an in-memory representation containing a cross reference table.
// If the passed Go context is cancelled, reading will be interrupted.
func ReadWithContext(c ContextContext, rs io.ReadSeeker, conf *Configuration) (*Context, error) {
	ctx, err := NewContext(rs, conf)
	if err != nil {
		return nil, err
	}

	if ctx.Read.FileSize == 0 {
		return nil, errors.New("The file could not be opened because it is empty.")
	}

	// Populate xRefTable.
	if err = readXRefTable(c, ctx); err != nil {
		return nil, errors.Wrap(err, "Read: xRefTable failed")
	}

	// Make all objects explicitly available (load into memory) in corresponding xRefTable entries.
	// Also decode any involved object streams.
	if err = dereferenceXRefTable(c, ctx); err != nil {
		return nil, err
	}

	// Some PDFWriters write an incorrect Size into trailer.
	if ctx.XRefTable.Size == nil || *ctx.XRefTable.Size != ctx.MaxObjNr+1 {
		maxObjNr := ctx.MaxObjNr + 1
		ctx.XRefTable.Size = &maxObjNr
	}

	return ctx, nil
}

func Read(rs io.ReadSeeker, conf *Configuration) (*Context, error) {
	return ReadWithContext(Background(), rs, conf)
}

// ReadContext uses an io.ReadSeeker to build an internal structure holding its cross reference table aka the ContextContext.
func ReadContext(rs io.ReadSeeker, conf *Configuration) (*Context, error) {
	if rs == nil {
		return nil, errors.New("pdfcpu: ReadContext: missing rs")
	}
	return Read(rs, conf)
}

func validateStreamDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(StreamDict) bool) (*StreamDict, error) {
	o, found, err := d.Entry(dictName, entryName, required)
	if err != nil {
		return nil, err
	}
	if o == nil {
		if !found {
			return nil, nil
		}
		if xRefTable.ValidationMode == ValidationStrict {
			return nil, errors.Errorf("pdfcpu: validateStreamDictEntry: dict=%s optional entry=%s is corrupt", dictName, entryName)
		}
		delete(d, entryName)
	}

	sd, valid, err := xRefTable.DereferenceStreamDict(o)
	if valid {
		return nil, nil
	}

	if err != nil {
		return nil, err
	}

	if sd == nil {
		if required {
			return nil, errors.Errorf("pdfcpu: validateStreamDictEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateStreamDictEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion(fmt.Sprintf("dict=%s entry=%s", dictName, entryName), sinceVersion); err != nil {
		return nil, err
	}

	// Validation
	if validate != nil && !validate(*sd) {
		return nil, errors.Errorf("pdfcpu: validateStreamDictEntry: dict=%s entry=%s invalid dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStreamDictEntry end: entry=%s\n", entryName)
	// }

	return sd, nil
}

func validatePermissions(ctx *Context) (bool, error) {
	// Algorithm 3.2a 5.

	if ctx.E.R != 5 && ctx.E.R != 6 {
		return true, nil
	}

	cb, err := aes.NewCipher(ctx.EncKey[:])
	if err != nil {
		return false, err
	}

	p := make([]byte, len(ctx.E.Perms))
	cb.Decrypt(p, ctx.E.Perms)
	if string(p[9:12]) != "adb" {
		return false, nil
	}

	b := binary.LittleEndian.Uint32(p[:4])
	return int32(b) == int32(ctx.E.P), nil
}

func validateNameEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(string) bool) (*NameType, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("pdfcpu: validateNameEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateNameEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	name, ok := o.(NameType)
	if !ok {
		return nil, errors.Errorf("pdfcpu: validateNameEntry: dict=%s entry=%s invalid type %T", dictName, entryName, o)
	}

	// Validation
	v := name.Value()
	if validate != nil && (required || len(v) > 0) && !validate(v) {
		return &name, errors.Errorf("pdfcpu: validateNameEntry: dict=%s entry=%s invalid dict entry: %s", dictName, entryName, v)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameEntry end: entry=%s\n", entryName)
	// }

	return &name, nil
}

const (

	// REQUIRED is used for required dict entries.
	REQUIRED = true

	// OPTIONAL is used for optional dict entries.
	OPTIONAL = false
)

func validateMetadataStream(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) (*StreamDict, error) {
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}

	sd, err := validateStreamDictEntry(xRefTable, d, "dict", "Metadata", required, sinceVersion, nil)
	if err != nil {
		return nil, err
	}
	if sd == nil {
		delete(d, "Metadata")
		return nil, nil
	}

	dictName := "metaDataDict"

	if _, err = validateNameEntry(xRefTable, sd.Dict, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Metadata" }); err != nil {
		return nil, err
	}

	if _, err = validateNameEntry(xRefTable, sd.Dict, dictName, "Subtype", OPTIONAL, sinceVersion, func(s string) bool { return s == "XML" }); err != nil {
		return nil, err
	}

	return sd, nil
}

func catalogMetaData(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) (*XMPMeta, error) {
	sd, err := validateMetadataStream(xRefTable, rootDict, required, sinceVersion)
	if err != nil || sd == nil {
		return nil, err
	}

	// if xRefTable.Version() < V20 {
	// 	return nil
	// }

	// Decode streamDict for supported filters only.
	err = sd.Decode()
	if err == ErrUnsupportedFilter {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}

	x := XMPMeta{}

	if err = xml.Unmarshal(sd.Content, &x); err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return nil, err
		}
		return nil, nil
	}

	return &x, nil
}

// EqualObjects returns true if two objects are equal in the context of given xrefTable.
// Some object and an indirect reference to it are treated as equal.
// Objects may in fact be object trees.
func EqualObjects(o1, o2 Object, xRefTable *XRefTable) (ok bool, err error) {
	// log.Debug.Printf("equalObjects: comparing %T with %T \n", o1, o2)

	ir1, ok := o1.(IndirectRef)
	if ok {
		ir2, ok := o2.(IndirectRef)
		if ok && ir1 == ir2 {
			return true, nil
		}
	}

	o1, err = xRefTable.Dereference(o1)
	if err != nil {
		return false, err
	}

	o2, err = xRefTable.Dereference(o2)
	if err != nil {
		return false, err
	}

	if o1 == nil {
		return o2 != nil, nil
	}

	o1Type := fmt.Sprintf("%T", o1)
	o2Type := fmt.Sprintf("%T", o2)
	// log.Debug.Printf("equalObjects: comparing dereferenced %s with %s \n", o1Type, o2Type)

	if o1Type != o2Type {
		return false, nil
	}

	switch o1.(type) {

	case NameType, StringLiteral, HexLiteral,
		Integer, Float, Boolean:
		ok = o1 == o2

	case Dict:
		ok, err = equalDicts(o1.(Dict), o2.(Dict), xRefTable)

	case StreamDict:
		sd1 := o1.(StreamDict)
		sd2 := o2.(StreamDict)
		ok, err = EqualStreamDicts(&sd1, &sd2, xRefTable)

	case Array:
		ok, err = equalArrays(o1.(Array), o2.(Array), xRefTable)

	default:
		err = errors.Errorf("equalObjects: unhandled compare for type %s\n", o1Type)
	}

	return ok, err
}

func equalArrays(a1, a2 Array, xRefTable *XRefTable) (bool, error) {
	if len(a1) != len(a2) {
		return false, nil
	}

	for i, o1 := range a1 {

		ok, err := EqualObjects(o1, a2[i], xRefTable)
		if err != nil {
			return false, err
		}

		if !ok {
			return false, nil
		}
	}

	return true, nil
}

// EqualStreamDicts returns true if two stream dicts are equal and contain the same bytes.
func EqualStreamDicts(sd1, sd2 *StreamDict, xRefTable *XRefTable) (bool, error) {
	ok, err := equalDicts(sd1.Dict, sd2.Dict, xRefTable)
	if err != nil {
		return false, err
	}

	if !ok {
		return false, nil
	}

	if sd1.Raw == nil || sd2 == nil {
		return false, errors.New("pdfcpu: EqualStreamDicts: stream dict not loaded")
	}

	return bytes.Equal(sd1.Raw, sd2.Raw), nil
}

func equalFontNames(v1, v2 Object, xRefTable *XRefTable) (bool, error) {
	v1, err := xRefTable.Dereference(v1)
	if err != nil {
		return false, err
	}
	bf1, ok := v1.(NameType)
	if !ok {
		return false, errors.Errorf("equalFontNames: type cast problem")
	}

	v2, err = xRefTable.Dereference(v2)
	if err != nil {
		return false, err
	}
	bf2, ok := v2.(NameType)
	if !ok {
		return false, errors.Errorf("equalFontNames: type cast problem")
	}

	// Ignore fontname prefix
	i := strings.Index(string(bf1), "+")
	if i > 0 {
		bf1 = bf1[i+1:]
	}

	i = strings.Index(string(bf2), "+")
	if i > 0 {
		bf2 = bf2[i+1:]
	}

	// log.Debug.Printf("equalFontNames: bf1=%s fb2=%s\n", bf1, bf2)

	return bf1 == bf2, nil
}

func equalDicts(d1, d2 Dict, xRefTable *XRefTable) (bool, error) {
	// log.Debug.Printf("equalDicts: %v\n%v\n", d1, d2)

	if d1.Len() != d2.Len() {
		return false, nil
	}

	t1, t2 := d1.Type(), d2.Type()
	fontDicts := (t1 != nil && *t1 == "Font") && (t2 != nil && *t2 == "Font")

	for key, v1 := range d1 {

		v2, found := d2[key]
		if !found {
			// log.Debug.Printf("equalDict: return false, key=%s\n", key)
			return false, nil
		}

		// Special treatment for font dicts
		if fontDicts && (key == "BaseFont" || key == "FontName" || key == "Name") {

			ok, err := equalFontNames(v1, v2, xRefTable)
			if err != nil {
				// log.Debug.Printf("equalDict: return2 false, key=%s v1=%v\nv2=%v\n", key, v1, v2)
				return false, err
			}

			if !ok {
				// log.Debug.Printf("equalDict: return3 false, key=%s v1=%v\nv2=%v\n", key, v1, v2)
				return false, nil
			}

			continue
		}

		ok, err := EqualObjects(v1, v2, xRefTable)
		if err != nil {
			// log.Debug.Printf("equalDict: return4 false, key=%s v1=%v\nv2=%v\n%v\n", key, v1, v2, err)
			return false, err
		}

		if !ok {
			// log.Debug.Printf("equalDict: return5 false, key=%s v1=%v\nv2=%v\n", key, v1, v2)
			return false, nil
		}

	}

	// log.Debug.Println("equalDict: return true")

	return true, nil
}

// EqualFontDicts returns true, if two font dicts are equal.
func EqualFontDicts(fd1, fd2 Dict, xRefTable *XRefTable) (bool, error) {
	// log.Debug.Printf("EqualFontDicts: %v\n%v\n", fd1, fd2)

	if fd1 == nil {
		return fd2 == nil, nil
	}

	if fd2 == nil {
		return false, nil
	}

	ok, err := equalDicts(fd1, fd2, xRefTable)
	if err != nil {
		return false, err
	}

	return ok, nil
}

func fixInfoDict(xRefTable *XRefTable, rootDict Dict) error {
	indRef := rootDict.IndirectRefEntry("Metadata")
	ok, err := EqualObjects(*indRef, *xRefTable.Info, xRefTable)
	if err != nil {
		return err
	}
	if ok {
		// infoDict indRef falsely points to meta data.
		xRefTable.Info = nil
	}
	return nil
}

func timeOfDateObject(xRefTable *XRefTable, o Object, sinceVersion Version) (*time.Time, error) {
	s, err := xRefTable.DereferenceStringOrHexLiteral(o, sinceVersion, nil)
	if err != nil {
		return nil, err
	}

	if s == "" {
		return nil, nil
	}

	t, ok := DateTime(s, xRefTable.ValidationMode == ValidationRelaxed)
	if !ok {
		return nil, errors.Errorf("pdfcpu: validateDateObject: <%s> invalid date", s)
	}

	return &t, nil
}

func metaDataModifiedAfterInfoDict(xRefTable *XRefTable) (bool, error) {
	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return false, err
	}

	xmpMeta, err := catalogMetaData(xRefTable, rootDict, OPTIONAL, V14)
	if err != nil {
		return false, err
	}

	if xmpMeta != nil {
		xRefTable.CatalogXMPMeta = xmpMeta
		if xRefTable.Info != nil {
			if err := fixInfoDict(xRefTable, rootDict); err != nil {
				return false, err
			}
		}
	}

	if !(xmpMeta != nil && xRefTable.Info != nil) {
		return false, nil
	}

	d, err := xRefTable.DereferenceDict(*xRefTable.Info)
	if err != nil {
		return false, err
	}
	if d == nil {
		return true, nil
	}

	modDate, ok := d["ModDate"]
	if !ok {
		return true, nil
	}

	modTimestampInfoDict, err := timeOfDateObject(xRefTable, modDate, V10)
	if err != nil {
		return false, err
	}
	if modTimestampInfoDict == nil {
		return true, nil
	}

	modTimestampMetaData := time.Time(xmpMeta.RDF.Description.ModDate)
	if modTimestampMetaData.IsZero() {
		//  xmlns:xap='http://ns.adobe.com/xap/1.0/ ...xap:ModifyDate='2006-06-05T21:58:13-05:00'></rdf:Description>
		// fmt.Println("metadata modificationDate is zero -> older than infodict")
		return false, nil
	}

	// fmt.Printf("infoDict: %s metaData: %s\n", modTimestampInfoDict, modTimestampMetaData)

	if *modTimestampInfoDict == modTimestampMetaData {
		return false, nil
	}

	infoDictOlderThanMetaDict := (*modTimestampInfoDict).Before(modTimestampMetaData)

	return infoDictOlderThanMetaDict, nil
}

func validateKeywords(xRefTable *XRefTable, v Object) (err error) {
	xRefTable.Keywords, err = xRefTable.DereferenceStringOrHexLiteral(v, V11, nil)
	if err != nil {
		return err
	}

	ss := strings.FieldsFunc(xRefTable.Keywords, func(c rune) bool { return c == ',' || c == ';' || c == '\r' })
	for _, s := range ss {
		keyword := strings.TrimSpace(s)
		xRefTable.KeywordList[keyword] = true
	}

	return nil
}

func validateDateObject(xRefTable *XRefTable, o Object, sinceVersion Version) (string, error) {
	s, err := xRefTable.DereferenceStringOrHexLiteral(o, sinceVersion, nil)
	if err != nil {
		return "", err
	}

	if s == "" {
		return s, nil
	}

	t, ok := DateTime(s, xRefTable.ValidationMode == ValidationRelaxed)
	if !ok {
		return "", errors.Errorf("pdfcpu: validateDateObject: <%s> invalid date", s)
	}

	return DateString(t), nil
}

func validateInfoDictDate(xRefTable *XRefTable, name string, o Object) (string, error) {
	s, err := validateDateObject(xRefTable, o, V10)
	if err != nil && xRefTable.ValidationMode == ValidationRelaxed {
		err = nil
	}
	return s, err
}

func validateInfoDictTrapped(xRefTable *XRefTable, o Object) error {
	sinceVersion := V13

	validate := func(s string) bool { return MemberOf(s, []string{"True", "False", "Unknown"}) }

	if xRefTable.ValidationMode == ValidationRelaxed {
		validate = func(s string) bool {
			return MemberOf(s, []string{"True", "False", "Unknown", "true", "false", "unknown"})
		}
	}

	_, err := xRefTable.DereferenceName(o, sinceVersion, validate)
	if err == nil {
		return nil
	}

	if xRefTable.ValidationMode == ValidationRelaxed {
		_, err = xRefTable.DereferenceBoolean(o, sinceVersion)
	}

	return err
}

func handleProperties(xRefTable *XRefTable, key string, val Object) error {
	v, err := xRefTable.DereferenceStringOrHexLiteral(val, V10, nil)
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
		_, err = xRefTable.Dereference(val)
		return err
	}

	if v != "" {

		k, err := DecodeName(key)
		if err != nil {
			return err
		}

		xRefTable.Properties[k] = v
	}

	return nil
}

func validateDocInfoDictEntry(xRefTable *XRefTable, k string, v Object) (bool, error) {
	var (
		err        error
		hasModDate bool
	)

	switch k {

	// text string, opt, since V1.1
	case "Title":
		xRefTable.Title, err = xRefTable.DereferenceStringOrHexLiteral(v, V11, nil)

	// text string, optional
	case "Author":
		xRefTable.Author, err = xRefTable.DereferenceStringOrHexLiteral(v, V10, nil)

	// text string, optional, since V1.1
	case "Subject":
		xRefTable.Subject, err = xRefTable.DereferenceStringOrHexLiteral(v, V11, nil)

	// text string, optional, since V1.1
	case "Keywords":
		if err := validateKeywords(xRefTable, v); err != nil {
			return hasModDate, err
		}

	// text string, optional
	case "Creator":
		xRefTable.Creator, err = xRefTable.DereferenceStringOrHexLiteral(v, V10, nil)

	// text string, optional
	case "Producer":
		xRefTable.Producer, err = xRefTable.DereferenceStringOrHexLiteral(v, V10, nil)

	// date, optional
	case "CreationDate":
		xRefTable.CreationDate, err = validateInfoDictDate(xRefTable, "CreationDate", v)

	// date, required if PieceInfo is present in document catalog.
	case "ModDate":
		hasModDate = true
		xRefTable.ModDate, err = validateInfoDictDate(xRefTable, "ModDate", v)

	// name, optional, since V1.3
	case "Trapped":
		err = validateInfoDictTrapped(xRefTable, v)

	case "AAPL:Keywords":
		xRefTable.CustomExtensions = true

	// text string, optional
	default:
		err = handleProperties(xRefTable, k, v)
	}

	return hasModDate, err
}

func validateDocumentInfoDict(xRefTable *XRefTable, obj Object) (bool, error) {
	// Document info object is optional.
	d, err := xRefTable.DereferenceDict(obj)
	if err != nil {
		return false, err
	}
	if d == nil {
		xRefTable.Info = nil
		return false, nil
	}

	hasModDate := false

	for k, v := range d {

		hmd, err := validateDocInfoDictEntry(xRefTable, k, v)

		if err == ErrInvalidUTF16BE {
			// Fix for #264:
			err = nil
		}

		if err != nil {
			return false, err
		}

		if !hasModDate && hmd {
			hasModDate = true
		}
	}

	return hasModDate, nil
}

func validateDocumentInfoObject(xRefTable *XRefTable) error {
	// Document info object is optional.
	if xRefTable.Info == nil {
		return nil
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("*** validateDocumentInfoObject begin ***")
	// }

	hasModDate, err := validateDocumentInfoDict(xRefTable, *xRefTable.Info)
	if err != nil {
		if xRefTable.ValidationMode != ValidationRelaxed || !strings.Contains(err.Error(), "wrong type") {
			return err
		}
		xRefTable.Info = nil
		return nil
	}

	hasPieceInfo, err := xRefTable.CatalogHasPieceInfo()
	if err != nil {
		return err
	}

	if hasPieceInfo && !hasModDate {
		if xRefTable.ValidationMode == ValidationStrict {
			return errors.Errorf("validateDocumentInfoObject: missing required entry \"ModDate\"")
		}
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("*** validateDocumentInfoObject end ***")
	// }

	return nil
}

func validateRootVersion(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	_, err := validateNameEntry(xRefTable, rootDict, "rootDict", "Version", OPTIONAL, sinceVersion, nil)
	return err
}

func validateExtensions(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 7.12 Extensions Dictionary

	_, err := validateDictEntry(xRefTable, rootDict, "rootDict", "Extensions", required, sinceVersion, nil)

	// No validation due to lack of documentation.

	return err
}

func validateIntegerEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(int) bool) (*Integer, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntegerEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("pdfcpu: validateIntegerEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateIntegerEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	i, ok := o.(Integer)
	if !ok {
		return nil, errors.Errorf("pdfcpu: validateIntegerEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// Validation
	if validate != nil && !validate(i.Value()) {
		return nil, errors.Errorf("pdfcpu: validateIntegerEntry: dict=%s entry=%s invalid dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntegerEntry end: entry=%s\n", entryName)
	// }
	return &i, nil
}

func validatePageLabelDict(xRefTable *XRefTable, o Object) error {
	// see 12.4.2 Page Labels

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	dictName := "pageLabelDict"

	// Type, optional, name
	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "PageLabel" })
	if err != nil {
		return err
	}

	// Optional name entry S
	// The numbering style that shall be used for the numeric portion of each page label.
	validate := func(s string) bool { return MemberOf(s, []string{"D", "R", "r", "A", "a"}) }
	_, err = validateNameEntry(xRefTable, d, dictName, "S", OPTIONAL, V10, validate)
	if err != nil {
		return err
	}

	// Optional string entry P
	// Label prefix for page labels in this range.
	_, err = validateStringEntry(xRefTable, d, dictName, "P", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Optional integer entry St
	// The value of the numeric portion for the first page label in the range.
	_, err = validateIntegerEntry(xRefTable, d, dictName, "St", OPTIONAL, V10, func(i int) bool { return i >= 1 })

	return err
}

func validateIntegerArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntegerArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		if _, ok := o.(Integer); !ok {
			return nil, errors.Errorf("pdfcpu: validateIntegerArrayEntry: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntegerArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateNumberTreeDictLimitsEntry(xRefTable *XRefTable, d Dict, firstKey, lastKey int) error {
	a, err := validateIntegerArrayEntry(xRefTable, d, "numberTreeDict", "Limits", REQUIRED, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	fk, _ := a[0].(Integer)
	lk, _ := a[1].(Integer)

	if firstKey < fk.Value() || lastKey > lk.Value() {
		return errors.Errorf("pdfcpu: validateNumberTreeDictLimitsEntry: invalid leaf node: firstKey(%d vs. %d) lastKey(%d vs. %d)\n", firstKey, fk.Value(), lastKey, lk.Value())
	}

	return nil
}

func validateMarkedContentReferenceDict(xRefTable *XRefTable, d Dict) error {
	var err error

	// Pg: optional, indirect reference
	// Page object representing a page on which the graphics object in the marked-content sequence shall be rendered.
	if ir := d.IndirectRefEntry("Pg"); ir != nil {
		err = processStructElementDictPgEntry(xRefTable, *ir)
		if err != nil {
			return err
		}
	}

	// Stm: optional, indirect reference
	// The content stream containing the marked-content sequence.
	if ir := d.IndirectRefEntry("Stm"); ir != nil {
		_, err = xRefTable.Dereference(ir)
		if err != nil {
			return err
		}
	}

	// StmOwn: optional, indirect reference
	// The PDF object owning the stream identified by Stems annotation to which an appearance stream belongs.
	if ir := d.IndirectRefEntry("StmOwn"); ir != nil {
		_, err = xRefTable.Dereference(ir)
		if err != nil {
			return err
		}
	}

	// MCID: required, integer
	// The marked-content identifier of the marked-content sequence within its content stream.

	if d.IntEntry("MCID") == nil {
		err = errors.Errorf("pdfcpu: validateMarkedContentReferenceDict: missing entry \"MCID\".")
	}

	return err
}

func validateObjectReferenceDict(xRefTable *XRefTable, d Dict) error {
	// Pg: optional, indirect reference
	// Page object representing a page on which some or all of the content items designated by the K entry shall be rendered.
	if ir := d.IndirectRefEntry("Pg"); ir != nil {
		err := processStructElementDictPgEntry(xRefTable, *ir)
		if err != nil {
			return err
		}
	}

	// Obj: required, indirect reference
	ir := d.IndirectRefEntry("Obj")
	if xRefTable.ValidationMode == ValidationStrict && ir == nil {
		return errors.New("pdfcpu: validateObjectReferenceDict: missing required entry \"Obj\"")
	}

	if ir == nil {
		return nil
	}

	obj, err := xRefTable.Dereference(*ir)
	if err != nil {
		return err
	}

	if obj == nil {
		return errors.Errorf("pdfcpu: validateObjectReferenceDict: missing obj#%s", ir.ObjectNumber)
	}

	return nil
}

func validateStructElementKArrayElement(xRefTable *XRefTable, o Object) error {
	switch o := o.(type) {

	case Integer:
		return nil

	case Dict:

		dictType := o.Type()

		if dictType == nil || *dictType == "StructElem" {
			return validateStructElementDict(xRefTable, o)
		}

		if *dictType == "MCR" {
			return validateMarkedContentReferenceDict(xRefTable, o)
		}

		if *dictType == "OBJR" {
			return validateObjectReferenceDict(xRefTable, o)
		}

		return errors.Errorf("validateStructElementKArrayElement: invalid dictType %s (should be \"StructElem\" or \"OBJR\" or \"MCR\")\n", *dictType)

	}

	return errors.New("validateStructElementKArrayElement: unsupported PDF object")
}

func validateStructElementDictEntryKArray(xRefTable *XRefTable, a Array) error {
	for _, o := range a {

		// Avoid recursion.
		ir, ok := o.(IndirectRef)
		if ok {
			valid, err := xRefTable.IsValid(ir)
			if err != nil {
				return err
			}
			if valid {
				continue
			}
			if err := xRefTable.SetValid(ir); err != nil {
				return err
			}
		}

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return err
		}

		if o == nil {
			continue
		}

		if err := validateStructElementKArrayElement(xRefTable, o); err != nil {
			return err
		}

	}

	return nil
}

func validateStructElementDictEntryK(xRefTable *XRefTable, o Object) error {
	// K: optional, the children of this structure element
	//
	// struct element dict
	// marked content reference dict
	// object reference dict
	// marked content id int
	// array of all above

	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Integer:

	case Dict:
		dictType := o.Type()

		if dictType == nil || *dictType == "StructElem" {
			err = validateStructElementDict(xRefTable, o)
			if err != nil {
				return err
			}
			break
		}

		if *dictType == "MCR" {
			err = validateMarkedContentReferenceDict(xRefTable, o)
			if err != nil {
				return err
			}
			break
		}

		if *dictType == "OBJR" {
			err = validateObjectReferenceDict(xRefTable, o)
			if err != nil {
				return err
			}
			break
		}

		return errors.Errorf("pdfcpu: validateStructElementDictEntryK: invalid dictType %s (should be \"StructElem\" or \"OBJR\" or \"MCR\")\n", *dictType)

	case Array:

		err = validateStructElementDictEntryKArray(xRefTable, o)
		if err != nil {
			return err
		}

	default:
		return errors.New("pdfcpu: validateStructElementDictEntryK: unsupported PDF object")

	}

	return nil
}

func processStructElementDictPgEntry(xRefTable *XRefTable, ir IndirectRef) error {
	// is this object a known page object?

	o, err := xRefTable.Dereference(ir)
	if err != nil {
		return errors.Errorf("pdfcpu: processStructElementDictPgEntry: Pg obj:#%d gen:%d unknown\n", ir.ObjectNumber, ir.GenerationNumber)
	}

	// logInfoWriter.Printf("known object for Pg: %v %s\n", obj, obj)

	if xRefTable.ValidationMode == ValidationRelaxed && o == nil {
		return nil
	}

	pageDict, ok := o.(Dict)
	if !ok {
		return errors.Errorf("pdfcpu: processStructElementDictPgEntry: Pg object corrupt dict: %s\n", o)
	}

	if t := pageDict.Type(); t == nil || *t != "Page" {
		return errors.Errorf("pdfcpu: processStructElementDictPgEntry: Pg object no pageDict: %s\n", pageDict)
	}

	return nil
}

func validateStructElementDictEntryA(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Dict: // No further processing.

	case StreamDict: // No further processing.

	case Array:

		for _, o := range o {

			o, err := xRefTable.Dereference(o)
			if err != nil {
				return err
			}

			if o == nil {
				continue
			}

			switch o.(type) {

			case Integer:
				// Each array element may be followed by a revision number (int).sort

			case Dict:
				// No further processing.

			case StreamDict:
				// No further processing.

			default:
				return errors.Errorf("pdfcpu: validateStructElementDictEntryA: unsupported PDF object: %v\n.", o)
			}
		}

	default:
		return errors.Errorf("pdfcpu: validateStructElementDictEntryA: unsupported PDF object: %v\n.", o)

	}

	return nil
}

func validateStructElementDictEntryC(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		// No further processing.

	case Array:

		for _, o := range o {

			o, err := xRefTable.Dereference(o)
			if err != nil {
				return err
			}

			if o == nil {
				continue
			}

			switch o.(type) {

			case NameType:
				// No further processing.

			case Integer:
				// Each array element may be followed by a revision number.

			default:
				return errors.New("pdfcpu: validateStructElementDictEntryC: unsupported PDF object")

			}
		}

	default:
		return errors.New("pdfcpu: validateStructElementDictEntryC: unsupported PDF object")

	}

	return nil
}

func processStructTreeClassMapDict(xRefTable *XRefTable, d Dict) error {
	for _, o := range d {

		// Process dict or array of dicts.

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return err
		}

		if o == nil {
			continue
		}

		switch o := o.(type) {

		case Dict:
			// no further processing.

		case Array:

			for _, o := range o {

				_, err = xRefTable.DereferenceDict(o)
				if err != nil {
					return err
				}

			}

		default:
			return errors.New("pdfcpu: processStructTreeClassMapDict: unsupported PDF object")

		}

	}

	return nil
}

func validateStructTreeRootDictEntryParentTree(xRefTable *XRefTable, ir *IndirectRef) error {
	if xRefTable.ValidationMode == ValidationRelaxed {

		// Accept empty dict
		d, err := xRefTable.DereferenceDict(*ir)
		if err != nil {
			return err
		}
		if d == nil || d.Len() == 0 {
			return nil
		}
	}

	d, err := xRefTable.DereferenceDict(*ir)
	if err != nil {
		return err
	}

	_, _, err = validateNumberTree(xRefTable, "StructTree", d, true)
	return err
}

func validateStructTreeRootDict(xRefTable *XRefTable, d Dict) error {
	dictName := "StructTreeRootDict"

	// required entry Type: name:StructTreeRoot
	if d.Type() == nil || *d.Type() != "StructTreeRoot" {
		return errors.New("pdfcpu: validateStructTreeRootDict: missing type")
	}

	// Optional entry K: struct element dict or array of struct element dicts
	if o, found := d.Find("K"); found {
		err := validateStructTreeRootDictEntryK(xRefTable, o)
		if err != nil {
			return err
		}
	}

	// Optional entry IDTree: name tree, key=elementId value=struct element dict
	// A name tree that maps element identifiers to the structure elements they denote.
	ir := d.IndirectRefEntry("IDTree")
	if ir != nil {
		d, err := xRefTable.DereferenceDict(*ir)
		if err != nil {
			return err
		}
		if len(d) > 0 {
			_, _, _, err = validateNameTree(xRefTable, "IDTree", d, true)
			if err != nil {
				return err
			}
		}
	}

	// Optional entry ParentTree: number tree, value=indRef of struct element dict or array of struct element dicts
	// A number tree used in finding the structure elements to which content items belong.
	if ir = d.IndirectRefEntry("ParentTree"); ir != nil {
		err := validateStructTreeRootDictEntryParentTree(xRefTable, ir)
		if err != nil {
			return err
		}
	}

	// Optional entry ParentTreeNextKey: integer
	_, err := validateIntegerEntry(xRefTable, d, dictName, "ParentTreeNextKey", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Optional entry RoleMap: dict
	// A dictionary that shall map the names of structure used in the document
	// to their approximate equivalents in the set of standard structure
	_, err = validateDictEntry(xRefTable, d, dictName, "RoleMap", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Optional entry ClassMap: dict
	// A dictionary that shall map name objects designating attribute classes
	// to the corresponding attribute objects or arrays of attribute objects.
	d1, err := validateDictEntry(xRefTable, d, dictName, "ClassMap", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = processStructTreeClassMapDict(xRefTable, d1)
	}

	return err
}

func validateStructTree(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// 14.7.2 Structure Hierarchy

	d, err := validateDictEntry(xRefTable, rootDict, "RootDict", "StructTreeRoot", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	return validateStructTreeRootDict(xRefTable, d)
}

func validateStructElementDictPart1(xRefTable *XRefTable, d Dict, dictName string) error {
	// S: structure type, required, name, see 14.7.3 and Annex E.
	_, err := validateNameEntry(xRefTable, d, dictName, "S", OPTIONAL, V10, nil)
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
		i, err := validateIntegerEntry(xRefTable, d, dictName, "S", OPTIONAL, V10, nil)
		if err != nil {
			return err
		}
		if i != nil {
			// "Repair"
			d["S"] = NameType(strconv.Itoa((*i).Value()))
		}
	}

	// P: immediate parent, required, indirect reference
	ir := d.IndirectRefEntry("P")
	if xRefTable.ValidationMode != ValidationRelaxed {
		if ir == nil {
			return errors.Errorf("pdfcpu: validateStructElementDict: missing entry P: %s\n", d)
		}

		// Check if parent structure element exists.
		if _, ok := xRefTable.FindTableEntryForIndRef(ir); !ok {
			return errors.Errorf("pdfcpu: validateStructElementDict: unknown parent: %v\n", ir)
		}
	}

	// ID: optional, byte string
	_, err = validateStringEntry(xRefTable, d, dictName, "ID", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Pg: optional, indirect reference
	// Page object representing a page on which some or all of the content items designated by the K entry shall be rendered.
	if ir := d.IndirectRefEntry("Pg"); ir != nil {
		err = processStructElementDictPgEntry(xRefTable, *ir)
		if err != nil {
			return err
		}
	}

	// K: optional, the children of this structure element.
	if o, found := d.Find("K"); found {
		err = validateStructElementDictEntryK(xRefTable, o)
		if err != nil {
			return err
		}
	}

	// A: optional, attribute objects: dict or stream dict or array of these.
	if o, ok := d.Find("A"); ok {
		err = validateStructElementDictEntryA(xRefTable, o)
	}

	return err
}

func validateStructElementDictPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// C: optional, name or array
	if o, ok := d.Find("C"); ok {
		err := validateStructElementDictEntryC(xRefTable, o)
		if err != nil {
			return err
		}
	}

	// R: optional, integer >= 0
	_, err := validateIntegerEntry(xRefTable, d, dictName, "R", OPTIONAL, V10, func(i int) bool { return i >= 0 })
	if err != nil {
		return err
	}

	// T: optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "T", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Lang: optional, text string, since 1.4
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateStringEntry(xRefTable, d, dictName, "Lang", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Alt: optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "Alt", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// E: optional, text string, since 1.5
	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	_, err = validateStringEntry(xRefTable, d, dictName, "E", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// ActualText: optional, text string, since 1.4
	sinceVersion = V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateStringEntry(xRefTable, d, dictName, "ActualText", OPTIONAL, sinceVersion, nil)

	return err
}

func validateStructElementDict(xRefTable *XRefTable, d Dict) error {
	// See table 323

	dictName := "StructElementDict"

	err := validateStructElementDictPart1(xRefTable, d, dictName)
	if err != nil {
		return err
	}

	return validateStructElementDictPart2(xRefTable, d, dictName)
}

func validateStructTreeRootDictEntryKArray(xRefTable *XRefTable, a Array) error {
	for _, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return err
		}

		if o == nil {
			continue
		}

		switch o := o.(type) {

		case Dict:

			dictType := o.Type()

			if dictType == nil || *dictType == "StructElem" {
				err = validateStructElementDict(xRefTable, o)
				if err != nil {
					return err
				}
				break
			}

			return errors.Errorf("pdfcpu: validateStructTreeRootDictEntryKArray: invalid dictType %s (should be \"StructElem\")\n", *dictType)

		default:
			return errors.New("pdfcpu: validateStructTreeRootDictEntryKArray: unsupported PDF object")

		}
	}

	return nil
}

func validateStructTreeRootDictEntryK(xRefTable *XRefTable, o Object) error {
	// The immediate child or children of the structure tree root in the structure hierarchy.
	// The value may be either a dictionary representing a single structure element or an array of such dictionaries.

	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Dict:

		dictType := o.Type()

		if dictType == nil || *dictType == "StructElem" {
			err = validateStructElementDict(xRefTable, o)
			if err != nil {
				return err
			}
			break
		}

		return errors.Errorf("validateStructTreeRootDictEntryK: invalid dictType %s (should be \"StructElem\")\n", *dictType)

	case Array:

		err = validateStructTreeRootDictEntryKArray(xRefTable, o)
		if err != nil {
			return err
		}

	default:
		return errors.New("pdfcpu: validateStructTreeRootDictEntryK: unsupported PDF object")

	}

	return nil
}

func validateNumberTreeDictNumsEntry(xRefTable *XRefTable, d Dict, name string) (firstKey, lastKey int, err error) {
	// Nums: array of the form [key1 value1 key2 value2 ... key n value n]
	o, found := d.Find("Nums")
	if !found {
		return 0, 0, errors.New("pdfcpu: validateNumberTreeDictNumsEntry: missing \"Kids\" or \"Nums\" entry")
	}

	a, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return 0, 0, err
	}
	if a == nil {
		return 0, 0, errors.New("pdfcpu: validateNumberTreeDictNumsEntry: missing \"Nums\" array")
	}

	// arr length needs to be even because of contained key value pairs.
	if len(a)%2 == 1 {
		return 0, 0, errors.Errorf("pdfcpu: validateNumberTreeDictNumsEntry: Nums array entry length needs to be even, length=%d\n", len(a))
	}

	// every other entry is a value
	// value = indRef to an array of indRefs of structElemDicts
	// or
	// value = indRef of structElementDict.

	for i, o := range a {

		if i%2 == 0 {

			o, err = xRefTable.Dereference(o)
			if err != nil {
				return 0, 0, err
			}

			i, ok := o.(Integer)
			if !ok {
				return 0, 0, errors.Errorf("pdfcpu: validateNumberTreeDictNumsEntry: corrupt key <%v>\n", o)
			}

			if firstKey == 0 {
				firstKey = i.Value()
			}

			lastKey = i.Value()

			continue
		}

		switch name {

		case "PageLabel":
			err = validatePageLabelDict(xRefTable, o)
			if err != nil {
				return 0, 0, err
			}

		case "StructTree":
			err = validateStructTreeRootDictEntryK(xRefTable, o)
			if err != nil {
				return 0, 0, err
			}
		}

	}

	return firstKey, lastKey, nil
}

func validateNumberTree(xRefTable *XRefTable, name string, d Dict, root bool) (firstKey, lastKey int, err error) {
	// A node has "Kids" or "Nums" entry.

	// Kids: array of indirect references to the immediate children of this node.
	// if Kids present then recurse
	if o, found := d.Find("Kids"); found {

		a, err := xRefTable.DereferenceArray(o)
		if err != nil {
			return 0, 0, err
		}
		if a == nil {
			return 0, 0, errors.New("pdfcpu: validateNumberTree: missing \"Kids\" array")
		}

		for _, o := range a {

			d1, err := xRefTable.DereferenceDict(o)
			if err != nil {
				return 0, 0, err
			}

			var fk int
			fk, lastKey, err = validateNumberTree(xRefTable, name, d1, false)
			if err != nil {
				return 0, 0, err
			}
			if firstKey == 0 {
				firstKey = fk
			}
		}

	} else {

		// Leaf node
		firstKey, lastKey, err = validateNumberTreeDictNumsEntry(xRefTable, d, name)
		if err != nil {
			return 0, 0, err
		}
	}

	if !root {

		// Verify calculated key range.
		err = validateNumberTreeDictLimitsEntry(xRefTable, d, firstKey, lastKey)
		if err != nil {
			return 0, 0, err
		}

	}

	return firstKey, lastKey, nil
}

func validatePageLabels(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// optional since PDF 1.3
	// => 7.9.7 Number Trees, 12.4.2 Page Labels

	// Dict or indirect ref to Dict

	ir := rootDict.IndirectRefEntry("PageLabels")
	if ir == nil {
		if required {
			return errors.Errorf("validatePageLabels: required entry \"PageLabels\" missing")
		}
		return nil
	}

	dictName := "PageLabels"

	// Version check
	err := xRefTable.ValidateVersion(dictName, sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(*ir)
	if err != nil {
		return err
	}

	_, _, err = validateNumberTree(xRefTable, "PageLabel", d, true)

	return err
}

func validateDestinationArrayFirstElement(xRefTable *XRefTable, a Array) (Object, error) {
	o, err := xRefTable.Dereference(a[0])
	if err != nil || o == nil {
		return nil, err
	}

	switch o := o.(type) {

	case Integer, NameType: // no further processing

	case Dict:
		if o.Type() == nil || (o.Type() != nil && (*o.Type() != "Page" && *o.Type() != "Pages")) {
			err = errors.Errorf("pdfcpu: validateDestinationArrayFirstElement: must be a pageDict indRef or an integer: %v (%T)", o, o)
		}

	default:
		err = errors.Errorf("pdfcpu: validateDestinationArrayFirstElement: must be a pageDict indRef or an integer: %v (%T)", o, o)
		if xRefTable.ValidationMode == ValidationRelaxed {
			err = nil
		}
	}

	return o, err
}

func validateDestinationArrayLength(a Array) bool {
	return len(a) >= 2 && len(a) <= 6
}

func validateDestType(a Array, destType NameType) error {
	switch destType {
	case "Fit":
	case "FitB":
		if len(a) > 2 {
			return errors.Errorf("pdfcpu: validateDestinationArray: %s - invalid length: %d", destType, len(a))
		}
	case "FitH":
	case "FitV":
	case "FitBH":
	case "FitBV":
		if len(a) > 3 {
			return errors.Errorf("pdfcpu: validateDestinationArray: %s - invalid length: %d", destType, len(a))
		}
	case "XYZ":
		if len(a) > 5 {
			return errors.Errorf("pdfcpu: validateDestinationArray: %s - invalid length: %d", destType, len(a))
		}
	case "FitR":
		if len(a) > 6 {
			return errors.Errorf("pdfcpu: validateDestinationArray: %s - invalid length: %d", destType, len(a))
		}
	default:
		return errors.Errorf("pdfcpu: validateDestinationArray     j- invalid mode: %s", destType)
	}

	return nil
}

func validateDestinationArray(xRefTable *XRefTable, a Array) error {
	if !validateDestinationArrayLength(a) {
		return errors.Errorf("pdfcpu: validateDestinationArray: invalid length: %d", len(a))
	}

	// Validate first element: indRef of page dict or pageNumber(int) of remote doc for remote Go-to Action or nil.
	o, err := validateDestinationArrayFirstElement(xRefTable, a)
	if err != nil || o == nil {
		return err
	}

	name, ok := a[1].(NameType)
	if !ok {
		return errors.Errorf("pdfcpu: validateDestinationArray: second element must be a name %v", a[1])
	}

	return validateDestType(a, name)
}

func validateDestinationDict(xRefTable *XRefTable, d Dict) error {
	// D, required, array
	a, err := validateArrayEntry(xRefTable, d, "DestinationDict", "D", REQUIRED, V10, nil)
	if err != nil || a == nil {
		return err
	}

	return validateDestinationArray(xRefTable, a)
}

func validateDestination(xRefTable *XRefTable, o Object, forAction bool) (string, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return "", err
	}

	switch o := o.(type) {

	case NameType:
		return o.Value(), nil

	case StringLiteral:
		return StringLiteralToString(o)

	case HexLiteral:
		return HexLiteralToString(o)

	case Dict:
		if forAction {
			return "", errors.New("pdfcpu: validateDestination: unsupported PDF object")
		}
		err = validateDestinationDict(xRefTable, o)

	case Array:
		err = validateDestinationArray(xRefTable, o)

	default:
		err = errors.New("pdfcpu: validateDestination: unsupported PDF object")

	}

	return "", err
}

func validateEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) (Object, error) {
	o, found := d.Find(entryName)
	if !found || o == nil {
		if required {
			return nil, errors.Errorf("dict=%s required entry=%s missing (obj#%d).", dictName, entryName, xRefTable.CurObj)
		}
		return nil, nil
	}

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("dict=%s required entry=%s missing (obj#%d).", dictName, entryName, xRefTable.CurObj)
		}
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion(fmt.Sprintf("dict=%s entry=%s (obj#%d)", dictName, entryName, xRefTable.CurObj), sinceVersion); err != nil {
		return nil, err
	}

	return o, nil
}

func validateActionDestinationEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	// see 12.3.2

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil {
		return err
	}

	name, err := validateDestination(xRefTable, o, true)
	if err != nil {
		return err
	}

	if len(name) > 0 && xRefTable.IsMerging() {
		nm := xRefTable.NameRef("Dests")
		nm.Add(name, d)
	}

	return nil
}

func validateDestsNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// Version check
	err := xRefTable.ValidateVersion("DestsNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	_, err = validateDestination(xRefTable, o, false)
	return err
}

const (

	// ExcludePatternCS ...
	ExcludePatternCS = true

	// IncludePatternCS ...
	IncludePatternCS = false

	isAlternateImageStreamDict   = true
	isNoAlternateImageStreamDict = false
)

func validateReferenceDictPageEntry(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o.(type) {

	case Integer, StringLiteral, HexLiteral:
		// no further processing

	default:
		return errors.New("pdfcpu: validateReferenceDictPageEntry: corrupt type")

	}

	return nil
}

// See 7.11.4

func validateFileSpecString(s string) bool {
	// see 7.11.2
	// The standard format for representing a simple file specification in string form divides the string into component substrings
	// separated by the SOLIDUS character (2Fh) (/). The SOLIDUS is a generic component separator that shall be mapped to the appropriate
	// platform-specific separator when generating a platform-dependent file name. Any of the components may be empty.
	// If a component contains one or more literal SOLIDI, each shall be preceded by a REVERSE SOLIDUS (5Ch) (\), which in turn shall be
	// preceded by another REVERSE SOLIDUS to indicate that it is part of the string and not an escape character.
	//
	// EXAMPLE ( in\\/out )
	// represents the file name in/out

	// I have not seen an instance of a single file spec string that actually complies with this definition and uses
	// the double reverse solidi in front of the solidus, because of that we simply
	return true
}

func validateURLString(s string) bool {
	// RFC1738 compliant URL, see 7.11.5

	_, err := url.ParseRequestURI(s)

	return err == nil
}

func validateEmbeddedFileStreamMacParameterDict(xRefTable *XRefTable, d Dict) error {
	dictName := "embeddedFileStreamMacParameterDict"

	// Subtype, optional integer
	// The embedded file's file type integer encoded according to Mac OS conventions.
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "Subtype", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// Creator, optional integer
	// The embedded file's creator signature integer encoded according to Mac OS conventions.
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "Creator", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// ResFork, optional stream dict
	// The binary contents of the embedded file's resource fork.
	if _, err := validateStreamDictEntry(xRefTable, d, dictName, "ResFork", OPTIONAL, V10, nil); err != nil {
		return err
	}

	return nil
}

func validateDateEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) (*time.Time, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateDateEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	s, err := xRefTable.DereferenceStringOrHexLiteral(o, sinceVersion, nil)
	if err != nil {
		return nil, err
	}

	if s == "" {
		if required {
			return nil, errors.Errorf("validateDateEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateDateEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	time, ok := DateTime(s, xRefTable.ValidationMode == ValidationRelaxed)
	if !ok {
		return nil, errors.Errorf("pdfcpu: validateDateEntry: <%s> invalid date", s)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateDateEntry end: entry=%s\n", entryName)
	// }

	return &time, nil
}

func validateEmbeddedFileStreamParameterDict(xRefTable *XRefTable, o Object) error {
	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	dictName := "embeddedFileStreamParmDict"

	// Size, optional integer
	if _, err = validateIntegerEntry(xRefTable, d, dictName, "Size", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// CreationDate, optional date
	if _, err = validateDateEntry(xRefTable, d, dictName, "CreationDate", OPTIONAL, V10); err != nil {
		return err
	}

	// ModDate, optional date
	if _, err = validateDateEntry(xRefTable, d, dictName, "ModDate", OPTIONAL, V10); err != nil {
		return err
	}

	// Mac, optional dict
	macDict, err := validateDictEntry(xRefTable, d, dictName, "Mac", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}
	if macDict != nil {
		if err = validateEmbeddedFileStreamMacParameterDict(xRefTable, macDict); err != nil {
			return err
		}
	}

	// CheckSum, optional string
	_, err = validateStringEntry(xRefTable, d, dictName, "CheckSum", OPTIONAL, V10, nil)

	return err
}

func validateEmbeddedFileStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	dictName := "embeddedFileStreamDict"

	// Type, optional, name
	if _, err := validateNameEntry(xRefTable, sd.Dict, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "EmbeddedFile" }); err != nil {
		return err
	}

	// Subtype, optional, name
	if _, err := validateNameEntry(xRefTable, sd.Dict, dictName, "Subtype", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// Params, optional, dict
	// parameter dict containing additional file-specific information.
	if o, found := sd.Dict.Find("Params"); found && o != nil {
		if err := validateEmbeddedFileStreamParameterDict(xRefTable, o); err != nil {
			return err
		}
	}

	return nil
}

func validateFileSpecDictEntriesEFAndRFKeys(k string) bool {
	return k == "F" || k == "UF" || k == "DOS" || k == "Mac" || k == "Unix" || k == "Subtype"
}

func validateStreamDict(xRefTable *XRefTable, o Object) (*StreamDict, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateStreamDict begin")
	// }

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		return nil, errors.New("pdfcpu: validateStreamDict: missing object")
	}

	sd, ok := o.(StreamDict)
	if !ok {
		return nil, errors.New("pdfcpu: validateStreamDict: invalid type")
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateStreamDict endobj")
	// }

	return &sd, nil
}

func validateFileSpecDictEntryEFDict(xRefTable *XRefTable, d Dict) error {
	for k, obj := range d {

		if !validateFileSpecDictEntriesEFAndRFKeys(k) {
			return errors.Errorf("validateFileSpecEntriesEFAndRF: invalid key: %s", k)
		}

		if k == "F" || k == "UF" {
			// value must be embedded file stream dict
			// see 7.11.4
			sd, err := validateStreamDict(xRefTable, obj)
			if err != nil {
				return err
			}
			if sd == nil {
				continue
			}

			if err = validateEmbeddedFileStreamDict(xRefTable, sd); err != nil {
				return err
			}
		}

	}

	return nil
}

func validateRFDictFilesArray(xRefTable *XRefTable, a Array) error {
	if len(a)%2 > 0 {
		return errors.New("pdfcpu: validateRFDictFilesArray: rfDict array corrupt")
	}

	for k, v := range a {

		if v == nil {
			return errors.New("pdfcpu: validateRFDictFilesArray: rfDict, array entry nil")
		}

		o, err := xRefTable.Dereference(v)
		if err != nil {
			return err
		}

		if o == nil {
			return errors.New("pdfcpu: validateRFDictFilesArray: rfDict, array entry nil")
		}

		if k%2 > 0 {

			_, ok := o.(StringLiteral)
			if !ok {
				return errors.New("pdfcpu: validateRFDictFilesArray: rfDict, array entry corrupt")
			}

		} else {

			// value must be embedded file stream dict
			// see 7.11.4
			sd, err := validateStreamDict(xRefTable, o)
			if err != nil {
				return err
			}

			if err = validateEmbeddedFileStreamDict(xRefTable, sd); err != nil {
				return err
			}

		}
	}

	return nil
}

func validateFileSpecDictEntriesEFAndRF(xRefTable *XRefTable, efDict, rfDict Dict) error {
	// EF only or EF and RF

	if efDict == nil {
		return errors.Errorf("pdfcpu: validateFileSpecEntriesEFAndRF: missing required efDict.")
	}

	if err := validateFileSpecDictEntryEFDict(xRefTable, efDict); err != nil {
		return err
	}

	for k, val := range rfDict {

		if _, ok := efDict.Find(k); !ok {
			return errors.Errorf("pdfcpu: validateFileSpecEntriesEFAndRF: rfDict entry=%s missing corresponding efDict entry\n", k)
		}

		// value must be related files array.
		// see 7.11.4.2
		a, err := xRefTable.DereferenceArray(val)
		if err != nil {
			return err
		}

		if a == nil {
			continue
		}

		if err = validateRFDictFilesArray(xRefTable, a); err != nil {
			return err
		}

	}

	return nil
}

func requiredF(dosFound, macFound, unixFound bool) bool {
	return !dosFound && !macFound && !unixFound
}

func validateFileSpecDictEFAndRF(xRefTable *XRefTable, d Dict, dictName string, hasEP bool) error {
	// RF, optional, dict of related files arrays, since V1.3
	rfDict, err := validateDictEntry(xRefTable, d, dictName, "RF", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// EF, required if RF present, dict of embedded file streams, since 1.3
	efDict, err := validateDictEntry(xRefTable, d, dictName, "EF", rfDict != nil, V13, nil)
	if err != nil {
		return err
	}

	// Type, required if EF, EP or RF present, name
	validate := func(s string) bool {
		return s == "Filespec" || (xRefTable.ValidationMode == ValidationRelaxed && s == "F")
	}
	required := rfDict != nil || efDict != nil || hasEP
	if _, err = validateNameEntry(xRefTable, d, dictName, "Type", required, V10, validate); err != nil {
		return err
	}

	if efDict != nil {
		err = validateFileSpecDictEntriesEFAndRF(xRefTable, efDict, rfDict)
	}

	return err
}

func validateFileSpecDictPart1(xRefTable *XRefTable, d Dict, dictName string) error {
	// FS, optional, name
	fsName, err := validateNameEntry(xRefTable, d, dictName, "FS", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// UF, optional, text string
	sinceVersion := V17
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	uf, err := validateStringEntry(xRefTable, d, dictName, "UF", OPTIONAL, sinceVersion, validateFileSpecString)
	if err != nil {
		return err
	}

	// DOS, byte string, optional, obsolescent.
	_, dosFound := d.Find("DOS")

	// Mac, byte string, optional, obsolescent.
	_, macFound := d.Find("Mac")

	// Unix, byte string, optional, obsolescent.
	_, unixFound := d.Find("Unix")

	// F, file spec string
	validate := validateFileSpecString
	if fsName != nil && fsName.Value() == "URL" {
		validate = validateURLString
	}

	required := requiredF(dosFound, macFound, unixFound)
	if xRefTable.ValidationMode == ValidationRelaxed && uf != nil {
		required = OPTIONAL
	}
	if _, err = validateStringEntry(xRefTable, d, dictName, "F", required, V10, validate); err != nil {
		return err
	}

	return nil
}

func validateStringArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStringArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		switch o.(type) {

		case StringLiteral:
			// no further processing.

		case HexLiteral:
			// no further processing

		default:
			return nil, errors.Errorf("pdfcpu: validateStringArrayEntry: invalid type at index %d\n", i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStringArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateFileSpecDictPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// ID, optional, array of strings
	if _, err := validateStringArrayEntry(xRefTable, d, dictName, "ID", OPTIONAL, V11, func(a Array) bool { return len(a) == 2 }); err != nil {
		return err
	}

	// V, optional, boolean, since V1.2
	if _, err := validateBooleanEntry(xRefTable, d, dictName, "V", OPTIONAL, V12, nil); err != nil {
		return err
	}

	// EP, optional, encrypted payload dict, since V2.0
	epDict, err := validateDictEntry(xRefTable, d, dictName, "EP", OPTIONAL, V20, nil)
	if err != nil {
		return err
	}
	if err = validateFileSpecDictEFAndRF(xRefTable, d, dictName, len(epDict) > 0); err != nil {
		return err
	}

	// Desc, optional, text string, since V1.6
	sinceVersion := V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V10
	}
	if _, err = validateStringEntry(xRefTable, d, dictName, "Desc", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// CI, optional, collection item dict, since V1.7
	if _, err = validateDictEntry(xRefTable, d, dictName, "CI", OPTIONAL, V17, nil); err != nil {
		return err
	}

	// Thumb, optional, thumbnail image, since V2.0
	sinceVersion = V20
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V17
	}
	if _, err := validateStreamDictEntry(xRefTable, d, dictName, "Thumb", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// AFRelationship, optional, associated file semantics, since V2.0
	validateAFRelationship := func(s string) bool {
		return MemberOf(s, []string{"Source", "Data", "Alternative", "Supplement", "EncryptedPayload", "FormData", "Schema", "Unspecified"})
	}
	sinceVersion = V20
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if _, err := validateNameEntry(xRefTable, d, dictName, "AFRelationship", OPTIONAL, sinceVersion, validateAFRelationship); err != nil {
		return err
	}

	return nil
}

func validateFileSpecDict(xRefTable *XRefTable, d Dict) error {
	// See 7.11.3

	dictName := "fileSpecDict"

	if err := validateFileSpecDictPart1(xRefTable, d, dictName); err != nil {
		return err
	}

	if err := validateFileSpecDictPart2(xRefTable, d, dictName); err != nil {
		return err
	}

	return nil
}

func validateFileSpecification(xRefTable *XRefTable, o Object) (Object, error) {
	// See 7.11

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	switch o := o.(type) {

	case StringLiteral, HexLiteral:
		s := o.(interface{ Value() string }).Value()
		if !validateFileSpecString(s) {
			return nil, errors.Errorf("pdfcpu: validateFileSpecification: invalid file spec string: %s", s)
		}

	case Dict:
		if err = validateFileSpecDict(xRefTable, o); err != nil {
			return nil, err
		}

	default:
		return nil, errors.Errorf("pdfcpu: validateFileSpecification: invalid type")

	}

	return o, nil
}

func validateURLSpecification(xRefTable *XRefTable, o Object) (Object, error) {
	// See 7.11.4

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return nil, err
	}

	if d == nil {
		return nil, errors.New("pdfcpu: validateURLSpecification: missing dict")
	}

	dictName := "urlSpec"

	// FS, required, name
	if _, err = validateNameEntry(xRefTable, d, dictName, "FS", REQUIRED, V10, func(s string) bool { return s == "URL" }); err != nil {
		return nil, err
	}

	// F, required, string, URL (Internet RFC 1738)
	_, err = validateStringEntry(xRefTable, d, dictName, "F", REQUIRED, V10, validateURLString)

	return o, err
}

func validateFileSpecEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) (Object, error) {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return nil, err
	}

	if err = xRefTable.ValidateVersion("fileSpec", sinceVersion); err != nil {
		return nil, err
	}

	return validateFileSpecification(xRefTable, o)
}

func validateURLSpecEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) (Object, error) {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return nil, err
	}

	if err = xRefTable.ValidateVersion("URLSpec", sinceVersion); err != nil {
		return nil, err
	}

	return validateURLSpecification(xRefTable, o)
}

func validateFileSpecificationOrFormObject(xRefTable *XRefTable, obj Object) error {
	sd, ok := obj.(StreamDict)
	if ok {
		return validateFormStreamDict(xRefTable, &sd)
	}

	_, err := validateFileSpecification(xRefTable, obj)

	return err
}

func validateReferenceDict(xRefTable *XRefTable, d Dict) error {
	// see 8.10.4 Reference XObjects

	dictName := "refDict"

	// F, file spec, required
	_, err := validateFileSpecEntry(xRefTable, d, dictName, "F", REQUIRED, V10)
	if err != nil {
		return err
	}

	// Page, integer or text string, required
	o, ok := d.Find("Page")
	if !ok {
		return errors.New("pdfcpu: validateReferenceDict: missing required entry \"Page\"")
	}

	err = validateReferenceDictPageEntry(xRefTable, o)
	if err != nil {
		return err
	}

	// ID, string array, optional
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "ID", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })

	return err
}

func validateNumber(xRefTable *XRefTable, o Object) (Object, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateNumber begin")
	// }

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		return nil, errors.New("pdfcpu: validateNumber: missing object")
	}

	switch o.(type) {

	case Integer:
		// no further processing.

	case Float:
		// no further processing.

	default:
		return nil, errors.New("pdfcpu: validateNumber: invalid type")

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateNumber end ")
	// }

	return o, nil
}

func validateNumberArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNumberArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		switch o.(type) {

		case Integer:
			// no further processing.

		case Float:
			// no further processing.

		default:
			return nil, errors.Errorf("pdfcpu: validateNumberArrayEntry: invalid type at index %d\n", i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNumberArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateNumberEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(f float64) bool) (Object, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNumberEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	if o, err = validateNumber(xRefTable, o); err != nil {
		return nil, err
	}

	var f float64

	// Validation
	switch o := o.(type) {

	case Integer:
		f = float64(o.Value())

	case Float:
		f = o.Value()
	}

	if validate != nil && !validate(f) {
		return nil, errors.Errorf("pdfcpu: validateFloatEntry: dict=%s entry=%s invalid dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNumberEntry end: entry=%s\n", entryName)
	// }

	return o, nil
}

func validateRectangleEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateRectangleEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateNumberArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, func(a Array) bool { return len(a) == 4 })
	if err != nil || a == nil {
		return nil, err
	}

	if validate != nil && !validate(a) {
		return nil, errors.Errorf("pdfcpu: validateRectangleEntry: dict=%s entry=%s invalid rectangle entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateRectangleEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateOPIDictV13Part1(xRefTable *XRefTable, d Dict, dictName string) error {
	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "OPI" })
	if err != nil {
		return err
	}

	// Version, required, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "Version", REQUIRED, V10, func(f float64) bool { return f == 1.3 })
	if err != nil {
		return err
	}

	// F, required, file specification
	_, err = validateFileSpecEntry(xRefTable, d, dictName, "F", REQUIRED, V10)
	if err != nil {
		return err
	}

	// ID, optional, byte string
	_, err = validateStringEntry(xRefTable, d, dictName, "ID", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Comments, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "Comments", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Size, required, array of integers, len 2
	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "Size", REQUIRED, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// CropRect, required, array of integers, len 4
	_, err = validateRectangleEntry(xRefTable, d, dictName, "CropRect", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// CropFixed, optional, array of numbers, len 4
	_, err = validateRectangleEntry(xRefTable, d, dictName, "CropFixed", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Position, required, array of numbers, len 8
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Position", REQUIRED, V10, func(a Array) bool { return len(a) == 8 })

	return err
}

func validateOPIDictV13Part2(xRefTable *XRefTable, d Dict, dictName string) error {
	// Resolution, optional, array of numbers, len 2
	_, err := validateNumberArrayEntry(xRefTable, d, dictName, "Resolution", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// ColorType, optional, name
	_, err = validateNameEntry(xRefTable, d, dictName, "ColorType", OPTIONAL, V10, func(s string) bool { return s == "Process" || s == "Spot" || s == "Separation" })
	if err != nil {
		return err
	}

	// Color, optional, array, len 5
	_, err = validateArrayEntry(xRefTable, d, dictName, "Color", OPTIONAL, V10, func(a Array) bool { return len(a) == 5 })
	if err != nil {
		return err
	}

	// Tint, optional, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "Tint", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Overprint, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Overprint", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// ImageType, optional, array of integers, len 2
	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "ImageType", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// GrayMap, optional, array of integers
	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "GrayMap", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Transparency, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Transparency", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Tags, optional, array
	_, err = validateArrayEntry(xRefTable, d, dictName, "Tags", OPTIONAL, V10, nil)

	return err
}

func validateOPIDictV13(xRefTable *XRefTable, d Dict) error {
	// 14.11.7 Open Prepresse interface (OPI)

	dictName := "opiDictV13"

	err := validateOPIDictV13Part1(xRefTable, d, dictName)
	if err != nil {
		return err
	}

	return validateOPIDictV13Part2(xRefTable, d, dictName)
}

func validateOPIDictInks(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		if colorant := o.Value(); colorant != "full_color" && colorant != "registration" {
			return errors.New("pdfcpu: validateOPIDictInks: corrupt colorant name")
		}

	case Array:
		// no further processing

	default:
		return errors.New("pdfcpu: validateOPIDictInks: corrupt type")

	}

	return nil
}

func validateOPIDictV20(xRefTable *XRefTable, d Dict) error {
	// 14.11.7 Open Prepresse interface (OPI)

	dictName := "opiDictV20"

	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "OPI" })
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "Version", REQUIRED, V10, func(f float64) bool { return f == 2.0 })
	if err != nil {
		return err
	}

	_, err = validateFileSpecEntry(xRefTable, d, dictName, "F", REQUIRED, V10)
	if err != nil {
		return err
	}

	_, err = validateStringEntry(xRefTable, d, dictName, "MainImage", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateArrayEntry(xRefTable, d, dictName, "Tags", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Size", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	_, err = validateRectangleEntry(xRefTable, d, dictName, "CropRect", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateBooleanEntry(xRefTable, d, dictName, "Overprint", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	if o, found := d.Find("Inks"); found {
		err = validateOPIDictInks(xRefTable, o)
		if err != nil {
			return err
		}
	}

	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "IncludedImageDimensions", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, d, dictName, "IncludedImageQuality", OPTIONAL, V10, func(i int) bool { return i >= 1 && i <= 3 })

	return err
}

func validateOPIVersionDict(xRefTable *XRefTable, d Dict) error {
	// 14.11.7 Open Prepresse interface (OPI)

	if d.Len() != 1 {
		return errors.New("pdfcpu: validateOPIVersionDict: must have exactly one entry keyed 1.3 or 2.0")
	}

	validateOPIVersion := func(s string) bool { return MemberOf(s, []string{"1.3", "2.0"}) }

	for opiVersion, obj := range d {

		if !validateOPIVersion(opiVersion) {
			return errors.New("pdfcpu: validateOPIVersionDict: invalid OPI version")
		}

		d, err := xRefTable.DereferenceDict(obj)
		if err != nil || d == nil {
			return err
		}

		if opiVersion == "1.3" {
			err = validateOPIDictV13(xRefTable, d)
		} else {
			err = validateOPIDictV20(xRefTable, d)
		}

		if err != nil {
			return err
		}

	}

	return nil
}

func validateMaskStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	if sd.Type() != nil && *sd.Type() != "XObject" {
		return errors.New("pdfcpu: validateMaskStreamDict: corrupt imageStreamDict type")
	}

	if sd.Subtype() == nil || *sd.Subtype() != "Image" {
		return errors.New("pdfcpu: validateMaskStreamDict: corrupt imageStreamDict subtype")
	}

	return validateImageStreamDict(xRefTable, sd, isNoAlternateImageStreamDict)
}

func validateMaskEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// stream ("explicit masking", another Image XObject) or array of colors ("color key masking")

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case StreamDict:
		err = validateMaskStreamDict(xRefTable, &o)
		if err != nil {
			return err
		}

	case Array:
		// no further processing

	default:

		return errors.Errorf("pdfcpu: validateMaskEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return nil
}

// PDF defines the following Color Spaces:
const (
	DeviceGrayCS = "DeviceGray"
	DeviceRGBCS  = "DeviceRGB"
	DeviceCMYKCS = "DeviceCMYK"
	CalGrayCS    = "CalGray"
	CalRGBCS     = "CalRGB"
	LabCS        = "Lab"
	ICCBasedCS   = "ICCBased"
	IndexedCS    = "Indexed"
	PatternCS    = "Pattern"
	SeparationCS = "Separation"
	DeviceNCS    = "DeviceN"
)

func validateAlternateImageStreamDicts(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil {
		return err
	}
	if a == nil {
		if required {
			return errors.Errorf("pdfcpu: validateAlternateImageStreamDicts: dict=%s required entry \"%s\" missing.", dictName, entryName)
		}
		return nil
	}

	for _, o := range a {

		sd, err := validateStreamDict(xRefTable, o)
		if err != nil {
			return err
		}

		if sd == nil {
			continue
		}

		err = validateImageStreamDict(xRefTable, sd, isAlternateImageStreamDict)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateDeviceColorSpaceName(s string) bool {
	return MemberOf(s, []string{DeviceGrayCS, DeviceRGBCS, DeviceCMYKCS})
}

func validateAllColorSpaceNamesExceptPattern(s string) bool {
	return MemberOf(s, []string{DeviceGrayCS, DeviceRGBCS, DeviceCMYKCS, CalGrayCS, CalRGBCS, LabCS, ICCBasedCS, IndexedCS, SeparationCS, DeviceNCS})
}

func validateCalGrayColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	dictName := "calGrayCSDict"

	// Version check
	err := xRefTable.ValidateVersion(dictName, sinceVersion)
	if err != nil {
		return err
	}

	if len(a) != 2 {
		return errors.Errorf("validateCalGrayColorSpace: invalid array length %d (expected 2) \n.", len(a))
	}

	d, err := xRefTable.DereferenceDict(a[1])
	if err != nil || d == nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "WhitePoint", REQUIRED, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "BlackPoint", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "Gamma", OPTIONAL, sinceVersion, nil)

	return err
}

func validateCalRGBColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	dictName := "calRGBCSDict"

	err := xRefTable.ValidateVersion(dictName, sinceVersion)
	if err != nil {
		return err
	}

	if len(a) != 2 {
		return errors.Errorf("validateCalRGBColorSpace: invalid array length %d (expected 2) \n.", len(a))
	}

	d, err := xRefTable.DereferenceDict(a[1])
	if err != nil || d == nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "WhitePoint", REQUIRED, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "BlackPoint", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Gamma", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Matrix", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 9 })

	return err
}

func validateLabColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	dictName := "labCSDict"

	err := xRefTable.ValidateVersion(dictName, sinceVersion)
	if err != nil {
		return err
	}

	if len(a) != 2 {
		return errors.Errorf("validateLabColorSpace: invalid array length %d (expected 2) \n.", len(a))
	}

	d, err := xRefTable.DereferenceDict(a[1])
	if err != nil || d == nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "WhitePoint", REQUIRED, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "BlackPoint", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Range", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 4 })

	return err
}

func validateAlternateColorSpaceEntryForICC(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, excludePatternCS bool) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, V10)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		if ok := validateAllColorSpaceNamesExceptPattern(o.Value()); !ok {
			err = errors.Errorf("pdfcpu: validateAlternateColorSpaceEntryForICC: invalid NameType:%s\n", o.Value())
		}

	case Array:
		err = validateColorSpaceArray(xRefTable, o, excludePatternCS)

	default:
		err = errors.Errorf("pdfcpu: validateAlternateColorSpaceEntryForICC: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateICCBasedColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	// see 8.6.5.5

	dictName := "ICCBasedColorSpace"

	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}
	err := xRefTable.ValidateVersion(dictName, sinceVersion)
	if err != nil {
		return err
	}

	if len(a) != 2 {
		return errors.Errorf("validateICCBasedColorSpace: invalid array length %d (expected 2) \n.", len(a))
	}

	valid, err := xRefTable.IsValid(a[1].(IndirectRef))
	if err != nil {
		return err
	}
	if valid {
		return nil
	}

	sd, err := validateStreamDict(xRefTable, a[1])
	if err != nil || sd == nil {
		return err
	}
	if err := xRefTable.SetValid(a[1].(IndirectRef)); err != nil {
		return err
	}

	validate := func(i int) bool { return IntMemberOf(i, []int{1, 3, 4}) }
	N, err := validateIntegerEntry(xRefTable, sd.Dict, dictName, "N", REQUIRED, sinceVersion, validate)
	if err != nil {
		return err
	}

	err = validateAlternateColorSpaceEntryForICC(xRefTable, sd.Dict, dictName, "Alternate", OPTIONAL, ExcludePatternCS)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Range", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 2*N.Value() })
	if err != nil {
		return err
	}

	// Metadata, stream, optional since V1.4
	return validateMetadata(xRefTable, sd.Dict, OPTIONAL, V14)
}

func validateIndexedColorSpaceLookuptable(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o.(type) {

	case StringLiteral, HexLiteral:
		err = xRefTable.ValidateVersion("IndexedColorSpaceLookuptable", V12)

	case StreamDict:
		err = xRefTable.ValidateVersion("IndexedColorSpaceLookuptable", sinceVersion)

	default:
		err = errors.Errorf("validateIndexedColorSpaceLookuptable: invalid type\n")

	}

	return err
}

func validateInteger(xRefTable *XRefTable, o Object, validate func(int) bool) (*Integer, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateInteger begin")
	// }

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		return nil, errors.New("pdfcpu: validateInteger: missing object")
	}

	i, ok := o.(Integer)
	if !ok {
		return nil, errors.New("pdfcpu: validateInteger: invalid type")
	}

	// Validation
	if validate != nil && !validate(i.Value()) {
		return nil, errors.Errorf("pdfcpu: validateInteger: invalid integer: %s\n", i)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateInteger end")
	// }

	return &i, nil
}

func validateIndexedColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	// see 8.6.6.3

	err := xRefTable.ValidateVersion("IndexedColorSpace", sinceVersion)
	if err != nil {
		return err
	}

	if len(a) != 4 {
		return errors.Errorf("validateIndexedColorSpace: invalid array length %d (expected 4) \n.", len(a))
	}

	// arr[1] base: base colorspace
	err = validateColorSpace(xRefTable, a[1], ExcludePatternCS)
	if err != nil {
		return err
	}

	// arr[2] hival: 0 <= int <= 255
	_, err = validateInteger(xRefTable, a[2], func(i int) bool { return i >= 0 && i <= 255 })
	if err != nil {
		return err
	}

	// arr[3] lookup: stream since V1.2 or byte string
	return validateIndexedColorSpaceLookuptable(xRefTable, a[3], sinceVersion)
}

func validatePatternColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	err := xRefTable.ValidateVersion("PatternColorSpace", sinceVersion)
	if err != nil {
		return err
	}

	if len(a) < 1 || len(a) > 2 {
		return errors.Errorf("validatePatternColorSpace: invalid array length %d (expected 1 or 2) \n.", len(a))
	}

	// 8.7.3.3: arr[1]: name of underlying color space, any cs except PatternCS
	if len(a) == 2 {
		err := validateColorSpace(xRefTable, a[1], ExcludePatternCS)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateName(xRefTable *XRefTable, o Object, validate func(string) bool) (*NameType, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateName begin")
	// }

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		return nil, errors.New("pdfcpu: validateName: missing object")
	}

	name, ok := o.(NameType)
	if !ok {
		return nil, errors.New("pdfcpu: validateName: invalid type")
	}

	// Validation
	if validate != nil && !validate(name.Value()) {
		return nil, errors.Errorf("pdfcpu: validateName: invalid name: %s\n", name)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateName end")
	// }

	return &name, nil
}

// see 7.10 Functions

func validateExponentialInterpolationFunctionDict(xRefTable *XRefTable, d Dict) error {
	dictName := "exponentialInterpolationFunctionDict"

	// Version check
	err := xRefTable.ValidateVersion(dictName, V13)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Domain", REQUIRED, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Range", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "C0", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "C1", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "N", REQUIRED, V13, nil)

	return err
}

func validateFunctionArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateFunctionArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for _, o := range a {
		if err = validateFunction(xRefTable, o); err != nil {
			return nil, err
		}
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateFunctionArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateStitchingFunctionDict(xRefTable *XRefTable, d Dict) error {
	dictName := "stitchingFunctionDict"

	// Version check
	err := xRefTable.ValidateVersion(dictName, V13)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Domain", REQUIRED, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Range", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateFunctionArrayEntry(xRefTable, d, dictName, "Functions", REQUIRED, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Bounds", REQUIRED, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Encode", REQUIRED, V13, nil)

	return err
}

func validateSampledFunctionStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	dictName := "sampledFunctionStreamDict"

	// Version check
	err := xRefTable.ValidateVersion(dictName, V12)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Domain", REQUIRED, V12, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Range", REQUIRED, V12, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerArrayEntry(xRefTable, sd.Dict, dictName, "Size", REQUIRED, V12, nil)
	if err != nil {
		return err
	}

	validate := func(i int) bool { return IntMemberOf(i, []int{1, 2, 4, 8, 12, 16, 24, 32}) }
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "BitsPerSample", REQUIRED, V12, validate)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Order", OPTIONAL, V12, func(i int) bool { return i == 1 || i == 3 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Encode", OPTIONAL, V12, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Decode", OPTIONAL, V12, nil)

	return err
}

func validatePostScriptCalculatorFunctionStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	dictName := "postScriptCalculatorFunctionStreamDict"

	// Version check
	err := xRefTable.ValidateVersion(dictName, V13)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Domain", REQUIRED, V13, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Range", REQUIRED, V13, nil)

	return err
}

func processFunctionDict(xRefTable *XRefTable, d Dict) error {
	funcType, err := validateIntegerEntry(xRefTable, d, "functionDict", "FunctionType", REQUIRED, V10, func(i int) bool { return i == 2 || i == 3 })
	if err != nil {
		return err
	}

	switch *funcType {

	case 2:
		err = validateExponentialInterpolationFunctionDict(xRefTable, d)

	case 3:
		err = validateStitchingFunctionDict(xRefTable, d)

	}

	return err
}

func processFunctionStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	funcType, err := validateIntegerEntry(xRefTable, sd.Dict, "functionDict", "FunctionType", REQUIRED, V10, func(i int) bool { return i == 0 || i == 4 })
	if err != nil {
		return err
	}

	switch *funcType {
	case 0:
		err = validateSampledFunctionStreamDict(xRefTable, sd)

	case 4:
		err = validatePostScriptCalculatorFunctionStreamDict(xRefTable, sd)

	}

	return err
}

func processFunction(xRefTable *XRefTable, o Object) (err error) {
	// Function dict: dict or stream dict with required entry "FunctionType" (integer):
	// 0: Sampled function (stream dict)
	// 2: Exponential interpolation function (dict)
	// 3: Stitching function (dict)
	// 4: PostScript calculator function (stream dict), since V1.3

	switch o := o.(type) {

	case Dict:

		// process function  2,3
		err = processFunctionDict(xRefTable, o)

	case StreamDict:

		// process function  0,4
		err = processFunctionStreamDict(xRefTable, &o)

	default:
		return errors.New("pdfcpu: processFunction: obj must be dict or stream dict")
	}

	return err
}

func validateFunction(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil {
		return err
	}
	if o == nil {
		return errors.New("pdfcpu: validateFunction: missing object")
	}

	return processFunction(xRefTable, o)
}

func validateSeparationColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	// see 8.6.6.4

	err := xRefTable.ValidateVersion("SeparationColorSpace", sinceVersion)
	if err != nil {
		return err
	}

	if len(a) != 4 {
		return errors.Errorf("validateSeparationColorSpace: invalid array length %d (expected 4) \n.", len(a))
	}

	// arr[1]: colorant name, arbitrary
	_, err = validateName(xRefTable, a[1], nil)
	if err != nil {
		return err
	}

	// arr[2]: alternate space
	err = validateColorSpace(xRefTable, a[2], ExcludePatternCS)
	if err != nil {
		return err
	}

	// arr[3]: tintTransform, function
	return validateFunction(xRefTable, a[3])
}

func validateDeviceNColorSpaceColorantsDict(xRefTable *XRefTable, d Dict) error {
	for _, obj := range d {

		a, err := xRefTable.DereferenceArray(obj)
		if err != nil {
			return err
		}

		if a != nil {
			err = validateSeparationColorSpace(xRefTable, a, V12)
			if err != nil {
				return err
			}
		}

	}

	return nil
}

func validateNameArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(a Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		if _, ok := o.(NameType); !ok {
			return nil, errors.Errorf("pdfcpu: validateNameArrayEntry: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateDeviceNColorSpaceProcessDict(xRefTable *XRefTable, d Dict) error {
	dictName := "DeviceNCSProcessDict"

	err := validateColorSpaceEntry(xRefTable, d, dictName, "ColorSpace", REQUIRED, true)
	if err != nil {
		return err
	}

	_, err = validateNameArrayEntry(xRefTable, d, dictName, "Components", REQUIRED, V10, nil)

	return err
}

func validateFloat(xRefTable *XRefTable, o Object, validate func(float64) bool) (*Float, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateFloat begin")
	// }

	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		return nil, errors.New("pdfcpu: validateFloat: missing object")
	}

	f, ok := o.(Float)
	if !ok {
		return nil, errors.New("pdfcpu: validateFloat: invalid type")
	}

	// Validation
	if validate != nil && !validate(f.Value()) {
		return nil, errors.Errorf("pdfcpu: validateFloat: invalid float: %s\n", f)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateFloat end")
	// }

	return &f, nil
}

func validateDeviceNColorSpaceSoliditiesDict(xRefTable *XRefTable, d Dict) error {
	for _, obj := range d {
		_, err := validateFloat(xRefTable, obj, func(f float64) bool { return f >= 0.0 && f <= 1.0 })
		if err != nil {
			return err
		}
	}

	return nil
}

func validateDeviceNColorSpaceDotGainDict(xRefTable *XRefTable, d Dict) error {
	for _, obj := range d {
		err := validateFunction(xRefTable, obj)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateDeviceNColorSpaceMixingHintsDict(xRefTable *XRefTable, d Dict) error {
	dictName := "deviceNCSMixingHintsDict"

	d1, err := validateDictEntry(xRefTable, d, dictName, "Solidities", OPTIONAL, V11, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateDeviceNColorSpaceSoliditiesDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	_, err = validateNameArrayEntry(xRefTable, d, dictName, "PrintingOrder", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	d1, err = validateDictEntry(xRefTable, d, dictName, "DotGain", OPTIONAL, V11, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateDeviceNColorSpaceDotGainDict(xRefTable, d1)
	}

	return err
}

func validateDeviceNColorSpaceAttributesDict(xRefTable *XRefTable, o Object) error {
	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	dictName := "deviceNCSAttributesDict"

	sinceVersion := V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}

	_, err = validateNameEntry(xRefTable, d, dictName, "Subtype", OPTIONAL, sinceVersion, func(s string) bool { return s == "DeviceN" || s == "NChannel" })
	if err != nil {
		return err
	}

	d1, err := validateDictEntry(xRefTable, d, dictName, "Colorants", OPTIONAL, V11, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateDeviceNColorSpaceColorantsDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	d1, err = validateDictEntry(xRefTable, d, dictName, "Process", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateDeviceNColorSpaceProcessDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	d1, err = validateDictEntry(xRefTable, d, dictName, "MixingHints", OPTIONAL, V16, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateDeviceNColorSpaceMixingHintsDict(xRefTable, d1)
	}

	return err
}

func validateNameArray(xRefTable *XRefTable, o Object) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateNameArray begin")
	// }

	a, err := xRefTable.DereferenceArray(o)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		if _, ok := o.(NameType); !ok {
			return nil, errors.Errorf("pdfcpu: validateNameArray: invalid type at index %d\n", i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateNameArray end")
	// }

	return a, nil
}

func validateDeviceNColorSpace(xRefTable *XRefTable, a Array, sinceVersion Version) error {
	// see 8.6.6.5

	err := xRefTable.ValidateVersion("DeviceNColorSpace", sinceVersion)
	if err != nil {
		return err
	}

	if len(a) < 4 || len(a) > 5 {
		return errors.Errorf("writeDeviceNColorSpace: invalid array length %d (expected 4 or 5) \n.", len(a))
	}

	// arr[1]: array of names specifying the individual color components
	// length subject to implementation limit.
	_, err = validateNameArray(xRefTable, a[1])
	if err != nil {
		return err
	}

	// arr[2]: alternate space
	err = validateColorSpace(xRefTable, a[2], ExcludePatternCS)
	if err != nil {
		return err
	}

	// arr[3]: tintTransform, function
	err = validateFunction(xRefTable, a[3])
	if err != nil {
		return err
	}

	// arr[4]: color space attributes dict, optional
	if len(a) == 5 {
		err = validateDeviceNColorSpaceAttributesDict(xRefTable, a[4])
	}

	return err
}

func validateCSArray(xRefTable *XRefTable, a Array, csName string) error {
	// see 8.6 Color Spaces

	switch csName {

	// CIE-based
	case CalGrayCS:
		return validateCalGrayColorSpace(xRefTable, a, V11)

	case CalRGBCS:
		return validateCalRGBColorSpace(xRefTable, a, V11)

	case LabCS:
		return validateLabColorSpace(xRefTable, a, V11)

	case ICCBasedCS:
		return validateICCBasedColorSpace(xRefTable, a, V13)

	// Special
	case IndexedCS:
		return validateIndexedColorSpace(xRefTable, a, V11)

	case PatternCS:
		return validatePatternColorSpace(xRefTable, a, V12)

	case SeparationCS:
		return validateSeparationColorSpace(xRefTable, a, V12)

	case DeviceNCS:
		return validateDeviceNColorSpace(xRefTable, a, V13)

	default:
		return errors.Errorf("validateColorSpaceArray: undefined color space: %s\n", csName)
	}
}

func validateColorSpaceArraySubset(xRefTable *XRefTable, a Array, cs []string) error {
	csName, ok := a[0].(NameType)
	if !ok {
		return errors.New("pdfcpu: validateColorSpaceArraySubset: corrupt Colorspace array")
	}

	for _, v := range cs {
		if csName.Value() == v {
			return validateCSArray(xRefTable, a, v)
		}
	}

	return errors.Errorf("pdfcpu: validateColorSpaceArraySubset: invalid color space: %s\n", csName)
}

func validateColorSpaceArray(xRefTable *XRefTable, a Array, excludePatternCS bool) (err error) {
	// see 8.6 Color Spaces

	name, ok := a[0].(NameType)
	if !ok {
		return errors.New("pdfcpu: validateColorSpaceArray: corrupt Colorspace array")
	}

	switch name {

	// CIE-based
	case CalGrayCS:
		err = validateCalGrayColorSpace(xRefTable, a, V11)

	case CalRGBCS:
		err = validateCalRGBColorSpace(xRefTable, a, V11)

	case LabCS:
		err = validateLabColorSpace(xRefTable, a, V11)

	case ICCBasedCS:
		err = validateICCBasedColorSpace(xRefTable, a, V13)

	// Special
	case IndexedCS:
		err = validateIndexedColorSpace(xRefTable, a, V11)

	case PatternCS:
		if excludePatternCS {
			return errors.New("pdfcpu: validateColorSpaceArray: Pattern color space not allowed")
		}
		err = validatePatternColorSpace(xRefTable, a, V12)

	case SeparationCS:
		err = validateSeparationColorSpace(xRefTable, a, V12)

	case DeviceNCS:
		err = validateDeviceNColorSpace(xRefTable, a, V13)

	case DeviceGrayCS, DeviceRGBCS, DeviceCMYKCS:
		if xRefTable.ValidationMode != ValidationRelaxed {
			err = errors.Errorf("pdfcpu: validateColorSpaceArray: undefined color space: %s\n", name)
		}

	default:
		err = errors.Errorf("pdfcpu: validateColorSpaceArray: undefined color space: %s\n", name)
	}

	return err
}

func validateColorSpace(xRefTable *XRefTable, o Object, excludePatternCS bool) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		validateSpecialColorSpaceName := func(s string) bool { return MemberOf(s, []string{"Pattern"}) }
		if ok := validateDeviceColorSpaceName(o.Value()) || validateSpecialColorSpaceName(o.Value()); !ok {
			err = errors.Errorf("validateColorSpace: invalid device color space name: %v\n", o)
		}

	case Array:
		err = validateColorSpaceArray(xRefTable, o, excludePatternCS)

	default:
		err = errors.New("pdfcpu: validateColorSpace: corrupt obj typ, must be Name or Array")

	}

	return err
}

func validateColorSpaceEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, excludePatternCS bool) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, V10)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		if ok := validateDeviceColorSpaceName(o.Value()); !ok {
			err = errors.Errorf("pdfcpu: validateColorSpaceEntry: NameType:%s\n", o.Value())
		}

	case Array:
		err = validateColorSpaceArray(xRefTable, o, excludePatternCS)

	default:
		err = errors.Errorf("pdfcpu: validateColorSpaceEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateColorSpaceResourceDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 8.6 Color Spaces

	// Version check
	err := xRefTable.ValidateVersion("ColorSpaceResourceDict", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// Iterate over colorspace resource dictionary
	for _, o := range d {

		// Process colorspace
		err = validateColorSpace(xRefTable, o, IncludePatternCS)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateImageStreamDictPart1(xRefTable *XRefTable, sd *StreamDict, dictName string) (isImageMask bool, err error) {
	// Width, integer, required
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Width", REQUIRED, V10, nil)
	if err != nil {
		return false, err
	}

	// Height, integer, required
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Height", REQUIRED, V10, nil)
	if err != nil {
		return false, err
	}

	// ImageMask, boolean, optional
	imageMask, err := validateBooleanEntry(xRefTable, sd.Dict, dictName, "ImageMask", OPTIONAL, V10, nil)
	if err != nil {
		return false, err
	}

	isImageMask = (imageMask != nil) && *imageMask

	// ColorSpace, name or array, required unless used filter is JPXDecode; not allowed for imagemasks.
	if !isImageMask {

		required := REQUIRED

		if sd.HasSoleFilterNamed(JPX) {
			required = OPTIONAL
		}

		if sd.HasSoleFilterNamed(CCITTFax) && xRefTable.ValidationMode == ValidationRelaxed {
			required = OPTIONAL
		}

		err = validateColorSpaceEntry(xRefTable, sd.Dict, dictName, "ColorSpace", required, ExcludePatternCS)
		if err != nil {
			return false, err
		}

	}

	return isImageMask, nil
}

func validateImageStreamDictPart2(xRefTable *XRefTable, sd *StreamDict, dictName string, isImageMask, isAlternate bool) error {
	// BitsPerComponent, integer
	required := REQUIRED
	if sd.HasSoleFilterNamed(JPX) || isImageMask {
		required = OPTIONAL
	}
	// For imageMasks BitsPerComponent must be 1.
	var validateBPC func(i int) bool
	if isImageMask {
		validateBPC = func(i int) bool {
			return i == 1
		}
	}
	_, err := validateIntegerEntry(xRefTable, sd.Dict, dictName, "BitsPerComponent", required, V10, validateBPC)
	if err != nil {
		return err
	}

	// Note 8.6.5.8: If a PDF processor does not recognise the specified name, it shall use the RelativeColorimetric intent by default.
	_, err = validateNameEntry(xRefTable, sd.Dict, dictName, "Intent", OPTIONAL, V11, nil)
	if err != nil {
		return err
	}

	// Mask, stream or array, optional since V1.3; not allowed for image masks.
	if !isImageMask {
		err = validateMaskEntry(xRefTable, sd.Dict, dictName, "Mask", OPTIONAL, V13)
		if err != nil {
			return err
		}
	}

	// Decode, array, optional
	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Decode", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Interpolate, boolean, optional
	_, err = validateBooleanEntry(xRefTable, sd.Dict, dictName, "Interpolate", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Alternates, array, optional, since V1.3
	if !isAlternate {
		err = validateAlternateImageStreamDicts(xRefTable, sd.Dict, dictName, "Alternates", OPTIONAL, V13)
	}

	return err
}

func validateMetadata(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// => 14.3 Metadata
	// In general, any PDF stream or dictionary may have metadata attached to it
	// as long as the stream or dictionary represents an actual information resource,
	// as opposed to serving as an implementation artifact.
	// Some PDF constructs are considered implementational, and hence may not have associated metadata.

	_, err := validateMetadataStream(xRefTable, d, required, sinceVersion)
	return err
}

func validateRootMetadata(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	if xRefTable.CatalogXMPMeta == nil {
		return nil
	}

	x := xRefTable.CatalogXMPMeta

	// fmt.Printf("       Title: %v\n", x.RDF.Description.Title.Alt.Entries)
	// fmt.Printf("      Author: %v\n", x.RDF.Description.Author.Seq.Entries)
	// fmt.Printf("     Subject: %v\n", x.RDF.Description.Subject.Alt.Entries)
	// fmt.Printf("     Creator: %s\n", x.RDF.Description.Creator)
	// fmt.Printf("CreationDate: %v\n", time.Time(x.RDF.Description.CreationDate).Format(time.RFC3339Nano))
	// fmt.Printf("     ModDate: %v\n", time.Time(x.RDF.Description.ModDate).Format(time.RFC3339Nano))
	// fmt.Printf("    Producer: %s\n", x.RDF.Description.Producer)
	// fmt.Printf("     Trapped: %t\n", x.RDF.Description.Trapped)
	// fmt.Printf("    Keywords: %s\n", x.RDF.Description.Keywords)

	d := x.RDF.Description
	xRefTable.Title = strings.Join(d.Title.Alt.Entries, ", ")
	xRefTable.Author = strings.Join(d.Author.Seq.Entries, ", ")
	xRefTable.Subject = strings.Join(d.Subject.Alt.Entries, ", ")
	xRefTable.Creator = d.Creator
	xRefTable.CreationDate = time.Time(d.CreationDate).Format(time.RFC3339Nano)
	xRefTable.ModDate = time.Time(d.ModDate).Format(time.RFC3339Nano)
	xRefTable.Producer = d.Producer
	// xRefTable.Trapped = d.Trapped

	ss := strings.FieldsFunc(d.Keywords, func(c rune) bool { return c == ',' || c == ';' || c == '\r' })
	for _, s := range ss {
		keyword := strings.TrimSpace(s)
		xRefTable.KeywordList[keyword] = true
	}

	return nil
}

func validateImageStreamDict(xRefTable *XRefTable, sd *StreamDict, isAlternate bool) error {
	dictName := "imageStreamDict"
	var isImageMask bool

	isImageMask, err := validateImageStreamDictPart1(xRefTable, sd, dictName)
	if err != nil {
		return err
	}

	err = validateImageStreamDictPart2(xRefTable, sd, dictName, isImageMask, isAlternate)
	if err != nil {
		return err
	}

	// SMask, stream, optional, since V1.4
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}
	sd1, err := validateStreamDictEntry(xRefTable, sd.Dict, dictName, "SMask", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if sd1 != nil {
		err = validateImageStreamDict(xRefTable, sd1, isNoAlternateImageStreamDict)
		if err != nil {
			return err
		}
	}

	// SMaskInData, integer, optional
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "SMaskInData", OPTIONAL, V10, func(i int) bool { return i >= 0 && i <= 2 })
	if err != nil {
		return err
	}

	// NameType, name, required for V10
	// Shall no longer be used.
	// _, err = validateNameEntry(xRefTable, sd.Dict, dictName, "Name", xRefTable.Version() == V10, V10, nil)
	// if err != nil {
	// 	return err
	// }

	// StructParent, integer, optional
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "StructParent", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// ID, byte string, optional, since V1.3
	_, err = validateStringEntry(xRefTable, sd.Dict, dictName, "ID", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// OPI, dict, optional since V1.2
	err = validateEntryOPI(xRefTable, sd.Dict, dictName, "OPI", OPTIONAL, V12)
	if err != nil {
		return err
	}

	// Metadata, stream, optional since V1.4
	err = validateMetadata(xRefTable, sd.Dict, OPTIONAL, V14)
	if err != nil {
		return err
	}

	// OC, dict, optional since V1.5
	return validateEntryOC(xRefTable, sd.Dict, dictName, "OC", OPTIONAL, V15)
}

func validateFormStreamDictPart1(xRefTable *XRefTable, sd *StreamDict, dictName string) error {
	var err error
	if xRefTable.ValidationMode == ValidationRelaxed {
		_, err = validateNumberEntry(xRefTable, sd.Dict, dictName, "FormType", OPTIONAL, V10, func(f float64) bool { return f == 1. })
	} else {
		_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "FormType", OPTIONAL, V10, func(i int) bool { return i == 1 })
	}
	if err != nil {
		return err
	}

	_, err = validateRectangleEntry(xRefTable, sd.Dict, dictName, "BBox", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Matrix", OPTIONAL, V10, func(a Array) bool { return len(a) == 6 })
	if err != nil {
		return err
	}

	// Resources, dict, optional, since V1.2
	if o, ok := sd.Find("Resources"); ok {
		_, err = validateResourceDict(xRefTable, o)
		if err != nil {
			return err
		}
	}

	// Group, dict, optional, since V1.4
	err = validatePageEntryGroup(xRefTable, sd.Dict, OPTIONAL, V14)
	if err != nil {
		return err
	}

	// Ref, dict, optional, since V1.4
	d, err := validateDictEntry(xRefTable, sd.Dict, dictName, "Ref", OPTIONAL, V14, nil)
	if err != nil {
		return err
	}
	if d != nil {
		err = validateReferenceDict(xRefTable, d)
		if err != nil {
			return err
		}
	}

	// Metadata, stream, optional, since V1.4
	return validateMetadata(xRefTable, sd.Dict, OPTIONAL, V14)
}

func validateOptionalContentGroupIntent(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see 8.11.2.1

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	validate := func(s string) bool {
		return s == "View" || s == "Design" || s == "All"
	}

	switch o := o.(type) {

	case NameType:
		if !validate(o.Value()) {
			return errors.Errorf("validateOptionalContentGroupIntent: invalid intent: %s", o.Value())
		}

	case Array:

		for i, v := range o {

			if v == nil {
				continue
			}

			n, ok := v.(NameType)
			if !ok {
				return errors.Errorf("pdfcpu: validateOptionalContentGroupIntent: invalid type at index %d\n", i)
			}

			if !validate(n.Value()) {
				return errors.Errorf("pdfcpu: validateOptionalContentGroupIntent: invalid intent: %s", n.Value())
			}
		}

	default:
		return errors.New("pdfcpu: validateOptionalContentGroupIntent: invalid type")
	}

	return nil
}

func validateOptionalContentGroupUsageDict(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see 8.11.4.4

	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "OCUsageDict"

	// CreatorInfo, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "CreatorInfo", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Language, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "Language", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Export, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "Export", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Zoom, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "Zoom", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Print, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "Print", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// View, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "View", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// User, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "User", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// PageElement, optional, dict
	_, err = validateDictEntry(xRefTable, d1, dictName, "PageElement", OPTIONAL, sinceVersion, nil)

	return err
}

func validateOptionalContentGroupDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 8.11 Optional Content

	dictName := "optionalContentGroupDict"

	// Type, required, name, OCG
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", REQUIRED, sinceVersion, func(s string) bool { return s == "OCG" })
	if err != nil {
		return err
	}

	// NameType, required, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "Name", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Intent, optional, name or array
	err = validateOptionalContentGroupIntent(xRefTable, d, dictName, "Intent", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// Usage, optional, usage dict
	return validateOptionalContentGroupUsageDict(xRefTable, d, dictName, "Usage", OPTIONAL, sinceVersion)
}

func validateOptionalContentGroupArray(xRefTable *XRefTable, d Dict, dictName, dictEntry string, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, dictEntry, OPTIONAL, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for _, v := range a {

		if v == nil {
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateOptionalContentGroupDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateOCGs(xRefTable *XRefTable, d Dict, dictName, entryName string, sinceVersion Version) error {
	// see 8.11.2.2

	o, _, err := d.Entry(dictName, entryName, OPTIONAL)
	if err != nil || o == nil {
		return err
	}

	// Version check
	err = xRefTable.ValidateVersion("OCGs", sinceVersion)
	if err != nil {
		return err
	}

	o, err = xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	d1, ok := o.(Dict)
	if ok {
		return validateOptionalContentGroupDict(xRefTable, d1, sinceVersion)
	}

	return validateOptionalContentGroupArray(xRefTable, d, dictName, entryName, sinceVersion)
}

func validateOptionalContentMembershipDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 8.11.2.2

	dictName := "OCMDict"

	// OCGs, optional, dict or array
	err := validateOCGs(xRefTable, d, dictName, "OCGs", sinceVersion)
	if err != nil {
		return err
	}

	// P, optional, name
	validate := func(s string) bool { return MemberOf(s, []string{"AllOn", "AnyOn", "AnyOff", "AllOff"}) }
	_, err = validateNameEntry(xRefTable, d, dictName, "P", OPTIONAL, sinceVersion, validate)
	if err != nil {
		return err
	}

	// VE, optional, array, since V1.6
	_, err = validateArrayEntry(xRefTable, d, dictName, "VE", OPTIONAL, V16, nil)

	return err
}

func validateOptionalContent(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	validate := func(s string) bool { return s == "OCG" || s == "OCMD" }
	t, err := validateNameEntry(xRefTable, d1, "optionalContent", "Type", REQUIRED, sinceVersion, validate)
	if err != nil {
		return err
	}

	if *t == "OCG" {
		return validateOptionalContentGroupDict(xRefTable, d1, sinceVersion)
	}

	return validateOptionalContentMembershipDict(xRefTable, d1, sinceVersion)
}

func validateUsageApplicationDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "usageAppDict"

	// Event, required, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Event", REQUIRED, sinceVersion, func(s string) bool { return s == "View" || s == "Print" || s == "Export" })
	if err != nil {
		return err
	}

	// OCGs, optional, array of content groups
	err = validateOptionalContentGroupArray(xRefTable, d, dictName, "OCGs", sinceVersion)
	if err != nil {
		return err
	}

	// Category, required, array of names
	_, err = validateNameArrayEntry(xRefTable, d, dictName, "Category", REQUIRED, sinceVersion, nil)

	return err
}

func validateUsageApplicationDictArray(xRefTable *XRefTable, d Dict, dictName, dictEntry string, required bool, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, dictEntry, required, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for _, v := range a {

		if v == nil {
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateUsageApplicationDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateOptionalContentConfigurationDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "optContentConfigDict"

	// NameType, optional, string
	_, err := validateStringEntry(xRefTable, d, dictName, "Name", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Creator, optional, string
	_, err = validateStringEntry(xRefTable, d, dictName, "Creator", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// BaseState, optional, name
	validate := func(s string) bool { return MemberOf(s, []string{"ON", "OFF", "UNCHANGED"}) }
	baseState, err := validateNameEntry(xRefTable, d, dictName, "BaseState", OPTIONAL, sinceVersion, validate)
	if err != nil {
		return err
	}

	if baseState != nil {

		if baseState.Value() != "ON" {
			// ON, optional, content group array
			err = validateOptionalContentGroupArray(xRefTable, d, dictName, "ON", sinceVersion)
			if err != nil {
				return err
			}
		}

		if baseState.Value() != "OFF" {
			// OFF, optional, content group array
			err = validateOptionalContentGroupArray(xRefTable, d, dictName, "OFF", sinceVersion)
			if err != nil {
				return err
			}
		}

	}

	// Intent, optional, name or array
	err = validateOptionalContentGroupIntent(xRefTable, d, dictName, "Intent", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// AS, optional, usage application dicts array
	err = validateUsageApplicationDictArray(xRefTable, d, dictName, "AS", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// Order, optional, array
	_, err = validateArrayEntry(xRefTable, d, dictName, "Order", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// ListMode, optional, name
	validate = func(s string) bool { return MemberOf(s, []string{"AllPages", "VisiblePages"}) }
	_, err = validateNameEntry(xRefTable, d, dictName, "ListMode", OPTIONAL, sinceVersion, validate)
	if err != nil {
		return err
	}

	// RBGroups, optional, array
	_, err = validateArrayEntry(xRefTable, d, dictName, "RBGroups", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Locked, optional, array
	return validateOptionalContentGroupArray(xRefTable, d, dictName, "Locked", V16)
}

func validateIndRefArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIndRefArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {
		if o == nil {
			continue
		}
		if _, ok := o.(IndirectRef); !ok {
			return nil, errors.Errorf("pdfcpu: validateIndRefArrayEntry: invalid type at index %d\n", i)
		}
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIndRefArrayEntry end: entry=%s \n", entryName)
	// }

	return a, nil
}

func validateOCProperties(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// aka optional content properties dict.

	// => 8.11.4 Configuring Optional Content

	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "OCProperties", required, sinceVersion, nil)
	if err != nil || len(d) == 0 {
		return err
	}

	dictName := "optContentPropertiesDict"

	// "OCGs" required array of already written indRefs
	r := true
	if xRefTable.ValidationMode == ValidationRelaxed {
		r = false
	}
	_, err = validateIndRefArrayEntry(xRefTable, d, dictName, "OCGs", r, sinceVersion, nil)
	if err != nil {
		return err
	}

	// "D" required dict, default viewing optional content configuration dict.
	d1, err := validateDictEntry(xRefTable, d, dictName, "D", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}
	err = validateOptionalContentConfigurationDict(xRefTable, d1, sinceVersion)
	if err != nil {
		return err
	}

	// "Configs" optional array of alternate optional content configuration dicts.
	a, err := validateArrayEntry(xRefTable, d, dictName, "Configs", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	for _, o := range a {

		d, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateOptionalContentConfigurationDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateEntryOC(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateOptionalContentGroupDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateEntryOPI(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateOPIVersionDict(xRefTable, d1)
	}

	return err
}

func validateFormStreamDictPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// PieceInfo, dict, optional, since V1.3
	if xRefTable.ValidationMode != ValidationRelaxed {
		hasPieceInfo, err := validatePieceInfo(xRefTable, d, dictName, "PieceInfo", OPTIONAL, V13)
		if err != nil {
			return err
		}

		// LastModified, date, required if PieceInfo present, since V1.3
		lm, err := validateDateEntry(xRefTable, d, dictName, "LastModified", OPTIONAL, V13)
		if err != nil {
			return err
		}

		if hasPieceInfo && lm == nil {
			err = errors.New("pdfcpu: validateFormStreamDictPart2: missing \"LastModified\" (required by \"PieceInfo\")")
			return err
		}
	}

	// StructParent, integer
	sp, err := validateIntegerEntry(xRefTable, d, dictName, "StructParent", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// StructParents, integer
	sps, err := validateIntegerEntry(xRefTable, d, dictName, "StructParents", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}
	if sp != nil && sps != nil {
		return errors.New("pdfcpu: validateFormStreamDictPart2: only \"StructParent\" or \"StructParents\" allowed")
	}

	// OPI, dict, optional, since V1.2
	err = validateEntryOPI(xRefTable, d, dictName, "OPI", OPTIONAL, V12)
	if err != nil {
		return err
	}

	// OC, optional, content group dict or content membership dict, since V1.5
	// Specifying the optional content properties for the annotation.
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	err = validateOptionalContent(xRefTable, d, dictName, "OC", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// NameType, name, optional (required in 1.0)
	required := xRefTable.Version() == V10
	_, err = validateNameEntry(xRefTable, d, dictName, "Name", required, V10, nil)

	return err
}

func validateFormStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	// 8.10 Form XObjects

	dictName := "formStreamDict"

	err := validateFormStreamDictPart1(xRefTable, sd, dictName)
	if err != nil {
		return err
	}

	return validateFormStreamDictPart2(xRefTable, sd.Dict, dictName)
}

func validateXObjectType(xRefTable *XRefTable, sd *StreamDict) error {
	ss := []string{"XObject"}
	if xRefTable.ValidationMode == ValidationRelaxed {
		ss = append(ss, "Xobject")
	}

	n, err := validateNameEntry(xRefTable, sd.Dict, "xObjectStreamDict", "Type", OPTIONAL, V10, func(s string) bool { return MemberOf(s, ss) })
	if err != nil {
		return err
	}

	// Repair "Xobject" to "XObject".
	if n != nil && *n == "Xobject" {
		sd.Dict["Type"] = NameType("XObject")
	}

	return nil
}

func validateXObjectStreamDict(xRefTable *XRefTable, o Object) error {
	// see 8.8 External Objects

	// Dereference stream dict and ensure it is validated exactly once in order
	// to handle XObjects(forms) with recursive structures like produced by Microsoft.
	sd, valid, err := xRefTable.DereferenceStreamDict(o)
	if valid {
		return nil
	}
	if err != nil || sd == nil {
		return err
	}

	dictName := "xObjectStreamDict"

	if err := validateXObjectType(xRefTable, sd); err != nil {
		return err
	}

	required := REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}
	subtype, err := validateNameEntry(xRefTable, sd.Dict, dictName, "Subtype", required, V10, nil)
	if err != nil {
		return err
	}

	if subtype == nil {
		// relaxed
		_, found := sd.Find("BBox")
		if found {
			return validateFormStreamDict(xRefTable, sd)
		}

		// Relaxed for page Thumb
		return validateImageStreamDict(xRefTable, sd, isNoAlternateImageStreamDict)
	}

	switch *subtype {

	case "Form":
		err = validateFormStreamDict(xRefTable, sd)

	case "Image":
		err = validateImageStreamDict(xRefTable, sd, isNoAlternateImageStreamDict)

	case "PS":
		err = errors.Errorf("pdfcpu: validateXObjectStreamDict: PostScript XObjects should not be used")

	default:
		return errors.Errorf("pdfcpu: validateXObjectStreamDict: unknown Subtype: %s\n", *subtype)

	}

	return err
}

func validateGroupAttributesDict(xRefTable *XRefTable, o Object) error {
	// see 11.6.6 Transparency Group XObjects

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	dictName := "groupAttributesDict"

	// Type, name, optional
	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "Group" })
	if err != nil {
		return err
	}

	// S, name, required
	_, err = validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, V10, func(s string) bool { return s == "Transparency" })
	if err != nil {
		return err
	}

	// CS, colorSpace, optional
	err = validateColorSpaceEntry(xRefTable, d, dictName, "CS", OPTIONAL, ExcludePatternCS)
	if err != nil {
		return err
	}

	// I, boolean, optional
	_, err = validateBooleanEntry(xRefTable, d, dictName, "I", OPTIONAL, V10, nil)

	return err
}

func validateXObjectResourceDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// Version check
	err := xRefTable.ValidateVersion("XObjectResourceDict", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// fmt.Printf("XObjResDict:\n%s\n", d)

	// Iterate over XObject resource dictionary
	for _, o := range d {

		// Process XObject dict
		err = validateXObjectStreamDict(xRefTable, o)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateAPNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// Version check
	err := xRefTable.ValidateVersion("APNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	return validateXObjectStreamDict(xRefTable, o)
}

func validateJavaScript(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, V13)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case StringLiteral:
		// Ensure UTF16 correctness.
		_, err = StringLiteralToString(o)

	case HexLiteral:
		// Ensure UTF16 correctness.
		_, err = HexLiteralToString(o)

	case StreamDict:
		// no further processing

	default:
		err = errors.Errorf("validateJavaScript: invalid type\n")

	}

	return err
}

func validateJavaScriptActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.16

	// JS, required, text string or stream
	return validateJavaScript(xRefTable, d, dictName, "JS", REQUIRED)
}

func validateJavaScriptNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// Version check
	err := xRefTable.ValidateVersion("JavaScriptNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return err
	}

	// Javascript Action:
	return validateJavaScriptActionDict(xRefTable, d, "JavaScript")
}

func validatePagesNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 12.7.6

	// Version check
	err := xRefTable.ValidateVersion("PagesNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	// Value is a page dict.

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return err
	}

	if d == nil {
		return errors.New("pdfcpu: validatePagesNameTreeValue: value is nil")
	}

	_, err = validateNameEntry(xRefTable, d, "pageDict", "Type", REQUIRED, V10, func(s string) bool { return s == "Page" })

	return err
}

func validateTemplatesNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 12.7.6

	// Version check
	err := xRefTable.ValidateVersion("TemplatesNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	// Value is a template dict.

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return err
	}
	if d == nil {
		return errors.New("pdfcpu: validatePagesNameTreeValue: value is nil")
	}

	_, err = validateNameEntry(xRefTable, d, "templateDict", "Type", REQUIRED, V10, func(s string) bool { return s == "Template" })

	return err
}

func validateURLAliasDict(xRefTable *XRefTable, d Dict) error {
	dictName := "urlAliasDict"

	// U, required, ASCII string
	_, err := validateStringEntry(xRefTable, d, dictName, "U", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// C, optional, array of strings
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "C", OPTIONAL, V10, nil)

	return err
}

func validateCommandSettingsDict(xRefTable *XRefTable, d Dict) error {
	// see 14.10.5.4

	dictName := "cmdSettingsDict"

	// G, optional, dict
	_, err := validateDictEntry(xRefTable, d, dictName, "G", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// C, optional, dict
	_, err = validateDictEntry(xRefTable, d, dictName, "C", OPTIONAL, V10, nil)

	return err
}

func validateStringOrStreamEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStringOrStreamEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateStringOrStreamEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateStringOrStreamEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	switch o.(type) {

	case StringLiteral, HexLiteral, StreamDict:
		// no further processing

	default:
		return errors.Errorf("pdfcpu: validateStringOrStreamEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStringOrStreamEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateCaptureCommandDict(xRefTable *XRefTable, d Dict) error {
	dictName := "captureCommandDict"

	// URL, required, string
	_, err := validateStringEntry(xRefTable, d, dictName, "URL", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// L, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "L", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// F, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "F", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// P, optional, string or stream
	err = validateStringOrStreamEntry(xRefTable, d, dictName, "P", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// CT, optional, ASCII string
	_, err = validateStringEntry(xRefTable, d, dictName, "CT", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// H, optional, string
	_, err = validateStringEntry(xRefTable, d, dictName, "H", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// S, optional, command settings dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "S", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateCommandSettingsDict(xRefTable, d1)
	}

	return err
}

func validateSourceInfoDictEntryAU(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case StringLiteral, HexLiteral:
		// no further processing

	case Dict:
		err = validateURLAliasDict(xRefTable, o)
		if err != nil {
			return err
		}

	default:
		return errors.New("pdfcpu: validateSourceInfoDict: entry \"AU\" must be string or dict")

	}

	return nil
}

func validateIndRefEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) (*IndirectRef, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIndRefEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	ir, ok := o.(IndirectRef)
	if !ok {
		return nil, errors.Errorf("pdfcpu: validateIndRefEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIndRefEntry end: entry=%s\n", entryName)
	// }

	return &ir, nil
}

func validateSourceInfoDict(xRefTable *XRefTable, d Dict) error {
	dictName := "sourceInfoDict"

	// AU, required, ASCII string or dict
	err := validateSourceInfoDictEntryAU(xRefTable, d, dictName, "AU", REQUIRED, V10)
	if err != nil {
		return err
	}

	// E, optional, date
	_, err = validateDateEntry(xRefTable, d, dictName, "E", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// S, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "S", OPTIONAL, V10, func(i int) bool { return 0 <= i && i <= 2 })
	if err != nil {
		return err
	}

	// C, optional, indRef of command dict
	ir, err := validateIndRefEntry(xRefTable, d, dictName, "C", OPTIONAL, V10)
	if err != nil {
		return err
	}

	if ir != nil {

		d1, err := xRefTable.DereferenceDict(*ir)
		if err != nil {
			return err
		}

		return validateCaptureCommandDict(xRefTable, d1)

	}

	return nil
}

func validateEntrySI(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see 14.10.5, table 355, source information dictionary

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Dict:
		err = validateSourceInfoDict(xRefTable, o)
		if err != nil {
			return err
		}

	case Array:

		for _, v := range o {

			if v == nil {
				continue
			}

			d1, err := xRefTable.DereferenceDict(v)
			if err != nil {
				return err
			}

			err = validateSourceInfoDict(xRefTable, d1)
			if err != nil {
				return err
			}

		}

	}

	return nil
}

func validateIntegerOrArrayOfInteger(xRefTable *XRefTable, o Object, dictName, entryName string) error {
	switch o := o.(type) {

	case Integer:
		// no further processing

	case Array:

		for i, o := range o {

			o, err := xRefTable.Dereference(o)
			if err != nil {
				return err
			}

			if o == nil {
				continue
			}

			if _, ok := o.(Integer); !ok {
				return errors.Errorf("pdfcpu: validateIntegerOrArrayOfInteger: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
			}

		}

	default:
		return errors.Errorf("pdfcpu: validateIntegerOrArrayOfInteger: dict=%s entry=%s invalid type", dictName, entryName)
	}

	return nil
}

func validateIntegerOrArrayOfIntegerEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntegerOrArrayOfIntegerEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateIntegerOrArrayOfIntegerEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateIntegerOrArrayOfIntegerEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	if err := validateIntegerOrArrayOfInteger(xRefTable, o, dictName, entryName); err != nil {
		return err
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntegerOrArrayOfIntegerEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateWebCaptureContentSetDict(XRefTable *XRefTable, d Dict) error {
	// see 14.10.4

	dictName := "webCaptureContentSetDict"

	// Type, optional, name
	_, err := validateNameEntry(XRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "SpiderContentSet" })
	if err != nil {
		return err
	}

	// S, required, name
	s, err := validateNameEntry(XRefTable, d, dictName, "S", REQUIRED, V10, func(s string) bool { return s == "SPS" || s == "SIS" })
	if err != nil {
		return err
	}

	// ID, required, byte string
	_, err = validateStringEntry(XRefTable, d, dictName, "ID", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// O, required, array of indirect references.
	_, err = validateIndRefArrayEntry(XRefTable, d, dictName, "O", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// SI, required, source info dict or array of source info dicts
	err = validateEntrySI(XRefTable, d, dictName, "SI", REQUIRED, V10)
	if err != nil {
		return err
	}

	// CT, optional, string
	_, err = validateStringEntry(XRefTable, d, dictName, "CT", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// TS, optional, date
	_, err = validateDateEntry(XRefTable, d, dictName, "TS", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// spider page set
	if *s == "SPS" {

		// T, optional, string
		_, err = validateStringEntry(XRefTable, d, dictName, "T", OPTIONAL, V10, nil)
		if err != nil {
			return err
		}

		// TID, optional, byte string
		_, err = validateStringEntry(XRefTable, d, dictName, "TID", OPTIONAL, V10, nil)
		if err != nil {
			return err
		}
	}

	// spider image set
	if *s == "SIS" {
		// R, required, integer or array of integers
		err = validateIntegerOrArrayOfIntegerEntry(XRefTable, d, dictName, "R", REQUIRED, V10)
	}

	return err
}

func validateIDSNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 14.10.4

	// Version check
	err := xRefTable.ValidateVersion("IDSNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	// Value is a web capture content set.
	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	return validateWebCaptureContentSetDict(xRefTable, d)
}

func validateURLSNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 14.10.4

	// Version check
	err := xRefTable.ValidateVersion("URLSNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	// Value is a web capture content set.
	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	return validateWebCaptureContentSetDict(xRefTable, d)
}

func validateEmbeddedFilesNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 7.11.4

	// Value is a file specification for an embedded file stream.

	// Version check
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	err := xRefTable.ValidateVersion("EmbeddedFilesNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	if o == nil {
		return nil
	}

	_, err = validateFileSpecification(xRefTable, o)

	return err
}

func validateSlideShowDict(XRefTable *XRefTable, d Dict) error {
	// see 13.5, table 297

	dictName := "slideShowDict"

	// Type, required, name, since V1.4
	_, err := validateNameEntry(XRefTable, d, dictName, "Type", REQUIRED, V14, func(s string) bool { return s == "SlideShow" })
	if err != nil {
		return err
	}

	// Subtype, required, name, since V1.4
	_, err = validateNameEntry(XRefTable, d, dictName, "Subtype", REQUIRED, V14, func(s string) bool { return s == "Embedded" })
	if err != nil {
		return err
	}

	// Resources, required, name tree, since V1.4
	// Note: This is really an array of (string,indRef) pairs.
	_, err = validateArrayEntry(XRefTable, d, dictName, "Resources", REQUIRED, V14, nil)
	if err != nil {
		return err
	}

	// StartResource, required, byte string, since V1.4
	_, err = validateStringEntry(XRefTable, d, dictName, "StartResource", REQUIRED, V14, nil)

	return err
}

func validateAlternatePresentationsNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 13.5

	// Value is a slide show dict.

	// Version check
	err := xRefTable.ValidateVersion("AlternatePresentationsNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return err
	}

	if d != nil {
		err = validateSlideShowDict(xRefTable, d)
	}

	return err
}

func validateSelectorRenditionDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// table 272

	dictName := "selectorRendDict"

	a, err := validateArrayEntry(xRefTable, d, dictName, "R", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	for _, v := range a {

		if v == nil {
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateRenditionDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateMinimumBitDepthDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see table 269

	dictName := "minBitDepthDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MinBitDepth" })
	if err != nil {
		return err
	}

	// V, required, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "V", REQUIRED, sinceVersion, func(i int) bool { return i >= 0 })
	if err != nil {
		return err
	}

	// M, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "M", OPTIONAL, sinceVersion, nil)

	return err
}

func validateMediaCriteriaDictEntryD(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "D", required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateMinimumBitDepthDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateMinimumScreenSizeDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see table 269

	dictName := "minBitDepthDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MinScreenSize" })
	if err != nil {
		return err
	}

	// V, required, integer array, length 2
	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "V", REQUIRED, sinceVersion, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// M, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "M", OPTIONAL, sinceVersion, nil)

	return err
}

func validateMediaCriteriaDictEntryZ(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "Z", required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateMinimumScreenSizeDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateSoftwareIdentifierDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see table 292

	dictName := "swIdDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "SoftwareIdentifier" })
	if err != nil {
		return err
	}

	// U, required, ASCII string
	_, err = validateStringEntry(xRefTable, d, dictName, "U", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// L, optional, array
	_, err = validateArrayEntry(xRefTable, d, dictName, "L", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// LI, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "LI", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// H, optional, array
	_, err = validateArrayEntry(xRefTable, d, dictName, "H", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// HI, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "HI", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// OS, optional, array
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "OS", OPTIONAL, sinceVersion, nil)

	return err
}

func validateMediaCriteriaDictEntryV(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, "V", required, sinceVersion, nil)
	if err != nil {
		return err
	}

	for _, v := range a {

		if v == nil {
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d != nil {
			err = validateSoftwareIdentifierDict(xRefTable, d, sinceVersion)
			if err != nil {
				return err
			}
		}

	}

	return nil
}

func validateMediaCriteriaDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see table 268

	dictName := "mediaCritDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaCriteria" })
	if err != nil {
		return err
	}

	// A, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "A", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// C, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "C", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// O, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "O", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// S, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "S", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// R, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "R", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// D, optional, dict
	err = validateMediaCriteriaDictEntryD(xRefTable, d, dictName, OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// Z, optional, dict
	err = validateMediaCriteriaDictEntryZ(xRefTable, d, dictName, OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// V, optional, array
	err = validateMediaCriteriaDictEntryV(xRefTable, d, dictName, OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// P, optional, array
	_, err = validateNameArrayEntry(xRefTable, d, dictName, "P", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 1 || len(a) == 2 })
	if err != nil {
		return err
	}

	// L, optional, array
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "L", OPTIONAL, sinceVersion, nil)

	return err
}

func validateMediaPermissionsDict(xRefTable *XRefTable, d Dict, dictName string, sinceVersion Version) error {
	// see table 275
	d1, err := validateDictEntry(xRefTable, d, dictName, "P", OPTIONAL, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "mediaPermissionDict"

	// Type, optional, name
	_, err = validateNameEntry(xRefTable, d1, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaPermissions" })
	if err != nil {
		return err
	}

	// TF, optional, ASCII string
	validateTempFilePolicy := func(s string) bool {
		return MemberOf(s, []string{"TEMPNEVER", "TEMPEXTRACT", "TEMPACCESS", "TEMPALWAYS"})
	}
	_, err = validateStringEntry(xRefTable, d1, dictName, "TF", OPTIONAL, sinceVersion, validateTempFilePolicy)

	return err
}

func validateMediaPlayerInfoDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see table 291

	dictName := "mediaPlayerInfoDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaPlayerInfo" })
	if err != nil {
		return err
	}

	// PID, required, software identifier dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "PID", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}
	err = validateSoftwareIdentifierDict(xRefTable, d1, sinceVersion)
	if err != nil {
		return err
	}

	// MH, optional, dict
	_, err = validateDictEntry(xRefTable, d, dictName, "MH", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// BE, optional, dict
	_, err = validateDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion, nil)

	return err
}

func validateMediaPlayersDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.7.2

	dictName := "mediaPlayersDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaPlayers" })
	if err != nil {
		return err
	}

	// MU, optional, array of media player info dicts
	a, err := validateArrayEntry(xRefTable, d, dictName, "MU", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	for _, v := range a {

		if v == nil {
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateMediaPlayerInfoDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateFileSpecOrFormXObjectEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	return validateFileSpecificationOrFormObject(xRefTable, o)
}

func validateMediaClipDataDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.4.2

	dictName := "mediaClipDataDict"

	// D, required, file specification or stream
	err := validateFileSpecOrFormXObjectEntry(xRefTable, d, dictName, "D", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// CT, optional, ASCII string
	_, err = validateStringEntry(xRefTable, d, dictName, "CT", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// P, optional, media permissions dict
	err = validateMediaPermissionsDict(xRefTable, d, dictName, sinceVersion)
	if err != nil {
		return err
	}

	// Alt, optional, string array
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "Alt", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// PL, optional, media players dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "PL", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaPlayersDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// MH, optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "MH", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		// BU, optional, ASCII string
		_, err = validateStringEntry(xRefTable, d1, "", "BU", OPTIONAL, sinceVersion, nil)
		if err != nil {
			return err
		}
	}

	// BE. optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		// BU, optional, ASCII string
		_, err = validateStringEntry(xRefTable, d1, "", "BU", OPTIONAL, sinceVersion, nil)
	}

	return err
}

func validateTimespanDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "timespanDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Timespan" })
	if err != nil {
		return err
	}

	// S, required, name
	_, err = validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, sinceVersion, func(s string) bool { return s == "S" })
	if err != nil {
		return err
	}

	// V, required, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "V", REQUIRED, sinceVersion, nil)

	return err
}

func validateMediaOffsetDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.6.2

	dictName := "mediaOffsetDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaOffset" })
	if err != nil {
		return err
	}

	// S, required, name
	subType, err := validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, sinceVersion, func(s string) bool { return MemberOf(s, []string{"T", "F", "M"}) })
	if err != nil {
		return err
	}

	switch *subType {

	case "T":
		d1, err := validateDictEntry(xRefTable, d, dictName, "T", REQUIRED, sinceVersion, nil)
		if err != nil {
			return err
		}
		err = validateTimespanDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}

	case "F":
		_, err = validateIntegerEntry(xRefTable, d, dictName, "F", REQUIRED, sinceVersion, func(i int) bool { return i >= 0 })
		if err != nil {
			return err
		}

	case "M":
		_, err = validateStringEntry(xRefTable, d, dictName, "M", REQUIRED, sinceVersion, nil)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateMediaClipSectionDictMHBE(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "mediaClipSectionMHBE"

	d1, err := validateDictEntry(xRefTable, d, dictName, "B", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaOffsetDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	d1, err = validateDictEntry(xRefTable, d, dictName, "E", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaOffsetDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateMediaClipSectionDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.4.3

	dictName := "mediaClipSectionDict"

	// D, required, media clip dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "D", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}
	err = validateMediaClipDict(xRefTable, d1, sinceVersion)
	if err != nil {
		return err
	}

	// Alt, optional, string array
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "Alt", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// MH, optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "MH", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaClipSectionDictMHBE(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// BE, optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaClipSectionDictMHBE(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateMediaClipDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.4

	dictName := "mediaClipDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaClip" })
	if err != nil {
		return err
	}

	// S, required, name
	subType, err := validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, sinceVersion, func(s string) bool { return s == "MCD" || s == "MCS" })
	if err != nil {
		return err
	}

	// N, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "N", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if *subType == "MCD" {
		err = validateMediaClipDataDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}
	}

	if *subType == "MCS" {
		err = validateMediaClipSectionDict(xRefTable, d, sinceVersion)
	}

	return err
}

func validateMediaDurationDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "mediaDurationDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaDuration" })
	if err != nil {
		return err
	}

	// S, required, name
	validate := func(s string) bool { return MemberOf(s, []string{"I", "F", "T"}) }
	s, err := validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, sinceVersion, validate)
	if err != nil {
		return err
	}

	// T, required if S == "T", timespann dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "T", *s == "T", sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateTimespanDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateMediaPlayParamsMHBEDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "mediaPlayParamsMHBEDict"

	// V, optional, integer
	_, err := validateIntegerEntry(xRefTable, d, dictName, "V", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// C, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "C", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// F, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "RT", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// D, optional, media duration dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "D", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaDurationDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// A, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "A", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// RC, optional, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "RC", OPTIONAL, sinceVersion, nil)

	return err
}

func validateMediaPlayParamsDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.5

	dictName := "mediaPlayParamsDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaPlayParams" })
	if err != nil {
		return err
	}

	// PL, optional, media players dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "PL", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaPlayersDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// MH, optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "MH", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaPlayParamsMHBEDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// BE, optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaPlayParamsMHBEDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateFloatingWindowsParameterDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see table 284

	dictName := "floatWinParamsDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "FWParams" })
	if err != nil {
		return err
	}

	// D, required, array of integers
	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "D", REQUIRED, sinceVersion, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// RT, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "RT", OPTIONAL, sinceVersion, func(i int) bool { return IntMemberOf(i, []int{0, 1, 2, 3}) })
	if err != nil {
		return err
	}

	// P, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "P", OPTIONAL, sinceVersion, func(i int) bool { return IntMemberOf(i, []int{0, 1, 2, 3, 4, 5, 6, 7, 8}) })
	if err != nil {
		return err
	}

	// O, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "O", OPTIONAL, sinceVersion, func(i int) bool { return IntMemberOf(i, []int{0, 1, 2}) })
	if err != nil {
		return err
	}

	// T, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "T", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// UC, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "UC", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// R, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "R", OPTIONAL, sinceVersion, func(i int) bool { return IntMemberOf(i, []int{0, 1, 2}) })
	if err != nil {
		return err
	}

	// TT, optional, string array
	_, err = validateStringArrayEntry(xRefTable, d, dictName, "TT", OPTIONAL, sinceVersion, nil)

	return err
}

func validateScreenParametersMHBEDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "screenParmsMHBEDict"

	w := 3

	// W, optional, integer
	i, err := validateIntegerEntry(xRefTable, d, dictName, "W", OPTIONAL, sinceVersion, func(i int) bool { return IntMemberOf(i, []int{0, 1, 2, 3}) })
	if err != nil {
		return err
	}
	if i != nil {
		w = (*i).Value()
	}

	// B, optional, array of 3 numbers
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "B", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	// O, optional, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "O", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// M, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "M", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// F, required if W == 0, floating windows parameter dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "F", w == 0, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateFloatingWindowsParameterDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateScreenParametersDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 13.2.

	dictName := "screenParmsDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "MediaScreenParams" })
	if err != nil {
		return err
	}

	// MH, optional, dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "MH", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateScreenParametersMHBEDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// BE. optional. dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateScreenParametersMHBEDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateMediaRenditionDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// table 271

	dictName := "mediaRendDict"

	// C, optional, dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "C", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaClipDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// P, required if C not present, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "P", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateMediaPlayParamsDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// SP, optional, dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "SP", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateScreenParametersDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateRenditionDictEntryMH(xRefTable *XRefTable, d Dict, dictName string, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "MH", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {

		d2, err := validateDictEntry(xRefTable, d1, "MHDict", "C", OPTIONAL, sinceVersion, nil)
		if err != nil {
			return err
		}

		if d2 != nil {
			return validateMediaCriteriaDict(xRefTable, d2, sinceVersion)
		}

	}

	return nil
}

func validateRenditionDictEntryBE(xRefTable *XRefTable, d Dict, dictName string, sinceVersion Version) (err error) {
	d1, err := validateDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {

		d2, err := validateDictEntry(xRefTable, d1, "BEDict", "C", OPTIONAL, sinceVersion, nil)
		if err != nil {
			return err
		}

		return validateMediaCriteriaDict(xRefTable, d2, sinceVersion)

	}

	return nil
}

func validateRenditionDict(xRefTable *XRefTable, d Dict, sinceVersion Version) (err error) {
	dictName := "renditionDict"

	// Type, optional, name
	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Rendition" })
	if err != nil {
		return err
	}

	// S, required, name
	renditionType, err := validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, sinceVersion, func(s string) bool { return s == "MR" || s == "SR" })
	if err != nil {
		return
	}

	// N, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "N", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// MH, optional, dict
	err = validateRenditionDictEntryMH(xRefTable, d, dictName, sinceVersion)
	if err != nil {
		return err
	}

	// BE, optional, dict
	err = validateRenditionDictEntryBE(xRefTable, d, dictName, sinceVersion)
	if err != nil {
		return err
	}

	if *renditionType == "MR" {
		err = validateMediaRenditionDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}
	}

	if *renditionType == "SR" {
		err = validateSelectorRenditionDict(xRefTable, d, sinceVersion)
	}

	return err
}

func validateRenditionsNameTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 13.2.3

	// Value is a rendition object.

	// Version check
	err := xRefTable.ValidateVersion("RenditionsNameTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return err
	}

	if d != nil {
		err = validateRenditionDict(xRefTable, d, sinceVersion)
	}

	return err
}

func validateIDTreeValue(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// Version check
	err := xRefTable.ValidateVersion("IDTreeValue", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	dictType := d.Type()
	if dictType == nil || *dictType == "StructElem" {
		err = validateStructElementDict(xRefTable, d)
		if err != nil {
			return err
		}
	} else {
		return errors.Errorf("pdfcpu: validateIDTreeValue: invalid dictType %s (should be \"StructElem\")\n", *dictType)
	}

	return nil
}

func validateNameTreeValue(name string, xRefTable *XRefTable, o Object) (err error) {
	// The values associated with the keys may be objects of any type.
	// Stream objects shall be specified by indirect object references.
	// Dictionary, array, and string objects should be specified by indirect object references.
	// Other PDF objects (nulls, numbers, booleans, and names) should be specified as direct objects.

	for k, v := range map[string]struct {
		validate     func(xRefTable *XRefTable, o Object, sinceVersion Version) error
		sinceVersion Version
	}{
		"Dests":                  {validateDestsNameTreeValue, V12},
		"AP":                     {validateAPNameTreeValue, V13},
		"JavaScript":             {validateJavaScriptNameTreeValue, V13},
		"Pages":                  {validatePagesNameTreeValue, V13},
		"Templates":              {validateTemplatesNameTreeValue, V13},
		"IDS":                    {validateIDSNameTreeValue, V13},
		"URLS":                   {validateURLSNameTreeValue, V13},
		"EmbeddedFiles":          {validateEmbeddedFilesNameTreeValue, V14},
		"AlternatePresentations": {validateAlternatePresentationsNameTreeValue, V14},
		"Renditions":             {validateRenditionsNameTreeValue, V15},
		"IDTree":                 {validateIDTreeValue, V13},
	} {
		if name == k {
			return v.validate(xRefTable, o, v.sinceVersion)
		}
	}

	return errors.Errorf("pdfcpu: validateNameTreeDictNamesEntry: unknown dict name: %s", name)
}

func validateNameTreeDictNamesEntry(xRefTable *XRefTable, d Dict, name string, node *Node) (string, string, error) {
	// fmt.Printf("validateNameTreeDictNamesEntry begin %s\n", d)

	// Names: array of the form [key1 value1 key2 value2 ... key n value n]
	o, found := d.Find("Names")
	if !found {
		return "", "", errors.Errorf("pdfcpu: validateNameTreeDictNamesEntry: missing \"Kids\" or \"Names\" entry.")
	}

	a, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return "", "", err
	}
	if a == nil {
		return "", "", errors.Errorf("pdfcpu: validateNameTreeDictNamesEntry: missing \"Names\" array.")
	}

	// arr length needs to be even because of contained key value pairs.
	if len(a)%2 == 1 {
		return "", "", errors.Errorf("pdfcpu: validateNameTreeDictNamesEntry: Names array entry length needs to be even, length=%d\n", len(a))
	}

	var key, firstKey, lastKey string

	for i := 0; i < len(a); i++ {
		o := a[i]

		if i%2 == 0 {

			// TODO Do we really need to process indRefs here?
			o, err = xRefTable.Dereference(o)
			if err != nil {
				return "", "", err
			}

			k, err := StringOrHexLiteral(o)
			if err != nil {
				return "", "", err
			}

			key = *k

			if firstKey == "" {
				firstKey = key
			}

			lastKey = key

			continue
		}

		err = validateNameTreeValue(name, xRefTable, o)
		if err != nil {
			return "", "", err
		}

		node.AppendToNames(key, o)

	}

	return firstKey, lastKey, nil
}

func validateNameTreeDictLimitsEntry(xRefTable *XRefTable, d Dict, firstKey, lastKey string) error {
	a, err := validateStringArrayEntry(xRefTable, d, "nameTreeDict", "Limits", REQUIRED, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	o, err := xRefTable.Dereference(a[0])
	if err != nil {
		return err
	}
	s, err := StringOrHexLiteral(o)
	if err != nil {
		return err
	}
	fkv := *s

	o, err = xRefTable.Dereference(a[1])
	if err != nil {
		return err
	}
	s, err = StringOrHexLiteral(o)
	if err != nil {
		return err
	}
	lkv := *s

	if xRefTable.ValidationMode == ValidationRelaxed {

		if fkv != firstKey && xRefTable.ValidationMode == ValidationRelaxed {
			fkv = firstKey
			a[0] = StringLiteral(fkv)
		}

		if lkv != lastKey && xRefTable.ValidationMode == ValidationRelaxed {
			lkv = lastKey
			a[1] = StringLiteral(lkv)
		}

	}

	if firstKey != fkv || lastKey != lkv {
		return errors.Errorf("pdfcpu: validateNameTreeDictLimitsEntry: invalid leaf node (firstKey: %s vs %s) (lastKey: %s vs %s)\n", firstKey, fkv, lastKey, lkv)
	}

	return nil
}

func validateNameTree(xRefTable *XRefTable, name string, d Dict, root bool) (string, string, *Node, error) {
	// fmt.Printf("validateNameTree begin %s\n", d)

	// see 7.7.4

	// A node has "Kids" or "Names" entry.

	// fmt.Printf("validateNameTree %s\n", name)

	node := &Node{D: d}
	var kmin, kmax string
	var err error

	// Kids: array of indirect references to the immediate children of this node.
	// if Kids present then recurse
	if o, found := d.Find("Kids"); found {

		// Intermediate node

		a, err := xRefTable.DereferenceArray(o)
		if err != nil {
			return "", "", nil, err
		}

		if len(a) == 0 {
			if xRefTable.ValidationMode == ValidationStrict {
				return "", "", nil, errors.New("pdfcpu: validateNameTree: missing \"Kids\" array")
			}
			return "", "", nil, nil
		}

		for _, o := range a {

			d, err := xRefTable.DereferenceDict(o)
			if err != nil {
				return "", "", nil, err
			}

			var kminKid string
			var kidNode *Node
			kminKid, kmax, kidNode, err = validateNameTree(xRefTable, name, d, false)
			if err != nil {
				if xRefTable.ValidationMode == ValidationStrict {
					return "", "", nil, err
				}
				continue
			}
			if kmin == "" {
				kmin = kminKid
			}

			node.Kids = append(node.Kids, kidNode)
		}

	} else {

		// Leaf node
		kmin, kmax, err = validateNameTreeDictNamesEntry(xRefTable, d, name, node)
		if err != nil {
			return "", "", nil, err
		}
	}

	if !root {

		// Verify calculated key range.
		err = validateNameTreeDictLimitsEntry(xRefTable, d, kmin, kmax)
		if err != nil {
			return "", "", nil, err
		}
	}

	// We track limits for all nodes internally.
	node.Kmin = kmin
	node.Kmax = kmax

	// fmt.Println("validateNameTree end")

	return kmin, kmax, node, nil
}

func validateNames(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 7.7.4 Name Dictionary

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "Names", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	validateNameTreeName := func(s string) bool {
		return MemberOf(s, []string{
			"Dests", "AP", "JavaScript", "Pages", "Templates", "IDS",
			"URLS", "EmbeddedFiles", "AlternatePresentations", "Renditions",
		})
	}

	d1 := Dict{}

	for treeName, value := range d {

		if ok := validateNameTreeName(treeName); !ok {
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.Errorf("validateNames: unknown name tree name: %s\n", treeName)
			}
			continue
		}

		if xRefTable.Names[treeName] != nil {
			// Already internalized.
			continue
		}

		d, err := xRefTable.DereferenceDict(value)
		if err != nil {
			return err
		}
		if len(d) == 0 {
			continue
		}

		_, _, tree, err := validateNameTree(xRefTable, treeName, d, true)
		if err != nil {
			return err
		}

		if tree != nil && tree.Kmin != "" && tree.Kmax != "" {
			// Internalize.
			xRefTable.Names[treeName] = tree
			d1.Insert(treeName, value)
		}

	}

	delete(rootDict, "Names")
	if len(d1) > 0 {
		rootDict["Names"] = d1
	}

	return nil
}

func validateNamedDestinations(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) (err error) {
	// => 12.3.2.3 Named Destinations

	// indRef or dict with destination array values.

	xRefTable.Dests, err = validateDictEntry(xRefTable, rootDict, "rootDict", "Dests", required, sinceVersion, nil)
	if err != nil || xRefTable.Dests == nil {
		return err
	}

	for _, o := range xRefTable.Dests {
		if _, err = validateDestination(xRefTable, o, false); err != nil {
			return err
		}
	}

	return nil
}

func pageLayoutValidator(v Version) func(s string) bool {
	layouts := []string{"SinglePage", "OneColumn", "TwoColumnLeft", "TwoColumnRight"}
	if v >= V15 {
		layouts = append(layouts, "TwoPageLeft", "TwoPageRight")
	}
	validate := func(s string) bool {
		return MemberOf(s, layouts)
	}
	return validate
}

func validatePageLayout(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	n, err := validateNameEntry(xRefTable, rootDict, "rootDict", "PageLayout", required, sinceVersion, pageLayoutValidator(xRefTable.Version()))
	if err != nil {
		return err
	}

	if n != nil {
		xRefTable.PageLayout = PageLayoutFor(n.String())
	}

	return nil
}

func pageModeValidator(v Version) func(s string) bool {
	// "None" is out of spec - but no need to repair.
	modes := []string{"UseNone", "UseOutlines", "UseThumbs", "FullScreen", "None"}
	if v >= V15 {
		modes = append(modes, "UseOC")
	}
	if v >= V16 {
		modes = append(modes, "UseAttachments")
	}
	return func(s string) bool { return MemberOf(s, modes) }
}

func validatePageMode(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	n, err := validateNameEntry(xRefTable, rootDict, "rootDict", "PageMode", required, sinceVersion, pageModeValidator(xRefTable.Version()))
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict || n == nil {
			return err
		}
		// Relax validation of "UseAttachments" before PDF v1.6.
		if *n != "UseAttachments" {
			return err
		}
	}

	if n != nil {
		xRefTable.PageMode = PageModeFor(n.String())
	}

	return nil
}

func validateGoToActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.2 Go-To Actions
	required := REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}

	// D, required, name, byte string or array
	return validateActionDestinationEntry(xRefTable, d, dictName, "D", required, V10)
}

func validateGoToRActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.3 Remote Go-To Actions

	// F, required, file specification
	_, err := validateFileSpecEntry(xRefTable, d, dictName, "F", REQUIRED, V11)
	if err != nil {
		return err
	}

	// D, required, name, byte string or array
	err = validateActionDestinationEntry(xRefTable, d, dictName, "D", REQUIRED, V10)
	if err != nil {
		return err
	}

	// NewWindow, optional, boolean, since V1.2
	_, err = validateBooleanEntry(xRefTable, d, dictName, "NewWindow", OPTIONAL, V12, nil)

	return err
}

func validateIntOrStringEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntOrStringEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateIntOrStringEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateIntOrStringEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	switch o.(type) {

	case StringLiteral, HexLiteral, Integer:
		// no further processing

	default:
		return errors.Errorf("pdfcpu: validateIntOrStringEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateIntOrStringEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateTargetDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// table 202

	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "targetDict"

	// R, required, name
	_, err = validateNameEntry(xRefTable, d1, dictName, "R", REQUIRED, V10, func(s string) bool { return s == "P" || s == "C" })
	if err != nil {
		return err
	}

	// N, optional, byte string
	_, err = validateStringEntry(xRefTable, d1, dictName, "N", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// P, optional, integer or byte string
	err = validateIntOrStringEntry(xRefTable, d1, dictName, "P", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// A, optional, integer or text string
	err = validateIntOrStringEntry(xRefTable, d1, dictName, "A", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// T, optional, target dict
	return validateTargetDictEntry(xRefTable, d1, dictName, "T", OPTIONAL, V10)
}

func validateGoToEActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.4 Embedded Go-To Actions

	// F, optional, file specification
	f, err := validateFileSpecEntry(xRefTable, d, dictName, "F", OPTIONAL, V11)
	if err != nil {
		return err
	}

	// D, required, name, byte string or array
	err = validateActionDestinationEntry(xRefTable, d, dictName, "D", REQUIRED, V10)
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
		if err = validateActionDestinationEntry(xRefTable, d, dictName, "Dest", REQUIRED, V10); err != nil {
			return err
		}
		d["D"] = d["Dest"]
		delete(d, "Dest")
	}

	// NewWindow, optional, boolean, since V1.2
	_, err = validateBooleanEntry(xRefTable, d, dictName, "NewWindow", OPTIONAL, V12, nil)
	if err != nil {
		return err
	}

	// T, required unless entry F is present, target dict
	return validateTargetDictEntry(xRefTable, d, dictName, "T", f == nil, V10)
}

func validateWinDict(xRefTable *XRefTable, d Dict) error {
	// see table 204

	dictName := "winDict"

	// F, required, byte string
	_, err := validateStringEntry(xRefTable, d, dictName, "F", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// D, optional, byte string
	_, err = validateStringEntry(xRefTable, d, dictName, "D", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// O, optional, ASCII string
	_, err = validateStringEntry(xRefTable, d, dictName, "O", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// P, optional, byte string
	_, err = validateStringEntry(xRefTable, d, dictName, "P", OPTIONAL, V10, nil)

	return err
}

func validateLaunchActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.5

	// F, optional, file specification
	_, err := validateFileSpecEntry(xRefTable, d, dictName, "F", OPTIONAL, V11)
	if err != nil {
		return err
	}

	// Win, optional, dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "Win", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateWinDict(xRefTable, d1)
	}

	// Mac, optional, undefined dict

	// Unix, optional, undefined dict

	return err
}

func validateDestinationThreadEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// The destination thread (table 205)

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o.(type) {

	case Dict, StringLiteral, Integer:
		// an indRef to a thread dictionary
		// or an index of the thread within the roots Threads array
		// or the title of the thread as specified in its thread info dict

	default:
		return errors.Errorf("validateDestinationThreadEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	return nil
}

func validateDestinationBeadEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// The bead in the destination thread (table 205)

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o.(type) {

	case Dict, Integer:
		// an indRef to a bead dictionary of a thread in the current file
		// or an index of the thread within its thread

	default:
		return errors.Errorf("validateDestinationBeadEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	return nil
}

func validateThreadActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.6

	// F, optional, file specification
	_, err := validateFileSpecEntry(xRefTable, d, dictName, "F", OPTIONAL, V11)
	if err != nil {
		return err
	}

	// D, required, indRef to thread dict, integer or text string.
	err = validateDestinationThreadEntry(xRefTable, d, dictName, "D", REQUIRED, V10)
	if err != nil {
		return err
	}

	// B, optional, indRef to bead dict or integer.
	return validateDestinationBeadEntry(xRefTable, d, dictName, "B", OPTIONAL, V10)
}

func hasURIForChecking(xRefTable *XRefTable, s string) bool {
	for _, links := range xRefTable.URIs {
		for uri := range links {
			if uri == s {
				return true
			}
		}
	}
	return false
}

func validateURIActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.7

	// URI, required, string
	uri, err := validateStringEntry(xRefTable, d, dictName, "URI", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// Record URIs for link checking.
	if xRefTable.ValidateLinks && uri != nil &&
		strings.HasPrefix(*uri, "http") && !hasURIForChecking(xRefTable, *uri) {
		if len(xRefTable.URIs[xRefTable.CurPage]) == 0 {
			xRefTable.URIs[xRefTable.CurPage] = map[string]string{}
		}
		xRefTable.URIs[xRefTable.CurPage][*uri] = ""
	}

	// IsMap, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "IsMap", OPTIONAL, V10, nil)

	return err
}

func validateSoundDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	sd, err := validateStreamDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || sd == nil {
		return err
	}

	dictName = "soundDict"

	// Type, optional, name
	_, err = validateNameEntry(xRefTable, sd.Dict, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "Sound" })
	if err != nil {
		return err
	}

	// R, required, number - sampling rate
	_, err = validateNumberEntry(xRefTable, sd.Dict, dictName, "R", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// C, required, integer - # of sound channels
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "C", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// B, required, integer - bits per sample value per channel
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "B", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// E, optional, name - encoding format
	validateSampleDataEncoding := func(s string) bool {
		return MemberOf(s, []string{"Raw", "Signed", "muLaw", "ALaw"})
	}
	_, err = validateNameEntry(xRefTable, sd.Dict, dictName, "E", OPTIONAL, V10, validateSampleDataEncoding)

	return err
}

func validateSoundActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.8

	// Sound, required, stream dict
	err := validateSoundDictEntry(xRefTable, d, dictName, "Sound", REQUIRED, V10)
	if err != nil {
		return err
	}

	// Volume, optional, number: -1.0 .. +1.0
	_, err = validateNumberEntry(xRefTable, d, dictName, "Volume", OPTIONAL, V10, func(f float64) bool { return -1.0 <= f && f <= 1.0 })
	if err != nil {
		return err
	}

	// Synchronous, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Synchronous", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Repeat, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Repeat", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Mix, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Mix", OPTIONAL, V10, nil)

	return err
}

func validateMovieStartOrDurationEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Integer, StringLiteral:
		// no further processing

	case Array:
		if len(o) != 2 {
			return errors.New("pdfcpu: validateMovieStartOrDurationEntry: array length <> 2")
		}
	}

	return nil
}

func validateMovieActivationDict(xRefTable *XRefTable, d Dict) error {
	dictName := "movieActivationDict"

	// Start, optional
	err := validateMovieStartOrDurationEntry(xRefTable, d, dictName, "Start", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// Duration, optional
	err = validateMovieStartOrDurationEntry(xRefTable, d, dictName, "Duration", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// Rate, optional, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "Rate", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Volume, optional, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "Volume", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// ShowControls, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "ShowControls", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Mode, optional, name
	validatePlayMode := func(s string) bool {
		return MemberOf(s, []string{"Once", "Open", "Repeat", "Palindrome"})
	}
	_, err = validateNameEntry(xRefTable, d, dictName, "Mode", OPTIONAL, V10, validatePlayMode)
	if err != nil {
		return err
	}

	// Synchronous, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Synchronous", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// FWScale, optional, array of 2 positive integers
	_, err = validateIntegerArrayEntry(xRefTable, d, dictName, "FWScale", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// FWPosition, optional, array of 2 numbers [0.0 .. 1.0]
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "FWPosition", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })

	return err
}

func validateMovieActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.9

	// is a movie activation dict
	err := validateMovieActivationDict(xRefTable, d)
	if err != nil {
		return err
	}

	// Needs either Annotation or T entry but not both.

	// T, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "T", OPTIONAL, V10, nil)
	if err == nil {
		return nil
	}

	// Annotation, indRef of movie annotation dict
	ir, err := validateIndRefEntry(xRefTable, d, dictName, "Annotation", REQUIRED, V10)
	if err != nil || ir == nil {
		return err
	}

	d, err = xRefTable.DereferenceDict(*ir)
	if err != nil || d == nil {
		return errors.New("pdfcpu: validateMovieActionDict: missing required entry \"T\" or \"Annotation\"")
	}

	_, err = validateNameEntry(xRefTable, d, "annotDict", "Subtype", REQUIRED, V10, func(s string) bool { return s == "Movie" })

	return err
}

func validateHideActionDictEntryT(xRefTable *XRefTable, o Object) error {
	switch o := o.(type) {

	case StringLiteral:
		// Ensure UTF16 correctness.
		_, err := StringLiteralToString(o)
		if err != nil {
			return err
		}

	case Dict:
		// annotDict,  Check for required name Subtype
		_, err := validateNameEntry(xRefTable, o, "annotDict", "Subtype", REQUIRED, V10, nil)
		if err != nil {
			return err
		}

	case Array:
		// mixed array of annotationDict indRefs and strings
		for _, v := range o {

			o, err := xRefTable.Dereference(v)
			if err != nil {
				return err
			}

			if o == nil {
				continue
			}

			switch o := o.(type) {

			case StringLiteral:
				// Ensure UTF16 correctness.
				_, err = StringLiteralToString(o)
				if err != nil {
					return err
				}

			case Dict:
				// annotDict,  Check for required name Subtype
				_, err = validateNameEntry(xRefTable, o, "annotDict", "Subtype", REQUIRED, V10, nil)
				if err != nil {
					return err
				}
			}
		}

	default:
		return errors.Errorf("validateHideActionDict: invalid entry \"T\"")

	}

	return nil
}

func validateHideActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.10

	// T, required, dict, text string or array
	o, found := d.Find("T")
	if !found || o == nil {
		return errors.New("pdfcpu: validateHideActionDict: missing required entry \"T\"")
	}

	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	err = validateHideActionDictEntryT(xRefTable, o)
	if err != nil {
		return err
	}

	// H, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "H", OPTIONAL, V10, nil)

	return err
}

func validateNamedActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.11

	validate := func(s string) bool {
		if MemberOf(s, []string{"NextPage", "PrevPage", "FirstPage", "LastPage"}) {
			return true
		}

		// Some known non standard named actions
		if MemberOf(s, []string{"GoToPage", "GoBack", "GoForward", "Find", "Print", "SaveAs", "Quit", "FullScreen"}) {
			return true
		}

		return false
	}

	_, err := validateNameEntry(xRefTable, d, dictName, "N", REQUIRED, V10, validate)

	return err
}

func validateSubmitFormActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.7.5.2

	// F, required, URL specification
	_, err := validateURLSpecEntry(xRefTable, d, dictName, "F", REQUIRED, V10)
	if err != nil {
		return err
	}

	// Fields, optional, array
	// Each element of the array shall be either an indirect reference to a field dictionary
	// or (PDF 1.3) a text string representing the fully qualified name of a field.
	a, err := validateArrayEntry(xRefTable, d, dictName, "Fields", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	for _, v := range a {
		switch v.(type) {
		case StringLiteral, IndirectRef:
			// no further processing

		default:
			return errors.New("pdfcpu: validateSubmitFormActionDict: unknown Fields entry")
		}
	}

	// Flags, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "Flags", OPTIONAL, V10, nil)

	return err
}

func validateResetFormActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.7.5.3

	// Fields, optional, array
	// Each element of the array shall be either an indirect reference to a field dictionary
	// or (PDF 1.3) a text string representing the fully qualified name of a field.
	a, err := validateArrayEntry(xRefTable, d, dictName, "Fields", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	for _, v := range a {
		switch v.(type) {
		case StringLiteral, IndirectRef:
			// no further processing

		default:
			return errors.New("pdfcpu: validateResetFormActionDict: unknown Fields entry")
		}
	}

	// Flags, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "Flags", OPTIONAL, V10, nil)

	return err
}

func validateImportDataActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.7.5.4

	// F, required, file specification
	_, err := validateFileSpecEntry(xRefTable, d, dictName, "F", OPTIONAL, V11)

	return err
}

func validateSetOCGStateActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.12

	// State, required, array
	_, err := validateArrayEntry(xRefTable, d, dictName, "State", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// PreserveRB, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "PreserveRB", OPTIONAL, V10, nil)

	return err
}

func validateRenditionActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.13

	// OP or JS need to be present.

	// OP, integer
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	op, err := validateIntegerEntry(xRefTable, d, dictName, "OP", OPTIONAL, sinceVersion, func(i int) bool { return 0 <= i && i <= 4 })
	if err != nil {
		return err
	}

	// JS, text string or stream
	err = validateJavaScript(xRefTable, d, dictName, "JS", op == nil)
	if err != nil {
		return err
	}

	// R, required for OP 0 and 4, rendition object dict
	required := func(op *Integer) bool {
		if op == nil {
			return false
		}
		v := op.Value()
		return v == 0 || v == 4
	}(op)

	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	d1, err := validateDictEntry(xRefTable, d, dictName, "R", required, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateRenditionDict(xRefTable, d1, sinceVersion)
		if err != nil {
			return err
		}
	}

	// AN, required for any OP 0..4, indRef of screen annotation dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "AN", op != nil, V10, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		_, err = validateNameEntry(xRefTable, d1, dictName, "Subtype", REQUIRED, V10, func(s string) bool { return s == "Screen" })
		if err != nil {
			return err
		}
	}

	return nil
}

func validateTransActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.14

	// Trans, required, transitionDict
	d1, err := validateDictEntry(xRefTable, d, dictName, "Trans", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	return validateTransitionDict(xRefTable, d1)
}

var errInvalidPageAnnotArray = errors.New("pdfcpu: validatePageAnnotations: page annotation array without indirect references.")

func validateBorderEffectDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see 12.5.4

	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "borderEffectDict"

	// S, optional, name, S or C
	if _, err = validateNameEntry(xRefTable, d1, dictName, "S", OPTIONAL, V10, func(s string) bool { return s == "S" || s == "C" }); err != nil {
		return err
	}

	// I, optional, number in the range 0 to 2
	if _, err = validateNumberEntry(xRefTable, d1, dictName, "I", OPTIONAL, V10, func(f float64) bool { return 0 <= f && f <= 2 }); err != nil {
		return err
	}

	return nil
}

func validateBorderStyleDict(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see 12.5.4

	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "borderStyleDict"

	// Type, optional, name, "Border"
	if _, err = validateNameEntry(xRefTable, d1, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "Border" }); err != nil {
		return err
	}

	// W, optional, number, border width in points
	if _, err = validateNumberEntry(xRefTable, d1, dictName, "W", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// S, optional, name, border style
	validate := func(s string) bool { return MemberOf(s, []string{"S", "D", "B", "I", "U", "A"}) }
	if _, err = validateNameEntry(xRefTable, d1, dictName, "S", OPTIONAL, V10, validate); err != nil {
		if !strings.Contains(err.Error(), "invalid dict entry") {
			return err
		}
		// The PDF spec mandates interpreting undefined values as "S".
		err = nil
	}

	// D, optional, dash array
	_, err = validateNumberArrayEntry(xRefTable, d1, dictName, "D", OPTIONAL, V10, nil)

	return err
}

func validateIconFitDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see table 247

	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "iconFitDict"

	// SW, optional, name, A,B,S,N
	validate := func(s string) bool { return MemberOf(s, []string{"A", "B", "S", "N"}) }
	if _, err = validateNameEntry(xRefTable, d1, dictName, "SW", OPTIONAL, V10, validate); err != nil {
		return err
	}

	// S, optional, name, A,P
	if _, err = validateNameEntry(xRefTable, d1, dictName, "S", OPTIONAL, V10, func(s string) bool { return s == "A" || s == "P" }); err != nil {
		return err
	}

	// A,optional, array of 2 numbers between 0.0 and 1.0
	if _, err = validateNumberArrayEntry(xRefTable, d1, dictName, "A", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// FB, optional, bool, since V1.5
	if _, err = validateBooleanEntry(xRefTable, d1, dictName, "FB", OPTIONAL, V10, nil); err != nil {
		return err
	}

	return nil
}

func validateAppearanceCharacteristicsDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// see 12.5.6.19

	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "appCharDict"

	// R, optional, integer
	if _, err = validateIntegerEntry(xRefTable, d1, dictName, "R", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// BC, optional, array of numbers, len=0,1,3,4
	if _, err = validateNumberArrayEntry(xRefTable, d1, dictName, "BC", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// BG, optional, array of numbers between 0.0 and 0.1, len=0,1,3,4
	if _, err = validateNumberArrayEntry(xRefTable, d1, dictName, "BG", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// CA, optional, text string
	if _, err = validateStringEntry(xRefTable, d1, dictName, "CA", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// RC, optional, text string
	if _, err = validateStringEntry(xRefTable, d1, dictName, "RC", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// AC, optional, text string
	if _, err = validateStringEntry(xRefTable, d1, dictName, "AC", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// I, optional, stream dict
	if _, err = validateStreamDictEntry(xRefTable, d1, dictName, "I", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// RI, optional, stream dict
	if _, err = validateStreamDictEntry(xRefTable, d1, dictName, "RI", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// IX, optional, stream dict
	if _, err = validateStreamDictEntry(xRefTable, d1, dictName, "IX", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// IF, optional, icon fit dict,
	if err = validateIconFitDictEntry(xRefTable, d1, dictName, "IF", OPTIONAL, V10); err != nil {
		return err
	}

	// TP, optional, integer 0..6
	_, err = validateIntegerEntry(xRefTable, d1, dictName, "TP", OPTIONAL, V10, func(i int) bool { return 0 <= i && i <= 6 })

	return err
}

func validateAnnotationDictText(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.4

	// Open, optional, boolean
	if _, err := validateBooleanEntry(xRefTable, d, dictName, "Open", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// NameType, optional, name
	if _, err := validateNameEntry(xRefTable, d, dictName, "Name", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// State, optional, text string, since V1.5
	state, err := validateStringEntry(xRefTable, d, dictName, "State", OPTIONAL, V15, nil)
	if err != nil {
		return err
	}

	// StateModel, text string, since V1.5
	validate := func(s string) bool { return MemberOf(s, []string{"Marked", "Review"}) }
	stateModel, err := validateStringEntry(xRefTable, d, dictName, "StateModel", state != nil, V15, validate)
	if err != nil {
		return err
	}

	if state == nil {
		if stateModel != nil {
			return errors.Errorf("pdfcpu: validateAnnotationDictText: dict=%s missing state for statemodel=%s", dictName, *stateModel)
		}
		return nil
	}

	// Ensure that the state/model combo is valid.
	validStates := []string{"Accepted", "Rejected", "Cancelled", "Completed", "None"} // stateModel "Review"
	if *stateModel == "Marked" {
		validStates = []string{"Marked", "Unmarked"}
	}
	if !MemberOf(*state, validStates) {
		return errors.Errorf("pdfcpu: validateAnnotationDictText: dict=%s invalid state=%s for state model=%s", dictName, *state, *stateModel)
	}

	return nil
}

func validateActionOrDestination(xRefTable *XRefTable, d Dict, dictName string, sinceVersion Version) (string, error) {
	// The action that shall be performed when this item is activated.
	d1, err := validateDictEntry(xRefTable, d, dictName, "A", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return "", err
	}
	if d1 != nil {
		return "", validateActionDict(xRefTable, d1)
	}

	// A destination that shall be displayed when this item is activated.
	obj, err := validateEntry(xRefTable, d, dictName, "Dest", OPTIONAL, sinceVersion)
	if err != nil || obj == nil {
		return "", err
	}

	name, err := validateDestination(xRefTable, obj, false)
	if err != nil {
		return "", err
	}

	if len(name) > 0 && xRefTable.IsMerging() {
		nm := xRefTable.NameRef("Dests")
		nm.Add(name, d)
	}

	return name, nil
}

func validateURIActionDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "URIActionDict"

	// Type, optional, name
	if _, err = validateNameEntry(xRefTable, d1, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "Action" }); err != nil {
		return err
	}

	// S, required, name, action Type
	if _, err = validateNameEntry(xRefTable, d1, dictName, "S", REQUIRED, V10, func(s string) bool { return s == "URI" }); err != nil {
		return err
	}

	return validateURIActionDict(xRefTable, d1, dictName)
}

func validateAnnotationDictLink(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.5

	// A or Dest, required either or
	if _, err := validateActionOrDestination(xRefTable, d, dictName, V11); err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
	}

	// H, optional, name, since V1.2
	if _, err := validateNameEntry(xRefTable, d, dictName, "H", OPTIONAL, V12, nil); err != nil {
		return err
	}

	// PA, optional, URI action dict, since V1.3
	if err := validateURIActionDictEntry(xRefTable, d, dictName, "PA", OPTIONAL, V13); err != nil {
		return err
	}

	// QuadPoints, optional, number array, len= a multiple of 8, since V1.6
	sinceVersion := V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "QuadPoints", OPTIONAL, sinceVersion, func(a Array) bool { return len(a)%8 == 0 }); err != nil {
		return err
	}

	// BS, optional, border style dict, since V1.6
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}
	return validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, sinceVersion)
}

func validateAppearanceSubDict(xRefTable *XRefTable, d Dict) error {
	// dict of xobjects
	for _, o := range d {

		if xRefTable.ValidationMode == ValidationRelaxed {
			if d, ok := o.(Dict); ok && len(d) == 0 {
				continue
			}
		}

		err := validateXObjectStreamDict(xRefTable, o)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateAppearanceDictEntry(xRefTable *XRefTable, o Object) error {
	// stream or dict
	// single appearance stream or subdict

	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Dict:
		err = validateAppearanceSubDict(xRefTable, o)

	case StreamDict:
		err = validateXObjectStreamDict(xRefTable, o)

	default:
		err = errors.New("pdfcpu: validateAppearanceDictEntry: unsupported PDF object")

	}

	return err
}

func validateAppearanceDict(xRefTable *XRefTable, o Object) error {
	// see 12.5.5 Appearance Streams

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// Normal Appearance
	o, ok := d.Find("N")
	if !ok {
		if xRefTable.ValidationMode == ValidationStrict {
			return errors.New("pdfcpu: validateAppearanceDict: missing required entry \"N\"")
		}
	} else {
		err = validateAppearanceDictEntry(xRefTable, o)
		if err != nil {
			return err
		}
	}

	// Rollover Appearance
	if o, ok = d.Find("R"); ok {
		err = validateAppearanceDictEntry(xRefTable, o)
		if err != nil {
			return err
		}
	}

	// Down Appearance
	if o, ok = d.Find("D"); ok {
		err = validateAppearanceDictEntry(xRefTable, o)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateDA(s string) bool {
	// A sequence of valid page-content graphics or text state operators.
	// At a minimum, the string shall include a Tf (text font) operator along with its two operands, font and size.
	da := strings.Fields(s)
	for i := 0; i < len(da); i++ {
		if da[i] == "Tf" {
			if i < 2 {
				return false
			}
			if da[i-2][0] != '/' {
				return false
			}
			fontID := da[i-2][1:]
			if len(fontID) == 0 {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-1], 64); err != nil {
				return false
			}
			continue
		}
		if da[i] == "rg" {
			if i < 3 {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-3], 32); err != nil {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-2], 32); err != nil {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-1], 32); err != nil {
				return false
			}
		}
		if da[i] == "g" {
			if i < 1 {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-1], 32); err != nil {
				return false
			}
		}
	}

	return true
}

func validateDARelaxed(s string) bool {
	// A sequence of valid page-content graphics or text state operators.
	// At a minimum, the string shall include a Tf (text font) operator along with its two operands, font and size.
	da := strings.Fields(s)
	for i := 0; i < len(da); i++ {
		if da[i] == "Tf" {
			if i < 2 {
				return false
			}
			if da[i-2][0] != '/' {
				return false
			}
			// fontID := da[i-2][1:]
			// if len(fontID) == 0 {
			// 	return false
			// }
			if _, err := strconv.ParseFloat(da[i-1], 64); err != nil {
				return false
			}
			continue
		}
		if da[i] == "rg" {
			if i < 3 {
				return false
			}
			if _, err := strconv.ParseFloat(strings.TrimPrefix(da[i-3], "["), 32); err != nil {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-2], 32); err != nil {
				return false
			}
			if _, err := strconv.ParseFloat(strings.TrimSuffix(da[i-1], "]"), 32); err != nil {
				return false
			}
		}
		if da[i] == "g" {
			if i < 1 {
				return false
			}
			if _, err := strconv.ParseFloat(da[i-1], 32); err != nil {
				return false
			}
		}
	}

	return true
}

func validateFormFieldDA(xRefTable *XRefTable, d Dict, dictName string, terminalNode bool, outFieldType *NameType, requiresDA bool) (bool, error) {
	validate := validateDA
	if xRefTable.ValidationMode == ValidationRelaxed {
		validate = validateDARelaxed
	}

	if outFieldType == nil || (*outFieldType).Value() == "Tx" {
		// if (*outFieldType).Value() == "Tx" {
		da, err := validateStringEntry(xRefTable, d, dictName, "DA", requiresDA, V10, validate)
		if err != nil {
			if !terminalNode && requiresDA {
				err = nil
			}
			return false, err
		}
		if xRefTable.ValidationMode == ValidationRelaxed && da != nil {
			// Repair DA
			d["DA"] = StringLiteral(*da)
		}

		return da != nil && *da != "", nil
	}

	return false, nil
}

func cacheSig(xRefTable *XRefTable, d Dict, dictName string, form bool, objNr, incr int) error {
	fieldType := d.NameEntry("FT")
	if fieldType == nil || *fieldType != "Sig" {
		return nil
	}

	sig := &Signature{Type: SigTypePage, ObjNr: objNr, Signed: d["V"] != nil, PageNr: xRefTable.CurPage}
	if form {
		sig.Type = SigTypeForm
	}

	var dts bool

	if indRef := d.IndirectRefEntry("V"); indRef != nil {
		sigDict, err := xRefTable.DereferenceDict(*indRef)
		if err != nil {
			return nil
		}
		if typ := sigDict.Type(); typ != nil {
			if *typ == "DocTimeStamp" {
				sig.Type = SigTypeDTS
				dts = true
			}
		}
	}

	arr, err := validateRectangleEntry(xRefTable, d, dictName, "Rect", REQUIRED, V10, nil)
	if err != nil {
		return err
	}
	r := RectForArray(arr)
	sig.Visible = r.Visible() && !dts

	if _, ok := xRefTable.Signatures[incr]; !ok {
		xRefTable.Signatures[incr] = map[int]Signature{}
	}
	if sig1, ok := xRefTable.Signatures[incr][sig.ObjNr]; !ok {
		xRefTable.Signatures[incr][sig.ObjNr] = *sig
	} else {
		sig1.PageNr = xRefTable.CurPage
		xRefTable.Signatures[incr][sig.ObjNr] = sig1
	}

	return nil
}

func isTextField(ft *NameType) bool {
	return ft != nil && *ft == "Tx"
}

func validateV(xRefTable *XRefTable, objNr, incr int, d Dict, dictName string, terminalNode, textField, oneKid bool) error {
	v, err := validateEntry(xRefTable, d, dictName, "V", OPTIONAL, V10)
	if err != nil {
		return err
	}
	if textField && v != nil && !terminalNode && !oneKid {
		return errors.New("\"V\" not allowed in non terminal text fields with more than one kid")
	}
	if err := cacheSig(xRefTable, d, dictName, true, objNr, incr); err != nil {
		return err
	}
	return nil
}

func validateDV(xRefTable *XRefTable, d Dict, dictName string, terminalNode, textField, oneKid bool) error {
	dv, err := validateEntry(xRefTable, d, dictName, "DV", OPTIONAL, V10)
	if err != nil {
		return err
	}
	if textField && dv != nil && !terminalNode && !oneKid {
		return errors.New("\"DV\" not allowed in non terminal text fields with more than one kid")
	}
	return nil
}

func validateFormFieldDictEntries(xRefTable *XRefTable, objNr, incr int, d Dict, terminalNode, oneKid bool, inFieldType *NameType, requiresDA bool) (outFieldType *NameType, hasDA bool, err error) {
	dictName := "formFieldDict"

	// FT: name, Btn,Tx,Ch,Sig
	validate := func(s string) bool { return MemberOf(s, []string{"Btn", "Tx", "Ch", "Sig"}) }
	fieldType, err := validateNameEntry(xRefTable, d, dictName, "FT", terminalNode && inFieldType == nil, V10, validate)
	if err != nil {
		return nil, false, err
	}

	outFieldType = inFieldType
	if fieldType != nil {
		outFieldType = fieldType
	}

	textField := isTextField(outFieldType)

	// Parent, required if this is a child in the field hierarchy.
	_, err = validateIndRefEntry(xRefTable, d, dictName, "Parent", OPTIONAL, V10)
	if err != nil {
		return nil, false, err
	}

	// T, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "T", OPTIONAL, V10, nil)
	if err != nil {
		return nil, false, err
	}

	// TU, optional, text string, since V1.3
	_, err = validateStringEntry(xRefTable, d, dictName, "TU", OPTIONAL, V13, nil)
	if err != nil {
		return nil, false, err
	}

	// TM, optional, text string, since V1.3
	_, err = validateStringEntry(xRefTable, d, dictName, "TM", OPTIONAL, V13, nil)
	if err != nil {
		return nil, false, err
	}

	// Ff, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "Ff", OPTIONAL, V10, nil)
	if err != nil {
		return nil, false, err
	}

	// V, optional, various
	if err := validateV(xRefTable, objNr, incr, d, dictName, terminalNode, textField, oneKid); err != nil {
		return nil, false, err
	}

	// DV, optional, various
	if err := validateDV(xRefTable, d, dictName, terminalNode, textField, oneKid); err != nil {
		return nil, false, err
	}

	// AA, optional, dict, since V1.2
	err = validateAdditionalActions(xRefTable, d, dictName, "AA", OPTIONAL, V12, "fieldOrAnnot")
	if err != nil {
		return nil, false, err
	}

	// DA, required for text fields, since ?
	// The default appearance string containing a sequence of valid page-content graphics or text state operators that define such properties as the field’s text size and colour.
	hasDA, err = validateFormFieldDA(xRefTable, d, dictName, terminalNode, outFieldType, requiresDA)

	return outFieldType, hasDA, err
}

func validateFormFieldParts(xRefTable *XRefTable, objNr, incr int, d Dict, inFieldType *NameType, requiresDA bool) error {
	// dict represents a terminal field and must have Subtype "Widget"
	if _, err := validateNameEntry(xRefTable, d, "formFieldDict", "Subtype", REQUIRED, V10, func(s string) bool { return s == "Widget" }); err != nil {
		d["Subtype"] = NameType("Widget")
	}

	// Validate field dict entries.
	if _, _, err := validateFormFieldDictEntries(xRefTable, objNr, incr, d, true, false, inFieldType, requiresDA); err != nil {
		return err
	}

	// Validate widget annotation - Validation of AA redundant because of merged acrofield with widget annotation.
	_, err := validateAnnotationDict(xRefTable, d)
	return err
}

func validateFormFieldKids(xRefTable *XRefTable, objNr, incr int, d Dict, o Object, inFieldType *NameType, requiresDA bool) error {
	var err error
	// dict represents a non terminal field.
	if d.Subtype() != nil && *d.Subtype() == "Widget" {
		return errors.New("pdfcpu: validateFormFieldKids: non terminal field can not be widget annotation")
	}

	a, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return err
	}

	// Validate field entries.
	var xInFieldType *NameType
	var hasDA bool
	if xInFieldType, hasDA, err = validateFormFieldDictEntries(xRefTable, objNr, incr, d, false, len(a) == 1, inFieldType, requiresDA); err != nil {
		return err
	}
	if requiresDA && hasDA {
		requiresDA = false
	}

	if len(a) == 0 {
		return nil
	}

	// Recurse over kids.
	for _, value := range a {
		ir, ok := value.(IndirectRef)
		if !ok {
			return errors.New("pdfcpu: validateFormFieldKids: corrupt kids array: entries must be indirect reference")
		}
		valid, err := xRefTable.IsValid(ir)
		if err != nil {
			return err
		}

		if !valid {
			if err = validateFormFieldDict(xRefTable, ir, xInFieldType, requiresDA); err != nil {
				return err
			}
		}
	}

	return nil
}

func validateFormFieldDict(xRefTable *XRefTable, ir IndirectRef, inFieldType *NameType, requiresDA bool) error {
	d, incr, err := xRefTable.DereferenceDictWithIncr(ir)
	if err != nil || d == nil {
		return err
	}

	if xRefTable.ValidationMode == ValidationRelaxed {
		if len(d) == 0 {
			return nil
		}
	}

	if err := xRefTable.SetValid(ir); err != nil {
		return err
	}

	objNr := ir.ObjectNumber.Value()

	if o, ok := d.Find("Kids"); ok {
		return validateFormFieldKids(xRefTable, objNr, incr, d, o, inFieldType, requiresDA)
	}

	return validateFormFieldParts(xRefTable, objNr, incr, d, inFieldType, requiresDA)
}

func validateFormFields(xRefTable *XRefTable, arr Array, requiresDA bool) error {
	for _, value := range arr {

		ir, ok := value.(IndirectRef)
		if !ok {
			return errors.New("pdfcpu: validateFormFields: corrupt form field array entry")
		}

		valid, err := xRefTable.IsValid(ir)
		if err != nil {
			return err
		}

		if !valid {
			if err = validateFormFieldDict(xRefTable, ir, nil, requiresDA); err != nil {
				return err
			}
		}

	}

	return nil
}

func validateFormCO(xRefTable *XRefTable, arr Array, sinceVersion Version, requiresDA bool) error {
	// see 12.6.3 Trigger Events
	// Array of indRefs to field dicts with calculation actions, since V1.3

	// Version check
	err := xRefTable.ValidateVersion("AcroFormCO", sinceVersion)
	if err != nil {
		return err
	}

	return validateFormFields(xRefTable, arr, requiresDA)
}

func validateFormXFA(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	// see 12.7.8

	o, ok := d.Find("XFA")
	if !ok {
		return nil
	}

	// streamDict or array of text,streamDict pairs

	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case StreamDict:
		// no further processing

	case Array:

		i := 0

		for _, v := range o {

			if v == nil {
				return errors.New("pdfcpu: validateFormXFA: array entry is nil")
			}

			o, err := xRefTable.Dereference(v)
			if err != nil {
				return err
			}

			if i%2 == 0 {

				_, ok := o.(StringLiteral)
				if !ok {
					return errors.New("pdfcpu: validateFormXFA: even array must be a string")
				}

			} else {

				_, ok := o.(StreamDict)
				if !ok {
					return errors.New("pdfcpu: validateFormXFA: odd array entry must be a streamDict")
				}

			}

			i++
		}

	default:
		return errors.New("pdfcpu: validateFormXFA: needs to be streamDict or array")
	}

	return xRefTable.ValidateVersion("AcroFormXFA", sinceVersion)
}

func validateQ(i int) bool { return i >= 0 && i <= 2 }

func validateFormEntryCO(xRefTable *XRefTable, d Dict, sinceVersion Version, requiresDA bool) error {
	o, ok := d.Find("CO")
	if !ok {
		return nil
	}

	arr, err := xRefTable.DereferenceArray(o)
	if err != nil || len(arr) == 0 {
		return err
	}

	return validateFormCO(xRefTable, arr, sinceVersion, requiresDA)
}

func validateFormEntryDR(xRefTable *XRefTable, d Dict) error {
	o, ok := d.Find("DR")
	if !ok {
		return nil
	}

	_, err := validateResourceDict(xRefTable, o)

	return err
}

func validateFormEntries(xRefTable *XRefTable, d Dict, dictName string, requiresDA bool, sinceVersion Version) error {
	// NeedAppearances: optional, boolean
	_, err := validateBooleanEntry(xRefTable, d, dictName, "NeedAppearances", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// SigFlags: optional, since 1.3, integer
	sinceV := V13
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceV = V12
	}
	sf, err := validateIntegerEntry(xRefTable, d, dictName, "SigFlags", OPTIONAL, sinceV, nil)
	if err != nil {
		return err
	}
	if sf != nil {
		i := sf.Value()
		xRefTable.SignatureExist = i&1 > 0
		xRefTable.AppendOnly = i&2 > 0
	}

	// CO: array
	err = validateFormEntryCO(xRefTable, d, V13, requiresDA)
	if err != nil {
		return err
	}

	// DR, optional, resource dict
	err = validateFormEntryDR(xRefTable, d)
	if err != nil {
		return err
	}

	// Q: optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "Q", OPTIONAL, V10, validateQ)
	if err != nil {
		return err
	}

	// XFA: optional, since 1.5, stream or array
	return validateFormXFA(xRefTable, d, sinceVersion)
}

func validateForm(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.7.2 Interactive Form Dictionary

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "AcroForm", OPTIONAL, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	// Version check
	if err = xRefTable.ValidateVersion("AcroForm", sinceVersion); err != nil {
		return err
	}

	// Fields, required, array of indirect references
	o, ok := d.Find("Fields")
	if !ok {
		// Fix empty AcroForm dict.
		rootDict.Delete("AcroForm")
		return nil
	}

	arr, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return err
	}
	if len(arr) == 0 {
		// Fix empty AcroForm dict.
		rootDict.Delete("AcroForm")
		return nil
	}

	xRefTable.Form = d

	dictName := "acroFormDict"

	// DA: optional, string
	validate := validateDA
	if xRefTable.ValidationMode == ValidationRelaxed {
		validate = validateDARelaxed
	}
	da, err := validateStringEntry(xRefTable, d, dictName, "DA", OPTIONAL, V10, validate)
	if err != nil {
		return err
	}
	if xRefTable.ValidationMode == ValidationRelaxed && da != nil {
		// Repair
		d["DA"] = StringLiteral(*da)
	}

	requiresDA := da == nil || len(*da) == 0

	err = validateFormFields(xRefTable, arr, requiresDA)
	if err != nil {
		return err
	}

	return validateFormEntries(xRefTable, d, dictName, requiresDA, sinceVersion)
}

func locateAnnForAPAndRect(d Dict, r *Rectangle, pageAnnots map[int]PgAnnots) *IndirectRef {
	if indRef1 := d.IndirectRefEntry("AP"); indRef1 != nil {
		apObjNr := indRef1.ObjectNumber.Value()
		for _, m := range pageAnnots {
			annots, ok := m[AnnWidget]
			if ok {
				for objNr, annRend := range annots.Map {
					if objNr > 0 {
						if annRend.RectString() == r.ShortString() && annRend.APObjNrInt() == apObjNr {
							return NewIndirectRef(objNr, 0)
						}
					}
				}
			}
		}
	}
	return nil
}

func pageAnnotIndRefForAcroField(xRefTable *XRefTable, indRef IndirectRef) (*IndirectRef, error) {
	// indRef should be part of a page annotation dict.

	for _, m := range xRefTable.PageAnnots {
		annots, ok := m[AnnWidget]
		if ok {
			for _, ir := range *annots.IndRefs {
				if ir == indRef {
					return &ir, nil
				}
			}
		}
	}

	// form field is duplicated, retrieve corresponding page annotation for Rect, AP

	d, err := xRefTable.DereferenceDict(indRef)
	if err != nil {
		return nil, err
	}

	arr, err := xRefTable.DereferenceArray(d["Rect"])
	if err != nil {
		return nil, err
	}
	if arr == nil {
		// Assumption: There are kids and the kids are allright.
		return &indRef, nil
	}

	r, err := xRefTable.RectForArray(arr)
	if err != nil {
		return nil, err
	}

	// Possible orphan sig field dicts.
	if ft := d.NameEntry("FT"); ft != nil && *ft == "Sig" {
		// Signature Field
		if _, ok := d.Find("V"); !ok {
			// without linked sig dict (unsigned)
			return &indRef, nil
		}
		// signed but invisible
		if !r.Visible() {
			return &indRef, nil
		}
	}

	if indRef := locateAnnForAPAndRect(d, r, xRefTable.PageAnnots); indRef != nil {
		return indRef, nil
	}

	return &indRef, nil
	// return nil, errors.Errorf("pdfcpu: can't repair form field: %d\n", indRef.ObjectNumber.Value())
}

func fixFormFieldsArray(xRefTable *XRefTable, arr Array) (Array, error) {
	arr1 := Array{}
	for _, obj := range arr {
		indRef, err := pageAnnotIndRefForAcroField(xRefTable, obj.(IndirectRef))
		if err != nil {
			return nil, err
		}
		arr1 = append(arr1, *indRef)
	}
	return arr1, nil
}

func validateFormFieldsAgainstPageAnnotations(xRefTable *XRefTable) error {
	o, found := xRefTable.Form.Find("Fields")
	if !found {
		return nil
	}

	indRef, ok := o.(IndirectRef)
	if !ok {
		arr, ok := o.(Array)
		if !ok {
			return errors.New("pdfcpu: invalid array object")
		}
		arr, err := fixFormFieldsArray(xRefTable, arr)
		if err != nil {
			return err
		}
		indRef, err := xRefTable.IndRefForNewObject(arr)
		if err != nil {
			return err
		}
		xRefTable.Form["Fields"] = *indRef
		return nil
	}

	arr, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return err
	}
	arr, err = fixFormFieldsArray(xRefTable, arr)
	if err != nil {
		return err
	}
	entry, _ := xRefTable.FindTableEntryForIndRef(&indRef)
	entry.Object = arr

	return nil
}

func validateAPAndDA(xRefTable *XRefTable, d Dict, dictName string) error {
	required := REQUIRED

	// DA, required, string
	validate := validateDA
	if xRefTable.ValidationMode == ValidationRelaxed {

		validate = validateDARelaxed

		// An existing AP entry takes precedence over a DA entry.
		d1, err := validateDictEntry(xRefTable, d, dictName, "AP", OPTIONAL, V12, nil)
		if err != nil {
			return err
		}
		if len(d1) > 0 {
			required = OPTIONAL
		}
	}

	da, err := validateStringEntry(xRefTable, d, dictName, "DA", required, V10, validate)
	if err != nil {
		return err
	}
	if xRefTable.ValidationMode == ValidationRelaxed && da != nil {
		// Repair
		d["DA"] = StringLiteral(*da)
	}

	return nil
}

func validateAnnotationDictFreeTextPart1(xRefTable *XRefTable, d Dict, dictName string) error {
	if err := validateAPAndDA(xRefTable, d, dictName); err != nil {
		return err
	}

	// Q, optional, integer, since V1.4, 0,1,2
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "Q", OPTIONAL, sinceVersion, func(i int) bool { return 0 <= i && i <= 2 }); err != nil {
		return err
	}

	// RC, optional, text string or text stream, since V1.5
	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if err := validateStringOrStreamEntry(xRefTable, d, dictName, "RC", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	// DS, optional, text string, since V1.5
	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateStringEntry(xRefTable, d, dictName, "DS", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// CL, optional, number array, since V1.6, len: 4 or 6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}

	_, err := validateNumberArrayEntry(xRefTable, d, dictName, "CL", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 4 || len(a) == 6 })

	return err
}

func validateAnnotationDictFreeTextPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// IT, optional, name, since V1.6
	sinceVersion := V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	validate := func(s string) bool {
		return MemberOf(s, []string{"FreeText", "FreeTextCallout", "FreeTextTypeWriter", "FreeTextTypewriter"})
	}
	if _, err := validateNameEntry(xRefTable, d, dictName, "IT", OPTIONAL, sinceVersion, validate); err != nil {
		return err
	}

	// BE, optional, border effect dict, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if err := validateBorderEffectDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	// RD, optional, rectangle, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if _, err := validateRectangleEntry(xRefTable, d, dictName, "RD", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// BS, optional, border style dict, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}
	if err := validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	// LE, optional, name, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	_, err := validateNameEntry(xRefTable, d, dictName, "LE", OPTIONAL, sinceVersion, nil)

	return err
}

func validateAnnotationDictFreeText(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.6

	if err := validateAnnotationDictFreeTextPart1(xRefTable, d, dictName); err != nil {
		return err
	}

	return validateAnnotationDictFreeTextPart2(xRefTable, d, dictName)
}

func validateEntryMeasure(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "Measure", required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateMeasureDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validateCP(s string) bool { return s == "Inline" || s == "Top" }

func validateAnnotationDictLinePart1(xRefTable *XRefTable, d Dict, dictName string) error {
	// L, required, array of numbers, len:4
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "L", REQUIRED, V10, func(a Array) bool { return len(a) == 4 }); err != nil {
		return err
	}

	// BS, optional, border style dict
	if err := validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, V10); err != nil {
		return err
	}

	// LE, optional, name array, since V1.4, len:2
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateNameArrayEntry(xRefTable, d, dictName, "LE", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 2 }); err != nil {
		return err
	}

	// IC, optional, number array, since V1.4, len:0,1,3,4
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "IC", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// LLE, optional, number, since V1.6, > 0
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	lle, err := validateNumberEntry(xRefTable, d, dictName, "LLE", OPTIONAL, sinceVersion, func(f float64) bool { return f > 0 })
	if err != nil {
		return err
	}

	// LL, required if LLE present, number, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if _, err := validateNumberEntry(xRefTable, d, dictName, "LL", lle != nil, sinceVersion, nil); err != nil {
		return err
	}

	// Cap, optional, bool, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Cap", OPTIONAL, sinceVersion, nil)

	return err
}

func validateAnnotationDictLinePart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// IT, optional, name, since V1.6
	if _, err := validateNameEntry(xRefTable, d, dictName, "IT", OPTIONAL, V16, nil); err != nil {
		return err
	}

	// LLO, optionl, number, since V1.7, >0
	if _, err := validateNumberEntry(xRefTable, d, dictName, "LLO", OPTIONAL, V17, func(f float64) bool { return f > 0 }); err != nil {
		return err
	}

	// CP, optional, name, since V1.7
	if _, err := validateNameEntry(xRefTable, d, dictName, "CP", OPTIONAL, V17, validateCP); err != nil {
		return err
	}

	// Measure, optional, measure dict, since V1.7
	if err := validateEntryMeasure(xRefTable, d, dictName, OPTIONAL, V17); err != nil {
		return err
	}

	// CO, optional, number array, since V1.7, len=2
	_, err := validateNumberArrayEntry(xRefTable, d, dictName, "CO", OPTIONAL, V17, func(a Array) bool { return len(a) == 2 })

	return err
}

func validateAnnotationDictLine(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.7

	if err := validateAnnotationDictLinePart1(xRefTable, d, dictName); err != nil {
		return err
	}

	return validateAnnotationDictLinePart2(xRefTable, d, dictName)
}

func validateAnnotationDictCircleOrSquare(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.8

	// BS, optional, border style dict
	if err := validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, V10); err != nil {
		return err
	}

	// IC, optional, array, since V1.4
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "IC", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// BE, optional, border effect dict, since V1.5
	if err := validateBorderEffectDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, V15); err != nil {
		return err
	}

	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}

	// RD, optional, rectangle, since V1.5
	_, err := validateRectangleEntry(xRefTable, d, dictName, "RD", OPTIONAL, sinceVersion, nil)

	return err
}

func validateEntryIT(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}

	// IT, optional, name, since V1.6
	validateIntent := func(s string) bool {
		if xRefTable.Version() == sinceVersion {
			return s == "PolygonCloud"
		}

		if xRefTable.Version() == V17 {
			if MemberOf(s, []string{"PolygonCloud", "PolyLineDimension", "PolygonDimension"}) {
				return true
			}
		}

		return false
	}

	_, err := validateNameEntry(xRefTable, d, dictName, "IT", required, sinceVersion, validateIntent)

	return err
}

func validateAnnotationDictPolyLine(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.9

	// Vertices, required, array of numbers
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "Vertices", REQUIRED, V10, nil); err != nil {
		return err
	}

	// LE, optional, array of 2 names, meaningful only for polyline annotations.
	if dictName == "PolyLine" {
		if _, err := validateNameArrayEntry(xRefTable, d, dictName, "LE", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 }); err != nil {
			return err
		}
	}

	// BS, optional, border style dict
	if err := validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, V10); err != nil {
		return err
	}

	// IC, optional, array of numbers [0.0 .. 1.0], len:1,3,4
	ensureArrayLength := func(a Array, lengths ...int) bool {
		for _, length := range lengths {
			if len(a) == length {
				return true
			}
		}
		return false
	}
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "IC", OPTIONAL, V14, func(a Array) bool { return ensureArrayLength(a, 1, 3, 4) }); err != nil {
		return err
	}

	// BE, optional, border effect dict, meaningful only for polygon annotations
	if dictName == "Polygon" {
		if err := validateBorderEffectDictEntry(xRefTable, d, dictName, "BE", OPTIONAL, V10); err != nil {
			return err
		}
	}

	return validateEntryIT(xRefTable, d, dictName, OPTIONAL, V16)
}

func validateTextMarkupAnnotation(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.10

	required := REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}
	// QuadPoints, required, number array, len: a multiple of 8
	_, err := validateNumberArrayEntry(xRefTable, d, dictName, "QuadPoints", required, V10, func(a Array) bool { return len(a)%8 == 0 })

	return err
}

func validateAnnotationDictStamp(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.12

	// NameType, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Name", OPTIONAL, V10, nil)

	return err
}

func validateAnnotationDictCaret(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.11

	// RD, optional, rectangle, since V1.5
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if _, err := validateRectangleEntry(xRefTable, d, dictName, "RD", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// Sy, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Sy", OPTIONAL, V10, func(s string) bool { return s == "P" || s == "None" })

	return err
}

func validateArrayArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateArrayArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		switch o.(type) {

		case Array:
			// no further processing.

		default:
			return nil, errors.Errorf("pdfcpu: validateArrayArrayEntry: invalid type at index %d\n", i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateArrayArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateAnnotationDictInk(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.13

	// InkList, required, array of stroked path arrays
	if _, err := validateArrayArrayEntry(xRefTable, d, dictName, "InkList", REQUIRED, V10, nil); err != nil {
		return err
	}

	// BS, optional, border style dict
	return validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, V10)
}

func validateAnnotationDictPopup(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.14

	// Parent, optional, dict indRef
	ir, err := validateIndRefEntry(xRefTable, d, dictName, "Parent", OPTIONAL, V10)
	if err != nil {
		return err
	}
	if ir != nil {
		d1, err := xRefTable.DereferenceDict(*ir)
		if err != nil || d1 == nil {
			return err
		}
	}

	// Open, optional, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "Open", OPTIONAL, V10, nil)

	return err
}

func validateNameOrStringEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameOrStringEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateNameOrStringEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateNameOrStringEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	switch o.(type) {

	case StringLiteral, NameType:
		// no further processing

	default:
		return errors.Errorf("pdfcpu: validateNameOrStringEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameOrStringEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateAnnotationDictFileAttachment(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.15

	// FS, required, file specification
	if _, err := validateFileSpecEntry(xRefTable, d, dictName, "FS", REQUIRED, V10); err != nil {
		return err
	}

	// NameType, optional, name
	return validateNameOrStringEntry(xRefTable, d, dictName, "Name", OPTIONAL, V10)
}

func validateAnnotationDictSound(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.16

	// Sound, required, stream dict
	if err := validateSoundDictEntry(xRefTable, d, dictName, "Sound", REQUIRED, V10); err != nil {
		return err
	}

	// NameType, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Name", OPTIONAL, V10, nil)

	return err
}

func validateBooleanOrStreamEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanOrStreamEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateBooleanOrStreamEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateBooleanOrStreamEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	switch o.(type) {

	case Boolean, StreamDict:
		// no further processing

	default:
		return errors.Errorf("pdfcpu: validateBooleanOrStreamEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanOrStreamEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateMovieDict(xRefTable *XRefTable, d Dict) error {
	dictName := "movieDict"

	// F, required, file specification
	if _, err := validateFileSpecEntry(xRefTable, d, dictName, "F", REQUIRED, V10); err != nil {
		return err
	}

	// Aspect, optional, integer array, length 2
	if _, err := validateIntegerArrayEntry(xRefTable, d, dictName, "Aspect", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 }); err != nil {
		return err
	}

	// Rotate, optional, integer
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "Rotate", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// Poster, optional boolean or stream
	return validateBooleanOrStreamEntry(xRefTable, d, dictName, "Poster", OPTIONAL, V10)
}

func validateAnnotationDictMovie(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.17 Movie Annotations
	// 13.4 Movies
	// The features described in this sub-clause are obsolescent and their use is no longer recommended.
	// They are superseded by the general multimedia framework described in 13.2, “Multimedia.”

	// T, optional, text string
	if _, err := validateStringEntry(xRefTable, d, dictName, "T", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// Movie, required, movie dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "Movie", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	if err = validateMovieDict(xRefTable, d1); err != nil {
		return err
	}

	// A, optional, boolean or movie activation dict
	o, found := d.Find("A")

	if found {

		o, err = xRefTable.Dereference(o)
		if err != nil {
			return err
		}

		if o != nil {
			switch o := o.(type) {
			case Boolean:
				// no further processing

			case Dict:
				err = validateMovieActivationDict(xRefTable, o)
				if err != nil {
					return err
				}
			}
		}

	}

	return nil
}

func validateAnnotationDictWidget(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.19

	// H, optional, name
	validate := func(s string) bool { return MemberOf(s, []string{"N", "I", "O", "P", "T", "A"}) }
	if _, err := validateNameEntry(xRefTable, d, dictName, "H", OPTIONAL, V10, validate); err != nil {
		return err
	}

	// MK, optional, dict
	// An appearance characteristics dictionary that shall be used in constructing
	// a dynamic appearance stream specifying the annotation’s visual presentation on the page.dict
	if err := validateAppearanceCharacteristicsDictEntry(xRefTable, d, dictName, "MK", OPTIONAL, V10); err != nil {
		return err
	}

	// A, optional, dict, since V1.1
	// An action that shall be performed when the annotation is activated.
	d1, err := validateDictEntry(xRefTable, d, dictName, "A", OPTIONAL, V11, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		if err = validateActionDict(xRefTable, d1); err != nil {
			return err
		}
	}

	// AA, optional, dict, since V1.2
	// An additional-actions dictionary defining the annotation’s behaviour in response to various trigger events.
	if err = validateAdditionalActions(xRefTable, d, dictName, "AA", OPTIONAL, V12, "fieldOrAnnot"); err != nil {
		return err
	}

	// BS, optional, border style dict, since V1.2
	// A border style dictionary specifying the width and dash pattern
	// that shall be used in drawing the annotation’s border.
	if err = validateBorderStyleDict(xRefTable, d, dictName, "BS", OPTIONAL, V12); err != nil {
		return err
	}

	// Parent, dict, required if one of multiple children in a field.
	// An indirect reference to the widget annotation’s parent field.
	_, err = validateIndRefEntry(xRefTable, d, dictName, "Parent", OPTIONAL, V10)

	return err
}

func validateAnnotationDictScreen(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.18

	// T, optional, name
	if _, err := validateNameEntry(xRefTable, d, dictName, "T", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// MK, optional, appearance characteristics dict
	if err := validateAppearanceCharacteristicsDictEntry(xRefTable, d, dictName, "MK", OPTIONAL, V10); err != nil {
		return err
	}

	// A, optional, action dict, since V1.0
	d1, err := validateDictEntry(xRefTable, d, dictName, "A", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		if err = validateActionDict(xRefTable, d1); err != nil {
			return err
		}
	}

	// AA, optional, additional-actions dict, since V1.2
	return validateAdditionalActions(xRefTable, d, dictName, "AA", OPTIONAL, V12, "fieldOrAnnot")
}

func validateAnnotationDictPrinterMark(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.20

	// MN, optional, name
	if _, err := validateNameEntry(xRefTable, d, dictName, "MN", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// F, required integer, since V1.1, annotation flags
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "F", REQUIRED, V11, nil); err != nil {
		return err
	}

	// AP, required, appearance dict, since V1.2
	return validateAppearDictEntry(xRefTable, d, dictName, REQUIRED, V12)
}

func validateAnnotationDictTrapNet(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.21

	// LastModified, optional, date
	if _, err := validateDateEntry(xRefTable, d, dictName, "LastModified", OPTIONAL, V10); err != nil {
		return err
	}

	// Version, optional, array
	if _, err := validateArrayEntry(xRefTable, d, dictName, "Version", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// AnnotStates, optional, array of names
	if _, err := validateNameArrayEntry(xRefTable, d, dictName, "AnnotStates", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// FontFauxing, optional, font dict array
	validateFontDictArray := func(a Array) bool {
		var retValue bool

		for _, v := range a {

			if v == nil {
				continue
			}

			d, err := xRefTable.DereferenceDict(v)
			if err != nil {
				return false
			}

			if d == nil {
				continue
			}

			if d.Type() == nil || *d.Type() != "Font" {
				return false
			}

			retValue = true

		}

		return retValue
	}

	if _, err := validateArrayEntry(xRefTable, d, dictName, "FontFauxing", OPTIONAL, V10, validateFontDictArray); err != nil {
		return err
	}

	_, err := validateIntegerEntry(xRefTable, d, dictName, "F", REQUIRED, V11, nil)

	return err
}

func validateAnnotationDictWatermark(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.22

	// FixedPrint, optional, dict

	validateFixedPrintDict := func(d Dict) bool {
		dictName := "fixedPrintDict"

		// Type, required, name
		if _, err := validateNameEntry(xRefTable, d, dictName, "Type", REQUIRED, V10, func(s string) bool { return s == "FixedPrint" }); err != nil {
			return false
		}

		// Matrix, optional, integer array, length = 6
		if _, err := validateIntegerArrayEntry(xRefTable, d, dictName, "Matrix", OPTIONAL, V10, func(a Array) bool { return len(a) == 6 }); err != nil {
			return false
		}

		// H, optional, number
		if _, err := validateNumberEntry(xRefTable, d, dictName, "H", OPTIONAL, V10, nil); err != nil {
			return false
		}

		// V, optional, number
		_, err := validateNumberEntry(xRefTable, d, dictName, "V", OPTIONAL, V10, nil)
		return err == nil
	}

	_, err := validateDictEntry(xRefTable, d, dictName, "FixedPrint", OPTIONAL, V10, validateFixedPrintDict)

	return err
}

func validateStreamDictOrDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStreamDictOrDictEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateStreamDictOrDictEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateStreamDictOrDictEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	switch o.(type) {

	case StreamDict:
		// TODO validate 3D stream dict

	case Dict:
		// TODO validate 3D reference dict

	default:
		return errors.Errorf("pdfcpu: validateStreamDictOrDictEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStreamDictOrDictEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateAnnotationDict3D(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 13.6.2

	// AP with entry N, required

	// 3DD, required, 3D stream or 3D reference dict
	if err := validateStreamDictOrDictEntry(xRefTable, d, dictName, "3DD", REQUIRED, V16); err != nil {
		return err
	}

	// 3DV, optional, various
	if _, err := validateEntry(xRefTable, d, dictName, "3DV", OPTIONAL, V16); err != nil {
		return err
	}

	// 3DA, optional, activation dict
	if _, err := validateDictEntry(xRefTable, d, dictName, "3DA", OPTIONAL, V16, nil); err != nil {
		return err
	}

	// 3DI, optional, boolean
	_, err := validateBooleanEntry(xRefTable, d, dictName, "3DI", OPTIONAL, V16, nil)

	return err
}

func validateEntryIC(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	// IC, optional, number array, length:3 [0.0 .. 1.0]
	validateICArray := func(a Array) bool {
		if len(a) != 3 {
			return false
		}

		for _, v := range a {

			o, err := xRefTable.Dereference(v)
			if err != nil {
				return false
			}

			switch o := o.(type) {
			case Integer:
				if o < 0 || o > 1 {
					return false
				}

			case Float:
				if o < 0.0 || o > 1.0 {
					return false
				}
			}
		}

		return true
	}

	_, err := validateNumberArrayEntry(xRefTable, d, dictName, "IC", required, sinceVersion, validateICArray)

	return err
}

func validateAnnotationDictRedact(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.5.6.23

	// QuadPoints, optional, len: a multiple of 8
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "QuadPoints", OPTIONAL, V10, func(a Array) bool { return len(a)%8 == 0 }); err != nil {
		return err
	}

	// IC, optional, number array, length:3 [0.0 .. 1.0]
	if err := validateEntryIC(xRefTable, d, dictName, OPTIONAL, V10); err != nil {
		return err
	}

	// RO, optional, stream
	if _, err := validateStreamDictEntry(xRefTable, d, dictName, "RO", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// OverlayText, optional, text string
	if _, err := validateStringEntry(xRefTable, d, dictName, "OverlayText", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// Repeat, optional, boolean
	if _, err := validateBooleanEntry(xRefTable, d, dictName, "Repeat", OPTIONAL, V10, nil); err != nil {
		return err
	}

	// DA, required, byte string
	validate := validateDA
	if xRefTable.ValidationMode == ValidationRelaxed {
		validate = validateDARelaxed
	}
	da, err := validateStringEntry(xRefTable, d, dictName, "DA", REQUIRED, V10, validate)
	if err != nil {
		return err
	}
	if xRefTable.ValidationMode == ValidationRelaxed && da != nil {
		// Repair
		d["DA"] = StringLiteral(*da)
	}

	// Q, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "Q", OPTIONAL, V10, nil)

	return err
}

func validateRichMediaAnnotation(xRefTable *XRefTable, d Dict, dictName string) error {
	// TODO See extension level 3.
	return nil
}

func validateExDataDict(xRefTable *XRefTable, d Dict) error {
	dictName := "ExData"

	if _, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "ExData" }); err != nil {
		return err
	}

	_, err := validateNameEntry(xRefTable, d, dictName, "Subtype", REQUIRED, V10, func(s string) bool { return s == "Markup3D" })

	return err
}

func validatePopupEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {

		if _, err = validateNameEntry(xRefTable, d1, dictName, "Subtype", REQUIRED, V10, func(s string) bool { return s == "Popup" }); err != nil {
			return err
		}

		if _, err = validateAnnotationDict(xRefTable, d1); err != nil {
			return err
		}

	}

	return nil
}

func validateIRTEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		if _, err = validateAnnotationDict(xRefTable, d1); err != nil {
			return err
		}
	}

	return nil
}

func validateMarkupAnnotationPart1(xRefTable *XRefTable, d Dict, dictName string) error {
	// T, optional, text string, since V1.1
	if _, err := validateStringEntry(xRefTable, d, dictName, "T", OPTIONAL, V11, nil); err != nil {
		return err
	}

	// Popup, optional, dict, since V1.3
	if err := validatePopupEntry(xRefTable, d, dictName, "Popup", OPTIONAL, V13); err != nil {
		return err
	}

	// CA, optional, number, since V1.4
	if _, err := validateNumberEntry(xRefTable, d, dictName, "CA", OPTIONAL, V14, nil); err != nil {
		return err
	}

	// RC, optional, text string or stream, since V1.5
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if err := validateStringOrStreamEntry(xRefTable, d, dictName, "RC", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	// CreationDate, optional, date, since V1.5
	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateDateEntry(xRefTable, d, dictName, "CreationDate", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	return nil
}

func validateMarkupAnnotationPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// IRT, optional, (in reply to) dict, since V1.5
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if err := validateIRTEntry(xRefTable, d, dictName, "IRT", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	// Subj, optional, text string, since V1.5
	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err := validateStringEntry(xRefTable, d, dictName, "Subj", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// RT, optional, name, since V1.6
	validate := func(s string) bool { return s == "R" || s == "Group" }
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if _, err := validateNameEntry(xRefTable, d, dictName, "RT", OPTIONAL, sinceVersion, validate); err != nil {
		return err
	}

	// IT, optional, name, since V1.6
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	if _, err := validateNameEntry(xRefTable, d, dictName, "IT", OPTIONAL, sinceVersion, nil); err != nil {
		return err
	}

	// ExData, optional, dict, since V1.7
	d1, err := validateDictEntry(xRefTable, d, dictName, "ExData", OPTIONAL, V17, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		if err := validateExDataDict(xRefTable, d1); err != nil {
			return err
		}
	}

	return nil
}

func validateMarkupAnnotation(xRefTable *XRefTable, d Dict) error {
	dictName := "markupAnnot"

	if err := validateMarkupAnnotationPart1(xRefTable, d, dictName); err != nil {
		return err
	}

	if err := validateMarkupAnnotationPart2(xRefTable, d, dictName); err != nil {
		return err
	}

	return nil
}

func validateEntryP(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	ir, err := validateIndRefEntry(xRefTable, d, dictName, "P", required, sinceVersion)
	if err != nil || ir == nil {
		return err
	}

	// check if this indRef points to a pageDict.

	d1, err := xRefTable.DereferenceDict(*ir)
	if err != nil {
		return err
	}

	if d1 == nil {
		d.Delete("P")
		return nil
	}

	_, err = validateNameEntry(xRefTable, d1, "pageDict", "Type", REQUIRED, V10, func(s string) bool { return s == "Page" })

	return err
}

func validateAppearDictEntry(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "AP", required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateAppearanceDict(xRefTable, d1)
	}

	return err
}

func validateDashPatternArray(xRefTable *XRefTable, arr Array) bool {
	// len must be 0,1,2,3 numbers (dont'allow only 0s)

	if len(arr) > 3 {
		return false
	}

	all0 := true
	for j := 0; j < len(arr); j++ {
		o, err := xRefTable.Dereference(arr[j])
		if err != nil || o == nil {
			return false
		}

		var f float64

		switch o := o.(type) {
		case Integer:
			f = float64(o.Value())
		case Float:
			f = o.Value()
		default:
			return false
		}

		if f < 0 {
			return false
		}

		if f != 0 {
			all0 = false
		}

	}

	if all0 {
		if xRefTable.ValidationMode != ValidationRelaxed {
			return false
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Println("digesting invalid dash pattern array: %s", arr)
		// }
	}

	return true
}

func validateBorderArray(xRefTable *XRefTable, a Array) bool {
	if len(a) == 0 {
		return true
	}

	if xRefTable.Version() == V10 {
		return len(a) == 3
	}

	if !(len(a) == 3 || len(a) == 4) {
		return false
	}

	for i := 0; i < len(a); i++ {

		if i == 3 {
			// validate dash pattern array
			// len must be 0,1,2,3 numbers (dont'allow only 0s)
			dpa, ok := a[i].(Array)
			if !ok {
				return xRefTable.ValidationMode == ValidationRelaxed
			}

			if len(dpa) == 0 {
				return true
			}

			return validateDashPatternArray(xRefTable, dpa)
		}

		o, err := xRefTable.Dereference(a[i])
		if err != nil || o == nil {
			return false
		}

		var f float64

		switch o := o.(type) {
		case Integer:
			f = float64(o.Value())
		case Float:
			f = o.Value()
		default:
			return false
		}

		if f < 0 {
			return false
		}
	}

	return true
}

func validateAnnotationDictGeneralPart1(xRefTable *XRefTable, d Dict, dictName string) (*NameType, error) {
	// Type, optional, name
	if _, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "Annot" }); err != nil {
		return nil, err
	}

	// Subtype, required, name
	subtype, err := validateNameEntry(xRefTable, d, dictName, "Subtype", REQUIRED, V10, nil)
	if err != nil {
		return nil, err
	}

	// Rect, required, rectangle
	if _, err = validateRectangleEntry(xRefTable, d, dictName, "Rect", REQUIRED, V10, nil); err != nil {
		return nil, err
	}

	// Contents, optional, text string
	if _, err = validateStringEntry(xRefTable, d, dictName, "Contents", OPTIONAL, V10, nil); err != nil {
		if xRefTable.ValidationMode != ValidationRelaxed {
			return nil, err
		}
		i, err := validateIntegerEntry(xRefTable, d, dictName, "Contents", OPTIONAL, V10, nil)
		if err != nil {
			return nil, err
		}
		if i != nil {
			// Repair
			s := strconv.Itoa(i.Value())
			d["Contents"] = StringLiteral(s)
		}
	}

	// P, optional, indRef of page dict
	if err = validateEntryP(xRefTable, d, dictName, OPTIONAL, V10); err != nil {
		return nil, err
	}

	// NM, optional, text string, since V1.4
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if _, err = validateStringEntry(xRefTable, d, dictName, "NM", OPTIONAL, sinceVersion, nil); err != nil {
		return nil, err
	}

	return subtype, nil
}

func validateAnnotationDictGeneralPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// M, optional, date string in any format, since V1.1
	if _, err := validateStringEntry(xRefTable, d, dictName, "M", OPTIONAL, V11, nil); err != nil {
		return err
	}

	// F, optional integer, since V1.1, annotation flags
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "F", OPTIONAL, V11, nil); err != nil {
		return err
	}

	// AP, optional, appearance dict, since V1.2
	if err := validateAppearDictEntry(xRefTable, d, dictName, OPTIONAL, V12); err != nil {
		return err
	}

	// AS, optional, name, since V1.2
	if _, err := validateNameEntry(xRefTable, d, dictName, "AS", OPTIONAL, V11, nil); err != nil {
		return err
	}

	// Border, optional, array of numbers
	obj, found := d.Find("BS")
	if !found || obj == nil || xRefTable.Version() < V12 {
		a, err := validateArrayEntry(xRefTable, d, dictName, "Border", OPTIONAL, V10, nil)
		if err != nil {
			return err
		}
		if !validateBorderArray(xRefTable, a) {
			return errors.Errorf("invalid border array: %s", a)
		}
	}

	// C, optional array, of numbers, since V1.1
	if _, err := validateNumberArrayEntry(xRefTable, d, dictName, "C", OPTIONAL, V11, nil); err != nil {
		return err
	}

	// StructParent, optional, integer, since V1.3
	if _, err := validateIntegerEntry(xRefTable, d, dictName, "StructParent", OPTIONAL, V13, nil); err != nil {
		return err
	}

	return nil
}

func validateAnnotationDictGeneral(xRefTable *XRefTable, d Dict, dictName string) (*NameType, error) {
	subType, err := validateAnnotationDictGeneralPart1(xRefTable, d, dictName)
	if err != nil {
		return nil, err
	}

	return subType, validateAnnotationDictGeneralPart2(xRefTable, d, dictName)
}

func validateAnnotationDictConcrete(xRefTable *XRefTable, d Dict, dictName string, subtype NameType) error {
	// OC, optional, content group dict or content membership dict, since V1.5
	// Specifying the optional content properties for the annotation.
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	if err := validateOptionalContent(xRefTable, d, dictName, "OC", OPTIONAL, sinceVersion); err != nil {
		return err
	}

	// see table 169

	for k, v := range map[string]struct {
		validate     func(xRefTable *XRefTable, d Dict, dictName string) error
		sinceVersion Version
		markup       bool
	}{
		"Text":           {validateAnnotationDictText, V10, true},
		"Link":           {validateAnnotationDictLink, V10, false},
		"FreeText":       {validateAnnotationDictFreeText, V12, true}, // V13
		"Line":           {validateAnnotationDictLine, V13, true},
		"Polygon":        {validateAnnotationDictPolyLine, V14, true}, // V15
		"PolyLine":       {validateAnnotationDictPolyLine, V14, true}, // V15
		"Highlight":      {validateTextMarkupAnnotation, V13, true},
		"Underline":      {validateTextMarkupAnnotation, V13, true},
		"Squiggly":       {validateTextMarkupAnnotation, V14, true},
		"StrikeOut":      {validateTextMarkupAnnotation, V13, true},
		"Square":         {validateAnnotationDictCircleOrSquare, V13, true},
		"Circle":         {validateAnnotationDictCircleOrSquare, V13, true},
		"Stamp":          {validateAnnotationDictStamp, V13, true},
		"Caret":          {validateAnnotationDictCaret, V14, true}, // V15
		"Ink":            {validateAnnotationDictInk, V13, true},
		"Popup":          {validateAnnotationDictPopup, V12, false}, // V13
		"FileAttachment": {validateAnnotationDictFileAttachment, V13, true},
		"Sound":          {validateAnnotationDictSound, V12, true},
		"Movie":          {validateAnnotationDictMovie, V12, false},
		"Widget":         {validateAnnotationDictWidget, V12, false},
		"Screen":         {validateAnnotationDictScreen, V14, false}, //  V15
		"PrinterMark":    {validateAnnotationDictPrinterMark, V14, false},
		"TrapNet":        {validateAnnotationDictTrapNet, V13, false},
		"Watermark":      {validateAnnotationDictWatermark, V16, false},
		"3D":             {validateAnnotationDict3D, V16, false},
		"Redact":         {validateAnnotationDictRedact, V17, true},
		"RichMedia":      {validateRichMediaAnnotation, V17, false},
	} {
		if subtype.Value() == k {

			err := xRefTable.ValidateVersion(k, v.sinceVersion)
			if err != nil {
				return err
			}

			if v.markup {
				err := validateMarkupAnnotation(xRefTable, d)
				if err != nil {
					return err
				}
			}

			return v.validate(xRefTable, d, k)
		}
	}

	xRefTable.CustomExtensions = true

	return nil
}

func validateAnnotationDict(xRefTable *XRefTable, d Dict) (isTrapNet bool, err error) {
	dictName := "annotDict"

	subtype, err := validateAnnotationDictGeneral(xRefTable, d, dictName)
	if err != nil {
		return false, err
	}

	if err = validateAnnotationDictConcrete(xRefTable, d, dictName, *subtype); err != nil {
		return false, err
	}

	return *subtype == "TrapNet", nil
}

func addAnnotation(ann AnnotationRenderer, pgAnnots PgAnnots, i int, hasIndRef bool, indRef IndirectRef) {
	annots, ok := pgAnnots[ann.Type()]
	if !ok {
		annots = Annot{}
		annots.IndRefs = &[]IndirectRef{}
		annots.Map = AnnotMap{}
		pgAnnots[ann.Type()] = annots
	}

	objNr := -i
	if hasIndRef {
		objNr = indRef.ObjectNumber.Value()
		*(annots.IndRefs) = append(*(annots.IndRefs), indRef)
	}
	annots.Map[objNr] = ann
}

func linkAnnotation(xRefTable *XRefTable, d Dict, r *Rectangle, apObjNr int, contents, nm string, f AnnotationFlags) (AnnotationRenderer, error) {
	var uri string
	o, found := d.Find("A")
	if found && o != nil {
		d, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return nil, err
		}

		bb, err := xRefTable.DereferenceStringEntryBytes(d, "URI")
		if err != nil {
			return nil, err
		}
		if len(bb) > 0 {
			uri = string(bb)
		}
	}
	dest := (*Destination)(nil) // will not collect link dest during validation.
	return NewLinkAnnotation(*r, apObjNr, contents, nm, "", f, nil, dest, uri, nil, false, 0, BSSolid), nil
}

// Annotation returns an annotation renderer.
// Validation sets up a cache of annotation renderers.
func Annotation(xRefTable *XRefTable, d Dict) (AnnotationRenderer, error) {
	subtype := d.NameEntry("Subtype")

	o, _ := d.Find("Rect")
	arr, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return nil, err
	}

	r, err := xRefTable.RectForArray(arr)
	if err != nil {
		return nil, err
	}

	var apObjNr int
	indRef := d.IndirectRefEntry("AP")
	if indRef != nil {
		apObjNr = indRef.ObjectNumber.Value()
	}

	contents := ""
	if c, ok := d["Contents"]; ok {
		contents, err = xRefTable.DereferenceStringOrHexLiteral(c, V10, nil)
		if err != nil {
			return nil, err
		}
		contents = RemoveControlChars(contents)
	}

	var nm string
	s := d.StringEntry("NM") // This is what pdfcpu refers to as the annotation id.
	if s != nil {
		nm = *s
	}

	var f AnnotationFlags
	i := d.IntEntry("F")
	if i != nil {
		f = AnnotationFlags(*i)
	}

	var ann AnnotationRenderer

	switch *subtype {

	case "Text":
		popupIndRef := d.IndirectRefEntry("Popup")
		ann = NewTextAnnotation(*r, apObjNr, contents, nm, "", f, nil, "", popupIndRef, nil, "", "", 0, 0, 0, true, "")

	case "Link":
		ann, err = linkAnnotation(xRefTable, d, r, apObjNr, contents, nm, f)
		if err != nil {
			return nil, err
		}

	case "Popup":
		parentIndRef := d.IndirectRefEntry("Parent")
		ann = NewPopupAnnotation(*r, apObjNr, contents, nm, "", f, nil, 0, 0, 0, parentIndRef, false)

	// TODO handle remaining annotation

	default:
		ann = NewAnnotationForRawType(*subtype, *r, apObjNr, contents, nm, "", f, nil, 0, 0, 0)

	}

	return ann, nil
}

func validateAnnotationsArray(xRefTable *XRefTable, a Array) error {
	// a ... array of indrefs to annotation dicts.

	var annotDict Dict

	pgAnnots := PgAnnots{}
	xRefTable.PageAnnots[xRefTable.CurPage] = pgAnnots

	// an optional TrapNetAnnotation has to be the final entry in this list.
	hasTrapNet := false

	for i, v := range a {

		if hasTrapNet {
			return errors.New("pdfcpu: validatePageAnnotations: invalid page annotation list, \"TrapNet\" has to be the last entry")
		}

		var (
			ok        bool
			hasIndRef bool
			indRef    IndirectRef
			incr      int
			err       error
		)

		if indRef, ok = v.(IndirectRef); ok {
			hasIndRef = true
			// if log.ValidateEnabled() {
			// 	log.Validate.Printf("processing annotDict %d\n", indRef.ObjectNumber)
			// }
			annotDict, incr, err = xRefTable.DereferenceDictWithIncr(indRef)
			if err != nil {
				return err
			}
			if len(annotDict) == 0 {
				continue
			}
		} else if xRefTable.ValidationMode != ValidationRelaxed {
			return errInvalidPageAnnotArray
		} else if annotDict, ok = v.(Dict); !ok {
			return errInvalidPageAnnotArray
		} else {
			// if log.ValidateEnabled() {
			// 	log.Validate.Println("digesting page annotation array w/o indirect references")
			// }
		}

		if hasIndRef {
			objNr := indRef.ObjectNumber.Value()
			if objNr > 0 {
				if err := cacheSig(xRefTable, annotDict, "formFieldDict", false, objNr, incr); err != nil {
					return err
				}
			}
		}

		hasTrapNet, err = validateAnnotationDict(xRefTable, annotDict)
		if err != nil {
			return err
		}

		// Collect annotation.

		ann, err := Annotation(xRefTable, annotDict)
		if err != nil {
			return err
		}

		addAnnotation(ann, pgAnnots, i, hasIndRef, indRef)
	}

	return nil
}

func validatePageAnnotations(xRefTable *XRefTable, d Dict) error {
	a, err := validateArrayEntry(xRefTable, d, "pageDict", "Annots", OPTIONAL, V10, nil)
	if err != nil || a == nil {
		return err
	}

	if len(a) == 0 {
		return nil
	}

	return validateAnnotationsArray(xRefTable, a)
}

func validatePagesAnnotations(xRefTable *XRefTable, d Dict, curPage int) (int, error) {
	// Iterate over page tree.
	kidsArray := d.ArrayEntry("Kids")

	for _, v := range kidsArray {

		if v == nil {
			// if log.ValidateEnabled() {
			// 	log.Validate.Println("validatePagesAnnotations: kid is nil")
			// }
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return curPage, err
		}
		if d == nil {
			return curPage, errors.New("pdfcpu: validatePagesAnnotations: pageNodeDict is null")
		}
		dictType := d.Type()
		if dictType == nil {
			return curPage, errors.New("pdfcpu: validatePagesAnnotations: missing pageNodeDict type")
		}

		switch *dictType {

		case "Pages":
			// Recurse over pagetree
			curPage, err = validatePagesAnnotations(xRefTable, d, curPage)
			if err != nil {
				return curPage, err
			}

		case "Page":
			curPage++
			xRefTable.CurPage = curPage
			if err = validatePageAnnotations(xRefTable, d); err != nil {
				return curPage, err
			}

		default:
			return curPage, errors.Errorf("validatePagesAnnotations: expected dict type: %s\n", *dictType)

		}

	}

	return curPage, nil
}

func validateGoTo3DViewActionDict(xRefTable *XRefTable, d Dict, dictName string) error {
	// see 12.6.4.15

	// TA, required, target annotation
	d1, err := validateDictEntry(xRefTable, d, dictName, "TA", REQUIRED, V16, nil)
	if err != nil {
		return err
	}

	_, err = validateAnnotationDict(xRefTable, d1)
	if err != nil {
		return err
	}

	// V, required, the view to use: 3DViewDict or integer or text string or name
	// TODO Validation.
	_, err = validateEntry(xRefTable, d, dictName, "V", REQUIRED, V16)

	return err
}

func validateActionDictCore(xRefTable *XRefTable, n *NameType, d Dict) error {
	for k, v := range map[string]struct {
		validate     func(xRefTable *XRefTable, d Dict, dictName string) error
		sinceVersion Version
	}{
		"GoTo":        {validateGoToActionDict, V10},
		"GoToR":       {validateGoToRActionDict, V10},
		"GoToE":       {validateGoToEActionDict, V16},
		"Launch":      {validateLaunchActionDict, V10},
		"Thread":      {validateThreadActionDict, V10},
		"URI":         {validateURIActionDict, V10},
		"Sound":       {validateSoundActionDict, V12},
		"Movie":       {validateMovieActionDict, V12},
		"Hide":        {validateHideActionDict, V12},
		"Named":       {validateNamedActionDict, V12},
		"SubmitForm":  {validateSubmitFormActionDict, V10},
		"ResetForm":   {validateResetFormActionDict, V12},
		"ImportData":  {validateImportDataActionDict, V12},
		"JavaScript":  {validateJavaScriptActionDict, V13},
		"SetOCGState": {validateSetOCGStateActionDict, V15},
		"Rendition":   {validateRenditionActionDict, V14}, // V15
		"Trans":       {validateTransActionDict, V15},
		"GoTo3DView":  {validateGoTo3DViewActionDict, V16},
	} {
		if n.Value() == k {

			err := xRefTable.ValidateVersion(k, v.sinceVersion)
			if err != nil {
				return err
			}

			return v.validate(xRefTable, d, k)
		}
	}

	return errors.Errorf("validateActionDictCore: unsupported action type: %s\n", *n)
}

func validateActionDict(xRefTable *XRefTable, d Dict) error {
	dictName := "actionDict"

	// Type, optional, name
	allowedTypes := []string{"Action"}
	if xRefTable.ValidationMode == ValidationRelaxed {
		allowedTypes = []string{"A", "Action"}
	}
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return MemberOf(s, allowedTypes) })
	if err != nil {
		return err
	}

	// S, required, name, action Type
	s, err := validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	err = validateActionDictCore(xRefTable, s, d)
	if err != nil {
		return err
	}

	if o, ok := d.Find("Next"); ok {

		// either optional action dict
		d, err := xRefTable.DereferenceDict(o)
		if err == nil {
			return validateActionDict(xRefTable, d)
		}

		// or optional array of action dicts
		a, err := xRefTable.DereferenceArray(o)
		if err != nil {
			return err
		}

		for _, v := range a {

			d, err := xRefTable.DereferenceDict(v)
			if err != nil {
				return err
			}

			if d == nil {
				continue
			}

			err = validateActionDict(xRefTable, d)
			if err != nil {
				return err
			}
		}

	}

	return nil
}

func validateRootAdditionalActions(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	return validateAdditionalActions(xRefTable, rootDict, "rootDict", "AA", required, sinceVersion, "root")
}

func validateAdditionalActions(xRefTable *XRefTable, dict Dict, dictName, entryName string, required bool, sinceVersion Version, source string) error {
	d, err := validateDictEntry(xRefTable, dict, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	validateAdditionalAction := func(s, source string) bool {
		switch source {

		case "root":
			if MemberOf(s, []string{"WC", "WS", "DS", "WP", "DP"}) {
				return true
			}

		case "page":
			if MemberOf(s, []string{"O", "C"}) {
				return true
			}

		case "fieldOrAnnot":
			// A terminal form field may be merged with a widget annotation.
			fieldOptions := []string{"K", "F", "V", "C"}
			annotOptions := []string{"E", "X", "D", "U", "Fo", "Bl", "PO", "PC", "PV", "Pl"}
			options := append(fieldOptions, annotOptions...)
			if MemberOf(s, options) {
				return true
			}

		}

		return false
	}

	for k, v := range d {

		if !validateAdditionalAction(k, source) {
			return errors.Errorf("validateAdditionalActions: action %s not allowed for source %s", k, source)
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateActionDict(xRefTable, d)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateOpenAction(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.3.2 Destinations, 12.6 Actions

	// A value specifying a destination that shall be displayed
	// or an action that shall be performed when the document is opened.
	// The value shall be either an array defining a destination (see 12.3.2, "Destinations")
	// or an action dictionary representing an action (12.6, "Actions").
	//
	// If this entry is absent, the document shall be opened
	// to the top of the first page at the default magnification factor.

	o, err := validateEntry(xRefTable, rootDict, "rootDict", "OpenAction", required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case Dict:
		err = validateActionDict(xRefTable, o)

	case Array:
		err = validateDestinationArray(xRefTable, o)

	default:
		err = errors.New("pdfcpu: validateOpenAction: unexpected object")
	}

	return err
}

func validateURI(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.6.4.7 URI Actions

	// URI dict with one optional entry Base, ASCII string

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "URI", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	// Base, optional, ASCII string
	_, err = validateStringEntry(xRefTable, d, "URIdict", "Base", OPTIONAL, V10, nil)

	return err
}

func validateMarkInfo(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 14.7 Logical Structure

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "MarkInfo", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	var isTaggedPDF bool

	dictName := "markInfoDict"

	// Marked, optional, boolean
	marked, err := validateBooleanEntry(xRefTable, d, dictName, "Marked", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}
	if marked != nil {
		isTaggedPDF = *marked
	}

	// Suspects: optional, since V1.6, boolean
	sinceVersion = V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V14
	}
	suspects, err := validateBooleanEntry(xRefTable, d, dictName, "Suspects", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if suspects != nil && *suspects {
		isTaggedPDF = false
	}

	xRefTable.Tagged = isTaggedPDF

	// UserProperties: optional, since V1.6, boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "UserProperties", OPTIONAL, V16, nil)

	return err
}

func validateLang(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	_, err := validateStringEntry(xRefTable, rootDict, "rootDict", "Lang", required, sinceVersion, nil)
	return err
}

func validateCaptureCommandDictArray(xRefTable *XRefTable, a Array) error {
	for _, o := range a {

		d, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateCaptureCommandDict(xRefTable, d)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateWebCaptureInfoDict(xRefTable *XRefTable, d Dict) error {
	dictName := "webCaptureInfoDict"

	// V, required, since V1.3, number
	_, err := validateNumberEntry(xRefTable, d, dictName, "V", REQUIRED, V13, nil)
	if err != nil {
		return err
	}

	// C, optional, since V1.3, array of web capture command dict indRefs
	a, err := validateIndRefArrayEntry(xRefTable, d, dictName, "C", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	if a != nil {
		err = validateCaptureCommandDictArray(xRefTable, a)
	}

	return err
}

func validateSpiderInfo(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// 14.10.2 Web Capture Information Dictionary

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "SpiderInfo", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	return validateWebCaptureInfoDict(xRefTable, d)
}

func validateOutputIntentDict(xRefTable *XRefTable, d Dict) error {
	dictName := "outputIntentDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "OutputIntent" })
	if err != nil {
		return err
	}

	// S: required, name
	_, err = validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// OutputCondition, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "OutputCondition", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// OutputConditionIdentifier, required, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "OutputConditionIdentifier", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// RegistryName, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "RegistryName", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// Info, optional, text string
	_, err = validateStringEntry(xRefTable, d, dictName, "Info", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// DestOutputProfile, optional, streamDict
	_, err = validateStreamDictEntry(xRefTable, d, dictName, "DestOutputProfile", OPTIONAL, V10, nil)

	return err
}

func validateOutputIntents(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 14.11.5 Output Intents

	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}

	a, err := validateArrayEntry(xRefTable, rootDict, "rootDict", "OutputIntents", required, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for _, o := range a {

		d, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateOutputIntentDict(xRefTable, d)
		if err != nil {
			return err
		}
	}

	return nil
}

func validatePieceDict(xRefTable *XRefTable, d Dict) error {
	dictName := "pieceDict"

	for _, o := range d {

		d1, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return err
		}

		if d1 == nil {
			continue
		}

		required := REQUIRED
		if xRefTable.ValidationMode == ValidationRelaxed {
			required = OPTIONAL
		}
		_, err = validateDateEntry(xRefTable, d1, dictName, "LastModified", required, V10)
		if err != nil {
			return err
		}

		_, err = validateEntry(xRefTable, d1, dictName, "Private", OPTIONAL, V10)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateRootPieceInfo(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	if xRefTable.ValidationMode == ValidationRelaxed {
		return nil
	}

	_, err := validatePieceInfo(xRefTable, rootDict, "rootDict", "PieceInfo", required, sinceVersion)

	return err
}

func validatePieceInfo(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) (hasPieceInfo bool, err error) {
	// 14.5 Page-Piece Dictionaries

	pieceDict, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || pieceDict == nil {
		return false, err
	}

	err = validatePieceDict(xRefTable, pieceDict)

	return hasPieceInfo, err
}

func validatePermissionsxReftable(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.8.4 Permissions

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "Perms", required, sinceVersion, nil)
	if err != nil {
		return err
	}
	if len(d) == 0 {
		return nil
	}

	i := 0

	if indRef := d.IndirectRefEntry("DocMDP"); indRef != nil {
		d1, err := xRefTable.DereferenceDict(*indRef)
		if err != nil {
			return err
		}
		if len(d1) > 0 {
			xRefTable.CertifiedSigObjNr = indRef.ObjectNumber.Value()
			i++
		}
	}

	d1, err := validateDictEntry(xRefTable, d, "permDict", "UR3", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if len(d1) == 0 {
		return nil
	}

	xRefTable.URSignature = d1
	i++

	if i == 0 {
		return errors.New("pdfcpu: validatePermissions: unsupported permissions detected")
	}

	return nil
}

// TODO implement
func validateLegal(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.8.5 Legal Content Attestations

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "Legal", required, sinceVersion, nil)
	if err != nil || len(d) == 0 {
		return err
	}

	return errors.New("pdfcpu: \"Legal\" not supported")
}

func validateRequirementDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "requirementDict"

	// Type, optional, name,
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Requirement" })
	if err != nil {
		return err
	}

	// S, required, name
	_, err = validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, sinceVersion, func(s string) bool { return s == "EnableJavaScripts" })
	if err != nil {
		return err
	}

	// The RH entry (requirement handler dicts) shall not be used in PDF 1.7.

	return nil
}

func validateRequirements(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.10 Document Requirements

	a, err := validateArrayEntry(xRefTable, rootDict, "rootDict", "Requirements", required, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for _, o := range a {

		d, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateRequirementDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateCollectionFieldDict(xRefTable *XRefTable, d Dict) error {
	dictName := "colFlddict"

	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "CollectionField" })
	if err != nil {
		return err
	}

	// Subtype, required name
	subTypes := []string{"S", "D", "N", "F", "Desc", "ModDate", "CreationDate", "Size"}

	if xRefTable.ValidationMode == ValidationRelaxed {
		// See i659.pdf
		subTypes = append(subTypes, "AFRelationship")
		subTypes = append(subTypes, "CompressedSize")
	}

	validateCollectionFieldSubtype := func(s string) bool {
		return MemberOf(s, subTypes)
	}
	_, err = validateNameEntry(xRefTable, d, dictName, "Subtype", REQUIRED, V10, validateCollectionFieldSubtype)
	if err != nil {
		return err
	}

	// N, required text string
	_, err = validateStringEntry(xRefTable, d, dictName, "N", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// O, optional integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "O", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// V, optional boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "V", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// E, optional boolean
	_, err = validateBooleanEntry(xRefTable, d, dictName, "E", OPTIONAL, V10, nil)

	return err
}

func validateCollectionSchemaDict(xRefTable *XRefTable, d Dict) error {
	for k, v := range d {

		if k == "Type" {

			var n NameType
			n, err := xRefTable.DereferenceName(v, V10, nil)
			if err != nil {
				return err
			}

			if n != "CollectionSchema" {
				return errors.New("pdfcpu: validateCollectionSchemaDict: invalid entry \"Type\"")
			}

			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateCollectionFieldDict(xRefTable, d)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateNameOrArrayOfName(xRefTable *XRefTable, o Object, dictName, entryName string) error {
	switch o := o.(type) {

	case NameType:
		// no further processing

	case Array:

		for i, o := range o {

			o, err := xRefTable.Dereference(o)
			if err != nil {
				return err
			}

			if o == nil {
				continue
			}

			if _, ok := o.(NameType); !ok {
				err = errors.Errorf("pdfcpu: validateNameOrArrayOfName: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
				return err
			}

		}

	default:
		return errors.Errorf("pdfcpu: validateNameOrArrayOfName: dict=%s entry=%s invalid type", dictName, entryName)
	}

	return nil
}

func validateNameOrArrayOfNameEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameOrArrayOfNameEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateNameOrArrayOfNameEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateNameOrArrayOfNameEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	if err := validateNameOrArrayOfName(xRefTable, o, dictName, entryName); err != nil {
		return err
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateNameOrArrayOfNameEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateBooleanOrArrayOfBoolean(xRefTable *XRefTable, o Object, dictName, entryName string) error {
	switch o := o.(type) {

	case Boolean:
		// no further processing

	case Array:

		for i, o := range o {

			o, err := xRefTable.Dereference(o)
			if err != nil {
				return err
			}

			if o == nil {
				continue
			}

			if _, ok := o.(Boolean); !ok {
				return errors.Errorf("pdfcpu: validateBooleanOrArrayOfBoolean: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
			}

		}

	default:
		return errors.Errorf("pdfcpu: validateBooleanOrArrayOfBoolean: dict=%s entry=%s invalid type", dictName, entryName)
	}

	return nil
}

func validateBooleanOrArrayOfBooleanEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanOrArrayOfBooleanEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateBooleanOrArrayOfBooleanEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateBooleanOrArrayOfBooleanEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	if err := validateBooleanOrArrayOfBoolean(xRefTable, o, dictName, entryName); err != nil {
		return err
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanOrArrayOfBooleanEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateCollectionSortDict(xRefTable *XRefTable, d Dict) error {
	dictName := "colSortDict"

	// S, required name or array of names.
	err := validateNameOrArrayOfNameEntry(xRefTable, d, dictName, "S", REQUIRED, V10)
	if err != nil {
		return err
	}

	// A, optional boolean or array of booleans.
	err = validateBooleanOrArrayOfBooleanEntry(xRefTable, d, dictName, "A", OPTIONAL, V10)

	return err
}

func validateInitialView(s string) bool { return s == "D" || s == "T" || s == "H" }
func validateDictEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Dict) bool) (Dict, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateDictEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("validateDictEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateDictEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	d, ok := o.(Dict)
	if !ok {
		return nil, errors.Errorf("validateDictEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// Validation
	if validate != nil && !validate(d) {
		return nil, errors.Errorf("validateDictEntry: dict=%s entry=%s invalid dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateDictEntry end: entry=%s\n", entryName)
	// }

	return d, nil
}

func decodeString(o Object, dictName, entryName string) (s string, err error) {
	switch o := o.(type) {
	case StringLiteral:
		s, err = StringLiteralToString(o)
	case HexLiteral:
		s, err = HexLiteralToString(o)
	default:
		err = errors.Errorf("pdfcpu: decodeString: dict=%s entry=%s invalid type %T", dictName, entryName, o)
	}
	return s, err
}

func validateStringEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(string) bool) (*string, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStringEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("pdfcpu: validateStringEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateStringEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion(fmt.Sprintf("dict=%s entry=%s", dictName, entryName), sinceVersion); err != nil {
		return nil, err
	}

	s, err := decodeString(o, dictName, entryName)
	if err != nil {
		return nil, err
	}

	// Validation
	if validate != nil && (required || len(s) > 0) && !validate(s) {
		return nil, errors.Errorf("pdfcpu: validateStringEntry: dict=%s entry=%s invalid dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateStringEntry end: entry=%s\n", entryName)
	// }

	return &s, nil
}

func validateCollection(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.3.5 Collections

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "Collection", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	dictName := "Collection"

	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Collection" })
	if err != nil {
		return err
	}

	// Schema, optional dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "Schema", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateCollectionSchemaDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	// D, optional string
	_, err = validateStringEntry(xRefTable, d, dictName, "D", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// View, optional name
	_, err = validateNameEntry(xRefTable, d, dictName, "View", OPTIONAL, sinceVersion, validateInitialView)
	if err != nil {
		return err
	}

	// Sort, optional dict
	d1, err = validateDictEntry(xRefTable, d, dictName, "Sort", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		err = validateCollectionSortDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateBooleanEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(bool) bool) (*bool, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("validateBooleanEntry: dict=%s required entry=%s missing", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateBooleanEntry end: entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	b, ok := o.(Boolean)
	if !ok {
		return nil, errors.Errorf("validateBooleanEntry: dict=%s entry=%s invalid type", dictName, entryName)
	}

	// Validation
	if validate != nil && !validate(b.Value()) {
		return nil, errors.Errorf("validateBooleanEntry: dict=%s entry=%s invalid name dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanEntry end: entry=%s\n", entryName)
	// }

	flag := b.Value()
	return &flag, nil
}

func validateNeedsRendering(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	_, err := validateBooleanEntry(xRefTable, rootDict, "rootDict", "NeedsRendering", required, sinceVersion, nil)
	return err
}

func validateDSS(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.8.4.3 Document Security Store

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "DSS", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	xRefTable.DSS = d

	return nil
}

func validateArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateArrayEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return nil, err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return nil, err
	}

	if o == nil {
		if required {
			return nil, errors.Errorf("validateArrayEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateArrayEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// Version check
	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return nil, err
	}

	a, ok := o.(Array)
	if !ok {
		return nil, errors.Errorf("validateArrayEntry: dict=%s entry=%s invalid type %T", dictName, entryName, o)
	}

	// Validation
	if validate != nil && !validate(a) {
		return nil, errors.Errorf("validateArrayEntry: dict=%s entry=%s invalid dict entry", dictName, entryName)
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateAF(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 14.13 Associated Files

	a, err := validateArrayEntry(xRefTable, rootDict, "rootDict", "AF", required, sinceVersion, nil)
	if err != nil || len(a) == 0 {
		return err
	}

	return errors.New("pdfcpu: PDF2.0 \"AF\" not supported")
}

func validateDPartRoot(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 14.12 Document Parts

	d, err := validateDictEntry(xRefTable, rootDict, "rootDict", "DPartRoot", required, sinceVersion, nil)
	if err != nil || len(d) == 0 {
		return err
	}

	return errors.New("pdfcpu: PDF2.0 \"DPartRoot\" not supported")
}

func checkLinks(xRefTable *XRefTable, client http.Client, pages []int) bool {
	var httpErr bool
	for _, page := range pages {
		for uri := range xRefTable.URIs[page] {
			// if log.CLIEnabled() {
			// 	fmt.Printf(".")
			// }
			_, err := url.ParseRequestURI(uri)
			if err != nil {
				httpErr = true
				xRefTable.URIs[page][uri] = "i"
				continue
			}
			res, err := client.Get(uri)
			if err != nil {
				if e, ok := err.(net.Error); ok && e.Timeout() {
					xRefTable.URIs[page][uri] = "t"
				} else {
					xRefTable.URIs[page][uri] = "s"
				}
				httpErr = true
				continue
			}
			defer res.Body.Close()
			if res.StatusCode != http.StatusOK {
				httpErr = true
				xRefTable.URIs[page][uri] = strconv.Itoa(res.StatusCode)
				continue
			}
		}
	}
	return httpErr
}

func checkForBrokenLinks(ctx *Context) error {
	if !ctx.XRefTable.ValidateLinks {
		return nil
	}
	if len(ctx.URIs) > 0 {
		if ctx.Offline {
			// if log.CLIEnabled() {
			// 	log.CLI.Printf("pdfcpu is offline, can't validate Links")
			// }
			return nil
		}
	}

	// if log.CLIEnabled() {
	// 	log.CLI.Println("validating URIs..")
	// }

	xRefTable := ctx.XRefTable

	pages := []int{}
	for i := range xRefTable.URIs {
		pages = append(pages, i)
	}
	sort.Ints(pages)

	client := http.Client{
		Timeout: time.Duration(ctx.Timeout) * time.Second,
	}

	httpErr := checkLinks(xRefTable, client, pages)

	// if log.CLIEnabled() {
	// 	logURIError(xRefTable, pages)
	// }

	if httpErr {
		return errors.New("broken links detected")
	}

	return nil
}

// see 8.4.5 Graphics State Parameter Dictionaries

func validateBlendMode(s string) bool {
	// see 11.3.5; table 136

	return MemberOf(s, []string{
		"None", "Normal", "Compatible", "Multiply", "Screen", "Overlay", "Darken", "Lighten",
		"ColorDodge", "ColorBurn", "HardLight", "SoftLight", "Difference", "Exclusion",
		"Hue", "Saturation", "Color", "Luminosity",
	})
}

func validateIntegerArray(xRefTable *XRefTable, o Object) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateIntegerArray begin")
	// }

	a, err := xRefTable.DereferenceArray(o)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		switch o.(type) {

		case Integer:
			// no further processing.

		default:
			return nil, errors.Errorf("pdfcpu: validateIntegerArray: invalid type at index %d\n", i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateIntegerArray end")
	// }

	return a, nil
}

func validateLineDashPatternEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, func(a Array) bool { return len(a) == 2 })
	if err != nil || a == nil {
		return err
	}

	_, err = validateIntegerArray(xRefTable, a[0])
	if err != nil {
		return err
	}

	_, err = validateInteger(xRefTable, a[1], nil)

	return err
}

func validateBGEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		if xRefTable.ValidationMode == ValidationStrict {
			err = errors.Errorf("pdfcpu: validateBGEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)
			break
		}
		s := o.Value()
		if s != "Identity" {
			err = errors.New("pdfcpu: validateBGEntry: corrupt name")
		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		err = errors.Errorf("pdfcpu: validateBGEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateBG2Entry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if s != "Default" {
			err = errors.New("pdfcpu: validateBG2Entry: corrupt name")
		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		err = errors.Errorf("pdfcpu: validateBG2Entry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateUCREntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		if xRefTable.ValidationMode == ValidationStrict {
			err = errors.Errorf("pdfcpu: validateUCREntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)
			break
		}
		s := o.Value()
		if s != "Identity" {
			err = errors.New("pdfcpu: writeUCREntry: corrupt name")
		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		err = errors.Errorf("pdfcpu: validateUCREntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateUCR2Entry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if s != "Default" {
			err = errors.New("pdfcpu: writeUCR2Entry: corrupt name")
		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		err = errors.Errorf("pdfcpu: validateUCR2Entry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateTransferFunction(xRefTable *XRefTable, o Object) (err error) {
	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if s != "Identity" {
			return errors.New("pdfcpu: validateTransferFunction: corrupt name")
		}

	case Array:

		if len(o) != 4 {
			return errors.New("pdfcpu: validateTransferFunction: corrupt function array")
		}

		for _, o := range o {

			o, err := xRefTable.Dereference(o)
			if err != nil {
				return err
			}
			if o == nil {
				continue
			}

			err = processFunction(xRefTable, o)
			if err != nil {
				return err
			}

		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		return errors.Errorf("validateTransferFunction: corrupt entry: %v\n", o)

	}

	return err
}

func validateTransferFunctionEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	return validateTransferFunction(xRefTable, o)
}

func validateTR(xRefTable *XRefTable, o Object) (err error) {
	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if s != "Identity" {
			return errors.Errorf("pdfcpu: validateTR: corrupt name\n")
		}

	case Array:

		if len(o) != 4 {
			return errors.New("pdfcpu: validateTR: corrupt function array")
		}

		for _, o := range o {

			o, err = xRefTable.Dereference(o)
			if err != nil {
				return
			}

			if o == nil {
				continue
			}

			if o, ok := o.(NameType); ok {
				s := o.Value()
				if s != "Identity" {
					return errors.Errorf("pdfcpu: validateTR: corrupt name\n")
				}
				continue
			}

			err = processFunction(xRefTable, o)
			if err != nil {
				return
			}

		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		return errors.Errorf("validateTR: corrupt entry %v\n", o)

	}

	return err
}

func validateTREntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	return validateTR(xRefTable, o)
}

func validateTR2Name(name NameType) error {
	s := name.Value()
	if s != "Identity" && s != "Default" {
		return errors.Errorf("pdfcpu: validateTR2: corrupt name\n")
	}
	return nil
}

func validateTR2(xRefTable *XRefTable, o Object) (err error) {
	switch o := o.(type) {

	case NameType:
		if err = validateTR2Name(o); err != nil {
			return err
		}

	case Array:

		if len(o) != 4 {
			return errors.New("pdfcpu: validateTR2: corrupt function array")
		}

		for _, o := range o {

			o, err = xRefTable.Dereference(o)
			if err != nil {
				return
			}

			if o == nil {
				continue
			}

			if o, ok := o.(NameType); ok {
				if err = validateTR2Name(o); err != nil {
					return err
				}
				continue
			}

			err = processFunction(xRefTable, o)
			if err != nil {
				return
			}

		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		return errors.Errorf("validateTR2: corrupt entry %v\n", o)

	}

	return err
}

func validateTR2Entry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	return validateTR2(xRefTable, o)
}

func validateSpotFunctionEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		validateSpotFunctionName := func(s string) bool {
			return MemberOf(s, []string{
				"SimpleDot", "InvertedSimpleDot", "DoubleDot", "InvertedDoubleDot", "CosineDot",
				"Double", "InvertedDouble", "Line", "LineX", "LineY", "Round", "Ellipse", "EllipseA",
				"InvertedEllipseA", "EllipseB", "EllipseC", "InvertedEllipseC", "Square", "Cross", "Rhomboid",
			})
		}
		s := o.Value()
		if !validateSpotFunctionName(s) {
			return errors.Errorf("validateSpotFunctionEntry: corrupt name\n")
		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		return errors.Errorf("validateSpotFunctionEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateType1HalftoneDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "type1HalftoneDict"

	// HalftoneName, optional, string
	_, err := validateStringEntry(xRefTable, d, dictName, "HalftoneName", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Frequency, required, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "Frequency", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Angle, required, number
	_, err = validateNumberEntry(xRefTable, d, dictName, "Angle", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// SpotFunction, required, function or name
	err = validateSpotFunctionEntry(xRefTable, d, dictName, "SpotFunction", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// TransferFunction, optional, function
	err = validateTransferFunctionEntry(xRefTable, d, dictName, "TransferFunction", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	_, err = validateBooleanEntry(xRefTable, d, dictName, "AccurateScreens", OPTIONAL, sinceVersion, nil)

	return err
}

func validateType5HalftoneDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "type5HalftoneDict"

	_, err := validateStringEntry(xRefTable, d, dictName, "HalftoneName", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	for _, c := range []string{"Gray", "Red", "Green", "Blue", "Cyan", "Magenta", "Yellow", "Black"} {
		err = validateHalfToneEntry(xRefTable, d, dictName, c, OPTIONAL, sinceVersion)
		if err != nil {
			return err
		}
	}

	return validateHalfToneEntry(xRefTable, d, dictName, "Default", REQUIRED, sinceVersion)
}

func validateType6HalftoneStreamDict(xRefTable *XRefTable, sd *StreamDict, sinceVersion Version) error {
	dictName := "type6HalftoneDict"

	_, err := validateStringEntry(xRefTable, sd.Dict, dictName, "HalftoneName", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Width", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Height", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	return validateTransferFunctionEntry(xRefTable, sd.Dict, dictName, "TransferFunction", OPTIONAL, sinceVersion)
}

func validateType10HalftoneStreamDict(xRefTable *XRefTable, sd *StreamDict, sinceVersion Version) error {
	dictName := "type10HalftoneDict"

	_, err := validateStringEntry(xRefTable, sd.Dict, dictName, "HalftoneName", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Xsquare", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Ysquare", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	return validateTransferFunctionEntry(xRefTable, sd.Dict, dictName, "TransferFunction", OPTIONAL, sinceVersion)
}

func validateType16HalftoneStreamDict(xRefTable *XRefTable, sd *StreamDict, sinceVersion Version) error {
	dictName := "type16HalftoneDict"

	_, err := validateStringEntry(xRefTable, sd.Dict, dictName, "HalftoneName", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Width", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Height", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Width2", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "Height2", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	return validateTransferFunctionEntry(xRefTable, sd.Dict, dictName, "TransferFunction", OPTIONAL, sinceVersion)
}

func validateHalfToneDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "halfToneDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Halftone" })
	if err != nil {
		return err
	}

	// HalftoneType, required, integer
	halftoneType, err := validateIntegerEntry(xRefTable, d, dictName, "HalftoneType", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	switch *halftoneType {

	case 1:
		err = validateType1HalftoneDict(xRefTable, d, sinceVersion)

	case 5:
		err = validateType5HalftoneDict(xRefTable, d, sinceVersion)

	default:
		err = errors.Errorf("validateHalfToneDict: unknown halftoneTyp: %d\n", *halftoneType)

	}

	return err
}

func validateHalfToneStreamDict(xRefTable *XRefTable, sd *StreamDict, sinceVersion Version) error {
	dictName := "writeHalfToneStreamDict"

	// Type, name, optional
	_, err := validateNameEntry(xRefTable, sd.Dict, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Halftone" })
	if err != nil {
		return err
	}

	// HalftoneType, required, integer
	halftoneType, err := validateIntegerEntry(xRefTable, sd.Dict, dictName, "HalftoneType", REQUIRED, sinceVersion, nil)
	if err != nil || halftoneType == nil {
		return err
	}

	switch *halftoneType {

	case 6:
		err = validateType6HalftoneStreamDict(xRefTable, sd, sinceVersion)

	case 10:
		err = validateType10HalftoneStreamDict(xRefTable, sd, sinceVersion)

	case 16:
		err = validateType16HalftoneStreamDict(xRefTable, sd, sinceVersion)

	default:
		err = errors.Errorf("validateHalfToneStreamDict: unknown halftoneTyp: %d\n", *halftoneType)

	}

	return err
}

func validateHalfToneEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) (err error) {
	// See 10.5

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		if o.Value() != "Default" {
			return errors.Errorf("pdfcpu: validateHalfToneEntry: undefined name: %s\n", o)
		}

	case Dict:
		err = validateHalfToneDict(xRefTable, o, sinceVersion)

	case StreamDict:
		err = validateHalfToneStreamDict(xRefTable, &o, sinceVersion)

	default:
		err = errors.New("pdfcpu: validateHalfToneEntry: corrupt (stream)dict")
	}

	return err
}

func validateBlendModeEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		_, err = xRefTable.DereferenceName(o, sinceVersion, validateBlendMode)
		if err != nil {
			return err
		}

	case Array:
		for _, o := range o {
			_, err = xRefTable.DereferenceName(o, sinceVersion, validateBlendMode)
			if err != nil {
				return err
			}
		}

	default:
		return errors.Errorf("validateBlendModeEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return nil
}

func validateSoftMaskTransferFunctionEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if s != "Identity" {
			return errors.New("pdfcpu: validateSoftMaskTransferFunctionEntry: corrupt name")
		}

	case Dict:
		err = processFunction(xRefTable, o)

	case StreamDict:
		err = processFunction(xRefTable, o)

	default:
		return errors.Errorf("pdfcpu: validateSoftMaskTransferFunctionEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateSoftMaskDict(xRefTable *XRefTable, d Dict) error {
	// see 11.6.5.2

	dictName := "softMaskDict"

	// Type, name, optional
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "Mask" })
	if err != nil {
		return err
	}

	// S, name, required
	_, err = validateNameEntry(xRefTable, d, dictName, "S", REQUIRED, V10, func(s string) bool { return s == "Alpha" || s == "Luminosity" })
	if err != nil {
		return err
	}

	// G, stream, required
	// A transparency group XObject (see “Transparency Group XObjects”)
	// to be used as the source of alpha or colour values for deriving the mask.
	sd, err := validateStreamDictEntry(xRefTable, d, dictName, "G", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	if sd != nil {
		err = validateXObjectStreamDict(xRefTable, *sd)
		if err != nil {
			return err
		}
	}

	// TR (Optional) function or name
	// A function object (see “Functions”) specifying the transfer function
	// to be used in deriving the mask values.
	err = validateSoftMaskTransferFunctionEntry(xRefTable, d, dictName, "TR", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// BC, number array, optional
	// Array of component values specifying the colour to be used
	// as the backdrop against which to composite the transparency group XObject G.
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "BC", OPTIONAL, V10, nil)

	return err
}

func validateSoftMaskEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	// see 11.3.7.2 Source Shape and Opacity
	// see 11.6.4.3 Mask Shape and Opacity

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if !validateBlendMode(s) {
			return errors.Errorf("pdfcpu: validateSoftMaskEntry: invalid soft mask: %s\n", s)
		}

	case Dict:
		err = validateSoftMaskDict(xRefTable, o)

	default:
		err = errors.Errorf("pdfcpu: validateSoftMaskEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return err
}

func validateExtGStateDictPart1(xRefTable *XRefTable, d Dict, dictName string) error {
	// LW, number, optional, since V1.3
	_, err := validateNumberEntry(xRefTable, d, dictName, "LW", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// LC, integer, optional, since V1.3
	_, err = validateIntegerEntry(xRefTable, d, dictName, "LC", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// LJ, integer, optional, since V1.3
	_, err = validateIntegerEntry(xRefTable, d, dictName, "LJ", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// ML, number, optional, since V1.3
	_, err = validateNumberEntry(xRefTable, d, dictName, "ML", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// D, array, optional, since V1.3, [dashArray dashPhase(integer)]
	err = validateLineDashPatternEntry(xRefTable, d, dictName, "D", OPTIONAL, V13)
	if err != nil {
		return err
	}

	// RI, name, optional, since V1.3
	_, err = validateNameEntry(xRefTable, d, dictName, "RI", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// OP, boolean, optional,
	_, err = validateBooleanEntry(xRefTable, d, dictName, "OP", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// op, boolean, optional, since V1.3
	_, err = validateBooleanEntry(xRefTable, d, dictName, "op", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// OPM, integer, optional, since V1.3
	_, err = validateIntegerEntry(xRefTable, d, dictName, "OPM", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// Font, array, optional, since V1.3
	_, err = validateArrayEntry(xRefTable, d, dictName, "Font", OPTIONAL, V13, nil)

	return err
}

func validateExtGStateDictPart2(xRefTable *XRefTable, d Dict, dictName string) error {
	// BG, function, optional, black-generation function, see 10.3.4
	err := validateBGEntry(xRefTable, d, dictName, "BG", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// BG2, function or name(/Default), optional, since V1.3
	err = validateBG2Entry(xRefTable, d, dictName, "BG2", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// UCR, function, optional, undercolor-removal function, see 10.3.4
	err = validateUCREntry(xRefTable, d, dictName, "UCR", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// UCR2, function or name(/Default), optional, since V1.3
	err = validateUCR2Entry(xRefTable, d, dictName, "UCR2", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// TR, function, array of 4 functions or name(/Identity), optional, see 10.4 transfer functions
	err = validateTREntry(xRefTable, d, dictName, "TR", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// TR2, function, array of 4 functions or name(/Identity,/Default), optional, since V1.3
	err = validateTR2Entry(xRefTable, d, dictName, "TR2", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// HT, dict, stream or name, optional
	// half tone dictionary or stream or /Default, see 10.5
	err = validateHalfToneEntry(xRefTable, d, dictName, "HT", OPTIONAL, V12)
	if err != nil {
		return err
	}

	// FL, number, optional, since V1.3, flatness tolerance, see 10.6.2
	_, err = validateNumberEntry(xRefTable, d, dictName, "FL", OPTIONAL, V13, nil)
	if err != nil {
		return err
	}

	// SM, number, optional, since V1.3, smoothness tolerance
	sinceVersion := V13
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V12
	}
	_, err = validateNumberEntry(xRefTable, d, dictName, "SM", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// SA, boolean, optional, see 10.6.5 Automatic Stroke Adjustment
	_, err = validateBooleanEntry(xRefTable, d, dictName, "SA", OPTIONAL, V10, nil)

	return err
}

func validateExtGStateDictPart3(xRefTable *XRefTable, d Dict, dictName string) error {
	// BM, name or array, optional, since V1.4
	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	err := validateBlendModeEntry(xRefTable, d, dictName, "BM", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// SMask, dict or name, optional, since V1.4
	sinceVersion = V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	err = validateSoftMaskEntry(xRefTable, d, dictName, "SMask", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// CA, number, optional, since V1.4, current stroking alpha constant, see 11.3.7.2 and 11.6.4.4
	sinceVersion = V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateNumberEntry(xRefTable, d, dictName, "CA", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// ca, number, optional, since V1.4, same as CA but for nonstroking operations.
	sinceVersion = V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateNumberEntry(xRefTable, d, dictName, "ca", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// AIS, alpha source flag "alpha is shape", boolean, optional, since V1.4
	sinceVersion = V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateBooleanEntry(xRefTable, d, dictName, "AIS", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// TK, boolean, optional, since V1.4, text knockout flag.
	sinceVersion = V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateBooleanEntry(xRefTable, d, dictName, "TK", OPTIONAL, sinceVersion, nil)

	return err
}

func validateExtGStateDict(xRefTable *XRefTable, o Object) error {
	// 8.4.5 Graphics State Parameter Dictionaries

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	dictName := "extGStateDict"

	// Type, name, optional
	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "ExtGState" })
	if err != nil {
		return err
	}

	err = validateExtGStateDictPart1(xRefTable, d, dictName)
	if err != nil {
		return err
	}

	err = validateExtGStateDictPart2(xRefTable, d, dictName)
	if err != nil {
		return err
	}

	err = validateExtGStateDictPart3(xRefTable, d, dictName)
	if err != nil {
		return err
	}

	// Check for AAPL extensions.
	o, _, err = d.Entry(dictName, "AAPL:AA", OPTIONAL)
	if err != nil {
		return err
	}
	if o != nil {
		xRefTable.CustomExtensions = true
	}

	return nil
}

func validateExtGStateResourceDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// Version check
	err = xRefTable.ValidateVersion("ExtGStateResourceDict", sinceVersion)
	if err != nil {
		return err
	}

	// Iterate over extGState resource dictionary
	for _, o := range d {

		// Process extGStateDict
		err = validateExtGStateDict(xRefTable, o)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateStandardType1Font(s string) bool {
	return MemberOf(s, []string{
		"Times-Roman", "Times-Bold", "Times-Italic", "Times-BoldItalic",
		"Helvetica", "Helvetica-Bold", "Helvetica-Oblique", "Helvetica-BoldOblique",
		"Courier", "Courier-Bold", "Courier-Oblique", "Courier-BoldOblique",
		"Symbol", "ZapfDingbats",
	})
}

func validateFontFile3SubType(sd *StreamDict, fontType string) error {
	// Hint about used font program.
	dictSubType := sd.Subtype()

	if dictSubType == nil {
		return errors.New("pdfcpu: validateFontFile3SubType: missing Subtype")
	}

	switch fontType {
	case "Type1":
		if *dictSubType != "Type1C" && *dictSubType != "OpenType" {
			return errors.Errorf("pdfcpu: validateFontFile3SubType: Type1: unexpected Subtype %s", *dictSubType)
		}

	case "MMType1":
		if *dictSubType != "Type1C" {
			return errors.Errorf("pdfcpu: validateFontFile3SubType: MMType1: unexpected Subtype %s", *dictSubType)
		}

	case "CIDFontType0":
		if *dictSubType != "CIDFontType0C" && *dictSubType != "OpenType" {
			return errors.Errorf("pdfcpu: validateFontFile3SubType: CIDFontType0: unexpected Subtype %s", *dictSubType)
		}

	case "CIDFontType2", "TrueType":
		if *dictSubType != "OpenType" {
			return errors.Errorf("pdfcpu: validateFontFile3SubType: %s: unexpected Subtype %s", fontType, *dictSubType)
		}
	}

	return nil
}

func validateFontFile(xRefTable *XRefTable, d Dict, dictName string, entryName string, fontType string, required bool, sinceVersion Version) error {
	sd, err := validateStreamDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || sd == nil {
		return err
	}

	// Process font file stream dict entries.

	// SubType
	if entryName == "FontFile3" {
		err = validateFontFile3SubType(sd, fontType)
		if err != nil {
			return err
		}

	}

	dName := "fontFileStreamDict"
	compactFontFormat := entryName == "FontFile3"

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dName, "Length1", (fontType == "Type1" || fontType == "TrueType") && !compactFontFormat, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dName, "Length2", fontType == "Type1" && !compactFontFormat, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dName, "Length3", fontType == "Type1" && !compactFontFormat, V10, nil)
	if err != nil {
		return err
	}

	// Metadata, stream, optional, since 1.4
	return validateMetadata(xRefTable, sd.Dict, OPTIONAL, V14)
}

func validateFontDescriptorType(xRefTable *XRefTable, d Dict) (err error) {
	dictType := d.Type()

	if dictType == nil {
		if xRefTable.ValidationMode == ValidationRelaxed {
			// if log.ValidateEnabled() {
			// 	log.Validate.Println("validateFontDescriptor: missing entry \"Type\"")
			// }
		} else {
			return errors.New("pdfcpu: validateFontDescriptor: missing entry \"Type\"")
		}
	}

	if dictType != nil && *dictType != "FontDescriptor" && *dictType != "Font" {
		return errors.New("pdfcpu: validateFontDescriptor: corrupt font descriptor dict")
	}

	return nil
}

func validateFontDescriptorPart1(xRefTable *XRefTable, d Dict, dictName, fontDictType string) error {
	err := validateFontDescriptorType(xRefTable, d)
	if err != nil {
		return err
	}

	required := true
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = false
	}
	_, err = validateNameEntry(xRefTable, d, dictName, "FontName", required, V10, nil)
	if err != nil {
		_, err = validateStringEntry(xRefTable, d, dictName, "FontName", required, V10, nil)
		if err != nil {
			if xRefTable.ValidationMode != ValidationRelaxed {
				return err
			}
		}
	}

	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateStringEntry(xRefTable, d, dictName, "FontFamily", OPTIONAL, sinceVersion, nil)
	if err != nil {
		// Repair
		_, err = validateNameEntry(xRefTable, d, dictName, "FontFamily", OPTIONAL, sinceVersion, nil)
		return err
	}

	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateNameEntry(xRefTable, d, dictName, "FontStretch", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	sinceVersion = V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err = validateNumberEntry(xRefTable, d, dictName, "FontWeight", OPTIONAL, sinceVersion, nil)
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
		validateFontWeight := func(s string) bool {
			return MemberOf(s, []string{"Regular", "Bold", "Italic"})
		}
		validateNameEntry(xRefTable, d, dictName, "FontWeight", OPTIONAL, sinceVersion, validateFontWeight)
	}

	_, err = validateIntegerEntry(xRefTable, d, dictName, "Flags", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateRectangleEntry(xRefTable, d, dictName, "FontBBox", fontDictType != "Type3", V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "ItalicAngle", REQUIRED, V10, nil)

	return err
}

func validateFontDescriptorPart2(xRefTable *XRefTable, d Dict, dictName, fontDictType string) error {
	_, err := validateNumberEntry(xRefTable, d, dictName, "Ascent", fontDictType != "Type3", V10, nil)
	if err != nil {
		return err
	}

	required := fontDictType != "Type3"
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = false
	}
	_, err = validateNumberEntry(xRefTable, d, dictName, "Descent", required, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "Leading", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "CapHeight", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "XHeight", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	required = fontDictType != "Type3"
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = false
	}
	_, err = validateNumberEntry(xRefTable, d, dictName, "StemV", required, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "StemH", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "AvgWidth", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "MaxWidth", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, d, dictName, "MissingWidth", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	err = validateFontDescriptorFontFile(xRefTable, d, dictName, fontDictType)
	if err != nil {
		return err
	}

	_, err = validateStringEntry(xRefTable, d, dictName, "CharSet", OPTIONAL, V11, nil)

	return err
}

func validateFontDescriptorFontFile(xRefTable *XRefTable, d Dict, dictName, fontDictType string) (err error) {
	switch fontDictType {

	case "Type1", "MMType1":

		err = validateFontFile(xRefTable, d, dictName, "FontFile", fontDictType, OPTIONAL, V10)
		if err != nil {
			return err
		}

		err = validateFontFile(xRefTable, d, dictName, "FontFile3", fontDictType, OPTIONAL, V12)

	case "TrueType", "CIDFontType2":
		err = validateFontFile(xRefTable, d, dictName, "FontFile2", fontDictType, OPTIONAL, V11)

	case "CIDFontType0":
		err = validateFontFile(xRefTable, d, dictName, "FontFile3", fontDictType, OPTIONAL, V13)

	case "Type3": // No fontfile.

	default:
		return errors.Errorf("pdfcpu: unknown fontDictType: %s\n", fontDictType)

	}

	return err
}

func validateFontDescriptor(xRefTable *XRefTable, d Dict, fontDictName string, fontDictType string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, fontDictName, "FontDescriptor", required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName := "fdDict"

	// Process font descriptor dict

	err = validateFontDescriptorPart1(xRefTable, d1, dictName, fontDictType)
	if err != nil {
		return err
	}

	err = validateFontDescriptorPart2(xRefTable, d1, dictName, fontDictType)
	if err != nil {
		return err
	}

	if fontDictType == "CIDFontType0" || fontDictType == "CIDFontType2" {

		validateStyleDict := func(d Dict) bool {
			// see 9.8.3.2

			if d.Len() != 1 {
				return false
			}

			_, found := d.Find("Panose")

			return found
		}

		// Style, optional, dict
		_, err = validateDictEntry(xRefTable, d1, dictName, "Style", OPTIONAL, V10, validateStyleDict)
		if err != nil {
			return err
		}

		// Lang, optional, name
		sinceVersion := V15
		if xRefTable.ValidationMode == ValidationRelaxed {
			sinceVersion = V13
		}
		_, err = validateNameEntry(xRefTable, d1, dictName, "Lang", OPTIONAL, sinceVersion, nil)
		if err != nil {
			return err
		}

		// FD, optional, dict
		_, err = validateDictEntry(xRefTable, d1, dictName, "FD", OPTIONAL, V10, nil)
		if err != nil {
			return err
		}

		// CIDSet, optional, stream
		_, err = validateStreamDictEntry(xRefTable, d1, dictName, "CIDSet", OPTIONAL, V10, nil)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateFontEncoding(xRefTable *XRefTable, d Dict, dictName string, required bool) error {
	entryName := "Encoding"

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, V10)
	if err != nil || o == nil {
		return err
	}

	encodings := []string{"MacRomanEncoding", "MacExpertEncoding", "WinAnsiEncoding"}
	if xRefTable.ValidationMode == ValidationRelaxed {
		encodings = append(encodings, "FontSpecific", "StandardEncoding", "SymbolSetEncoding")
	}

	switch o := o.(type) {

	case NameType:
		s := o.Value()
		validateFontEncodingName := func(s string) bool {
			return MemberOf(s, encodings)
		}
		if !validateFontEncodingName(s) {
			return errors.Errorf("validateFontEncoding: invalid Encoding name: %s\n", s)
		}

	case Dict:
		// no further processing

	default:
		return errors.Errorf("validateFontEncoding: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return nil
}

func validateTrueTypeFontDict(xRefTable *XRefTable, d Dict) error {
	// see 9.6.3
	dictName := "trueTypeFontDict"

	// NameType, name, obsolet and should not be used.

	// BaseFont, required, name
	_, err := validateNameEntry(xRefTable, d, dictName, "BaseFont", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// FirstChar, required, integer
	required := REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}
	_, err = validateIntegerEntry(xRefTable, d, dictName, "FirstChar", required, V10, nil)
	if err != nil {
		return err
	}

	// LastChar, required, integer
	required = REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}
	_, err = validateIntegerEntry(xRefTable, d, dictName, "LastChar", required, V10, nil)
	if err != nil {
		return err
	}

	// Widths, array of numbers.
	required = REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Widths", required, V10, nil)
	if err != nil {
		return err
	}

	// FontDescriptor, required, dictionary
	required = REQUIRED
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = OPTIONAL
	}
	err = validateFontDescriptor(xRefTable, d, dictName, "TrueType", required, V10)
	if err != nil {
		return err
	}

	// Encoding, optional, name or dict
	err = validateFontEncoding(xRefTable, d, dictName, OPTIONAL)
	if err != nil {
		return err
	}

	// ToUnicode, optional, stream
	_, err = validateStreamDictEntry(xRefTable, d, dictName, "ToUnicode", OPTIONAL, V12, nil)

	return err
}

func validateCIDToGIDMap(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		s := o.Value()
		if s != "Identity" {
			return errors.Errorf("pdfcpu: validateCIDToGIDMap: invalid name: %s - must be \"Identity\"\n", s)
		}

	case StreamDict:
		// no further processing

	default:
		return errors.New("pdfcpu: validateCIDToGIDMap: corrupt entry")

	}

	return nil
}

func validateNumberArray(xRefTable *XRefTable, o Object) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateNumberArray begin")
	// }

	a, err := xRefTable.DereferenceArray(o)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}

		if o == nil {
			continue
		}

		switch o.(type) {

		case Integer:
			// no further processing.

		case Float:
			// no further processing.

		default:
			return nil, errors.Errorf("pdfcpu: validateNumberArray: invalid type at index %d\n", i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("validateNumberArray end")
	// }

	return a, err
}

func validateCIDFontGlyphWidths(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil || o == nil {
			return err
		}

		switch o.(type) {

		case Integer:
			// no further processing.

		case Float:
			// no further processing

		case Array:
			_, err = validateNumberArray(xRefTable, o)
			if err != nil {
				return err
			}

		default:
			return errors.Errorf("validateCIDFontGlyphWidths: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
		}

	}

	return nil
}

func validateCIDFontDictEntryCIDSystemInfo(xRefTable *XRefTable, d Dict, dictName string) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "CIDSystemInfo", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateCIDSystemInfoDict(xRefTable, d1)
	}

	return err
}

func validateCIDFontDictEntryCIDToGIDMap(xRefTable *XRefTable, d Dict, isCIDFontType2 bool) error {
	if o, found := d.Find("CIDToGIDMap"); found {

		if xRefTable.ValidationMode == ValidationStrict && !isCIDFontType2 {
			return errors.New("pdfcpu: validateCIDFontDict: entry CIDToGIDMap not allowed - must be CIDFontType2")
		}

		err := validateCIDToGIDMap(xRefTable, o)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateCIDFontDict(xRefTable *XRefTable, d Dict) error {
	// see 9.7.4

	dictName := "CIDFontDict"

	// Type, required, name
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", REQUIRED, V10, func(s string) bool { return s == "Font" })
	if err != nil {
		return err
	}

	var isCIDFontType2 bool
	var fontType string

	// Subtype, required, name
	subType, err := validateNameEntry(xRefTable, d, dictName, "Subtype", REQUIRED, V10, func(s string) bool { return s == "CIDFontType0" || s == "CIDFontType2" })
	if err != nil {
		return err
	}

	isCIDFontType2 = *subType == "CIDFontType2"
	fontType = subType.Value()

	// BaseFont, required, name
	_, err = validateNameEntry(xRefTable, d, dictName, "BaseFont", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// CIDSystemInfo, required, dict
	err = validateCIDFontDictEntryCIDSystemInfo(xRefTable, d, "CIDFontDict")
	if err != nil {
		return err
	}

	// FontDescriptor, required, dict
	err = validateFontDescriptor(xRefTable, d, dictName, fontType, REQUIRED, V10)
	if err != nil {
		return err
	}

	// DW, optional, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "DW", OPTIONAL, V10, nil)
	if err != nil {
		return err
	}

	// W, optional, array
	err = validateCIDFontGlyphWidths(xRefTable, d, dictName, "W", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// DW2, optional, array
	// An array of two numbers specifying the default metrics for vertical writing.
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "DW2", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// W2, optional, array
	err = validateCIDFontGlyphWidths(xRefTable, d, dictName, "W2", OPTIONAL, V10)
	if err != nil {
		return err
	}

	// CIDToGIDMap, stream or (name /Identity)
	// optional, Type 2 CIDFonts with embedded associated TrueType font program only.
	return validateCIDFontDictEntryCIDToGIDMap(xRefTable, d, isCIDFontType2)
}

func validateDescendantFonts(xRefTable *XRefTable, d Dict, fontDictName string, required bool) error {
	// A one-element array holding a CID font dictionary.

	a, err := validateArrayEntry(xRefTable, d, fontDictName, "DescendantFonts", required, V10, func(a Array) bool { return len(a) == 1 })
	if err != nil || a == nil {
		return err
	}

	if len(a) != 1 {
		return ErrCorruptFontDict
	}

	d1, err := xRefTable.DereferenceDict(a[0])
	if err != nil {
		return err
	}

	if d1 == nil {
		if required {
			return errors.Errorf("validateDescendantFonts: dict=%s required descendant font dict missing.\n", fontDictName)
		}
		return nil
	}

	return validateCIDFontDict(xRefTable, d1)
}

func validateType0FontDict(xRefTable *XRefTable, d Dict) error {
	dictName := "type0FontDict"

	// BaseFont, required, name
	_, err := validateNameEntry(xRefTable, d, dictName, "BaseFont", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// Encoding, required,  name or CMap stream dict
	err = validateType0FontEncoding(xRefTable, d, dictName, REQUIRED)
	if err != nil {
		return err
	}

	// DescendantFonts: one-element array specifying the CIDFont dictionary that is the descendant of this Type 0 font, required.
	err = validateDescendantFonts(xRefTable, d, dictName, REQUIRED)
	if err != nil {
		return err
	}

	// ToUnicode, optional, CMap stream dict
	_, err = validateStreamDictEntry(xRefTable, d, dictName, "ToUnicode", OPTIONAL, V12, nil)
	if err != nil && xRefTable.ValidationMode == ValidationRelaxed {
		_, err = validateNameEntry(xRefTable, d, dictName, "ToUnicode", REQUIRED, V12, func(s string) bool { return s == "Identity-H" })
	}

	return err
}

func validateType1FontDict(xRefTable *XRefTable, d Dict) error {
	// see 9.6.2

	dictName := "type1FontDict"

	// NameType, name, obsolet and should not be used.

	// BaseFont, required, name
	fontName, err := validateNameEntry(xRefTable, d, dictName, "BaseFont", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	fn := (*fontName).Value()
	required := xRefTable.Version() >= V15 || !validateStandardType1Font(fn)
	if xRefTable.ValidationMode == ValidationRelaxed {
		required = false
	}
	// FirstChar,  required except for standard 14 fonts. since 1.5 always required, integer
	fc, err := validateIntegerEntry(xRefTable, d, dictName, "FirstChar", required, V10, nil)
	if err != nil {
		return err
	}

	if !required && fc != nil {
		// For the standard 14 fonts, the entries FirstChar, LastChar, Widths and FontDescriptor shall either all be present or all be absent.
		if xRefTable.ValidationMode == ValidationStrict {
			required = true
		}
	}

	// LastChar, required except for standard 14 fonts. since 1.5 always required, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "LastChar", required, V10, nil)
	if err != nil {
		return err
	}

	// Widths, required except for standard 14 fonts. since 1.5 always required, array of numbers
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Widths", required, V10, nil)
	if err != nil {
		return err
	}

	// FontDescriptor, required since version 1.5; required unless standard font for version < 1.5, dict
	err = validateFontDescriptor(xRefTable, d, dictName, "Type1", required, V10)
	if err != nil {
		return err
	}

	// Encoding, optional, name or dict
	err = validateFontEncoding(xRefTable, d, dictName, OPTIONAL)
	if err != nil {
		return err
	}

	// ToUnicode, optional, stream
	_, err = validateStreamDictEntry(xRefTable, d, dictName, "ToUnicode", OPTIONAL, V12, nil)

	return err
}

func validateCharProcsDict(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, "CharProcs", required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	for _, v := range d1 {

		_, _, err = xRefTable.DereferenceStreamDict(v)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateUseCMapEntry(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version) error {
	entryName := "UseCMap"

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, sinceVersion)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		// no further processing

	case StreamDict:
		err = validateCMapStreamDict(xRefTable, &o)
		if err != nil {
			return err
		}

	default:
		return errors.Errorf("validateUseCMapEntry: dict=%s corrupt entry \"%s\"\n", dictName, entryName)

	}

	return nil
}

func validateCIDSystemInfoDict(xRefTable *XRefTable, d Dict) error {
	dictName := "CIDSystemInfoDict"

	// Registry, required, ASCII string
	_, err := validateStringEntry(xRefTable, d, dictName, "Registry", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// Ordering, required, ASCII string
	_, err = validateStringEntry(xRefTable, d, dictName, "Ordering", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// Supplement, required, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "Supplement", REQUIRED, V10, nil)

	return err
}

func validateCMapStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	// See table 120

	dictName := "CMapStreamDict"

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, sd.Dict, dictName, "Type", OPTIONAL, V10, func(s string) bool { return s == "CMap" })
	if err != nil {
		return err
	}

	// CMapName, required, name
	_, err = validateNameEntry(xRefTable, sd.Dict, dictName, "CMapName", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// CIDFontType0SystemInfo, required, dict
	d, err := validateDictEntry(xRefTable, sd.Dict, dictName, "CIDSystemInfo", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	if d != nil {
		err = validateCIDSystemInfoDict(xRefTable, d)
		if err != nil {
			return err
		}
	}

	// WMode, optional, integer, 0 or 1
	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "WMode", OPTIONAL, V10, func(i int) bool { return i == 0 || i == 1 })
	if err != nil {
		return err
	}

	// UseCMap, name or cmap stream dict, optional.
	// If present, the referencing CMap shall specify only
	// the character mappings that differ from the referenced CMap.
	return validateUseCMapEntry(xRefTable, sd.Dict, dictName, OPTIONAL, V10)
}

func validateType0FontEncoding(xRefTable *XRefTable, d Dict, dictName string, required bool) error {
	entryName := "Encoding"

	o, err := validateEntry(xRefTable, d, dictName, entryName, required, V10)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case NameType:
		// no further processing

	case StreamDict:
		err = validateCMapStreamDict(xRefTable, &o)

	default:
		err = errors.Errorf("validateType0FontEncoding: dict=%s corrupt entry \"Encoding\"\n", dictName)

	}

	return err
}

func validateType3FontDict(xRefTable *XRefTable, d Dict) error {
	// see 9.6.5

	dictName := "type3FontDict"

	// NameType, name, obsolet and should not be used.

	// FontBBox, required, rectangle
	_, err := validateRectangleEntry(xRefTable, d, dictName, "FontBBox", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// FontMatrix, required, number array
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "FontMatrix", REQUIRED, V10, func(a Array) bool { return len(a) == 6 })
	if err != nil {
		return err
	}

	// CharProcs, required, dict
	err = validateCharProcsDict(xRefTable, d, dictName, REQUIRED, V10)
	if err != nil {
		return err
	}

	// Encoding, required, name or dict
	err = validateFontEncoding(xRefTable, d, dictName, REQUIRED)
	if err != nil {
		return err
	}

	// FirstChar, required, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "FirstChar", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// LastChar, required, integer
	_, err = validateIntegerEntry(xRefTable, d, dictName, "LastChar", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// Widths, required, array of number
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Widths", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	// FontDescriptor, required since version 1.5 for tagged PDF documents, dict
	sinceVersion := V15
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	err = validateFontDescriptor(xRefTable, d, dictName, "Type3", xRefTable.Tagged, sinceVersion)
	if err != nil {
		return err
	}

	// Resources, optional, dict, since V1.2
	d1, err := validateDictEntry(xRefTable, d, dictName, "Resources", OPTIONAL, V12, nil)
	if err != nil {
		return err
	}
	if d1 != nil {
		_, err := validateResourceDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	// ToUnicode, optional, stream
	_, err = validateStreamDictEntry(xRefTable, d, dictName, "ToUnicode", OPTIONAL, V12, nil)

	return err
}

func _validateFontDict(xRefTable *XRefTable, d Dict, isIndRef bool, indRef IndirectRef) (err error) {
	subtype := d.Subtype()
	if subtype == nil {
		return errors.New("pdfcpu: validateFontDict: missing Subtype")
	}

	switch *subtype {

	case "TrueType":
		err = validateTrueTypeFontDict(xRefTable, d)

	case "Type0":
		err = validateType0FontDict(xRefTable, d)

	case "Type1":
		err = validateType1FontDict(xRefTable, d)

	case "MMType1":
		return validateType1FontDict(xRefTable, d)

	case "Type3":
		err = validateType3FontDict(xRefTable, d)

	default:
		return errors.Errorf("pdfcpu: validateFontDict: unknown Subtype: %s\n", *subtype)

	}

	if isIndRef {
		if err1 := xRefTable.SetValid(indRef); err1 != nil {
			return err1
		}
	}

	return err
}

func validateFontDict(xRefTable *XRefTable, o Object) (err error) {
	indRef, isIndRef := o.(IndirectRef)
	if isIndRef {

		if ok, err := xRefTable.IsValid(indRef); err != nil || ok {
			return err
		}

		if ok, err := xRefTable.IsBeingValidated(indRef); err != nil || ok {
			return err
		}

		if err := xRefTable.SetBeingValidated(indRef); err != nil {
			return err
		}
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	if xRefTable.ValidationMode == ValidationRelaxed {
		if len(d) == 0 {
			return nil
		}
	}

	if d.Type() == nil || *d.Type() != "Font" {
		return errors.New("pdfcpu: validateFontDict: corrupt font dict")
	}

	return _validateFontDict(xRefTable, d, isIndRef, indRef)
}

func validateFontResourceDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// Version check
	err := xRefTable.ValidateVersion("fontResourceDict", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// Iterate over font resource dict
	for _, obj := range d {

		// Process fontDict
		err = validateFontDict(xRefTable, obj)
		if err != nil {
			return err
		}

	}

	return nil
}

func validatePropertiesDict(xRefTable *XRefTable, o Object) error {
	// see 14.6.2
	// a dictionary containing private information meaningful to the conforming writer creating marked content.
	// anything possible +
	// empty dict ok
	// Optional Metadata entry ok
	// Optional Contents entry ok
	// Optional Resources entry ok
	// Optional content group /OCG see 8.11.2
	// Optional content membership dict. /OCMD see 8.11.2.2
	// Optional MCID integer entry
	// Optional Alt since 1.5 see 14.9.3
	// Optional ActualText since 1.5 see 14.9.4
	// Optional E see since 1.4 14.9.5
	// Optional Lang string RFC 3066 see 14.9.2

	logProp := func(qual, k string, v Object) {
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validatePropertiesDict: %s key=%s val=%v\n", qual, k, v)
		// }
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	if err = validateMetadata(xRefTable, d, OPTIONAL, V14); err != nil {
		return err
	}

	for key, val := range d {
		switch key {

		case "Metadata":
			logProp("known", key, val)

		case "Contents":
			logProp("known", key, val)
			if _, err = validateStreamDict(xRefTable, val); err != nil {
				return err
			}

		case "Resources":
			logProp("known", key, val)
			if _, err = validateResourceDict(xRefTable, val); err != nil {
				return err
			}

		case "OCG":
			logProp("unsupported", key, val)
			return errors.Errorf("validatePropertiesDict: unsupported key \"%s\"\n", key)

		case "OCMD":
			logProp("unsupported", key, val)
			return errors.Errorf("validatePropertiesDict: unsupported key \"%s\"\n", key)

		// case "MCID": -> default
		// case "Alt": -> default
		// case "ActualText": -> default
		// case "E": -> default
		// case "Lang": -> default

		default:
			logProp("unknown", key, val)
			if _, err = xRefTable.Dereference(val); err != nil {
				return err
			}
		}
	}

	return nil
}

func validatePropertiesResourceDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	if err := xRefTable.ValidateVersion("PropertiesResourceDict", sinceVersion); err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// Iterate over properties resource dict
	for _, o := range d {
		if err = validatePropertiesDict(xRefTable, o); err != nil {
			return err
		}
	}

	return nil
}

func validateTilingPatternDict(xRefTable *XRefTable, sd *StreamDict, sinceVersion Version) error {
	dictName := "tilingPatternDict"

	if err := xRefTable.ValidateVersion(dictName, sinceVersion); err != nil {
		return err
	}

	_, err := validateNameEntry(xRefTable, sd.Dict, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Pattern" })
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "PatternType", REQUIRED, sinceVersion, func(i int) bool { return i == 1 })
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "PaintType", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, sd.Dict, dictName, "TilingType", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateRectangleEntry(xRefTable, sd.Dict, dictName, "BBox", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, sd.Dict, dictName, "XStep", REQUIRED, sinceVersion, func(f float64) bool { return f != 0 })
	if err != nil {
		return err
	}

	_, err = validateNumberEntry(xRefTable, sd.Dict, dictName, "YStep", REQUIRED, sinceVersion, func(f float64) bool { return f != 0 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, sd.Dict, dictName, "Matrix", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 6 })
	if err != nil {
		return err
	}

	o, ok := sd.Find("Resources")
	if !ok {
		return errors.New("pdfcpu: validateTilingPatternDict: missing required entry Resources")
	}

	_, err = validateResourceDict(xRefTable, o)

	return err
}

func validateBitsPerComponent(i int) bool {
	return IntMemberOf(i, []int{1, 2, 4, 8, 12, 16})
}

func validateBitsPerCoordinate(i int) bool {
	return IntMemberOf(i, []int{1, 2, 4, 8, 12, 16, 24, 32})
}

func validateBitsPerFlag(i int) bool {
	return IntMemberOf(i, []int{2, 4, 8})
}

func validateShadingDictCommonEntries(xRefTable *XRefTable, dict Dict) (shadType int, err error) {
	dictName := "shadingDictCommonEntries"

	shadingType, err := validateIntegerEntry(xRefTable, dict, dictName, "ShadingType", REQUIRED, V10, func(i int) bool { return i >= 1 && i <= 7 })
	if err != nil {
		return 0, err
	}

	err = validateColorSpaceEntry(xRefTable, dict, dictName, "ColorSpace", OPTIONAL, ExcludePatternCS)
	if err != nil {
		return 0, err
	}

	_, err = validateArrayEntry(xRefTable, dict, dictName, "Background", OPTIONAL, V10, nil)
	if err != nil {
		return 0, err
	}

	_, err = validateRectangleEntry(xRefTable, dict, dictName, "BBox", OPTIONAL, V10, nil)
	if err != nil {
		return 0, err
	}

	_, err = validateBooleanEntry(xRefTable, dict, dictName, "AntiAlias", OPTIONAL, V10, nil)

	return shadingType.Value(), err
}

func validateFunctionOrArrayOfFunctionsEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateFunctionOrArrayOfFunctionsEntry begin: entry=%s\n", entryName)
	// }

	o, _, err := d.Entry(dictName, entryName, required)
	if err != nil || o == nil {
		return err
	}

	if o, err = xRefTable.Dereference(o); err != nil {
		return err
	}

	if o == nil {
		if required {
			return errors.Errorf("pdfcpu: validateFunctionOrArrayOfFunctionsEntry: dict=%s required entry=%s is nil", dictName, entryName)
		}
		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validateFunctionOrArrayOfFunctionsEntry end: optional entry %s is nil\n", entryName)
		// }
		return nil
	}

	switch o := o.(type) {

	case Array:

		for _, o := range o {

			if o == nil {
				continue
			}

			if err = validateFunction(xRefTable, o); err != nil {
				return err
			}

		}

	default:
		if err = validateFunction(xRefTable, o); err != nil {
			return err
		}

	}

	if err = xRefTable.ValidateVersion("dict="+dictName+" entry="+entryName, sinceVersion); err != nil {
		return err
	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateFunctionOrArrayOfFunctionsEntry end: entry=%s\n", entryName)
	// }

	return nil
}

func validateFunctionBasedShadingDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "functionBasedShadingDict"

	_, err := validateNumberArrayEntry(xRefTable, dict, dictName, "Domain", OPTIONAL, V10, func(a Array) bool { return len(a) == 4 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Matrix", OPTIONAL, V10, func(a Array) bool { return len(a) == 6 })
	if err != nil {
		return err
	}

	return validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", REQUIRED, V10)
}

func validateBooleanArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version, validate func(Array) bool) (Array, error) {
	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanArrayEntry begin: entry=%s\n", entryName)
	// }

	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, validate)
	if err != nil || a == nil {
		return nil, err
	}

	for i, o := range a {

		o, err := xRefTable.Dereference(o)
		if err != nil {
			return nil, err
		}
		if o == nil {
			continue
		}

		if _, ok := o.(Boolean); !ok {
			return nil, errors.Errorf("validateBooleanArrayEntry: dict=%s entry=%s invalid type at index %d\n", dictName, entryName, i)
		}

	}

	// if log.ValidateEnabled() {
	// 	log.Validate.Printf("validateBooleanArrayEntry end: entry=%s\n", entryName)
	// }

	return a, nil
}

func validateAxialShadingDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "axialShadingDict"

	_, err := validateNumberArrayEntry(xRefTable, dict, dictName, "Coords", REQUIRED, V10, func(a Array) bool { return len(a) == 4 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Domain", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	err = validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", REQUIRED, V10)
	if err != nil {
		return err
	}

	_, err = validateBooleanArrayEntry(xRefTable, dict, dictName, "Extend", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })

	return err
}

func validateRadialShadingDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "radialShadingDict"

	_, err := validateNumberArrayEntry(xRefTable, dict, dictName, "Coords", REQUIRED, V10, func(a Array) bool { return len(a) == 6 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Domain", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	err = validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", REQUIRED, V10)
	if err != nil {
		return err
	}

	_, err = validateBooleanArrayEntry(xRefTable, dict, dictName, "Extend", OPTIONAL, V10, func(a Array) bool { return len(a) == 2 })

	return err
}

func validateShadingDict(xRefTable *XRefTable, dict Dict) error {
	// Shading 1-3

	shadingType, err := validateShadingDictCommonEntries(xRefTable, dict)
	if err != nil {
		return err
	}

	switch shadingType {
	case 1:
		err = validateFunctionBasedShadingDict(xRefTable, dict)

	case 2:
		err = validateAxialShadingDict(xRefTable, dict)

	case 3:
		err = validateRadialShadingDict(xRefTable, dict)

	default:
		return errors.Errorf("validateShadingDict: unexpected shadingType: %d\n", shadingType)
	}

	return err
}

func validateFreeFormGouroudShadedTriangleMeshesDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "freeFormGouraudShadedTriangleMeshesDict"

	_, err := validateIntegerEntry(xRefTable, dict, dictName, "BitsPerCoordinate", REQUIRED, V10, validateBitsPerCoordinate)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerComponent", REQUIRED, V10, validateBitsPerComponent)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerFlag", REQUIRED, V10, validateBitsPerFlag)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Decode", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	return validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", OPTIONAL, V10)
}

func validateLatticeFormGouraudShadedTriangleMeshesDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "latticeFormGouraudShadedTriangleMeshesDict"

	_, err := validateIntegerEntry(xRefTable, dict, dictName, "BitsPerCoordinate", REQUIRED, V10, validateBitsPerCoordinate)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerComponent", REQUIRED, V10, validateBitsPerComponent)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "VerticesPerRow", REQUIRED, V10, func(i int) bool { return i >= 2 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Decode", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	return validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", OPTIONAL, V10)
}

func validateCoonsPatchMeshesDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "coonsPatchMeshesDict"

	_, err := validateIntegerEntry(xRefTable, dict, dictName, "BitsPerCoordinate", REQUIRED, V10, validateBitsPerCoordinate)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerComponent", REQUIRED, V10, validateBitsPerComponent)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerFlag", REQUIRED, V10, validateBitsPerFlag)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Decode", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	return validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", OPTIONAL, V10)
}

func validateTensorProductPatchMeshesDict(xRefTable *XRefTable, dict Dict) error {
	dictName := "tensorProductPatchMeshesDict"

	_, err := validateIntegerEntry(xRefTable, dict, dictName, "BitsPerCoordinate", REQUIRED, V10, validateBitsPerCoordinate)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerComponent", REQUIRED, V10, validateBitsPerComponent)
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, dict, dictName, "BitsPerFlag", REQUIRED, V10, validateBitsPerFlag)
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, dict, dictName, "Decode", REQUIRED, V10, nil)
	if err != nil {
		return err
	}

	return validateFunctionOrArrayOfFunctionsEntry(xRefTable, dict, dictName, "Function", OPTIONAL, V10)
}

func validateShadingStreamDict(xRefTable *XRefTable, sd *StreamDict) error {
	// Shading 4-7

	dict := sd.Dict

	shadingType, err := validateShadingDictCommonEntries(xRefTable, dict)
	if err != nil {
		return err
	}

	switch shadingType {

	case 4:
		err = validateFreeFormGouroudShadedTriangleMeshesDict(xRefTable, dict)

	case 5:
		err = validateLatticeFormGouraudShadedTriangleMeshesDict(xRefTable, dict)

	case 6:
		err = validateCoonsPatchMeshesDict(xRefTable, dict)

	case 7:
		err = validateTensorProductPatchMeshesDict(xRefTable, dict)

	default:
		return errors.Errorf("pdfcpu: validateShadingStreamDict: unexpected shadingType: %d\n", shadingType)
	}

	return err
}

func validateShading(xRefTable *XRefTable, obj Object) error {
	// see 8.7.4.3 Shading Dictionaries

	obj, err := xRefTable.Dereference(obj)
	if err != nil || obj == nil {
		return err
	}

	switch obj := obj.(type) {

	case Dict:
		err = validateShadingDict(xRefTable, obj)

	case StreamDict:
		err = validateShadingStreamDict(xRefTable, &obj)

	default:
		return errors.New("pdfcpu: validateShading: corrupt obj typ, must be dict or stream dict")

	}

	return err
}

func validateShadingResourceDict(xRefTable *XRefTable, obj Object, sinceVersion Version) error {
	// see 8.7.4.3 Shading Dictionaries

	// Version check
	err := xRefTable.ValidateVersion("shadingResourceDict", sinceVersion)
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(obj)
	if err != nil || d == nil {
		return err
	}

	// Iterate over shading resource dictionary
	for _, obj := range d {

		// Process shading
		err = validateShading(xRefTable, obj)
		if err != nil {
			return err
		}
	}

	return nil
}

func validateShadingPatternDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "shadingPatternDict"

	if err := xRefTable.ValidateVersion(dictName, sinceVersion); err != nil {
		return err
	}

	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Pattern" })
	if err != nil {
		return err
	}

	_, err = validateIntegerEntry(xRefTable, d, dictName, "PatternType", REQUIRED, sinceVersion, func(i int) bool { return i == 2 })
	if err != nil {
		return err
	}

	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "Matrix", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 6 })
	if err != nil {
		return err
	}

	d1, err := validateDictEntry(xRefTable, d, dictName, "ExtGState", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateExtGStateDict(xRefTable, d1)
		if err != nil {
			return err
		}
	}

	// Shading: required, dict or stream dict.
	o, ok := d.Find("Shading")
	if !ok {
		return errors.Errorf("pdfcpu: validateShadingPatternDict: missing required entry \"Shading\".")
	}

	return validateShading(xRefTable, o)
}

func validatePattern(xRefTable *XRefTable, o Object) error {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return err
	}

	switch o := o.(type) {

	case StreamDict:
		err = validateTilingPatternDict(xRefTable, &o, V10)

	case Dict:
		err = validateShadingPatternDict(xRefTable, o, V13)

	default:
		err = errors.New("pdfcpu: validatePattern: corrupt obj typ, must be dict or stream dict")

	}

	return err
}

func validatePatternResourceDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	// see 8.7 Patterns

	// Version check
	if err := xRefTable.ValidateVersion("PatternResourceDict", sinceVersion); err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	// Iterate over pattern resource dictionary
	for _, o := range d {
		// Process pattern
		if err = validatePattern(xRefTable, o); err != nil {
			return err
		}
	}

	return nil
}

func validateResourceDict(xRefTable *XRefTable, o Object) (hasResources bool, err error) {
	d, err := xRefTable.DereferenceDict(o)
	if err != nil || d == nil {
		return false, err
	}

	for k, v := range map[string]struct {
		validate     func(xRefTable *XRefTable, o Object, sinceVersion Version) error
		sinceVersion Version
	}{
		"ExtGState":  {validateExtGStateResourceDict, V10},
		"Font":       {validateFontResourceDict, V10},
		"XObject":    {validateXObjectResourceDict, V10},
		"Properties": {validatePropertiesResourceDict, V10},
		"ColorSpace": {validateColorSpaceResourceDict, V10},
		"Pattern":    {validatePatternResourceDict, V10},
		"Shading":    {validateShadingResourceDict, V13},
	} {
		if o, ok := d.Find(k); ok {
			err = v.validate(xRefTable, o, v.sinceVersion)
			if err != nil {
				return false, err
			}
		}
	}

	allowedResDictKeys := []string{"ExtGState", "Font", "XObject", "Properties", "ColorSpace", "Pattern", "ProcSet", "Shading"}
	if xRefTable.ValidationMode == ValidationRelaxed {
		allowedResDictKeys = append(allowedResDictKeys, "Encoding")
		allowedResDictKeys = append(allowedResDictKeys, "ProcSets")
	}

	// Note: Beginning with PDF V1.4 the "ProcSet" feature is considered to be obsolete!

	for k := range d {
		if !MemberOf(k, allowedResDictKeys) {
			d.Delete(k)
		}
	}

	return true, nil
}

func validateContents(obj Object, xRefTable *XRefTable, d Dict) (hasContents bool, err error) {
	switch obj := obj.(type) {

	case StreamDict:
		// no further processing.
		hasContents = true

	case Array:
		// process array of content stream dicts.

		for _, obj := range obj {
			o1, _, err := xRefTable.DereferenceStreamDict(obj)
			if err != nil {
				return false, err
			}

			if o1 == nil {
				continue
			}

			hasContents = true

		}

		if hasContents {
			break
		}

		if xRefTable.ValidationMode == ValidationStrict {
			return false, errors.Errorf("validatePageContents: empty page content array detected")
		}

		// Digest empty array.
		d.Delete("Contents")

	case StringLiteral:

		s := strings.TrimSpace(obj.Value())

		if len(s) > 0 || xRefTable.ValidationMode == ValidationStrict {
			return false, errors.Errorf("validatePageContents: page content must be stream dict or array, got: %T", obj)
		}

		// Digest empty string literal.
		d.Delete("Contents")

	case Dict:

		if len(obj) > 0 || xRefTable.ValidationMode == ValidationStrict {
			return false, errors.Errorf("validatePageContents: page content must be stream dict or array, got: %T", obj)
		}

		// Digest empty dict.
		d.Delete("Contents")

	default:
		return false, errors.Errorf("validatePageContents: page content must be stream dict or array, got: %T", obj)
	}

	return hasContents, nil
}

func validatePageContents(xRefTable *XRefTable, d Dict) (hasContents bool, err error) {
	o, found := d.Find("Contents")
	if !found {
		return false, err
	}

	o, err = xRefTable.Dereference(o)
	if err != nil || o == nil {
		return false, err
	}

	return validateContents(o, xRefTable, d)
}

func validatePageResources(xRefTable *XRefTable, d Dict) error {
	if o, found := d.Find("Resources"); found {
		_, err := validateResourceDict(xRefTable, o)
		return err
	}

	// TODO Check if contents need resources (#169)
	// if !hasResources && hasContents {
	// 	return errors.New("pdfcpu: validatePageResources: missing required entry \"Resources\" - should be inherited")
	// }

	return nil
}

func validatePageEntryMediaBox(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) (hasMediaBox bool, err error) {
	o, err := validateRectangleEntry(xRefTable, d, "pageDict", "MediaBox", required, sinceVersion, nil)
	if err != nil {
		return false, err
	}
	if o != nil {
		hasMediaBox = true
	}

	return hasMediaBox, nil
}

func validatePageEntryCropBox(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateRectangleEntry(xRefTable, d, "pagesDict", "CropBox", required, sinceVersion, nil)

	return err
}

func validatePageEntryBleedBox(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateRectangleEntry(xRefTable, d, "pagesDict", "BleedBox", required, sinceVersion, nil)

	return err
}

func validatePageEntryTrimBox(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateRectangleEntry(xRefTable, d, "pagesDict", "TrimBox", required, sinceVersion, nil)

	return err
}

func validatePageEntryArtBox(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateRectangleEntry(xRefTable, d, "pagesDict", "ArtBox", required, sinceVersion, nil)

	return err
}

func validateBoxStyleDictEntry(xRefTable *XRefTable, d Dict, dictName string, entryName string, required bool, sinceVersion Version) error {
	d1, err := validateDictEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	dictName = "boxStyleDict"

	// C, number array with 3 elements, optional
	_, err = validateNumberArrayEntry(xRefTable, d1, dictName, "C", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	// W, number, optional
	_, err = validateNumberEntry(xRefTable, d1, dictName, "W", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// S, name, optional
	validate := func(s string) bool { return MemberOf(s, []string{"S", "D"}) }
	_, err = validateNameEntry(xRefTable, d1, dictName, "S", OPTIONAL, sinceVersion, validate)
	if err != nil {
		return err
	}

	// D, array, optional, since V1.3, dashArray
	_, err = validateIntegerArrayEntry(xRefTable, d1, dictName, "D", OPTIONAL, sinceVersion, nil)

	return err
}

func validatePageBoxColorInfo(xRefTable *XRefTable, pageDict Dict, required bool, sinceVersion Version) error {
	// box color information dict
	// see 14.11.2.2

	dictName := "pageDict"

	d, err := validateDictEntry(xRefTable, pageDict, dictName, "BoxColorInfo", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	dictName = "boxColorInfoDict"

	err = validateBoxStyleDictEntry(xRefTable, d, dictName, "CropBox", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	err = validateBoxStyleDictEntry(xRefTable, d, dictName, "BleedBox", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	err = validateBoxStyleDictEntry(xRefTable, d, dictName, "TrimBox", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	return validateBoxStyleDictEntry(xRefTable, d, dictName, "ArtBox", OPTIONAL, sinceVersion)
}

func validatePageEntryRotate(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	validate := func(i int) bool { return i%90 == 0 }
	_, err := validateIntegerEntry(xRefTable, d, "pagesDict", "Rotate", required, sinceVersion, validate)

	return err
}

func validatePageEntryGroup(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}

	d1, err := validateDictEntry(xRefTable, d, "pageDict", "Group", required, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateGroupAttributesDict(xRefTable, d1)
	}

	return err
}

func validatePageEntryThumb(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	sd, err := validateStreamDictEntry(xRefTable, d, "pagesDict", "Thumb", required, sinceVersion, nil)
	if err != nil || sd == nil {
		return err
	}

	if err := validateXObjectStreamDict(xRefTable, *sd); err != nil {
		return err
	}

	indRef := d.IndirectRefEntry("Thumb")
	xRefTable.PageThumbs[xRefTable.CurPage] = *indRef
	// fmt.Printf("adding thumb page:%d obj#:%d\n", xRefTable.CurPage, indRef.ObjectNumber.Value())

	return nil
}

func validatePageEntryB(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// Note: Only makes sense if "Threads" entry in document root and bead dicts present.

	_, err := validateIndRefArrayEntry(xRefTable, d, "pagesDict", "B", required, sinceVersion, nil)

	return err
}

func validatePageEntryDur(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateNumberEntry(xRefTable, d, "pagesDict", "Dur", required, sinceVersion, nil)

	return err
}

func validateTransitionDictEntryDi(d Dict) error {
	o, found := d.Find("Di")
	if !found {
		return nil
	}

	switch o := o.(type) {

	case Integer:
		validate := func(i int) bool { return IntMemberOf(i, []int{0, 90, 180, 270, 315}) }
		if !validate(o.Value()) {
			return errors.New("pdfcpu: validateTransitionDict: entry Di int value undefined")
		}

	case NameType:
		if o.Value() != "None" {
			return errors.New("pdfcpu: validateTransitionDict: entry Di name value undefined")
		}
	}

	return nil
}

func validateTransitionDictEntryM(xRefTable *XRefTable, d Dict, dictName string, transStyle *NameType) error {
	// see 12.4.4
	validateTransitionDirectionOfMotion := func(s string) bool { return MemberOf(s, []string{"I", "O"}) }

	validateM := func(s string) bool {
		return validateTransitionDirectionOfMotion(s) &&
			(transStyle != nil && (*transStyle == "Split" || *transStyle == "Box" || *transStyle == "Fly"))
	}

	_, err := validateNameEntry(xRefTable, d, dictName, "M", OPTIONAL, V10, validateM)

	return err
}

func validateTransitionDict(xRefTable *XRefTable, d Dict) error {
	dictName := "transitionDict"

	// S, name, optional

	validateTransitionStyle := func(s string) bool {
		return MemberOf(s, []string{"Split", "Blinds", "Box", "Wipe", "Dissolve", "Glitter", "R"})
	}

	validate := validateTransitionStyle

	if xRefTable.Version() >= V15 {
		validate = func(s string) bool {
			if validateTransitionStyle(s) {
				return true
			}

			return MemberOf(s, []string{"Fly", "Push", "Cover", "Uncover", "Fade"})
		}
	}
	transStyle, err := validateNameEntry(xRefTable, d, dictName, "S", OPTIONAL, V10, validate)
	if err != nil {
		return err
	}

	// D, optional, number > 0
	_, err = validateNumberEntry(xRefTable, d, dictName, "D", OPTIONAL, V10, func(f float64) bool { return f > 0 })
	if err != nil {
		return err
	}

	// Dm, optional, name, see 12.4.4
	validateTransitionDimension := func(s string) bool { return MemberOf(s, []string{"H", "V"}) }

	validateDm := func(s string) bool {
		return validateTransitionDimension(s) && (transStyle != nil && (*transStyle == "Split" || *transStyle == "Blinds"))
	}
	_, err = validateNameEntry(xRefTable, d, dictName, "Dm", OPTIONAL, V10, validateDm)
	if err != nil {
		return err
	}

	// M, optional, name
	err = validateTransitionDictEntryM(xRefTable, d, dictName, transStyle)
	if err != nil {
		return err
	}

	// Di, optional, number or name
	err = validateTransitionDictEntryDi(d)
	if err != nil {
		return err
	}

	// SS, optional, number, since V1.5
	if transStyle != nil && *transStyle == "Fly" {
		_, err = validateNumberEntry(xRefTable, d, dictName, "SS", OPTIONAL, V15, nil)
		if err != nil {
			return err
		}
	}

	// B, optional, boolean, since V1.5
	validateB := func(b bool) bool { return transStyle != nil && *transStyle == "Fly" }
	_, err = validateBooleanEntry(xRefTable, d, dictName, "B", OPTIONAL, V15, validateB)

	return err
}

func validatePageEntryTrans(xRefTable *XRefTable, pageDict Dict, required bool, sinceVersion Version) error {
	d, err := validateDictEntry(xRefTable, pageDict, "pagesDict", "Trans", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	return validateTransitionDict(xRefTable, d)
}

func validatePageEntryStructParents(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateIntegerEntry(xRefTable, d, "pagesDict", "StructParents", required, sinceVersion, nil)

	return err
}

func validatePageEntryID(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	_, err := validateStringEntry(xRefTable, d, "pagesDict", "ID", required, sinceVersion, nil)

	return err
}

func validatePageEntryPZ(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// Preferred zoom factor, number

	_, err := validateNumberEntry(xRefTable, d, "pagesDict", "PZ", required, sinceVersion, nil)

	return err
}

func validatePageEntrySeparationInfo(xRefTable *XRefTable, pagesDict Dict, required bool, sinceVersion Version) error {
	// see 14.11.4

	d, err := validateDictEntry(xRefTable, pagesDict, "pagesDict", "SeparationInfo", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	dictName := "separationDict"

	_, err = validateIndRefArrayEntry(xRefTable, d, dictName, "Pages", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	err = validateNameOrStringEntry(xRefTable, d, dictName, "DeviceColorant", required, sinceVersion)
	if err != nil {
		return err
	}

	a, err := validateArrayEntry(xRefTable, d, dictName, "ColorSpace", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}
	if a != nil {
		err = validateColorSpaceArraySubset(xRefTable, a, []string{"Separation", "DeviceN"})
	}

	return err
}

func validatePageEntryTabs(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	validateTabs := func(s string) bool { return MemberOf(s, []string{"R", "C", "S", "A", "W"}) }

	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err := validateNameEntry(xRefTable, d, "pagesDict", "Tabs", required, sinceVersion, validateTabs)

	if err != nil && xRefTable.ValidationMode == ValidationRelaxed {
		_, err = validateStringEntry(xRefTable, d, "pagesDict", "Tabs", required, sinceVersion, validateTabs)
	}

	return err
}

func validatePageEntryTemplateInstantiated(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// see 12.7.6

	_, err := validateNameEntry(xRefTable, d, "pagesDict", "TemplateInstantiated", required, sinceVersion, nil)

	return err
}

// TODO implement
func validatePageEntryPresSteps(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// see 12.4.4.2

	d1, err := validateDictEntry(xRefTable, d, "pagesDict", "PresSteps", required, sinceVersion, nil)
	if err != nil || d1 == nil {
		return err
	}

	return errors.New("pdfcpu: validatePageEntryPresSteps: not supported")
}

func validatePageEntryUserUnit(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// UserUnit, optional, positive number, since V1.6
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	_, err := validateNumberEntry(xRefTable, d, "pagesDict", "UserUnit", required, sinceVersion, func(f float64) bool { return f > 0 })

	return err
}

func validateNumberFormatDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "numberFormatDict"

	// Type, name, optional
	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "NumberFormat" })
	if err != nil {
		return err
	}

	// U, text string, required
	_, err = validateStringEntry(xRefTable, d, dictName, "U", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// C, number, required
	_, err = validateNumberEntry(xRefTable, d, dictName, "C", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// F, name, optional
	_, err = validateNameEntry(xRefTable, d, dictName, "F", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// D, integer, optional
	_, err = validateIntegerEntry(xRefTable, d, dictName, "D", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// FD, bool, optional
	_, err = validateBooleanEntry(xRefTable, d, dictName, "FD", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// RT, text string, optional
	_, err = validateStringEntry(xRefTable, d, dictName, "RT", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// RD, text string, optional
	_, err = validateStringEntry(xRefTable, d, dictName, "RD", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// PS, text string, optional
	_, err = validateStringEntry(xRefTable, d, dictName, "PS", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// SS, text string, optional
	_, err = validateStringEntry(xRefTable, d, dictName, "SS", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// O, name, optional
	_, err = validateNameEntry(xRefTable, d, dictName, "O", OPTIONAL, sinceVersion, nil)

	return err
}

func validateNumberFormatArrayEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) error {
	a, err := validateArrayEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for _, v := range a {

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateNumberFormatDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateMeasureDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "measureDict"

	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Measure" })
	if err != nil {
		return err
	}

	// PDF 1.6 defines only a single type of coordinate system, a rectilinear coordinate system,
	// that shall be specified by the value RL for the Subtype entry.
	coordSys, err := validateNameEntry(xRefTable, d, dictName, "Subtype", OPTIONAL, sinceVersion, nil)
	if err != nil || coordSys == nil {
		return err
	}

	if *coordSys != "RL" {
		if xRefTable.Version() > sinceVersion {
			// unknown coord system
			return nil
		}
		return errors.Errorf("validateMeasureDict dict=%s entry=%s invalid dict entry: %s", dictName, "Subtype", coordSys.Value())
	}

	// R, text string, required, scale ratio
	_, err = validateStringEntry(xRefTable, d, dictName, "R", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// X, number format array, required, for measurement of change along the x axis and, if Y is not present, along the y axis as well.
	err = validateNumberFormatArrayEntry(xRefTable, d, dictName, "X", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// Y, number format array, required when the x and y scales have different units or conversion factors.
	err = validateNumberFormatArrayEntry(xRefTable, d, dictName, "Y", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// D, number format array, required, for measurement of distance in any direction.
	err = validateNumberFormatArrayEntry(xRefTable, d, dictName, "D", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// A, number format array, required, for measurement of area.
	err = validateNumberFormatArrayEntry(xRefTable, d, dictName, "A", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// T, number format array, optional, for measurement of angles.
	err = validateNumberFormatArrayEntry(xRefTable, d, dictName, "T", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// S, number format array, optional, for fmeasurement of the slope of a line.
	err = validateNumberFormatArrayEntry(xRefTable, d, dictName, "S", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	// O, number array, optional, array of two numbers that shall specify the origin of the measurement coordinate system in default user space coordinates.
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "O", OPTIONAL, sinceVersion, func(a Array) bool { return len(a) == 2 })
	if err != nil {
		return err
	}

	// CYX, number, optional, a factor that shall be used to convert the largest units along the y axis to the largest units along the x axis.
	_, err = validateNumberEntry(xRefTable, d, dictName, "CYX", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	return nil
}

func validateViewportDict(xRefTable *XRefTable, d Dict, sinceVersion Version) error {
	dictName := "viewportDict"

	_, err := validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Viewport" })
	if err != nil {
		return err
	}

	_, err = validateRectangleEntry(xRefTable, d, dictName, "BBox", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	_, err = validateStringEntry(xRefTable, d, dictName, "Name", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Measure, optional, dict
	d1, err := validateDictEntry(xRefTable, d, dictName, "Measure", OPTIONAL, sinceVersion, nil)
	if err != nil {
		return err
	}

	if d1 != nil {
		err = validateMeasureDict(xRefTable, d1, sinceVersion)
	}

	return err
}

func validatePageEntryVP(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) error {
	// see table 260

	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V15
	}
	a, err := validateArrayEntry(xRefTable, d, "pagesDict", "VP", required, sinceVersion, nil)
	if err != nil || a == nil {
		return err
	}

	for _, v := range a {

		if v == nil {
			continue
		}

		d, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}

		if d == nil {
			continue
		}

		err = validateViewportDict(xRefTable, d, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validatePageDict(xRefTable *XRefTable, d Dict, hasMediaBox bool) error {
	dictName := "pageDict"

	if ir := d.IndirectRefEntry("Parent"); ir == nil {
		return errors.New("pdfcpu: validatePageDict: missing parent")
	}

	// Contents
	_, err := validatePageContents(xRefTable, d)
	if err != nil {
		return err
	}

	// Resources
	err = validatePageResources(xRefTable, d)
	if err != nil {
		return err
	}

	// MediaBox
	_, err = validatePageEntryMediaBox(xRefTable, d, !hasMediaBox, V10)
	if err != nil {
		return err
	}

	// PieceInfo
	if xRefTable.ValidationMode != ValidationRelaxed {
		sinceVersion := V13
		if xRefTable.ValidationMode == ValidationRelaxed {
			sinceVersion = V10
		}

		hasPieceInfo, err := validatePieceInfo(xRefTable, d, dictName, "PieceInfo", OPTIONAL, sinceVersion)
		if err != nil {
			return err
		}

		// LastModified
		lm, err := validateDateEntry(xRefTable, d, dictName, "LastModified", OPTIONAL, V13)
		if err != nil {
			return err
		}

		if hasPieceInfo && lm == nil && xRefTable.ValidationMode == ValidationStrict {
			return errors.New("pdfcpu: validatePageDict: missing \"LastModified\" (required by \"PieceInfo\")")
		}
	}

	// AA
	err = validateAdditionalActions(xRefTable, d, dictName, "AA", OPTIONAL, V14, "page")
	if err != nil {
		return err
	}

	type v struct {
		validate     func(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) (err error)
		required     bool
		sinceVersion Version
	}

	for _, f := range []v{
		{validatePageEntryCropBox, OPTIONAL, V10},
		{validatePageEntryBleedBox, OPTIONAL, V13},
		{validatePageEntryTrimBox, OPTIONAL, V13},
		{validatePageEntryArtBox, OPTIONAL, V13},
		{validatePageBoxColorInfo, OPTIONAL, V14},
		{validatePageEntryRotate, OPTIONAL, V10},
		{validatePageEntryGroup, OPTIONAL, V14},
		{validatePageEntryThumb, OPTIONAL, V10},
		{validatePageEntryB, OPTIONAL, V11},
		{validatePageEntryDur, OPTIONAL, V11},
		{validatePageEntryTrans, OPTIONAL, V11},
		{validateMetadata, OPTIONAL, V14},
		{validatePageEntryStructParents, OPTIONAL, V10},
		{validatePageEntryID, OPTIONAL, V13},
		{validatePageEntryPZ, OPTIONAL, V13},
		{validatePageEntrySeparationInfo, OPTIONAL, V13},
		{validatePageEntryTabs, OPTIONAL, V15},
		{validatePageEntryTemplateInstantiated, OPTIONAL, V15},
		{validatePageEntryPresSteps, OPTIONAL, V15},
		{validatePageEntryUserUnit, OPTIONAL, V16},
		{validatePageEntryVP, OPTIONAL, V16},
	} {
		err = f.validate(xRefTable, d, f.required, f.sinceVersion)
		if err != nil {
			return err
		}
	}

	return nil
}

func dictTypeForPageNodeDict(d Dict) (string, error) {
	if d == nil {
		return "", errors.New("pdfcpu: dictTypeForPageNodeDict: pageNodeDict is null")
	}

	dictType := d.Type()
	if dictType == nil {
		return "", errors.New("pdfcpu: dictTypeForPageNodeDict: missing pageNodeDict type")
	}

	return *dictType, nil
}

func validateResources(xRefTable *XRefTable, d Dict) (hasResources bool, err error) {
	// Resources: optional, dict
	o, ok := d.Find("Resources")
	if !ok {
		return false, nil
	}

	return validateResourceDict(xRefTable, o)
}

func pagesDictKids(xRefTable *XRefTable, d Dict) Array {
	if xRefTable.ValidationMode != ValidationRelaxed {
		return d.ArrayEntry("Kids")
	}
	o, found := d.Find("Kids")
	if !found {
		return nil
	}
	kids, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return nil
	}
	return kids
}

func validateParent(pageNodeDict Dict, objNr int) error {
	parentIndRef := pageNodeDict.IndirectRefEntry("Parent")
	if parentIndRef == nil {
		return errors.New("pdfcpu: validatePagesDict: missing parent node")
	}
	if parentIndRef.ObjectNumber.Value() != objNr {
		return errors.New("pdfcpu: validatePagesDict: corrupt parent node")
	}
	return nil
}

func processPagesKids(xRefTable *XRefTable, kids Array, objNr int, hasResources, hasMediaBox bool, curPage *int) (Array, error) {
	var a Array

	for _, o := range kids {

		if o == nil {
			continue
		}

		ir, ok := o.(IndirectRef)
		if !ok {
			return nil, errors.New("pdfcpu: validatePagesDict: missing indirect reference for kid")
		}

		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("validatePagesDict: PageNode: %s\n", ir)
		// }

		objNumber := ir.ObjectNumber.Value()
		if objNumber == 0 {
			continue
		}

		a = append(a, ir)

		pageNodeDict, err := xRefTable.DereferenceDict(ir)
		if err != nil {
			return nil, err
		}
		if pageNodeDict == nil {
			return nil, errors.New("pdfcpu: validatePagesDict: corrupt page node")
		}

		if err := validateParent(pageNodeDict, objNr); err != nil {
			return nil, err
		}

		dictType, err := dictTypeForPageNodeDict(pageNodeDict)
		if err != nil {
			return nil, err
		}

		switch dictType {

		case "Pages":
			if err = validatePagesDict(xRefTable, pageNodeDict, objNumber, hasResources, hasMediaBox, curPage); err != nil {
				return nil, err
			}

		case "Page":
			*curPage++
			xRefTable.CurPage = *curPage
			if err = validatePageDict(xRefTable, pageNodeDict, hasMediaBox); err != nil {
				return nil, err
			}
			if err := xRefTable.SetValid(ir); err != nil {
				return nil, err
			}

		default:
			return nil, errors.Errorf("pdfcpu: validatePagesDict: Unexpected dict type: %s", dictType)
		}

	}

	return a, nil
}

func repairPagesDict(xRefTable *XRefTable, obj Object, rootDict Dict) (Dict, int, error) {
	d, err := xRefTable.DereferenceDict(obj)
	if err != nil {
		return nil, 0, err
	}

	if d == nil {
		return nil, 0, errors.New("pdfcpu: repairPagesDict: cannot dereference pageNodeDict")
	}

	indRef, err := xRefTable.IndRefForNewObject(d)
	if err != nil {
		return nil, 0, err
	}

	rootDict["Pages"] = *indRef

	objNr := indRef.ObjectNumber.Value()

	// Patch kids.parents

	kids := pagesDictKids(xRefTable, d)
	if kids == nil {
		return nil, 0, errors.New("pdfcpu: repairPagesDict: corrupt \"Kids\" entry")
	}

	for i := range kids {

		o := kids[i]

		if o == nil {
			continue
		}

		ir, ok := o.(IndirectRef)
		if !ok {
			return nil, 0, errors.New("pdfcpu: repairPagesDict: missing indirect reference for kid")
		}

		// if log.ValidateEnabled() {
		// 	log.Validate.Printf("repairPagesDict: PageNode: %s\n", ir)
		// }

		objNumber := ir.ObjectNumber.Value()
		if objNumber == 0 {
			continue
		}

		d, err := xRefTable.DereferenceDict(ir)
		if err != nil {
			return nil, 0, err
		}
		if d == nil {
			return nil, 0, errors.New("pdfcpu: repairPagesDict: corrupt page node")
		}

		d["Parent"] = *indRef
	}

	return d, objNr, nil
}

func validatePagesDictGeneralEntries(xRefTable *XRefTable, d Dict) (hasResources, hasMediaBox bool, err error) {
	hasResources, err = validateResources(xRefTable, d)
	if err != nil {
		return false, false, err
	}

	// MediaBox: optional, rectangle
	hasMediaBox, err = validatePageEntryMediaBox(xRefTable, d, OPTIONAL, V10)
	if err != nil {
		return false, false, err
	}

	// CropBox: optional, rectangle
	err = validatePageEntryCropBox(xRefTable, d, OPTIONAL, V10)
	if err != nil {
		return false, false, err
	}

	// Rotate:  optional, integer
	err = validatePageEntryRotate(xRefTable, d, OPTIONAL, V10)
	if err != nil {
		return false, false, err
	}

	return hasResources, hasMediaBox, nil
}

func validatePagesDict(xRefTable *XRefTable, d Dict, objNr int, hasResources, hasMediaBox bool, curPage *int) error {
	dHasResources, dHasMediaBox, err := validatePagesDictGeneralEntries(xRefTable, d)
	if err != nil {
		return err
	}

	if dHasResources {
		hasResources = true
	}

	if dHasMediaBox {
		hasMediaBox = true
	}

	kids := pagesDictKids(xRefTable, d)
	if kids == nil {
		return errors.New("pdfcpu: validatePagesDict: corrupt \"Kids\" entry")
	}

	d["Kids"], err = processPagesKids(xRefTable, kids, objNr, hasResources, hasMediaBox, curPage)

	return err
}

func validatePages(xRefTable *XRefTable, rootDict Dict) (Dict, error) {
	obj, found := rootDict.Find("Pages")
	if !found {
		return nil, errors.New("pdfcpu: validatePages: missing \"Pages\"")
	}

	var (
		objNr    int
		pageRoot Dict
		err      error
	)

	ir, ok := obj.(IndirectRef)
	if !ok {
		if xRefTable.ValidationMode != ValidationRelaxed {
			return nil, errors.New("pdfcpu: validatePages: missing indirect reference \"Pages\"")
		}
		pageRoot, objNr, err = repairPagesDict(xRefTable, obj, rootDict)
		if err != nil {
			return nil, err
		}
	}

	if ok {
		objNr = ir.ObjectNumber.Value()

		pageRoot, err = xRefTable.DereferenceDict(obj)
		if err != nil {
			return nil, err
		}

		if pageRoot == nil {
			return nil, errors.New("pdfcpu: validatePages: cannot dereference pageNodeDict")
		}
	}

	obj, found = pageRoot.Find("Count")
	if !found {
		return nil, errors.New("pdfcpu: validatePages: missing \"Count\" in page root dict")
	}

	i, err := xRefTable.DereferenceInteger(obj)
	if err != nil || i == nil {
		return nil, errors.New("pdfcpu: validatePages: corrupt \"Count\" in page root dict")
	}

	xRefTable.PageCount = i.Value()

	pc := 0
	err = validatePagesDict(xRefTable, pageRoot, objNr, false, false, &pc)
	if err != nil {
		return nil, err
	}

	if pc != xRefTable.PageCount {
		return nil, errors.New("pdfcpu: validatePages: page tree invalid")
	}

	return pageRoot, err
}

func validatePageBoundaries(xRefTable *XRefTable, d Dict, dictName string, vp *ViewerPreferences) error {
	validate := func(s string) bool {
		return MemberOf(s, []string{"MediaBox", "CropBox", "BleedBox", "TrimBox", "ArtBox"})
	}

	n, err := validateNameEntry(xRefTable, d, dictName, "ViewArea", OPTIONAL, V14, validate)
	if err != nil {
		return err
	}
	if n != nil {
		vp.ViewArea = PageBoundaryFor(n.String())
	}

	n, err = validateNameEntry(xRefTable, d, dictName, "PrintArea", OPTIONAL, V14, validate)
	if err != nil {
		return err
	}
	if n != nil {
		vp.PrintArea = PageBoundaryFor(n.String())
	}

	n, err = validateNameEntry(xRefTable, d, dictName, "ViewClip", OPTIONAL, V14, validate)
	if err != nil {
		return err
	}
	if n != nil {
		vp.ViewClip = PageBoundaryFor(n.String())
	}

	n, err = validateNameEntry(xRefTable, d, dictName, "PrintClip", OPTIONAL, V14, validate)
	if err != nil {
		return err
	}
	if n != nil {
		vp.PrintClip = PageBoundaryFor(n.String())
	}

	return nil
}

func validatePrintPageRange(xRefTable *XRefTable, d Dict, dictName string, vp *ViewerPreferences) error {
	validate := func(arr Array) bool {
		if len(arr) > 0 && len(arr)%2 > 0 {
			return false
		}
		for i := 0; i < len(arr); i += 2 {
			if arr[i].(Integer) >= arr[i+1].(Integer) {
				return false
			}
		}
		return true
	}

	arr, err := validateIntegerArrayEntry(xRefTable, d, dictName, "PrintPageRange", OPTIONAL, V17, validate)
	if err != nil {
		return err
	}

	if len(arr) > 0 {
		vp.PrintPageRange = arr
	}

	return nil
}

func validateEnforcePrintScaling(xRefTable *XRefTable, d Dict, dictName string, vp *ViewerPreferences) error {
	validate := func(arr Array) bool {
		if len(arr) != 1 {
			return false
		}
		return arr[0].String() == "PrintScaling"
	}

	arr, err := validateNameArrayEntry(xRefTable, d, dictName, "Enforce", OPTIONAL, V20, validate)
	if err != nil {
		return err
	}

	if len(arr) > 0 {
		if vp.PrintScaling != nil && *vp.PrintScaling == PrintScalingAppDefault {
			return errors.New("pdfcpu: viewpreference \"Enforce[\"PrintScaling\"]\" needs \"PrintScaling\" <> \"AppDefault\"")
		}
		vp.Enforce = NewNameArray("PrintScaling")
	}

	return nil
}

func validatePrinterPreferences(xRefTable *XRefTable, d Dict, dictName string, vp *ViewerPreferences) error {
	sinceVersion := V16
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V13
	}
	validate := func(s string) bool {
		return MemberOf(s, []string{"None", "AppDefault"})
	}
	n, err := validateNameEntry(xRefTable, d, dictName, "PrintScaling", OPTIONAL, sinceVersion, validate)
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
		// Ignore in relaxed mode.
	}
	if n != nil {
		vp.PrintScaling = PrintScalingFor(n.String())
	}

	validate = func(s string) bool {
		return MemberOf(s, []string{"Simplex", "DuplexFlipShortEdge", "DuplexFlipLongEdge"})
	}
	n, err = validateNameEntry(xRefTable, d, dictName, "Duplex", OPTIONAL, V17, validate)
	if err != nil {
		return err
	}
	if n != nil {
		vp.Duplex = PaperHandlingFor(n.String())
	}

	vp.PickTrayByPDFSize, err = validateFlexBooleanEntry(xRefTable, d, dictName, "PickTrayByPDFSize", OPTIONAL, V17)
	if err != nil {
		return err
	}

	vp.NumCopies, err = validateIntegerEntry(xRefTable, d, dictName, "NumCopies", OPTIONAL, V17, func(i int) bool { return i >= 1 })
	if err != nil {
		return err
	}

	if err := validatePrintPageRange(xRefTable, d, dictName, vp); err != nil {
		return err
	}

	return validateEnforcePrintScaling(xRefTable, d, dictName, vp)
}

func validateFlexBooleanEntry(xRefTable *XRefTable, d Dict, dictName, entryName string, required bool, sinceVersion Version) (*bool, error) {
	flag, err := validateBooleanEntry(xRefTable, d, dictName, entryName, required, sinceVersion, nil)
	if err == nil {
		return flag, nil
	}
	if xRefTable.ValidationMode != ValidationRelaxed {
		return nil, err
	}
	n, err := validateNameEntry(xRefTable, d, dictName, entryName, required, sinceVersion,
		func(s string) bool {
			return MemberOf(strings.ToLower(s), []string{"false", "true"})
		},
	)
	if err != nil || n == nil {
		return nil, err
	}

	*flag = strings.ToLower(n.Value()) == "true"

	return flag, nil
}

func validateViewerPreferencesFlags(xRefTable *XRefTable, d Dict, dictName string, vp *ViewerPreferences) error {
	var err error
	vp.HideToolbar, err = validateFlexBooleanEntry(xRefTable, d, dictName, "HideToolbar", OPTIONAL, V10)
	if err != nil {
		return err
	}

	vp.HideMenubar, err = validateFlexBooleanEntry(xRefTable, d, dictName, "HideMenubar", OPTIONAL, V10)
	if err != nil {
		return err
	}

	vp.HideWindowUI, err = validateFlexBooleanEntry(xRefTable, d, dictName, "HideWindowUI", OPTIONAL, V10)
	if err != nil {
		return err
	}

	vp.FitWindow, err = validateFlexBooleanEntry(xRefTable, d, dictName, "FitWindow", OPTIONAL, V10)
	if err != nil {
		return err
	}

	vp.CenterWindow, err = validateFlexBooleanEntry(xRefTable, d, dictName, "CenterWindow", OPTIONAL, V10)
	if err != nil {
		return err
	}

	sinceVersion := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		sinceVersion = V10
	}
	vp.DisplayDocTitle, err = validateFlexBooleanEntry(xRefTable, d, dictName, "DisplayDocTitle", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}

	return nil
}

func validateViewerPreferences(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.2 Viewer Preferences

	dictName := "rootDict"

	d, err := validateDictEntry(xRefTable, rootDict, dictName, "ViewerPreferences", required, sinceVersion, nil)
	if err != nil || d == nil {
		return err
	}

	vp := ViewerPreferences{}
	xRefTable.ViewerPref = &vp

	dictName = "ViewerPreferences"

	if err := validateViewerPreferencesFlags(xRefTable, d, dictName, &vp); err != nil {
		return err
	}

	validate := func(s string) bool {
		return MemberOf(s, []string{"UseNone", "UseOutlines", "UseThumbs", "UseOC"})
	}
	n, err := validateNameEntry(xRefTable, d, dictName, "NonFullScreenPageMode", OPTIONAL, V10, validate)
	if err != nil {
		return err
	}
	if n != nil {
		vp.NonFullScreenPageMode = (*NonFullScreenPageMode)(PageModeFor(n.String()))
	}

	validate = func(s string) bool { return MemberOf(s, []string{"L2R", "R2L"}) }
	n, err = validateNameEntry(xRefTable, d, dictName, "Direction", OPTIONAL, V13, validate)
	if err != nil {
		s, err := validateStringEntry(xRefTable, d, dictName, "Direction", OPTIONAL, V13, validate)
		if err != nil {
			return err
		}
		if s != nil {
			vp.Direction = DirectionFor(*s)
		}
	}
	if vp.Direction == nil && n != nil {
		vp.Direction = DirectionFor(n.String())
	}

	if err := validatePageBoundaries(xRefTable, d, dictName, &vp); err != nil {
		return err
	}

	return validatePrinterPreferences(xRefTable, d, dictName, &vp)
}

var ErrBookmarksRepair = errors.New("pdfcpu: bookmarks repair failed")

func validateTitle(xRefTable *XRefTable, d Dict, dictName string) error {
	_, err := validateStringEntry(xRefTable, d, dictName, "Title", REQUIRED, V10, nil)
	if err != nil {
		if xRefTable.ValidationMode == ValidationStrict {
			return err
		}
		if _, err := validateNameEntry(xRefTable, d, dictName, "Title", REQUIRED, V10, nil); err != nil {
			return err
		}
	}
	return nil
}

func validateOutlineItemDict(xRefTable *XRefTable, d Dict) error {
	dictName := "outlineItemDict"

	// Title, required, text string
	if err := validateTitle(xRefTable, d, dictName); err != nil {
		return err
	}

	// Parent, required, dict indRef
	ir, err := validateIndRefEntry(xRefTable, d, dictName, "Parent", REQUIRED, V10)
	if err != nil {
		return err
	}
	_, err = xRefTable.DereferenceDict(*ir)
	if err != nil {
		return err
	}

	// // Count, optional, int
	// _, err = validateIntegerEntry(xRefTable, d, dictName, "Count", OPTIONAL, V10, nil)
	// if err != nil {
	// 	return err
	// }

	// SE, optional, dict indRef, since V1.3
	ir, err = validateIndRefEntry(xRefTable, d, dictName, "SE", OPTIONAL, V13)
	if err != nil {
		return err
	}
	if ir != nil {
		_, err = xRefTable.DereferenceDict(*ir)
		if err != nil {
			return err
		}
	}

	// C, optional, array of 3 numbers, since V1.4
	version := V14
	if xRefTable.ValidationMode == ValidationRelaxed {
		version = V13
	}
	_, err = validateNumberArrayEntry(xRefTable, d, dictName, "C", OPTIONAL, version, func(a Array) bool { return len(a) == 3 })
	if err != nil {
		return err
	}

	// F, optional integer, since V1.4
	_, err = validateIntegerEntry(xRefTable, d, dictName, "F", OPTIONAL, V14, nil)
	if err != nil {
		return err
	}

	// Optional A or Dest, since V1.1
	destName, err := validateActionOrDestination(xRefTable, d, dictName, V11)
	if err != nil {
		return err
	}

	if destName != "" {
		_, err = xRefTable.DereferenceDestArray(destName)
		if err != nil && xRefTable.ValidationMode == ValidationRelaxed {
			return nil
		}
	}

	return err
}

func handleOutlineItemDict(xRefTable *XRefTable, ir IndirectRef, objNumber int) (Dict, error) {
	d, err := xRefTable.DereferenceDict(ir)
	if err != nil {
		return nil, err
	}
	if d == nil {
		return nil, errors.Errorf("validateOutlineTree: object #%d is nil.", objNumber)
	}

	if err = validateOutlineItemDict(xRefTable, d); err != nil {
		return nil, err
	}

	return d, nil
}

func leaf(firstChild, lastChild *IndirectRef, objNumber, validationMode int) (bool, error) {
	if firstChild == nil {
		if lastChild == nil {
			// Leaf
			return true, nil
		}
		if validationMode == ValidationStrict {
			return false, errors.Errorf("pdfcpu: validateOutlineTree: missing \"First\" at obj#%d", objNumber)
		}
	}
	if lastChild == nil && validationMode == ValidationStrict {
		return false, errors.Errorf("pdfcpu: validateOutlineTree: missing \"Last\" at obj#%d", objNumber)
	}
	if firstChild != nil && firstChild.ObjectNumber.Value() == objNumber &&
		lastChild != nil && lastChild.ObjectNumber.Value() == objNumber {
		// Degenerated leaf = node pointing to itself.
		if validationMode == ValidationStrict {
			return false, errors.Errorf("pdfcpu: validateOutlineTree: invalid at obj#%d", objNumber)
		}
		return true, nil
	}
	return false, nil
}

func evalOutlineCount(xRefTable *XRefTable, c, visc int, count int, total, visible *int) error {
	if visc == 0 {
		if count == 0 {
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.New("pdfcpu: validateOutlineTree: non-empty outline item dict needs \"Count\" <> 0")
			}
			count = c
		}
		if count != c && count != -c {
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.Errorf("pdfcpu: validateOutlineTree: non-empty outline item dict got \"Count\" %d, want %d or %d", count, c, -c)
			}
			count = c
		}
		if count == c {
			*total += c
		}
	}

	if visc > 0 {
		if count != c+visc {
			return errors.Errorf("pdfcpu: validateOutlineTree: non-empty outline item dict got \"Count\" %d, want %d", count, c+visc)
		}
		*total += c
		*visible += visc
	}

	return nil
}

func validateOutlineTree(xRefTable *XRefTable, first, last *IndirectRef, m map[int]bool, fixed *bool) (int, int, error) {
	var (
		d       Dict
		objNr   int
		total   int
		visible int
		err     error
	)

	// Process linked list of outline items.
	for ir := first; ir != nil; ir = d.IndirectRefEntry("Next") {
		objNr = ir.ObjectNumber.Value()
		total++

		d, err = handleOutlineItemDict(xRefTable, *ir, objNr)
		if err != nil {
			return 0, 0, err
		}

		var count int
		if c := d.IntEntry("Count"); c != nil {
			count = *c
		}

		firstChild := d.IndirectRefEntry("First")
		lastChild := d.IndirectRefEntry("Last")

		ok, err := leaf(firstChild, lastChild, objNr, xRefTable.ValidationMode)
		if err != nil {
			return 0, 0, err
		}
		if ok {
			if count != 0 {
				return 0, 0, errors.New("pdfcpu: validateOutlineTree: empty outline item dict \"Count\" must be 0")
			}
			continue
		}

		if err := scanOutlineItems(xRefTable, firstChild, lastChild, m, fixed); err != nil {
			return 0, 0, err
		}

		c, visc, err := validateOutlineTree(xRefTable, firstChild, lastChild, m, fixed)
		if err != nil {
			return 0, 0, err
		}

		if err := evalOutlineCount(xRefTable, c, visc, count, &total, &visible); err != nil {
			return 0, 0, err
		}

	}

	if xRefTable.ValidationMode == ValidationStrict && objNr != last.ObjectNumber.Value() {
		return 0, 0, errors.Errorf("pdfcpu: validateOutlineTree: invalid child list %d <> %d\n", objNr, last.ObjectNumber)
	}

	return total, visible, nil
}

func validateVisibleOutlineCount(xRefTable *XRefTable, total, visible int, count *int) error {
	if count == nil {
		return errors.Errorf("pdfcpu: validateOutlines: invalid, root \"Count\" is nil, expected to be %d", total+visible)
	}
	if xRefTable.ValidationMode == ValidationStrict && *count != total+visible {
		return errors.Errorf("pdfcpu: validateOutlines: invalid, root \"Count\" = %d, expected to be %d", *count, total+visible)
	}
	if xRefTable.ValidationMode == ValidationRelaxed && *count != total+visible && *count != -total-visible {
		return errors.Errorf("pdfcpu: validateOutlines: invalid, root \"Count\" = %d, expected to be %d", *count, total+visible)
	}

	return nil
}

func validateInvisibleOutlineCount(xRefTable *XRefTable, total int, count *int) error {
	if count != nil {
		if xRefTable.ValidationMode == ValidationStrict && *count == 0 {
			return errors.New("pdfcpu: validateOutlines: invalid, root \"Count\" shall be omitted if there are no open outline items")
		}
		if xRefTable.ValidationMode == ValidationStrict && *count != total && *count != -total {
			return errors.Errorf("pdfcpu: validateOutlines: invalid, root \"Count\" = %d, expected to be %d", *count, total)
		}
	}

	return nil
}

func validateOutlineCount(xRefTable *XRefTable, total, visible int, count *int) error {
	if visible == 0 {
		return validateInvisibleOutlineCount(xRefTable, total, count)
	}

	if visible > 0 {
		return validateVisibleOutlineCount(xRefTable, total, visible, count)
	}

	return nil
}

func firstOfRemainder(xRefTable *XRefTable, last *IndirectRef, duplObjNr, oneBeforeDuplObj int) (int, Dict, error) {
	// Starting with the last node, go back until we hit duplObjNr or oneBeforeDuplObj
	for ir := last; ir != nil; {
		objNr := ir.ObjectNumber.Value()
		d, err := xRefTable.DereferenceDict(*ir)
		if err != nil {
			return 0, nil, err
		}
		irPrev := d.IndirectRefEntry("Prev")
		if irPrev == nil {
			break
		}
		prevObjNr := irPrev.ObjectNumber.Value()
		if prevObjNr == duplObjNr {
			d["Prev"] = *NewIndirectRef(oneBeforeDuplObj, 0)
			return objNr, d, nil
		}
		if prevObjNr == oneBeforeDuplObj {
			return objNr, d, nil
		}
		ir = irPrev
	}

	return 0, nil, nil
}

func removeDuplFirst(xRefTable *XRefTable, first, last *IndirectRef, duplObjNr, oneBeforeDuplObj int) error {
	nextObjNr, nextDict, err := firstOfRemainder(xRefTable, last, duplObjNr, oneBeforeDuplObj)
	if err != nil {
		return err
	}
	if nextObjNr == 0 {
		return ErrBookmarksRepair
	}
	delete(nextDict, "Prev")
	first.ObjectNumber = Integer(oneBeforeDuplObj)
	return nil
}

func scanOutlineItems(xRefTable *XRefTable, first, last *IndirectRef, m map[int]bool, fixed *bool) error {
	var (
		dOld     Dict
		objNrOld int
	)

	visited := map[int]bool{}
	objNr := first.ObjectNumber.Value()

	for ir := first; ir != nil; {
		visited[objNr] = true
		d1, err := xRefTable.DereferenceDict(*ir)
		if err != nil {
			return err
		}
		if ir == first && d1["Prev"] != nil {
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.New("pdfcpu: validateOutlines: corrupt outline items detected")
			}
			delete(d1, "Prev")
			*fixed = true
		}
		if m[objNr] {
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.New("pdfcpu: validateOutlines: recursive outline items detected")
			}
			*fixed = true

			if ir == first {
				// Remove duplicate first.
				return removeDuplFirst(xRefTable, first, last, objNr, objNrOld)
			}

			if ir == last {
				// Remove duplicate last.
				delete(dOld, "Next")
				last.ObjectNumber = Integer(objNrOld)
				return nil
			}
			nextObjNr, _, _ := firstOfRemainder(xRefTable, last, objNr, objNrOld)
			if nextObjNr == 0 {
				return ErrBookmarksRepair
			}
			irNext := dOld.IndirectRefEntry("Next")
			if irNext == nil {
				return ErrBookmarksRepair
			}
			dOld["Next"] = *NewIndirectRef(nextObjNr, 0)
			break
		}
		m[objNr] = true
		objNrOld = objNr
		dOld = d1
		if ir = dOld.IndirectRefEntry("Next"); ir != nil {
			objNr = ir.ObjectNumber.Value()
			if visited[objNr] {
				if xRefTable.ValidationMode == ValidationStrict {
					return errors.New("pdfcpu: validateOutlines: circular outline items detected")
				}
				dOld["Prev"] = first
				delete(dOld, "Next")
				*fixed = true
				return nil
			}
		}
	}

	return nil
}

func validateOutlinesGeneral(xRefTable *XRefTable, rootDict Dict) (*IndirectRef, *IndirectRef, *int, error) {
	d := xRefTable.Outlines

	// Type, optional, name
	_, err := validateNameEntry(xRefTable, d, "outlineDict", "Type", OPTIONAL, V10, func(s string) bool {
		return s == "Outlines" || (xRefTable.ValidationMode == ValidationRelaxed && s == "Outline")
	})
	if err != nil {
		return nil, nil, nil, err
	}

	first := d.IndirectRefEntry("First")
	last := d.IndirectRefEntry("Last")

	if first == nil {
		if last != nil {
			return nil, nil, nil, errors.New("pdfcpu: validateOutlines: invalid, root missing \"First\"")
		}
		// empty outlines
		xRefTable.Outlines = nil
		rootDict.Delete("Outlines")
		return nil, nil, nil, nil
	}
	if last == nil {
		return nil, nil, nil, errors.New("pdfcpu: validateOutlines: invalid, root missing \"Last\"")
	}

	count := d.IntEntry("Count")
	if xRefTable.ValidationMode == ValidationStrict && count != nil && *count < 0 {
		return nil, nil, nil, errors.New("pdfcpu: validateOutlines: invalid, root \"Count\" can't be negative")
	}

	return first, last, count, nil
}

func validateOutlines(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.3.3 Document Outline

	ir, err := validateIndRefEntry(xRefTable, rootDict, "rootDict", "Outlines", required, sinceVersion)
	if err != nil || ir == nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(*ir)
	if err != nil {
		return err
	}

	if d == nil {
		xRefTable.Outlines = nil
		delete(rootDict, "Outlines")
		return nil
	}

	xRefTable.Outlines = d

	first, last, count, err := validateOutlinesGeneral(xRefTable, rootDict)
	if err != nil {
		return err
	}
	if first == nil && last == nil {
		return nil
	}

	m := map[int]bool{}
	var fixed bool

	if err := scanOutlineItems(xRefTable, first, last, m, &fixed); err != nil {
		return err
	}

	total, visible, err := validateOutlineTree(xRefTable, first, last, m, &fixed)
	if err != nil {
		return err
	}

	if err := validateOutlineCount(xRefTable, total, visible, count); err != nil {
		return err
	}

	if fixed {
		// ShowRepaired("bookmarks")
	}

	return nil
}

func validateEntryV(xRefTable *XRefTable, d Dict, dictName string, required bool, sinceVersion Version, pBeadIndRef *IndirectRef, objNumber int) error {
	previousBeadIndRef, err := validateIndRefEntry(xRefTable, d, dictName, "V", required, sinceVersion)
	if err != nil {
		return err
	}

	if *previousBeadIndRef != *pBeadIndRef {
		return errors.Errorf("pdfcpu: validateEntryV: obj#%d invalid entry V, corrupt previous Bead indirect reference", objNumber)
	}

	return nil
}

func validateBeadDict(xRefTable *XRefTable, beadIndRef, threadIndRef, pBeadIndRef, lBeadIndRef *IndirectRef) error {
	objNumber := beadIndRef.ObjectNumber.Value()

	dictName := "beadDict"
	sinceVersion := V10

	d, err := xRefTable.DereferenceDict(*beadIndRef)
	if err != nil {
		return err
	}
	if d == nil {
		return errors.Errorf("pdfcpu: validateBeadDict: obj#%d missing dict", objNumber)
	}

	// Validate optional entry Type, must be "Bead".
	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Bead" })
	if err != nil {
		return err
	}

	// Validate entry T, must refer to threadDict.
	indRefT, err := validateIndRefEntry(xRefTable, d, dictName, "T", OPTIONAL, sinceVersion)
	if err != nil {
		return err
	}
	if indRefT != nil && *indRefT != *threadIndRef {
		return errors.Errorf("pdfcpu: validateBeadDict: obj#%d invalid entry T (backpointer to ThreadDict)", objNumber)
	}

	// Validate required entry R, must be rectangle.
	_, err = validateRectangleEntry(xRefTable, d, dictName, "R", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	// Validate required entry P, must be indRef to pageDict.
	err = validateEntryP(xRefTable, d, dictName, REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// Validate required entry V, must refer to previous bead.
	err = validateEntryV(xRefTable, d, dictName, REQUIRED, sinceVersion, pBeadIndRef, objNumber)
	if err != nil {
		return err
	}

	// Validate required entry N, must refer to last bead.
	nBeadIndRef, err := validateIndRefEntry(xRefTable, d, dictName, "N", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	// Recurse until next bead equals last bead.
	if *nBeadIndRef != *lBeadIndRef {
		err = validateBeadDict(xRefTable, nBeadIndRef, threadIndRef, beadIndRef, lBeadIndRef)
		if err != nil {
			return err
		}
	}

	return nil
}

func soleBeadDict(beadIndRef, pBeadIndRef, nBeadIndRef *IndirectRef) bool {
	// if N and V reference this bead dict, must be the first and only one.
	return *pBeadIndRef == *nBeadIndRef && *beadIndRef == *pBeadIndRef
}

func validateBeadChainIntegrity(beadIndRef, pBeadIndRef, nBeadIndRef *IndirectRef) bool {
	return *pBeadIndRef != *beadIndRef && *nBeadIndRef != *beadIndRef
}

func validateFirstBeadDict(xRefTable *XRefTable, beadIndRef, threadIndRef *IndirectRef) error {
	dictName := "firstBeadDict"
	sinceVersion := V10

	d, err := xRefTable.DereferenceDict(*beadIndRef)
	if err != nil {
		return err
	}

	if d == nil {
		return errors.New("pdfcpu: validateFirstBeadDict: missing dict")
	}

	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Bead" })
	if err != nil {
		return err
	}

	indRefT, err := validateIndRefEntry(xRefTable, d, dictName, "T", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	if *indRefT != *threadIndRef {
		return errors.New("pdfcpu: validateFirstBeadDict: invalid entry T (backpointer to ThreadDict)")
	}

	_, err = validateRectangleEntry(xRefTable, d, dictName, "R", REQUIRED, sinceVersion, nil)
	if err != nil {
		return err
	}

	err = validateEntryP(xRefTable, d, dictName, REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	pBeadIndRef, err := validateIndRefEntry(xRefTable, d, dictName, "V", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	nBeadIndRef, err := validateIndRefEntry(xRefTable, d, dictName, "N", REQUIRED, sinceVersion)
	if err != nil {
		return err
	}

	if soleBeadDict(beadIndRef, pBeadIndRef, nBeadIndRef) {
		return nil
	}

	if !validateBeadChainIntegrity(beadIndRef, pBeadIndRef, nBeadIndRef) {
		return errors.New("pdfcpu: validateFirstBeadDict: corrupt chain of beads")
	}

	return validateBeadDict(xRefTable, nBeadIndRef, threadIndRef, beadIndRef, pBeadIndRef)
}

func validateThreadDict(xRefTable *XRefTable, o Object, sinceVersion Version) error {
	dictName := "threadDict"

	threadIndRef, ok := o.(IndirectRef)
	if !ok {
		return errors.New("pdfcpu: validateThreadDict: not an indirect ref")
	}

	objNumber := threadIndRef.ObjectNumber.Value()

	d, err := xRefTable.DereferenceDict(threadIndRef)
	if err != nil {
		return err
	}

	_, err = validateNameEntry(xRefTable, d, dictName, "Type", OPTIONAL, sinceVersion, func(s string) bool { return s == "Thread" })
	if err != nil {
		return err
	}

	// Validate optional thread information dict entry.
	o, found := d.Find("I")
	if found && o != nil {
		_, err = validateDocumentInfoDict(xRefTable, o)
		if err != nil {
			return err
		}
	}

	fBeadIndRef := d.IndirectRefEntry("F")
	if fBeadIndRef == nil {
		return errors.Errorf("pdfcpu: validateThreadDict: obj#%d required indirect entry \"F\" missing", objNumber)
	}

	// Validate the list of beads starting with the first bead dict.
	return validateFirstBeadDict(xRefTable, fBeadIndRef, &threadIndRef)
}

func validateThreads(xRefTable *XRefTable, rootDict Dict, required bool, sinceVersion Version) error {
	// => 12.4.3 Articles

	ir := rootDict.IndirectRefEntry("Threads")
	if ir == nil {
		if required {
			return errors.New("pdfcpu: validateThreads: required entry \"Threads\" missing")
		}
		return nil
	}

	a, err := xRefTable.DereferenceArray(*ir)
	if err != nil {
		return err
	}
	if a == nil {
		return nil
	}

	err = xRefTable.ValidateVersion("threads", sinceVersion)
	if err != nil {
		return err
	}

	for _, o := range a {

		if o == nil {
			continue
		}

		err = validateThreadDict(xRefTable, o, sinceVersion)
		if err != nil {
			return err
		}

	}

	return nil
}

func validateRootObject(ctx *Context) error {
	// if log.ValidateEnabled() {
	// 	log.Validate.Println("*** validateRootObject begin ***")
	// }

	// => 7.7.2 Document Catalog

	// Entry               opt  since       type            info
	// ------------------------------------------------------------------------------------
	// Type                 n               string          "Catalog"
	// Version              y   1.4         name            overrules header version if later
	// Extensions           y   ISO 32000   dict            => 7.12 Extensions Dictionary
	// Pages                n   -           (dict)          => 7.7.3 Page Tree
	// PageLabels           y   1.3         number tree     => 7.9.7 Number Trees, 12.4.2 Page Labels
	// Names                y   1.2         dict            => 7.7.4 Name Dictionary
	// Dests                y   only 1.1    (dict)          => 12.3.2.3 Named Destinations
	// ViewerPreferences    y   1.2         dict            => 12.2 Viewer Preferences
	// PageLayout           y   -           name            /SinglePage, /OneColumn etc.
	// PageMode             y   -           name            /UseNone, /FullScreen etc.
	// Outlines             y   -           (dict)          => 12.3.3 Document Outline
	// Threads              y   1.1         (array)         => 12.4.3 Articles
	// OpenAction           y   1.1         array or dict   => 12.3.2 Destinations, 12.6 Actions
	// AA                   y   1.4         dict            => 12.6.3 Trigger Events
	// URI                  y   1.1         dict            => 12.6.4.7 URI Actions
	// AcroForm             y   1.2         dict            => 12.7.2 Interactive Form Dictionary
	// Metadata             y   1.4         (stream)        => 14.3.2 Metadata Streams
	// StructTreeRoot       y   1.3         dict            => 14.7.2 Structure Hierarchy
	// Markinfo             y   1.4         dict            => 14.7 Logical Structure
	// Lang                 y   1.4         string
	// SpiderInfo           y   1.3         dict            => 14.10.2 Web Capture Information Dictionary
	// OutputIntents        y   1.4         array           => 14.11.5 Output Intents
	// PieceInfo            y   1.4         dict            => 14.5 Page-Piece Dictionaries
	// OCProperties         y   1.5         dict            => 8.11.4 Configuring Optional Content
	// Perms                y   1.5         dict            => 12.8.4 Permissions
	// Legal                y   1.5         dict            => 12.8.5 Legal Content Attestations
	// Requirements         y   1.7         array           => 12.10 Document Requirements
	// Collection           y   1.7         dict            => 12.3.5 Collections
	// NeedsRendering       y   1.7         boolean         => XML Forms Architecture (XFA) Spec.

	// DSS					y	2.0			dict			=> 12.8.4.3 Document Security Store	TODO
	// AF					y	2.0			array of dicts	=> 14.3 Associated Files			TODO
	// DPartRoot			y	2.0			dict			=> 14.12 Document parts				TODO

	xRefTable := ctx.XRefTable

	d, err := xRefTable.Catalog()
	if err != nil {
		return err
	}

	// Type
	_, err = validateNameEntry(xRefTable, d, "rootDict", "Type", REQUIRED, V10, func(s string) bool { return s == "Catalog" })
	if err != nil {
		return err
	}

	// Pages
	rootPageNodeDict, err := validatePages(xRefTable, d)
	if err != nil {
		return err
	}

	for _, f := range []struct {
		validate     func(xRefTable *XRefTable, d Dict, required bool, sinceVersion Version) (err error)
		required     bool
		sinceVersion Version
	}{
		{validateRootVersion, OPTIONAL, V14},
		{validateExtensions, OPTIONAL, V10},
		{validatePageLabels, OPTIONAL, V13},
		{validateNames, OPTIONAL, V12},
		{validateNamedDestinations, OPTIONAL, V11},
		{validateViewerPreferences, OPTIONAL, V12},
		{validatePageLayout, OPTIONAL, V10},
		{validatePageMode, OPTIONAL, V10},
		{validateOutlines, OPTIONAL, V10},
		{validateThreads, OPTIONAL, V11},
		{validateOpenAction, OPTIONAL, V11},
		{validateRootAdditionalActions, OPTIONAL, V14},
		{validateURI, OPTIONAL, V11},
		{validateForm, OPTIONAL, V12},
		{validateRootMetadata, OPTIONAL, V14},
		{validateStructTree, OPTIONAL, V13},
		{validateMarkInfo, OPTIONAL, V14},
		{validateLang, OPTIONAL, V10},
		{validateSpiderInfo, OPTIONAL, V13},
		{validateOutputIntents, OPTIONAL, V14},
		{validateRootPieceInfo, OPTIONAL, V14},
		{validateOCProperties, OPTIONAL, V15},
		{validatePermissionsxReftable, OPTIONAL, V15},
		{validateLegal, OPTIONAL, V17},
		{validateRequirements, OPTIONAL, V17},
		{validateCollection, OPTIONAL, V17},
		{validateNeedsRendering, OPTIONAL, V17},
		{validateDSS, OPTIONAL, V17},
		{validateAF, OPTIONAL, V20},
		{validateDPartRoot, OPTIONAL, V20},
	} {
		if !f.required && xRefTable.Version() < f.sinceVersion {
			// Ignore optional fields if currentVersion < sinceVersion
			// This is really a workaround for explicitly extending relaxed validation.
			continue
		}
		err = f.validate(xRefTable, d, f.required, f.sinceVersion)
		if err != nil {
			return err
		}
	}

	// Validate remainder of annotations after AcroForm validation only.
	if _, err = validatePagesAnnotations(xRefTable, rootPageNodeDict, 0); err != nil {
		return err
	}

	// Validate form fields against page annotations.
	if xRefTable.Form != nil {
		if err := validateFormFieldsAgainstPageAnnotations(xRefTable); err != nil {
			return err
		}
	}

	// Validate links.
	if err = checkForBrokenLinks(ctx); err == nil {
		// if log.ValidateEnabled() {
		// 	log.Validate.Println("*** validateRootObject end ***")
		// }
	}

	return err
}

// XRefTable validates a PDF cross reference table obeying the validation mode.
func XRefTableValidation(ctx *Context) error {
	xRefTable := ctx.XRefTable

	metaDataAuthoritative, err := metaDataModifiedAfterInfoDict(xRefTable)
	if err != nil {
		return err
	}

	if metaDataAuthoritative {
		// if both info dict and catalog metadata present and metadata modification date after infodict modification date
		// validate document information dictionary before catalog metadata.
		err := validateDocumentInfoObject(xRefTable)
		if err != nil {
			return err
		}
	}

	// Validate root object(aka the document catalog) and page tree.
	err = validateRootObject(ctx)
	if err != nil {
		return err
	}

	if !metaDataAuthoritative {
		// Validate document information dictionary after catalog metadata.
		err = validateDocumentInfoObject(xRefTable)
		if err != nil {
			return err
		}
	}

	// Validate offspec additional streams as declared in pdf trailer.
	// err = validateAdditionalStreams(xRefTable)
	// if err != nil {
	// 	return err
	// }

	xRefTable.Valid = true

	// if xRefTable.CustomExtensions && log.CLIEnabled() {
	// 	log.CLI.Println("Note: custom extensions will not be validated.")
	// }

	// if log.ValidateEnabled() {
	// 	log.Validate.Println("*** validateXRefTable end ***")
	// }

	return nil
}

// ValidateContext validates ctx.
func ValidateContext(ctx *Context) error {
	if ctx.XRefTable.Version() == V20 {
		// logDisclaimerPDF20()
	}
	return XRefTableValidation(ctx)
}

// ReadAndValidate returns a Context of rs ready for processing.
func ReadAndValidate(rs io.ReadSeeker, conf *Configuration) (ctx *Context, err error) {
	if ctx, err = ReadContext(rs, conf); err != nil {
		return nil, err
	}

	if err := ValidateContext(ctx); err != nil {
		return nil, err
	}

	return ctx, nil
}

func cmdAssumingOptimization(cmd CommandMode) bool {
	return cmd == OPTIMIZE ||
		cmd == FILLFORMFIELDS ||
		cmd == RESETFORMFIELDS ||
		cmd == LISTIMAGES ||
		cmd == UPDATEIMAGES ||
		cmd == EXTRACTIMAGES ||
		cmd == EXTRACTFONTS
}

func optimizeContentStreamUsage(ctx *Context, sd *StreamDict, objNr int) (*IndirectRef, error) {
	f := ctx.Optimize.ContentStreamCache
	if len(f) == 0 {
		f[objNr] = sd
		return nil, nil
	}

	if f[objNr] != nil {
		return nil, nil
	}

	cachedObjNrs := []int{}
	for objNr, sd1 := range f {
		if *sd1.StreamLength == *sd.StreamLength {
			cachedObjNrs = append(cachedObjNrs, objNr)
		}
	}
	if len(cachedObjNrs) == 0 {
		f[objNr] = sd
		return nil, nil
	}

	for _, objNr := range cachedObjNrs {
		sd1 := f[objNr]
		if bytes.Equal(sd.Raw, sd1.Raw) {
			ir := NewIndirectRef(objNr, 0)
			ctx.IncrementRefCount(ir)
			return ir, nil
		}
	}

	f[objNr] = sd
	return nil, nil
}

func removeEmptyContentStreams(ctx *Context, pageDict Dict, obj Object, pageObjNumber int) error {
	var contentArr Array

	if ir, ok := obj.(IndirectRef); ok {

		objNr := ir.ObjectNumber.Value()
		entry, found := ctx.FindTableEntry(objNr, ir.GenerationNumber.Value())
		if !found {
			return errors.Errorf("removeEmptyContentStreams: obj#:%d illegal indRef for Contents\n", pageObjNumber)
		}

		contentStreamDict, ok := entry.Object.(StreamDict)
		if ok {
			if err := contentStreamDict.Decode(); err != nil {
				return errors.Errorf("invalid content stream obj#%d: %v", pageObjNumber, err)
			}
			if len(contentStreamDict.Content) == 0 {
				pageDict.Delete("Contents")
			}
			return nil
		}

		contentArr, ok = entry.Object.(Array)
		if !ok {
			return errors.Errorf("removeEmptyContentStreams: obj#:%d page content entry neither stream dict nor array.\n", pageObjNumber)
		}

	} else if contentArr, ok = obj.(Array); !ok {
		return errors.Errorf("removeEmptyContentStreams: obj#:%d corrupt page content array", pageObjNumber)
	}

	var newContentArr Array

	for _, c := range contentArr {

		ir, ok := c.(IndirectRef)
		if !ok {
			return errors.Errorf("removeEmptyContentStreams: obj#:%d corrupt page content array entry\n", pageObjNumber)
		}

		objNr := ir.ObjectNumber.Value()
		entry, found := ctx.FindTableEntry(objNr, ir.GenerationNumber.Value())
		if !found {
			return errors.Errorf("removeEmptyContentStreams: obj#:%d illegal indRef for Contents\n", pageObjNumber)
		}

		contentStreamDict, ok := entry.Object.(StreamDict)
		if !ok {
			return errors.Errorf("identifyPageContent: obj#:%d page content entry is no stream dict\n", pageObjNumber)
		}

		if err := contentStreamDict.Decode(); err != nil {
			return err
		}
		if len(contentStreamDict.Content) > 0 {
			newContentArr = append(newContentArr, c)
		}
	}

	pageDict["Contents"] = newContentArr

	return nil
}

func optimizePageContent(ctx *Context, pageDict Dict, pageObjNumber int) error {
	o, found := pageDict.Find("Contents")
	if !found {
		return nil
	}

	if err := removeEmptyContentStreams(ctx, pageDict, o, pageObjNumber); err != nil {
		return err
	}

	o, found = pageDict.Find("Contents")
	if !found {
		return nil
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("identifyPageContent begin")
	// }

	var contentArr Array

	if ir, ok := o.(IndirectRef); ok {

		objNr := ir.ObjectNumber.Value()
		entry, found := ctx.FindTableEntry(objNr, ir.GenerationNumber.Value())
		if !found {
			return errors.Errorf("identifyPageContent: obj#:%d illegal indRef for Contents\n", pageObjNumber)
		}

		contentStreamDict, ok := entry.Object.(StreamDict)
		if ok {
			ir, err := optimizeContentStreamUsage(ctx, &contentStreamDict, objNr)
			if err != nil {
				return err
			}
			if ir != nil {
				pageDict["Contents"] = *ir
			}
			contentStreamDict.IsPageContent = true
			entry.Object = contentStreamDict
			// if log.OptimizeEnabled() {
			// 	log.Optimize.Printf("identifyPageContent end: ok obj#%d\n", objNr)
			// }
			return nil
		}

		contentArr, ok = entry.Object.(Array)
		if !ok {
			return errors.Errorf("identifyPageContent: obj#:%d page content entry neither stream dict nor array.\n", pageObjNumber)
		}

	} else if contentArr, ok = o.(Array); !ok {
		return errors.Errorf("identifyPageContent: obj#:%d corrupt page content array\n", pageObjNumber)
	}

	// TODO Activate content array optimization as soon as we have a proper test file.

	_ = contentArr

	// for i, c := range contentArr {

	// 	ir, ok := c.(IndirectRef)
	// 	if !ok {
	// 		return errors.Errorf("identifyPageContent: obj#:%d corrupt page content array entry\n", pageObjNumber)
	// 	}

	// 	objNr := ir.ObjectNumber.Value()
	// 	entry, found := ctx.FindTableEntry(objNr, ir.GenerationNumber.Value())
	// 	if !found {
	// 		return errors.Errorf("identifyPageContent: obj#:%d illegal indRef for Contents\n", pageObjNumber)
	// 	}

	// 	contentStreamDict, ok := entry.Object.(StreamDict)
	// 	if !ok {
	// 		return errors.Errorf("identifyPageContent: obj#:%d page content entry is no stream dict\n", pageObjNumber)
	// 	}

	// 	ir1, err := optimizeContentStreamUsage(ctx, &contentStreamDict, objNr)
	// 	if err != nil {
	// 		return err
	// 	}
	// 	if ir1 != nil {
	// 		contentArr[i] = *ir1
	// 	}

	// 	contentStreamDict.IsPageContent = true
	// 	entry.Object = contentStreamDict
	// 	log.Optimize.Printf("identifyPageContent: ok obj#%d\n", ir.GenerationNumber.Value())
	// }

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("identifyPageContent end")
	// }

	return nil
}

// resourcesDictForPageDict returns the resource dict for a page dict if there is any.
func resourcesDictForPageDict(xRefTable *XRefTable, pageDict Dict, pageObjNumber int) (Dict, error) {
	o, found := pageDict.Find("Resources")
	if !found {
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("resourcesDictForPageDict end: No resources dict for page object %d, may be inherited\n", pageObjNumber)
		// }
		return nil, nil
	}

	return xRefTable.DereferenceDict(o)
}

// handleDuplicateFontObject returns nil or the object number of the registered font if it matches this
func handleDuplicateFontObject(ctx *Context, fontDict Dict, fName, rName string, objNr, pageNr int) (*int, error) {
	// Get a slice of all font object numbers for font name.
	fontObjNrs, found := ctx.Optimize.Fonts[fName]
	if !found {
		// There is no registered font with fName.
		return nil, nil
	}

	// Get the set of font object numbers for pageNr.
	pageFonts := ctx.Optimize.PageFonts[pageNr]

	// Iterate over all registered font object numbers for font name.
	// Check if this font dict matches the font dict of each font object number.
	for _, fontObjNr := range fontObjNrs {

		if fontObjNr == objNr {
			continue
		}

		// Get the font object from the lookup table.
		fontObject, ok := ctx.Optimize.FontObjects[fontObjNr]
		if !ok {
			continue
		}

		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("handleDuplicateFontObject: comparing with fontDict Obj %d\n", fontObjNr)
		// }

		// Check if the input fontDict matches the fontDict of this fontObject.
		ok, err := EqualFontDicts(fontObject.FontDict, fontDict, ctx.XRefTable)
		if err != nil {
			return nil, err
		}

		if !ok {
			// No match!
			continue
		}

		// We have detected a redundant font dict!
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("handleDuplicateFontObject: redundant fontObj#:%d basefont %s already registered with obj#:%d !\n", objNr, fName, fontObjNr)
		// }

		// Register new page font with pageNr.
		// The font for font object number is used instead of objNr.
		pageFonts[fontObjNr] = true

		// Add the resource name of this duplicate font to the list of registered resource names.
		fontObject.AddResourceName(rName)

		// Register fontDict as duplicate.
		ctx.Optimize.DuplicateFonts[objNr] = fontDict

		// Return the fontObjectNumber that will be used instead of objNr.
		return &fontObjNr, nil
	}

	return nil, nil
}

func pageImages(ctx *Context, pageNr int) IntSet {
	pageImages := ctx.Optimize.PageImages[pageNr]
	if pageImages == nil {
		pageImages = IntSet{}
		ctx.Optimize.PageImages[pageNr] = pageImages
	}

	return pageImages
}

func pageFonts(ctx *Context, pageNr int) IntSet {
	pageFonts := ctx.Optimize.PageFonts[pageNr]
	if pageFonts == nil {
		pageFonts = IntSet{}
		ctx.Optimize.PageFonts[pageNr] = pageFonts
	}

	return pageFonts
}

func registerFontDictObjNr(ctx *Context, fName string, objNr int) {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("optimizeFontResourcesDict: adding new font %s obj#%d\n", fName, objNr)
	// }

	fontObjNrs, found := ctx.Optimize.Fonts[fName]
	if found {
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("optimizeFontResourcesDict: appending %d to %s\n", objNr, fName)
		// }
		ctx.Optimize.Fonts[fName] = append(fontObjNrs, objNr)
	} else {
		ctx.Optimize.Fonts[fName] = []int{objNr}
	}
}

// font

const (
	sfntVersionTrueType      = "\x00\x01\x00\x00"
	sfntVersionTrueTypeApple = "true"
	sfntVersionCFF           = "OTTO"
	ttfHeadMagicNumber       = 0x5F0F3CF5
	ttcTag                   = "ttcf"
)

type ttf struct {
	PostscriptName     string            // name: NameID 6
	Protected          bool              // OS/2: fsType
	UnitsPerEm         int               // head: unitsPerEm
	Ascent             int               // OS/2: sTypoAscender
	Descent            int               // OS/2: sTypoDescender
	CapHeight          int               // OS/2: sCapHeight
	FirstChar          uint16            // OS/2: fsFirstCharIndex
	LastChar           uint16            // OS/2: fsLastCharIndex
	UnicodeRange       [4]uint32         // OS/2: Unicode Character Range
	LLx, LLy, URx, URy float64           // head: xMin, yMin, xMax, yMax (fontbox)
	ItalicAngle        float64           // post: italicAngle
	FixedPitch         bool              // post: isFixedPitch
	Bold               bool              // OS/2: usWeightClass == 7
	HorMetricsCount    int               // hhea: numOfLongHorMetrics
	GlyphCount         int               // maxp: numGlyphs
	GlyphWidths        []int             // hmtx: fd.HorMetricsCount.advanceWidth
	Chars              map[uint32]uint16 // cmap: Unicode character to glyph index
	ToUnicode          map[uint16]uint32 // map glyph index to unicode character
	Planes             map[int]bool      // used Unicode planes
	FontFile           []byte
}

func (fd ttf) String() string {
	return fmt.Sprintf(`
 PostscriptName = %s
      Protected = %t
     UnitsPerEm = %d
         Ascent = %d
        Descent = %d 
      CapHeight = %d
      FirstChar = %d
       LastChar = %d
FontBoundingBox = (%.2f, %.2f, %.2f, %.2f)
    ItalicAngle = %.2f
     FixedPitch = %t
           Bold = %t
HorMetricsCount = %d
     GlyphCount = %d`,
		fd.PostscriptName,
		fd.Protected,
		fd.UnitsPerEm,
		fd.Ascent,
		fd.Descent,
		fd.CapHeight,
		fd.FirstChar,
		fd.LastChar,
		fd.LLx, fd.LLy, fd.URx, fd.URy,
		fd.ItalicAngle,
		fd.FixedPitch,
		fd.Bold,
		fd.HorMetricsCount,
		fd.GlyphCount,
	)
}

func (fd ttf) toPDFGlyphSpace(i int) int {
	return i * 1000 / fd.UnitsPerEm
}

type myUint32 []uint32

func (f myUint32) Len() int {
	return len(f)
}

func (f myUint32) Less(i, j int) bool {
	return f[i] < f[j]
}

func (f myUint32) Swap(i, j int) {
	f[i], f[j] = f[j], f[i]
}

func (fd ttf) PrintChars() string {
	min := uint16(0xFFFF)
	var max uint16
	var sb strings.Builder
	sb.WriteByte(0x0a)

	keys := make(myUint32, 0, len(fd.Chars))
	for k := range fd.Chars {
		keys = append(keys, k)
	}
	sort.Sort(keys)

	for _, c := range keys {
		g := fd.Chars[c]
		if g > max {
			max = g
		}
		if g < min {
			min = g
		}
		sb.WriteString(fmt.Sprintf("#%x -> #%x(%d)\n", c, g, g))
	}
	fmt.Printf("using glyphs[%08x,%08x] [%d,%d]\n", min, max, min, max)
	fmt.Printf("using glyphs #%x - #%x (%d-%d)\n", min, max, min, max)
	return sb.String()
}

type table struct {
	chksum uint32
	off    uint32
	size   uint32
	padded uint32
	data   []byte
}

func (t table) uint16(off int) uint16 {
	return binary.BigEndian.Uint16(t.data[off:])
}

func (t table) int16(off int) int16 {
	return int16(t.uint16(off))
}

func (t table) uint32(off int) uint32 {
	return binary.BigEndian.Uint32(t.data[off:])
}

func (t table) fixed32(off int) float64 {
	return float64(t.uint32(off)) / 65536.0
}

func (t table) parseFontHeaderTable(fd *ttf) error {
	// table "head"
	magic := t.uint32(12)
	if magic != ttfHeadMagicNumber {
		return fmt.Errorf("parseHead: wrong magic number")
	}

	unitsPerEm := t.uint16(18)
	// fmt.Printf("unitsPerEm: %d\n", unitsPerEm)
	fd.UnitsPerEm = int(unitsPerEm)

	llx := t.int16(36)
	// fmt.Printf("llx: %d\n", llx)
	fd.LLx = float64(fd.toPDFGlyphSpace(int(llx)))

	lly := t.int16(38)
	// fmt.Printf("lly: %d\n", lly)
	fd.LLy = float64(fd.toPDFGlyphSpace(int(lly)))

	urx := t.int16(40)
	// fmt.Printf("urx: %d\n", urx)
	fd.URx = float64(fd.toPDFGlyphSpace(int(urx)))

	ury := t.int16(42)
	// fmt.Printf("ury: %d\n", ury)
	fd.URy = float64(fd.toPDFGlyphSpace(int(ury)))

	return nil
}

func uint16ToBigEndianBytes(i uint16) []byte {
	b := make([]byte, 2)
	binary.BigEndian.PutUint16(b, i)
	return b
}

func uint32ToBigEndianBytes(i uint32) []byte {
	b := make([]byte, 4)
	binary.BigEndian.PutUint32(b, i)
	return b
}

func utf16BEToString(bb []byte) string {
	buf := make([]uint16, len(bb)/2)
	for i := 0; i < len(buf); i++ {
		buf[i] = binary.BigEndian.Uint16(bb[2*i:])
	}
	return string(utf16.Decode(buf))
}

func (t table) parsePostScriptTable(fd *ttf) error {
	// table "post"
	italicAngle := t.fixed32(4)
	// fmt.Printf("italicAngle: %2.2f\n", italicAngle)
	fd.ItalicAngle = italicAngle

	isFixedPitch := t.uint16(16)
	// fmt.Printf("isFixedPitch: %t\n", isFixedPitch != 0)
	fd.FixedPitch = isFixedPitch != 0

	return nil
}

// func printUnicodeRange(off int, r uint32) {
// 	for i := 0; i < 32; i++ {
// 		if r&1 > 0 {
// 			fmt.Printf("bit %d: on\n", off+i)
// 		}
// 		r >>= 1
// 	}
// }

func (t table) parseWindowsMetricsTable(fd *ttf) error {
	// table "OS/2"
	version := t.uint16(0)
	fsType := t.uint16(8)
	fd.Protected = fsType&2 > 0
	// fmt.Printf("protected: %t\n", fd.Protected)

	uniCodeRange1 := t.uint32(42)
	// fmt.Printf("uniCodeRange1: %032b\n", uniCodeRange1)
	fd.UnicodeRange[0] = uniCodeRange1

	uniCodeRange2 := t.uint32(46)
	// fmt.Printf("uniCodeRange2: %032b\n", uniCodeRange2)
	fd.UnicodeRange[1] = uniCodeRange2

	uniCodeRange3 := t.uint32(50)
	// fmt.Printf("uniCodeRange3: %032b\n", uniCodeRange3)
	fd.UnicodeRange[2] = uniCodeRange3

	uniCodeRange4 := t.uint32(54)
	// fmt.Printf("uniCodeRange4: %032b\n", uniCodeRange4)
	fd.UnicodeRange[3] = uniCodeRange4

	// printUnicodeRange(0, uniCodeRange1)
	// printUnicodeRange(32, uniCodeRange2)
	// printUnicodeRange(64, uniCodeRange3)
	// printUnicodeRange(96, uniCodeRange4)

	sTypoAscender := t.int16(68)
	fd.Ascent = fd.toPDFGlyphSpace(int(sTypoAscender))

	sTypoDescender := t.int16(70)
	fd.Descent = fd.toPDFGlyphSpace(int(sTypoDescender))

	// sCapHeight: This field was defined in version 2 of the OS/2 table.
	// sCapHeight = int16(0)
	if version >= 2 {
		sCapHeight := t.int16(88)
		fd.CapHeight = fd.toPDFGlyphSpace(int(sCapHeight))
	} else {
		// TODO the value may be set equal to the top of the unscaled and unhinted glyph bounding box
		// of the glyph encoded at U+0048 (LATIN CAPITAL LETTER H).
		fd.CapHeight = fd.Ascent
	}

	fsSelection := t.uint16(62)
	fd.Bold = fsSelection&0x40 > 0

	fsFirstCharIndex := t.uint16(64)
	fd.FirstChar = fsFirstCharIndex

	fsLastCharIndex := t.uint16(66)
	fd.LastChar = fsLastCharIndex

	return nil
}

func (t table) parseNamingTable(fd *ttf) error {
	// table "name"
	count := int(t.uint16(2))
	stringOffset := t.uint16(4)
	var nameID uint16
	baseOff := 6
	for i := 0; i < count; i++ {
		recOff := baseOff + i*12
		pf := t.uint16(recOff)
		enc := t.uint16(recOff + 2)
		lang := t.uint16(recOff + 4)
		nameID = t.uint16(recOff + 6)
		l := t.uint16(recOff + 8)
		o := t.uint16(recOff + 10)
		soff := stringOffset + o
		s := t.data[soff : soff+l]
		if nameID == 6 {
			if pf == 3 && enc == 1 && lang == 0x0409 {
				fd.PostscriptName = utf16BEToString(s)
				return nil
			}
			if pf == 1 && enc == 0 && lang == 0 {
				fd.PostscriptName = string(s)
				return nil
			}
		}
	}

	return errors.New("pdfcpu: unable to identify postscript name")
}

func (t table) parseHorizontalHeaderTable(fd *ttf) error {
	// table "hhea"
	ascent := t.int16(4)
	// fmt.Printf("ascent: %d\n", ascent)
	if fd.Ascent == 0 {
		fd.Ascent = fd.toPDFGlyphSpace(int(ascent))
	}

	descent := t.int16(6)
	// fmt.Printf("descent: %d\n", descent)
	if fd.Descent == 0 {
		fd.Descent = fd.toPDFGlyphSpace(int(descent))
	}

	// lineGap := t.int16(8)
	// fmt.Printf("lineGap: %d\n", lineGap)

	// advanceWidthMax := t.uint16(10)
	// fmt.Printf("advanceWidthMax: %d\n", advanceWidthMax)

	// minLeftSideBearing := t.int16(12)
	// fmt.Printf("minLeftSideBearing: %d\n", minLeftSideBearing)

	// minRightSideBearing := t.int16(14)
	// fmt.Printf("minRightSideBearing: %d\n", minRightSideBearing)

	// xMaxExtent := t.int16(16)
	// fmt.Printf("xMaxExtent: %d\n", xMaxExtent)

	numOfLongHorMetrics := t.uint16(34)
	// fmt.Printf("numOfLongHorMetrics: %d\n", numOfLongHorMetrics)
	fd.HorMetricsCount = int(numOfLongHorMetrics)

	return nil
}

func (t table) parseMaximumProfile(fd *ttf) error {
	// table "maxp"
	numGlyphs := t.uint16(4)
	fd.GlyphCount = int(numGlyphs)
	return nil
}

func (t table) parseHorizontalMetricsTable(fd *ttf) error {
	// table "hmtx"
	fd.GlyphWidths = make([]int, fd.GlyphCount)

	for i := 0; i < int(fd.HorMetricsCount); i++ {
		fd.GlyphWidths[i] = fd.toPDFGlyphSpace(int(t.uint16(i * 4)))
	}

	for i := fd.HorMetricsCount; i < fd.GlyphCount; i++ {
		fd.GlyphWidths[i] = fd.GlyphWidths[fd.HorMetricsCount-1]
	}

	return nil
}

func (t table) parseCMapFormat4(fd *ttf) error {
	fd.Planes[0] = true
	segCount := int(t.uint16(6) / 2)
	endOff := 14
	startOff := endOff + 2*segCount + 2
	deltaOff := startOff + 2*segCount
	rangeOff := deltaOff + 2*segCount

	count := 0
	for i := 0; i < segCount; i++ {
		sc := t.uint16(startOff + i*2)
		startCode := uint32(sc)
		if fd.FirstChar == 0 {
			fd.FirstChar = sc
		}
		ec := t.uint16(endOff + i*2)
		endCode := uint32(ec)
		if fd.LastChar == 0 {
			fd.LastChar = ec
		}
		idDelta := uint32(t.uint16(deltaOff + i*2))
		idRangeOff := int(t.uint16(rangeOff + i*2))
		var v uint16
		for c, j := startCode, 0; c <= endCode && c != 0xFFFF; c++ {
			if idRangeOff > 0 {
				v = t.uint16(rangeOff + i*2 + idRangeOff + j*2)
			} else {
				v = uint16(c + idDelta)
			}
			if gi := v; gi > 0 {
				fd.Chars[c] = gi
				fd.ToUnicode[gi] = c
				count++
			}
			j++
		}
	}
	return nil
}

func (t table) parseCMapFormat12(fd *ttf) error {
	numGroups := int(t.uint32(12))
	off := 16
	count := 0
	var (
		lowestStartCode uint32
		prevCode        uint32
	)
	for i := 0; i < numGroups; i++ {
		base := off + i*12
		startCode := t.uint32(base)
		if lowestStartCode == 0 {
			lowestStartCode = startCode
			fd.Planes[int(lowestStartCode/0x10000)] = true
		}
		if startCode/0x10000 != prevCode/0x10000 {
			fd.Planes[int(startCode/0x10000)] = true
		}
		endCode := t.uint32(base + 4)
		if startCode != endCode {
			if startCode/0x10000 != endCode/0x10000 {
				fd.Planes[int(endCode/0x10000)] = true
			}
		}
		prevCode = endCode
		startGlyphID := uint16(t.uint32(base + 8))
		for c, gi := startCode, startGlyphID; c <= endCode; c++ {
			fd.Chars[c] = gi
			fd.ToUnicode[gi] = c
			gi++
			count++
		}
	}
	return nil
}

func (t table) parseCharToGlyphMappingTable(fd *ttf) error {
	// table "cmap"

	fd.Chars = map[uint32]uint16{}
	fd.ToUnicode = map[uint16]uint32{}
	fd.Planes = map[int]bool{}
	tableCount := t.uint16(2)
	baseOff := 4
	var pf, enc, f uint16
	m := map[string]table{}

	for i := 0; i < int(tableCount); i++ {
		off := baseOff + i*8
		pf = t.uint16(off)
		enc = t.uint16(off + 2)
		o := t.uint32(off + 4)
		f = t.uint16(int(o))
		if f == 14 {
			continue
		}
		l := uint32(t.uint16(int(o) + 2))
		if f >= 8 {
			l = t.uint32(int(o) + 4)
		}
		b := t.data[o : o+l]
		t1 := table{off: o, size: uint32(l), data: b}
		k := fmt.Sprintf("p%02d.e%02d.f%02d", pf, enc, f)
		m[k] = t1
	}

	if t, ok := m["p00.e10.f12"]; ok {
		return t.parseCMapFormat12(fd)
	}
	if t, ok := m["p00.e04.f12"]; ok {
		return t.parseCMapFormat12(fd)
	}
	if t, ok := m["p03.e10.f12"]; ok {
		return t.parseCMapFormat12(fd)
	}
	if t, ok := m["p00.e03.f04"]; ok {
		return t.parseCMapFormat4(fd)
	}
	if t, ok := m["p03.e01.f04"]; ok {
		return t.parseCMapFormat4(fd)
	}

	return fmt.Errorf("pdfcpu: unsupported cmap table")
}

func calcTableChecksum(tag string, b []byte) uint32 {
	sum := uint32(0)
	c := (len(b) + 3) / 4
	for i := 0; i < c; i++ {
		if tag == "head" && i == 2 {
			continue
		}
		sum += binary.BigEndian.Uint32(b[i*4:])
	}
	return sum
}

func getNext32BitAlignedLength(i uint32) uint32 {
	if i%4 > 0 {
		return i + (4 - i%4)
	}
	return i
}

func headerAndTables(fn string, r io.ReaderAt, baseOff int64) ([]byte, map[string]*table, error) {
	header := make([]byte, 12)
	n, err := r.ReadAt(header, baseOff)
	if err != nil {
		return nil, nil, err
	}
	if n != 12 {
		return nil, nil, fmt.Errorf("pdfcpu: corrupt ttf file: %s", fn)
	}

	st := string(header[:4])

	if st == sfntVersionCFF {
		return nil, nil, fmt.Errorf("pdfcpu: %s is based on OpenType CFF and unsupported at the moment :(", fn)
	}

	if st != sfntVersionTrueType && st != sfntVersionTrueTypeApple {
		return nil, nil, fmt.Errorf("pdfcpu: unrecognized font format: %s", fn)
	}

	c := int(binary.BigEndian.Uint16(header[4:]))

	b := make([]byte, c*16)
	n, err = r.ReadAt(b, baseOff+12)
	if err != nil {
		return nil, nil, err
	}
	if n != c*16 {
		return nil, nil, fmt.Errorf("pdfcpu: corrupt ttf file: %s", fn)
	}

	byteCount := uint32(12)
	tables := map[string]*table{}

	for j := 0; j < c; j++ {
		off := j * 16
		b1 := b[off : off+16]
		tag := string(b1[:4])
		chk := binary.BigEndian.Uint32(b1[4:])
		o := binary.BigEndian.Uint32(b1[8:])
		l := binary.BigEndian.Uint32(b1[12:])
		ll := getNext32BitAlignedLength(l)
		byteCount += ll
		t := make([]byte, ll)
		n, err = r.ReadAt(t, int64(o))
		if err != nil {
			return nil, nil, err
		}
		if n != int(ll) {
			return nil, nil, fmt.Errorf("pdfcpu: corrupt table: %s", tag)
		}
		sum := calcTableChecksum(tag, t)
		if sum != chk {
			fmt.Printf("pdfcpu: fixing table<%s> checksum error; want:%d got:%d\n", tag, chk, sum)
			chk = sum
		}
		tables[tag] = &table{chksum: chk, off: o, size: l, padded: ll, data: t}
	}

	return header, tables, nil
}

func parse(tags map[string]*table, tag string, fd *ttf) error {
	t, found := tags[tag]
	if !found {
		// OS/2 is optional for True Type fonts.
		if tag == "OS/2" {
			return nil
		}
		return fmt.Errorf("pdfcpu: tag: %s unavailable", tag)
	}
	if t.data == nil {
		return fmt.Errorf("pdfcpu: tag: %s no data", tag)
	}

	var err error

	switch tag {
	case "head":
		err = t.parseFontHeaderTable(fd)
	case "OS/2":
		err = t.parseWindowsMetricsTable(fd)
	case "post":
		err = t.parsePostScriptTable(fd)
	case "name":
		err = t.parseNamingTable(fd)
	case "hhea":
		err = t.parseHorizontalHeaderTable(fd)
	case "maxp":
		err = t.parseMaximumProfile(fd)
	case "hmtx":
		err = t.parseHorizontalMetricsTable(fd)
	case "cmap":
		err = t.parseCharToGlyphMappingTable(fd)
	}

	return err
}

func writeGob(fileName string, fd ttf) error {
	// f, err := os.Create(fileName)
	// if err != nil {
	// 	return err
	// }
	// defer f.Close()
	// enc := gob.NewEncoder(f)
	// return enc.Encode(fd)
	return nil
}

func readGob(fileName string, fd *ttf) error {
	// f, err := os.Open(fileName)
	// if err != nil {
	// 	return err
	// }
	// defer f.Close()
	// dec := gob.NewDecoder(f)
	// return dec.Decode(fd)
	return nil
}

func installTrueTypeRep(fontDir, fontName string, header []byte, tables map[string]*table) error {
	fd := ttf{}
	// fmt.Println(fontName)
	for _, v := range []string{"head", "OS/2", "post", "name", "hhea", "maxp", "hmtx", "cmap"} {
		if err := parse(tables, v, &fd); err != nil {
			return err
		}
	}

	bb, err := createTTF(header, tables)
	if err != nil {
		return err
	}
	fd.FontFile = bb

	// if log.CLIEnabled() {
	// 	log.CLI.Println(fd.PostscriptName)
	// }

	gobName := filepath.Join(fontDir, fd.PostscriptName+".gob")

	// Write the populated ttf struct as gob.
	if err := writeGob(gobName, fd); err != nil {
		return err
	}

	// Read gob and double check integrity.
	fdNew := ttf{}
	if err := readGob(gobName, &fdNew); err != nil {
		return err
	}

	if !reflect.DeepEqual(fd, fdNew) {
		return errors.Errorf("pdfcpu: %s can't be installed", fontName)
	}

	return nil
}

func ttfTables(tableCount int, bb []byte) (map[string]*table, error) {
	tables := map[string]*table{}
	b := bb[12:]
	for j := 0; j < tableCount; j++ {
		off := j * 16
		b1 := b[off : off+16]
		tag := string(b1[:4])
		chksum := binary.BigEndian.Uint32(b1[4:])
		o := binary.BigEndian.Uint32(b1[8:])
		l := binary.BigEndian.Uint32(b1[12:])
		ll := getNext32BitAlignedLength(l)
		t := append([]byte(nil), bb[o:o+ll]...)
		tables[tag] = &table{chksum: chksum, off: o, size: l, padded: ll, data: t}
	}
	return tables, nil
}

func glyfOffset(loca *table, gid, indexToLocFormat int) int {
	if indexToLocFormat == 0 {
		// short offsets
		return 2 * int(loca.uint16(2*gid))
	}
	// 1 .. long offsets
	return int(loca.uint32(4 * gid))
}

func writeGlyfOffset(buf *bytes.Buffer, off, indexToLocFormat int) {
	var bb []byte
	if indexToLocFormat == 0 {
		// 0 .. short offsets
		bb = uint16ToBigEndianBytes(uint16(off / 2))
	} else {
		// 1 .. long offsets
		bb = uint32ToBigEndianBytes(uint32(off))
	}
	buf.Write(bb)
}

func pad(bb []byte) []byte {
	i := len(bb) % 4
	if i == 0 {
		return bb
	}
	for j := 0; j < 4-i; j++ {
		bb = append(bb, 0x00)
	}
	return bb
}

func glyphOffsets(gid int, locaFull, glyfsFull *table, numGlyphs, indexToLocFormat int) (int, int) {
	offFrom := glyfOffset(locaFull, gid, indexToLocFormat)
	var offThru int
	if gid == numGlyphs {
		offThru = int(glyfsFull.padded)
	} else {
		offThru = glyfOffset(locaFull, gid+1, indexToLocFormat)
	}
	return offFrom, offThru
}

func resolveCompoundGlyph(fontName string, bb []byte, usedGIDs map[uint16]bool,
	locaFull, glyfsFull *table, numGlyphs, indexToLocFormat int,
) error {
	last := false
	for off := 10; !last; {
		flags := binary.BigEndian.Uint16(bb[off:])
		last = flags&0x20 == 0
		wordArgs := flags&0x01 > 0

		gid := binary.BigEndian.Uint16(bb[off+2:])

		// Position behind arguments.
		off += 6
		if wordArgs {
			off += 2
		}

		// Position behind transform.
		if flags&0x08 > 0 {
			off += 2
		} else if flags&0x40 > 0 {
			off += 4
		} else if flags&0x80 > 0 {
			off += 8
		}

		if _, ok := usedGIDs[gid]; ok {
			// duplicate
			continue
		}

		offFrom, offThru := glyphOffsets(int(gid), locaFull, glyfsFull, numGlyphs, indexToLocFormat)
		if offThru < offFrom {
			return errors.Errorf("pdfcpu: illegal glyfOffset for font: %s", fontName)
		}
		if offFrom == offThru {
			// not available
			continue
		}

		usedGIDs[gid] = true

		cbb := glyfsFull.data[offFrom:offThru]
		if cbb[0]&0x80 == 0 {
			// simple
			continue
		}

		if err := resolveCompoundGlyph(fontName, cbb, usedGIDs, locaFull, glyfsFull, numGlyphs, indexToLocFormat); err != nil {
			return err
		}
	}
	return nil
}

func resolveCompoundGlyphs(fontName string, usedGIDs map[uint16]bool, locaFull, glyfsFull *table, numGlyphs, indexToLocFormat int) error {
	gids := make([]uint16, len(usedGIDs))
	for k := range usedGIDs {
		gids = append(gids, k)
	}
	for _, gid := range gids {
		offFrom, offThru := glyphOffsets(int(gid), locaFull, glyfsFull, numGlyphs, indexToLocFormat)
		if offThru < offFrom {
			return errors.Errorf("pdfcpu: illegal glyfOffset for font: %s", fontName)
		}
		if offFrom == offThru {
			continue
		}
		bb := glyfsFull.data[offFrom:offThru]
		if bb[0]&0x80 == 0 {
			// simple
			continue
		}
		if err := resolveCompoundGlyph(fontName, bb, usedGIDs, locaFull, glyfsFull, numGlyphs, indexToLocFormat); err != nil {
			return err
		}
	}
	return nil
}

func glyfAndLoca(fontName string, tables map[string]*table, usedGIDs map[uint16]bool) error {
	head, ok := tables["head"]
	if !ok {
		return errors.Errorf("pdfcpu: missing \"head\" table for font: %s", fontName)
	}

	maxp, ok := tables["maxp"]
	if !ok {
		return errors.Errorf("pdfcpu: missing \"maxp\" table for font: %s", fontName)
	}

	glyfsFull, ok := tables["glyf"]
	if !ok {
		return errors.Errorf("pdfcpu: missing \"glyf\" table for font: %s", fontName)
	}

	locaFull, ok := tables["loca"]
	if !ok {
		return errors.Errorf("pdfcpu: missing \"loca\" table for font: %s", fontName)
	}

	indexToLocFormat := int(head.uint16(50))
	// 0 .. short offsets
	// 1 .. long offsets
	numGlyphs := int(maxp.uint16(4))

	if err := resolveCompoundGlyphs(fontName, usedGIDs, locaFull, glyfsFull, numGlyphs, indexToLocFormat); err != nil {
		return err
	}

	gids := make([]int, 0, len(usedGIDs)+1)
	gids = append(gids, 0)
	for gid := range usedGIDs {
		gids = append(gids, int(gid))
	}
	sort.Ints(gids)

	glyfBytes := []byte{}
	var buf bytes.Buffer
	off := 0
	firstPendingGID := 0

	for _, gid := range gids {
		offFrom, offThru := glyphOffsets(gid, locaFull, glyfsFull, numGlyphs, indexToLocFormat)
		if offThru < offFrom {
			return errors.Errorf("pdfcpu: illegal glyfOffset for font: %s", fontName)
		}
		if offThru != offFrom {
			// We have a glyph outline.
			for i := 0; i < gid-firstPendingGID; i++ {
				writeGlyfOffset(&buf, off, indexToLocFormat)
			}
			glyfBytes = append(glyfBytes, glyfsFull.data[offFrom:offThru]...)
			writeGlyfOffset(&buf, off, indexToLocFormat)
			off += offThru - offFrom
			firstPendingGID = gid + 1
		}
	}
	for i := 0; i <= numGlyphs-firstPendingGID; i++ {
		writeGlyfOffset(&buf, off, indexToLocFormat)
	}

	bb := buf.Bytes()
	locaFull.size = uint32(len(bb))
	locaFull.data = pad(bb)
	locaFull.padded = uint32(len(locaFull.data))

	glyfsFull.size = uint32(len(glyfBytes))
	glyfsFull.data = pad(glyfBytes)
	glyfsFull.padded = uint32(len(glyfsFull.data))

	return nil
}

func createTTF(header []byte, tables map[string]*table) ([]byte, error) {
	tags := []string{}
	for t := range tables {
		tags = append(tags, t)
	}
	sort.Strings(tags)

	buf := bytes.NewBuffer(header)
	off := uint32(len(header) + len(tables)*16)
	o := off
	for _, tag := range tags {
		t := tables[tag]
		if _, err := buf.WriteString(tag); err != nil {
			return nil, err
		}
		if tag == "loca" || tag == "glyf" {
			t.chksum = calcTableChecksum(tag, t.data)
		}
		if _, err := buf.Write(uint32ToBigEndianBytes(t.chksum)); err != nil {
			return nil, err
		}
		t.off = o
		if _, err := buf.Write(uint32ToBigEndianBytes(t.off)); err != nil {
			return nil, err
		}
		if _, err := buf.Write(uint32ToBigEndianBytes(t.size)); err != nil {
			return nil, err
		}
		o += t.padded
	}

	for _, tag := range tags {
		t := tables[tag]
		n, err := buf.Write(t.data)
		if err != nil {
			return nil, err
		}
		if n != len(t.data) || n != int(t.padded) {
			return nil, errors.Errorf("pdfcpu: unable to write %s data\n", tag)
		}
	}

	return buf.Bytes(), nil
}

// UserFontDir is the location for installed TTF or OTF font files.
var UserFontDir string

// Read reads in the font file bytes from gob
// Note: For WASM compatibility, this function is disabled.
// Font operations are not supported in WASM mode.
func ReadFont(fileName string) ([]byte, error) {
	return nil, errors.New("pdfcpu: ReadFont not supported in WASM mode - font subsetting disabled")
}

// Subset creates a new font file based on usedGIDs.
func Subset(fontName string, usedGIDs map[uint16]bool) ([]byte, error) {
	bb, err := ReadFont(fontName)
	if err != nil {
		return nil, err
	}

	header := bb[:12]
	tableCount := int(binary.BigEndian.Uint16(header[4:]))
	tables, err := ttfTables(tableCount, bb)
	if err != nil {
		return nil, err
	}

	if err := glyfAndLoca(fontName, tables, usedGIDs); err != nil {
		return nil, err
	}

	return createTTF(header, tables)
}

type cjk struct {
	encoding   string
	ordering   string
	supplement int
}

// Mapping of supported ISO-15924 font script code keys to corresponding encoding and CIDSystemInfo.
var cjkParms = map[string]cjk{
	// C
	"HANS": {"UniGB-UTF16-H", "GB1", 5},
	"HANT": {"UniCNS-UTF16-H", "CNS1", 7},
	// J
	"HIRA": {"UniJIS-UTF16-H", "Japan1", 7},
	"KANA": {"UniJIS-UTF16-H", "Japan1", 7},
	"JPAN": {"UniJIS-UTF16-H", "Japan1", 7},
	// K
	"HANG": {"UniKS-UTF16-H", "Korea1", 1},
	"KORE": {"UniKS-UTF16-H", "Korea1", 1},
	//"HANG": {"UniKS-UTF16-H", "KR", 9},
	//"KORE": {"UniKS-UTF16-H", "KR", 9},
}

func SupportedScript(s string) bool {
	return MemberOf(s, []string{"HANS", "HANT", "HIRA", "KANA", "JPAN", "HANG", "KORE"})
}

// CJKEncodings returns true for supported encodings.
func CJKEncoding(s string) bool {
	return MemberOf(s, []string{"UniGB-UTF16-H", "UniCNS-UTF16-H", "UniJIS-UTF16-H", "UniKS-UTF16-H"})
}

func ScriptForEncoding(enc string) string {
	for k, v := range cjkParms {
		if v.encoding == enc {
			return k
		}
	}
	return ""
}

type Resource struct {
	ID     string
	IndRef *IndirectRef
}

type FontResource struct {
	Res       Resource
	Lang      string
	CIDSet    *IndirectRef
	FontFile  *IndirectRef
	ToUnicode *IndirectRef
	W         *IndirectRef
}

func flateEncodedStreamIndRef(xRefTable *XRefTable, data []byte) (*IndirectRef, error) {
	sd, _ := xRefTable.NewStreamDictForBuf(data)
	sd.InsertInt("Length1", len(data))
	if err := sd.Encode(); err != nil {
		return nil, err
	}
	return xRefTable.IndRefForNewObject(*sd)
}

func ttfFontFile(xRefTable *XRefTable, fontName string) (*IndirectRef, error) {
	bb, err := ReadFont(fontName)
	if err != nil {
		return nil, err
	}
	return flateEncodedStreamIndRef(xRefTable, bb)
}

func ttfSubFontFile(xRefTable *XRefTable, fontName string, indRef *IndirectRef) (*IndirectRef, error) {
	bb, err := Subset(fontName, xRefTable.UsedGIDs[fontName])
	if err != nil {
		return nil, err
	}
	if indRef == nil {
		return flateEncodedStreamIndRef(xRefTable, bb)
	}
	entry, _ := xRefTable.FindTableEntryForIndRef(indRef)
	sd, _ := entry.Object.(StreamDict)
	sd.Content = bb
	sd.InsertInt("Length1", len(bb))
	if err := sd.Encode(); err != nil {
		return nil, err
	}
	entry.Object = sd
	return indRef, nil
}

func PDFDocEncoding(xRefTable *XRefTable) (*IndirectRef, error) {
	arr := Array{
		Integer(24),
		NameType("breve"), NameType("caron"), NameType("circumflex"), NameType("dotaccent"),
		NameType("hungarumlaut"), NameType("ogonek"), NameType("ring"), NameType("tilde"),
		Integer(39),
		NameType("quotesingle"),
		Integer(96),
		NameType("grave"),
		Integer(128),
		NameType("bullet"), NameType("dagger"), NameType("daggerdbl"), NameType("ellipsis"), NameType("emdash"), NameType("endash"),
		NameType("florin"), NameType("fraction"), NameType("guilsinglleft"), NameType("guilsinglright"), NameType("minus"), NameType("perthousand"),
		NameType("quotedblbase"), NameType("quotedblleft"), NameType("quotedblright"), NameType("quoteleft"), NameType("quoteright"), NameType("quotesinglbase"),
		NameType("trademark"), NameType("fi"), NameType("fl"), NameType("Lslash"), NameType("OE"), NameType("Scaron"), NameType("Ydieresis"),
		NameType("Zcaron"), NameType("dotlessi"), NameType("lslash"), NameType("oe"), NameType("scaron"), NameType("zcaron"),
		Integer(160),
		NameType("Euro"),
		Integer(164),
		NameType("currency"),
		Integer(166),
		NameType("brokenbar"), Integer(168), NameType("dieresis"), NameType("copyright"), NameType("ordfeminine"),
		Integer(172),
		NameType("logicalnot"), NameType(".notdef"), NameType("registered"), NameType("macron"), NameType("degree"),
		NameType("plusminus"), NameType("twosuperior"), NameType("threesuperior"), NameType("acute"), NameType("mu"),
		Integer(183),
		NameType("periodcentered"), NameType("cedilla"), NameType("onesuperior"), NameType("ordmasculine"),
		Integer(188),
		NameType("onequarter"), NameType("onehalf"), NameType("threequarters"),
		Integer(192),
		NameType("Agrave"), NameType("Aacute"), NameType("Acircumflex"), NameType("Atilde"), NameType("Adieresis"), NameType("Aring"), NameType("AE"),
		NameType("Ccedilla"), NameType("Egrave"), NameType("Eacute"), NameType("Ecircumflex"), NameType("Edieresis"), NameType("Igrave"), NameType("Iacute"),
		NameType("Icircumflex"), NameType("Idieresis"), NameType("Eth"), NameType("Ntilde"), NameType("Ograve"), NameType("Oacute"), NameType("Ocircumflex"),
		NameType("Otilde"), NameType("Odieresis"), NameType("multiply"), NameType("Oslash"), NameType("Ugrave"), NameType("Uacute"), NameType("Ucircumflex"),
		NameType("Udieresis"), NameType("Yacute"), NameType("Thorn"), NameType("germandbls"), NameType("agrave"), NameType("aacute"), NameType("acircumflex"),
		NameType("atilde"), NameType("adieresis"), NameType("aring"), NameType("ae"), NameType("ccedilla"), NameType("egrave"), NameType("eacute"), NameType("ecircumflex"),
		NameType("edieresis"), NameType("igrave"), NameType("iacute"), NameType("icircumflex"), NameType("idieresis"), NameType("eth"), NameType("ntilde"),
		NameType("ograve"), NameType("oacute"), NameType("ocircumflex"), NameType("otilde"), NameType("odieresis"), NameType("divide"), NameType("oslash"),
		NameType("ugrave"), NameType("uacute"), NameType("ucircumflex"), NameType("udieresis"), NameType("yacute"), NameType("thorn"), NameType("ydieresis"),
	}

	d := Dict(
		map[string]Object{
			"Type":        NameType("Encoding"),
			"Differences": arr,
		},
	)

	return xRefTable.IndRefForNewObject(d)
}

func coreFontDict(xRefTable *XRefTable, coreFontName string) (*IndirectRef, error) {
	d := NewDict()
	d.InsertName("Type", "Font")
	d.InsertName("Subtype", "Type1")
	d.InsertName("BaseFont", coreFontName)
	if coreFontName != "Symbol" && coreFontName != "ZapfDingbats" {
		d.InsertName("Encoding", "WinAnsiEncoding")
	}
	return xRefTable.IndRefForNewObject(d)
}

// CIDSet computes a CIDSet for used glyphs and updates or returns a new object.
func CIDSet(xRefTable *XRefTable, ttf TTFLight, fontName string, indRef *IndirectRef) (*IndirectRef, error) {
	bb := make([]byte, ttf.GlyphCount/8+1)
	usedGIDs, ok := xRefTable.UsedGIDs[fontName]
	if ok {
		for gid := range usedGIDs {
			bb[gid/8] |= 1 << (7 - (gid % 8))
		}
	}
	if indRef == nil {
		return flateEncodedStreamIndRef(xRefTable, bb)
	}
	entry, _ := xRefTable.FindTableEntryForIndRef(indRef)
	sd, _ := entry.Object.(StreamDict)
	sd.Content = bb
	sd.InsertInt("Length1", len(bb))
	if err := sd.Encode(); err != nil {
		return nil, err
	}
	entry.Object = sd
	return indRef, nil
}

func ttfFontDescriptorFlags(ttf TTFLight) uint32 {
	// Bits:
	// 1 FixedPitch
	// 2 Serif
	// 3 Symbolic
	// 4 Script/cursive
	// 6 Nonsymbolic
	// 7 Italic
	// 17 AllCap

	flags := uint32(0)

	// Bit 1
	// fmt.Printf("fixedPitch: %t\n", ttf.FixedPitch)
	if ttf.FixedPitch {
		flags |= 0x01
	}

	// Bit 6 Set for non symbolic
	// Note: Symbolic fonts are unsupported.
	flags |= 0x20

	// Bit 7
	// fmt.Printf("italicAngle: %f\n", ttf.ItalicAngle)
	if ttf.ItalicAngle != 0 {
		flags |= 0x40
	}

	// fmt.Printf("flags: %08x\n", flags)

	return flags
}

// CIDFontFile returns a TrueType font file or subfont file for fontName.
func CIDFontFile(xRefTable *XRefTable, fontName string, subFont bool) (*IndirectRef, error) {
	if subFont {
		return ttfSubFontFile(xRefTable, fontName, nil)
	}
	return ttfFontFile(xRefTable, fontName)
}

// CIDFontDescriptor returns a font descriptor describing the CIDFont’s default metrics other than its glyph widths.
func CIDFontDescriptor(xRefTable *XRefTable, ttf TTFLight, fontName, baseFontName, fontLang string, embed bool) (*IndirectRef, error) {
	var (
		fontFile *IndirectRef
		err      error
	)

	d := Dict(
		map[string]Object{
			"Type":        NameType("FontDescriptor"),
			"FontName":    NameType(baseFontName),
			"Flags":       Integer(ttfFontDescriptorFlags(ttf)),
			"FontBBox":    NewNumberArray(ttf.LLx, ttf.LLy, ttf.URx, ttf.URy),
			"ItalicAngle": Float(ttf.ItalicAngle),
			"Ascent":      Integer(ttf.Ascent),
			"Descent":     Integer(ttf.Descent),
			"CapHeight":   Integer(ttf.CapHeight),
			"StemV":       Integer(70), // Irrelevant for embedded files.
		},
	)

	if embed {
		fontFile, err = CIDFontFile(xRefTable, fontName, true)
		if err != nil {
			return nil, err
		}
		d["FontFile2"] = *fontFile
	}

	if embed {
		// (Optional)
		// A stream identifying which CIDs are present in the CIDFont file. If this entry is present,
		// the CIDFont shall contain only a subset of the glyphs in the character collection defined by the CIDSystemInfo dictionary.
		// If it is absent, the only indication of a CIDFont subset shall be the subset tag in the FontName entry (see 9.6.4, "Font Subsets").
		// The stream’s data shall be organized as a table of bits indexed by CID.
		// The bits shall be stored in bytes with the high-order bit first. Each bit shall correspond to a CID.
		// The most significant bit of the first byte shall correspond to CID 0, the next bit to CID 1, and so on.
		cidSetIndRef, err := CIDSet(xRefTable, ttf, fontName, nil)
		if err != nil {
			return nil, err
		}
		d["CIDSet"] = *cidSetIndRef
	}

	if fontLang != "" {
		d["Lang"] = NameType(fontLang)
	}

	return xRefTable.IndRefForNewObject(d)
}

// TTFLight represents a TrueType font w/o font file.
type TTFLight struct {
	PostscriptName     string            // name: NameID 6
	Protected          bool              // OS/2: fsType
	UnitsPerEm         int               // head: unitsPerEm
	Ascent             int               // OS/2: sTypoAscender
	Descent            int               // OS/2: sTypoDescender
	CapHeight          int               // OS/2: sCapHeight
	FirstChar          uint16            // OS/2: fsFirstCharIndex
	LastChar           uint16            // OS/2: fsLastCharIndex
	UnicodeRange       [4]uint32         // OS/2: Unicode Character Range
	LLx, LLy, URx, URy float64           // head: xMin, yMin, xMax, yMax (fontbox)
	ItalicAngle        float64           // post: italicAngle
	FixedPitch         bool              // post: isFixedPitch
	Bold               bool              // OS/2: usWeightClass == 7
	HorMetricsCount    int               // hhea: numOfLongHorMetrics
	GlyphCount         int               // maxp: numGlyphs
	GlyphWidths        []int             // hmtx: fd.HorMetricsCount.advanceWidth
	Chars              map[uint32]uint16 // cmap: Unicode character to glyph index
	ToUnicode          map[uint16]uint32 // map glyph index to unicode character
	Planes             map[int]bool      // used Unicode planes
}

// FontDescriptor returns a TrueType font descriptor describing font’s default metrics other than its glyph widths.
func NewFontDescriptor(xRefTable *XRefTable, ttf TTFLight, fontName, fontLang string) (*IndirectRef, error) {
	fontFile, err := ttfFontFile(xRefTable, fontName)
	if err != nil {
		return nil, err
	}

	d := Dict(
		map[string]Object{
			"Ascent":      Integer(ttf.Ascent),
			"CapHeight":   Integer(ttf.CapHeight),
			"Descent":     Integer(ttf.Descent),
			"Flags":       Integer(ttfFontDescriptorFlags(ttf)),
			"FontBBox":    NewNumberArray(ttf.LLx, ttf.LLy, ttf.URx, ttf.URy),
			"FontFamily":  StringLiteral(fontName),
			"FontFile2":   *fontFile,
			"FontName":    NameType(fontName),
			"ItalicAngle": Float(ttf.ItalicAngle),
			"StemV":       Integer(70), // Irrelevant for embedded files.
			"Type":        NameType("FontDescriptor"),
		},
	)

	if fontLang != "" {
		d["Lang"] = NameType(fontLang)
	}

	return xRefTable.IndRefForNewObject(d)
}

func wArr(ttf TTFLight, from, thru int) Array {
	a := Array{}
	for i := from; i <= thru; i++ {
		a = append(a, Integer(ttf.GlyphWidths[i]))
	}
	return a
}

func prepGids(xRefTable *XRefTable, ttf TTFLight, fontName string, used bool) []int {
	gids := ttf.GlyphWidths
	if used {
		usedGIDs, ok := xRefTable.UsedGIDs[fontName]
		if ok {
			gids = make([]int, 0, len(usedGIDs))
			for gid := range usedGIDs {
				gids = append(gids, int(gid))
			}
			sort.Ints(gids)
		}
	}
	return gids
}

func handleEqualWidths(w, w0, wl, g, g0, gl *int, a *Array, skip, equalWidths *bool) {
	if *w == 1000 || *w != *wl || *g-*gl > 1 {
		// cutoff or switch to non-contiguous width block
		*a = append(*a, Integer(*g0), Integer(*gl), Integer(*w0)) // write last contiguous width block
		if *w == 1000 {
			// cutoff via default
			*skip = true
		} else {
			*g0, *w0 = *g, *w
			*gl, *wl = *g0, *w0
		}
		*equalWidths = false
	} else {
		// Remain in contiguous width block
		*gl = *g
	}
}

func finalizeWidths(ttf TTFLight, w0, g0, gl int, skip, equalWidths bool, a *Array) {
	if !skip {
		if equalWidths {
			// write last contiguous width block
			*a = append(*a, Integer(g0), Integer(gl), Integer(w0))
		} else {
			// write last non-contiguous width block
			*a = append(*a, Integer(g0))
			a1 := wArr(ttf, g0, gl)
			*a = append(*a, a1)
		}
	}
}

func calcWidthArray(xRefTable *XRefTable, ttf TTFLight, fontName string, used bool) Array {
	gids := prepGids(xRefTable, ttf, fontName, used)
	a := Array{}
	var g0, w0, gl, wl int
	start, equalWidths, skip := true, false, false

	for g, w := range gids {
		if used {
			g = w
			w = ttf.GlyphWidths[g]
		}

		if start {
			start = false
			if w == 1000 {
				skip = true
				continue
			}
			g0, w0 = g, w
			gl, wl = g0, w0
			continue
		}

		if skip {
			if w != 1000 {
				g0, w0 = g, w
				gl, wl = g0, w0
				skip, equalWidths = false, false
			}
			continue
		}

		if equalWidths {
			handleEqualWidths(&w, &w0, &wl, &g, &g0, &gl, &a, &skip, &equalWidths)
			continue
		}

		// Non-contiguous

		if w == 1000 {
			// cutoff via default
			a = append(a, Integer(g0)) // write non-contiguous width block
			a1 := wArr(ttf, g0, gl)
			a = append(a, a1)
			skip = true
			continue
		}

		if g-gl > 1 {
			// cutoff via gap for subsets only.
			a = append(a, Integer(g0)) // write non-contiguous width block
			a1 := wArr(ttf, g0, gl)
			a = append(a, a1)
			g0, w0 = g, w
			gl, wl = g0, w0
			continue
		}

		if w == wl {
			if g-g0 > 1 {
				// switch from non equalW to equalW
				a = append(a, Integer(g0)) // write non-contiguous width block
				tru := gl - 1
				if tru < g0 {
					tru = g0
				}
				a1 := wArr(ttf, g0, tru)
				a = append(a, a1)
				g0, w0 = gl, wl
			}
			// just started.
			// switch to contiguous width
			equalWidths = true
			gl = g
			continue
		}

		// Remain in non-contiguous width block
		gl, wl = g, w
	}

	finalizeWidths(ttf, w0, g0, gl, skip, equalWidths, &a)

	return a
}

// CIDWidths returns the value for W in a CIDFontDict.
func CIDWidths(xRefTable *XRefTable, ttf TTFLight, fontName string, subFont bool, indRef *IndirectRef) (*IndirectRef, error) {
	a := calcWidthArray(xRefTable, ttf, fontName, subFont)
	if len(a) == 0 {
		return nil, nil
	}

	if indRef == nil {
		return xRefTable.IndRefForNewObject(a)
	}

	entry, _ := xRefTable.FindTableEntryForIndRef(indRef)
	entry.Object = a

	return indRef, nil
}

// Widths returns the value for Widths in a TrueType FontDict.
func Widths(xRefTable *XRefTable, ttf TTFLight, first, last int) (*IndirectRef, error) {
	a := Array{}
	for i := first; i < last; i++ {
		pos, ok := ttf.Chars[uint32(i)]
		if !ok {
			pos = 0 // should be the "invalid char"
		}
		a = append(a, Integer(ttf.GlyphWidths[pos]))
	}
	return xRefTable.IndRefForNewObject(a)
}

func (fd TTFLight) Gids() []int {
	gids := make([]int, 0, len(fd.Chars))
	for _, g := range fd.Chars {
		gids = append(gids, int(g))
	}
	return gids
}

func bf(b *bytes.Buffer, ttf TTFLight, usedGIDs map[uint16]bool, subFont bool) {
	var gids []int
	if subFont {
		gids = make([]int, 0, len(usedGIDs))
		for gid := range usedGIDs {
			gids = append(gids, int(gid))
		}
	} else {
		gids = ttf.Gids()
	}
	sort.Ints(gids)

	c := 100
	if len(gids) < 100 {
		c = len(gids)
	}
	l := c

	fmt.Fprintf(b, "%d beginbfchar\n", c)
	j := 1
	for i := 0; i < l; i++ {
		gid := gids[i]
		fmt.Fprintf(b, "<%04X> <", gid)
		u := ttf.ToUnicode[uint16(gid)]
		s := utf16.Encode([]rune{rune(u)})
		for _, v := range s {
			fmt.Fprintf(b, "%04X", v)
		}
		fmt.Fprintf(b, ">\n")
		if j%100 == 0 {
			b.WriteString("endbfchar\n")
			if l-i < 100 {
				c = l - i
			}
			fmt.Fprintf(b, "%d beginbfchar\n", c)
		}
		j++
	}
	b.WriteString("endbfchar\n")
}

// toUnicodeCMap returns a stream dict containing a CMap file that maps character codes to Unicode values (see 9.10).
func toUnicodeCMap(xRefTable *XRefTable, ttf TTFLight, fontName string, subFont bool, indRef *IndirectRef) (*IndirectRef, error) {
	// n beginbfchar
	// srcCode dstString
	// <003A>  <0037>                                            : 003a:0037
	// <3A51>  <D840DC3E>                                        : 3a51:d840dc3e
	// ...
	// endbfchar

	// n beginbfrange
	// srcCode1 srcCode2 dstString
	// <0000>   <005E>   <0020>                                  : 0000:0020 0001:0021 0002:0022 ...
	// <005F>   <0061>   [<00660066> <00660069> <00660066006C>]  : 005F:00660066 0060:00660069 0061:00660066006C
	// endbfrange

	pro := `/CIDInit /ProcSet findresource begin
12 dict begin
begincmap
/CIDSystemInfo <<
	/Registry (Adobe)
	/Ordering (UCS)
	/Supplement 0
>> def
/CMapName /Adobe-Identity-UCS def
/CMapType 2 def
`

	r := `1 begincodespacerange
<0000> <FFFF>
endcodespacerange
`

	epi := `endcmap
CMapName currentdict /CMap defineresource pop
end
end`

	var b bytes.Buffer
	b.WriteString(pro)
	b.WriteString(r)
	usedGIDs := xRefTable.UsedGIDs[fontName]
	if usedGIDs == nil {
		usedGIDs = map[uint16]bool{}
	}
	bf(&b, ttf, usedGIDs, subFont)
	b.WriteString(epi)

	bb := b.Bytes()

	if indRef == nil {
		return flateEncodedStreamIndRef(xRefTable, bb)
	}

	entry, _ := xRefTable.FindTableEntryForIndRef(indRef)
	sd, _ := entry.Object.(StreamDict)
	sd.Content = bb
	sd.InsertInt("Length1", len(bb))
	if err := sd.Encode(); err != nil {
		return nil, err
	}
	entry.Object = sd

	return indRef, nil
}

var (
	errCorruptCMap     = errors.New("pdfcpu: corrupt CMap")
	ErrCorruptFontDict = errors.New("pdfcpu: corrupt fontDict")
)

func usedGIDsFromCMap(cMap string) ([]uint16, error) {
	gids := []uint16{}
	i := strings.Index(cMap, "endcodespacerange")
	if i < 0 {
		return nil, errCorruptCMap
	}
	scanner := bufio.NewScanner(strings.NewReader(cMap[i+len("endcodespacerange")+1:]))

	// scanLine: %d beginbfchar
	scanner.Scan()
	s := scanner.Text()

	var lastBlock bool

	for {
		ss := strings.Split(s, " ")
		i, err := strconv.Atoi(ss[0])
		if err != nil {
			return nil, errCorruptCMap
		}

		lastBlock = i < 100

		// scan i lines:
		for j := 0; j < i; j++ {
			scanner.Scan()
			s1 := scanner.Text()
			if s1[0] != '<' {
				return nil, errCorruptCMap
			}
			bb, err := hex.DecodeString(s1[1:5])
			if err != nil {
				return nil, errCorruptCMap
			}
			gid := binary.BigEndian.Uint16(bb)
			gids = append(gids, gid)
		}

		// scanLine: endbfchar
		scanner.Scan()
		if scanner.Text() != "endbfchar" {
			return nil, errCorruptCMap
		}

		// scanLine: endcmap => done, or %d beginbfchar
		scanner.Scan()
		s = scanner.Text()
		if s == "endcmap" {
			break
		}
		if lastBlock {
			return nil, errCorruptCMap
		}
	}

	return gids, nil
}

// UserFontMetrics represents font metrics for TTF or OTF font files installed into UserFontDir.
var (
	UserFontMetrics     = map[string]TTFLight{}
	UserFontMetricsLock = &sync.RWMutex{}
)

// UpdateUserfont updates the fontdict for fontName via supplied font resource.
func UpdateUserfont(xRefTable *XRefTable, fontName string, f FontResource) error {
	UserFontMetricsLock.RLock()
	ttf, ok := UserFontMetrics[fontName]
	UserFontMetricsLock.RUnlock()

	if !ok {
		return errors.Errorf("pdfcpu: userfont %s not available", fontName)
	}

	if err := usedGIDsFromCMapIndRef(xRefTable, fontName, *f.ToUnicode); err != nil {
		return err
	}

	if _, err := toUnicodeCMap(xRefTable, ttf, fontName, true, f.ToUnicode); err != nil {
		return err
	}

	if _, err := ttfSubFontFile(xRefTable, fontName, f.FontFile); err != nil {
		return err
	}

	if _, err := CIDWidths(xRefTable, ttf, fontName, true, f.W); err != nil {
		return err
	}

	if _, err := CIDSet(xRefTable, ttf, fontName, f.CIDSet); err != nil {
		return err
	}

	return nil
}

func usedGIDsFromCMapIndRef(xRefTable *XRefTable, fontName string, cmapIndRef IndirectRef) error {
	sd, _, err := xRefTable.DereferenceStreamDict(cmapIndRef)
	if err != nil {
		return err
	}
	if err := sd.Decode(); err != nil {
		return err
	}
	gids, err := usedGIDsFromCMap(string(sd.Content))
	if err != nil {
		return err
	}
	m, ok := xRefTable.UsedGIDs[fontName]
	if !ok {
		m = map[uint16]bool{}
		xRefTable.UsedGIDs[fontName] = m
	}
	for _, gid := range gids {
		m[gid] = true
	}
	return nil
}

func subFontPrefix() string {
	s := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	var r *randMath.Rand = randMath.New(randMath.NewSource(time.Now().UnixNano()))
	bb := make([]byte, 6)
	for i := range bb {
		bb[i] = s[r.Intn(len(s))]
	}
	return string(bb)
}

// CIDFontDict returns the descendant font dict with special encoding for Type0 fonts.
func CIDFontDict(xRefTable *XRefTable, ttf TTFLight, fontName, baseFontName, lang string, parms *cjk) (*IndirectRef, error) {
	fdIndRef, err := CIDFontDescriptor(xRefTable, ttf, fontName, baseFontName, lang, parms == nil)
	if err != nil {
		return nil, err
	}

	ordering := "Identity"
	if parms != nil {
		ordering = parms.ordering
	}

	supplement := 0
	if parms != nil {
		supplement = parms.supplement
	}

	d := Dict(
		map[string]Object{
			"Type":     NameType("Font"),
			"Subtype":  NameType("CIDFontType2"),
			"BaseFont": NameType(baseFontName),
			"CIDSystemInfo": Dict(
				map[string]Object{
					"Ordering":   StringLiteral(ordering),
					"Registry":   StringLiteral("Adobe"),
					"Supplement": Integer(supplement),
				},
			),
			"FontDescriptor": *fdIndRef,

			// (Optional)
			// The default width for glyphs in the CIDFont (see 9.7.4.3, "Glyph Metrics in CIDFonts").
			// Default value: 1000 (defined in user units).
			// "DW": Integer(1000),

			// (Optional)
			// A description of the widths for the glyphs in the CID
			// The array’s elements have a variable format that can specify individual widths for consecutive CIDs
			// or one width for a range of CIDs (see 9.7.4.3, "Glyph Metrics in CIDFonts").
			// Default value: none (the DW value shall be used for all glyphs).
			//"W": *wIndRef,

			// (Optional; applies only to CIDFonts used for vertical writing)
			// An array of two numbers specifying the default metrics for vertical writing (see 9.7.4.3, "Glyph Metrics in CIDFonts").
			// Default value: [880 −1000].
			// "DW2":             Integer(1000),

			// (Optional; applies only to CIDFonts used for vertical writing)
			// A description of the metrics for vertical writing for the glyphs in the CIDFont (see 9.7.4.3, "Glyph Metrics in CIDFonts").
			// Default value: none (the DW2 value shall be used for all glyphs).
			// "W2": nil,
		},
	)

	// (Optional; Type 2 CIDFonts only)
	// A specification of the mapping from CIDs to glyph indices.
	// maps CIDs to the glyph indices for the appropriate glyph descriptions in that font program.
	// if stream: the glyph index for a particular CID value c shall be a 2-byte value stored in bytes 2 × c and 2 × c + 1,
	// where the first byte shall be the high-order byte.))
	if ordering == "Identity" {
		d["CIDToGIDMap"] = NameType("Identity")
	}

	if parms == nil {
		wIndRef, err := CIDWidths(xRefTable, ttf, fontName, parms == nil, nil)
		if err != nil {
			return nil, err
		}
		if wIndRef != nil {
			d["W"] = *wIndRef
		}
	}

	return xRefTable.IndRefForNewObject(d)
}

func type0FontDict(xRefTable *XRefTable, fontName, lang, script string, indRef *IndirectRef) (*IndirectRef, error) {
	UserFontMetricsLock.RLock()
	ttf, ok := UserFontMetrics[fontName]
	UserFontMetricsLock.RUnlock()
	if !ok {
		return nil, errors.Errorf("pdfcpu: font %s not available", fontName)
	}

	subFont := script == ""

	// For consecutive pages or if no AP present using this
	if indRef != nil && subFont && !xRefTable.HasUsedGIDs(fontName) {
		if obj, _ := xRefTable.Dereference(*indRef); obj != nil {
			return indRef, nil
		}
	}

	baseFontName := fontName
	if subFont {
		baseFontName = subFontPrefix() + "+" + fontName
	}

	var parms *cjk
	if p, ok := cjkParms[script]; ok {
		parms = &p
	}

	encoding := "Identity-H"
	if parms != nil {
		encoding = parms.encoding
	}

	descendentFontIndRef, err := CIDFontDict(xRefTable, ttf, fontName, baseFontName, lang, parms)
	if err != nil {
		return nil, err
	}

	d := NewDict()
	d.InsertName("Type", "Font")
	d.InsertName("Subtype", "Type0")
	d.InsertName("BaseFont", baseFontName)
	d.InsertName("Name", fontName)
	d.InsertName("Encoding", encoding)
	d.Insert("DescendantFonts", Array{*descendentFontIndRef})

	if subFont {
		toUnicodeIndRef, err := toUnicodeCMap(xRefTable, ttf, fontName, subFont, nil)
		if err != nil {
			return nil, err
		}
		d.Insert("ToUnicode", *toUnicodeIndRef)
	}

	if subFont {
		// Reset used glyph ids.
		delete(xRefTable.UsedGIDs, fontName)
	}

	if indRef == nil {
		return xRefTable.IndRefForNewObject(d)
	}

	entry, _ := xRefTable.FindTableEntryForIndRef(indRef)
	entry.Object = d

	return indRef, nil
}

func trueTypeFontDict(xRefTable *XRefTable, fontName, fontLang string) (*IndirectRef, error) {
	UserFontMetricsLock.RLock()
	ttf, ok := UserFontMetrics[fontName]
	UserFontMetricsLock.RUnlock()
	if !ok {
		return nil, errors.Errorf("pdfcpu: font %s not available", fontName)
	}

	first, last := 0, 255
	wIndRef, err := Widths(xRefTable, ttf, first, last)
	if err != nil {
		return nil, err
	}

	fdIndRef, err := NewFontDescriptor(xRefTable, ttf, fontName, fontLang)
	if err != nil {
		return nil, err
	}

	d := NewDict()
	d.InsertName("Type", "Font")
	d.InsertName("Subtype", "TrueType")
	d.InsertName("BaseFont", fontName)
	d.InsertName("Name", fontName)
	d.InsertName("Encoding", "WinAnsiEncoding")
	d.InsertInt("FirstChar", first)
	d.InsertInt("LastChar", last)
	d.Insert("Widths", *wIndRef)
	d.Insert("FontDescriptor", *fdIndRef)

	return xRefTable.IndRefForNewObject(d)
}

// CJK returns true if script and lang imply a CJK
func CJK(script, lang string) bool {
	if script != "" {
		_, ok := cjkParms[script]
		return ok
	}
	return MemberOf(lang, []string{"ja", "ko", "zh"})
}

// RTL returns true if lang implies a right-to-left script.
func RTL(lang string) bool {
	return MemberOf(lang, []string{"ar", "fa", "he", "ur"})
}

type fontMetrics struct {
	FBox *Rectangle     // font box
	W    map[string]int // glyph widths
}

// CoreFontMetrics represents font metrics for the Adobe standard type 1 core fonts.
var CoreFontMetrics = map[string]fontMetrics{
	"Courier-Bold": {
		NewRectangle(-113.0, -250.0, 749.0, 801.0),
		map[string]int{"space": 600, "exclam": 600, "quotedbl": 600, "numbersign": 600, "dollar": 600, "percent": 600, "ampersand": 600, "quoteright": 600, "parenleft": 600, "parenright": 600, "asterisk": 600, "plus": 600, "comma": 600, "hyphen": 600, "period": 600, "slash": 600, "zero": 600, "one": 600, "two": 600, "three": 600, "four": 600, "five": 600, "six": 600, "seven": 600, "eight": 600, "nine": 600, "colon": 600, "semicolon": 600, "less": 600, "equal": 600, "greater": 600, "question": 600, "at": 600, "A": 600, "B": 600, "C": 600, "D": 600, "E": 600, "F": 600, "G": 600, "H": 600, "I": 600, "J": 600, "K": 600, "L": 600, "M": 600, "N": 600, "O": 600, "P": 600, "Q": 600, "R": 600, "S": 600, "T": 600, "U": 600, "V": 600, "W": 600, "X": 600, "Y": 600, "Z": 600, "bracketleft": 600, "backslash": 600, "bracketright": 600, "asciicircum": 600, "underscore": 600, "quoteleft": 600, "a": 600, "b": 600, "c": 600, "d": 600, "e": 600, "f": 600, "g": 600, "h": 600, "i": 600, "j": 600, "k": 600, "l": 600, "m": 600, "n": 600, "o": 600, "p": 600, "q": 600, "r": 600, "s": 600, "t": 600, "u": 600, "v": 600, "w": 600, "x": 600, "y": 600, "z": 600, "braceleft": 600, "bar": 600, "braceright": 600, "asciitilde": 600, "exclamdown": 600, "cent": 600, "sterling": 600, "fraction": 600, "yen": 600, "florin": 600, "section": 600, "currency": 600, "quotesingle": 600, "quotedblleft": 600, "guillemotleft": 600, "guilsinglleft": 600, "guilsinglright": 600, "fi": 600, "fl": 600, "endash": 600, "dagger": 600, "daggerdbl": 600, "periodcentered": 600, "paragraph": 600, "bullet": 600, "quotesinglbase": 600, "quotedblbase": 600, "quotedblright": 600, "guillemotright": 600, "ellipsis": 600, "perthousand": 600, "questiondown": 600, "grave": 600, "acute": 600, "circumflex": 600, "tilde": 600, "macron": 600, "breve": 600, "dotaccent": 600, "dieresis": 600, "ring": 600, "cedilla": 600, "hungarumlaut": 600, "ogonek": 600, "caron": 600, "emdash": 600, "AE": 600, "ordfeminine": 600, "Lslash": 600, "Oslash": 600, "OE": 600, "ordmasculine": 600, "ae": 600, "dotlessi": 600, "lslash": 600, "oslash": 600, "oe": 600, "germandbls": 600, "Idieresis": 600, "eacute": 600, "abreve": 600, "uhungarumlaut": 600, "ecaron": 600, "Ydieresis": 600, "divide": 600, "Yacute": 600, "Acircumflex": 600, "aacute": 600, "Ucircumflex": 600, "yacute": 600, "scommaaccent": 600, "ecircumflex": 600, "Uring": 600, "Udieresis": 600, "aogonek": 600, "Uacute": 600, "uogonek": 600, "Edieresis": 600, "Dcroat": 600, "commaaccent": 600, "copyright": 600, "Emacron": 600, "ccaron": 600, "aring": 600, "Ncommaaccent": 600, "lacute": 600, "agrave": 600, "Tcommaaccent": 600, "Cacute": 600, "atilde": 600, "Edotaccent": 600, "scaron": 600, "scedilla": 600, "iacute": 600, "lozenge": 600, "Rcaron": 600, "Gcommaaccent": 600, "ucircumflex": 600, "acircumflex": 600, "Amacron": 600, "rcaron": 600, "ccedilla": 600, "Zdotaccent": 600, "Thorn": 600, "Omacron": 600, "Racute": 600, "Sacute": 600, "dcaron": 600, "Umacron": 600, "uring": 600, "threesuperior": 600, "Ograve": 600, "Agrave": 600, "Abreve": 600, "multiply": 600, "uacute": 600, "Tcaron": 600, "partialdiff": 600, "ydieresis": 600, "Nacute": 600, "icircumflex": 600, "Ecircumflex": 600, "adieresis": 600, "edieresis": 600, "cacute": 600, "nacute": 600, "umacron": 600, "Ncaron": 600, "Iacute": 600, "plusminus": 600, "brokenbar": 600, "registered": 600, "Gbreve": 600, "Idotaccent": 600, "summation": 600, "Egrave": 600, "racute": 600, "omacron": 600, "Zacute": 600, "Zcaron": 600, "greaterequal": 600, "Eth": 600, "Ccedilla": 600, "lcommaaccent": 600, "tcaron": 600, "eogonek": 600, "Uogonek": 600, "Aacute": 600, "Adieresis": 600, "egrave": 600, "zacute": 600, "iogonek": 600, "Oacute": 600, "oacute": 600, "amacron": 600, "sacute": 600, "idieresis": 600, "Ocircumflex": 600, "Ugrave": 600, "Delta": 600, "thorn": 600, "twosuperior": 600, "Odieresis": 600, "mu": 600, "igrave": 600, "ohungarumlaut": 600, "Eogonek": 600, "dcroat": 600, "threequarters": 600, "Scedilla": 600, "lcaron": 600, "Kcommaaccent": 600, "Lacute": 600, "trademark": 600, "edotaccent": 600, "Igrave": 600, "Imacron": 600, "Lcaron": 600, "onehalf": 600, "lessequal": 600, "ocircumflex": 600, "ntilde": 600, "Uhungarumlaut": 600, "Eacute": 600, "emacron": 600, "gbreve": 600, "onequarter": 600, "Scaron": 600, "Scommaaccent": 600, "Ohungarumlaut": 600, "degree": 600, "ograve": 600, "Ccaron": 600, "ugrave": 600, "radical": 600, "Dcaron": 600, "rcommaaccent": 600, "Ntilde": 600, "otilde": 600, "Rcommaaccent": 600, "Lcommaaccent": 600, "Atilde": 600, "Aogonek": 600, "Aring": 600, "Otilde": 600, "zdotaccent": 600, "Ecaron": 600, "Iogonek": 600, "kcommaaccent": 600, "minus": 600, "Icircumflex": 600, "ncaron": 600, "tcommaaccent": 600, "logicalnot": 600, "odieresis": 600, "udieresis": 600, "notequal": 600, "gcommaaccent": 600, "eth": 600, "zcaron": 600, "ncommaaccent": 600, "onesuperior": 600, "imacron": 600, "Euro": 600},
	},
	"Courier-BoldOblique": {
		NewRectangle(-57.0, -250.0, 869.0, 801.0),
		map[string]int{"space": 600, "exclam": 600, "quotedbl": 600, "numbersign": 600, "dollar": 600, "percent": 600, "ampersand": 600, "quoteright": 600, "parenleft": 600, "parenright": 600, "asterisk": 600, "plus": 600, "comma": 600, "hyphen": 600, "period": 600, "slash": 600, "zero": 600, "one": 600, "two": 600, "three": 600, "four": 600, "five": 600, "six": 600, "seven": 600, "eight": 600, "nine": 600, "colon": 600, "semicolon": 600, "less": 600, "equal": 600, "greater": 600, "question": 600, "at": 600, "A": 600, "B": 600, "C": 600, "D": 600, "E": 600, "F": 600, "G": 600, "H": 600, "I": 600, "J": 600, "K": 600, "L": 600, "M": 600, "N": 600, "O": 600, "P": 600, "Q": 600, "R": 600, "S": 600, "T": 600, "U": 600, "V": 600, "W": 600, "X": 600, "Y": 600, "Z": 600, "bracketleft": 600, "backslash": 600, "bracketright": 600, "asciicircum": 600, "underscore": 600, "quoteleft": 600, "a": 600, "b": 600, "c": 600, "d": 600, "e": 600, "f": 600, "g": 600, "h": 600, "i": 600, "j": 600, "k": 600, "l": 600, "m": 600, "n": 600, "o": 600, "p": 600, "q": 600, "r": 600, "s": 600, "t": 600, "u": 600, "v": 600, "w": 600, "x": 600, "y": 600, "z": 600, "braceleft": 600, "bar": 600, "braceright": 600, "asciitilde": 600, "exclamdown": 600, "cent": 600, "sterling": 600, "fraction": 600, "yen": 600, "florin": 600, "section": 600, "currency": 600, "quotesingle": 600, "quotedblleft": 600, "guillemotleft": 600, "guilsinglleft": 600, "guilsinglright": 600, "fi": 600, "fl": 600, "endash": 600, "dagger": 600, "daggerdbl": 600, "periodcentered": 600, "paragraph": 600, "bullet": 600, "quotesinglbase": 600, "quotedblbase": 600, "quotedblright": 600, "guillemotright": 600, "ellipsis": 600, "perthousand": 600, "questiondown": 600, "grave": 600, "acute": 600, "circumflex": 600, "tilde": 600, "macron": 600, "breve": 600, "dotaccent": 600, "dieresis": 600, "ring": 600, "cedilla": 600, "hungarumlaut": 600, "ogonek": 600, "caron": 600, "emdash": 600, "AE": 600, "ordfeminine": 600, "Lslash": 600, "Oslash": 600, "OE": 600, "ordmasculine": 600, "ae": 600, "dotlessi": 600, "lslash": 600, "oslash": 600, "oe": 600, "germandbls": 600, "Idieresis": 600, "eacute": 600, "abreve": 600, "uhungarumlaut": 600, "ecaron": 600, "Ydieresis": 600, "divide": 600, "Yacute": 600, "Acircumflex": 600, "aacute": 600, "Ucircumflex": 600, "yacute": 600, "scommaaccent": 600, "ecircumflex": 600, "Uring": 600, "Udieresis": 600, "aogonek": 600, "Uacute": 600, "uogonek": 600, "Edieresis": 600, "Dcroat": 600, "commaaccent": 600, "copyright": 600, "Emacron": 600, "ccaron": 600, "aring": 600, "Ncommaaccent": 600, "lacute": 600, "agrave": 600, "Tcommaaccent": 600, "Cacute": 600, "atilde": 600, "Edotaccent": 600, "scaron": 600, "scedilla": 600, "iacute": 600, "lozenge": 600, "Rcaron": 600, "Gcommaaccent": 600, "ucircumflex": 600, "acircumflex": 600, "Amacron": 600, "rcaron": 600, "ccedilla": 600, "Zdotaccent": 600, "Thorn": 600, "Omacron": 600, "Racute": 600, "Sacute": 600, "dcaron": 600, "Umacron": 600, "uring": 600, "threesuperior": 600, "Ograve": 600, "Agrave": 600, "Abreve": 600, "multiply": 600, "uacute": 600, "Tcaron": 600, "partialdiff": 600, "ydieresis": 600, "Nacute": 600, "icircumflex": 600, "Ecircumflex": 600, "adieresis": 600, "edieresis": 600, "cacute": 600, "nacute": 600, "umacron": 600, "Ncaron": 600, "Iacute": 600, "plusminus": 600, "brokenbar": 600, "registered": 600, "Gbreve": 600, "Idotaccent": 600, "summation": 600, "Egrave": 600, "racute": 600, "omacron": 600, "Zacute": 600, "Zcaron": 600, "greaterequal": 600, "Eth": 600, "Ccedilla": 600, "lcommaaccent": 600, "tcaron": 600, "eogonek": 600, "Uogonek": 600, "Aacute": 600, "Adieresis": 600, "egrave": 600, "zacute": 600, "iogonek": 600, "Oacute": 600, "oacute": 600, "amacron": 600, "sacute": 600, "idieresis": 600, "Ocircumflex": 600, "Ugrave": 600, "Delta": 600, "thorn": 600, "twosuperior": 600, "Odieresis": 600, "mu": 600, "igrave": 600, "ohungarumlaut": 600, "Eogonek": 600, "dcroat": 600, "threequarters": 600, "Scedilla": 600, "lcaron": 600, "Kcommaaccent": 600, "Lacute": 600, "trademark": 600, "edotaccent": 600, "Igrave": 600, "Imacron": 600, "Lcaron": 600, "onehalf": 600, "lessequal": 600, "ocircumflex": 600, "ntilde": 600, "Uhungarumlaut": 600, "Eacute": 600, "emacron": 600, "gbreve": 600, "onequarter": 600, "Scaron": 600, "Scommaaccent": 600, "Ohungarumlaut": 600, "degree": 600, "ograve": 600, "Ccaron": 600, "ugrave": 600, "radical": 600, "Dcaron": 600, "rcommaaccent": 600, "Ntilde": 600, "otilde": 600, "Rcommaaccent": 600, "Lcommaaccent": 600, "Atilde": 600, "Aogonek": 600, "Aring": 600, "Otilde": 600, "zdotaccent": 600, "Ecaron": 600, "Iogonek": 600, "kcommaaccent": 600, "minus": 600, "Icircumflex": 600, "ncaron": 600, "tcommaaccent": 600, "logicalnot": 600, "odieresis": 600, "udieresis": 600, "notequal": 600, "gcommaaccent": 600, "eth": 600, "zcaron": 600, "ncommaaccent": 600, "onesuperior": 600, "imacron": 600, "Euro": 600},
	},
	"Courier-Oblique": {
		NewRectangle(-27.0, -250.0, 849.0, 805.0),
		map[string]int{"space": 600, "exclam": 600, "quotedbl": 600, "numbersign": 600, "dollar": 600, "percent": 600, "ampersand": 600, "quoteright": 600, "parenleft": 600, "parenright": 600, "asterisk": 600, "plus": 600, "comma": 600, "hyphen": 600, "period": 600, "slash": 600, "zero": 600, "one": 600, "two": 600, "three": 600, "four": 600, "five": 600, "six": 600, "seven": 600, "eight": 600, "nine": 600, "colon": 600, "semicolon": 600, "less": 600, "equal": 600, "greater": 600, "question": 600, "at": 600, "A": 600, "B": 600, "C": 600, "D": 600, "E": 600, "F": 600, "G": 600, "H": 600, "I": 600, "J": 600, "K": 600, "L": 600, "M": 600, "N": 600, "O": 600, "P": 600, "Q": 600, "R": 600, "S": 600, "T": 600, "U": 600, "V": 600, "W": 600, "X": 600, "Y": 600, "Z": 600, "bracketleft": 600, "backslash": 600, "bracketright": 600, "asciicircum": 600, "underscore": 600, "quoteleft": 600, "a": 600, "b": 600, "c": 600, "d": 600, "e": 600, "f": 600, "g": 600, "h": 600, "i": 600, "j": 600, "k": 600, "l": 600, "m": 600, "n": 600, "o": 600, "p": 600, "q": 600, "r": 600, "s": 600, "t": 600, "u": 600, "v": 600, "w": 600, "x": 600, "y": 600, "z": 600, "braceleft": 600, "bar": 600, "braceright": 600, "asciitilde": 600, "exclamdown": 600, "cent": 600, "sterling": 600, "fraction": 600, "yen": 600, "florin": 600, "section": 600, "currency": 600, "quotesingle": 600, "quotedblleft": 600, "guillemotleft": 600, "guilsinglleft": 600, "guilsinglright": 600, "fi": 600, "fl": 600, "endash": 600, "dagger": 600, "daggerdbl": 600, "periodcentered": 600, "paragraph": 600, "bullet": 600, "quotesinglbase": 600, "quotedblbase": 600, "quotedblright": 600, "guillemotright": 600, "ellipsis": 600, "perthousand": 600, "questiondown": 600, "grave": 600, "acute": 600, "circumflex": 600, "tilde": 600, "macron": 600, "breve": 600, "dotaccent": 600, "dieresis": 600, "ring": 600, "cedilla": 600, "hungarumlaut": 600, "ogonek": 600, "caron": 600, "emdash": 600, "AE": 600, "ordfeminine": 600, "Lslash": 600, "Oslash": 600, "OE": 600, "ordmasculine": 600, "ae": 600, "dotlessi": 600, "lslash": 600, "oslash": 600, "oe": 600, "germandbls": 600, "Idieresis": 600, "eacute": 600, "abreve": 600, "uhungarumlaut": 600, "ecaron": 600, "Ydieresis": 600, "divide": 600, "Yacute": 600, "Acircumflex": 600, "aacute": 600, "Ucircumflex": 600, "yacute": 600, "scommaaccent": 600, "ecircumflex": 600, "Uring": 600, "Udieresis": 600, "aogonek": 600, "Uacute": 600, "uogonek": 600, "Edieresis": 600, "Dcroat": 600, "commaaccent": 600, "copyright": 600, "Emacron": 600, "ccaron": 600, "aring": 600, "Ncommaaccent": 600, "lacute": 600, "agrave": 600, "Tcommaaccent": 600, "Cacute": 600, "atilde": 600, "Edotaccent": 600, "scaron": 600, "scedilla": 600, "iacute": 600, "lozenge": 600, "Rcaron": 600, "Gcommaaccent": 600, "ucircumflex": 600, "acircumflex": 600, "Amacron": 600, "rcaron": 600, "ccedilla": 600, "Zdotaccent": 600, "Thorn": 600, "Omacron": 600, "Racute": 600, "Sacute": 600, "dcaron": 600, "Umacron": 600, "uring": 600, "threesuperior": 600, "Ograve": 600, "Agrave": 600, "Abreve": 600, "multiply": 600, "uacute": 600, "Tcaron": 600, "partialdiff": 600, "ydieresis": 600, "Nacute": 600, "icircumflex": 600, "Ecircumflex": 600, "adieresis": 600, "edieresis": 600, "cacute": 600, "nacute": 600, "umacron": 600, "Ncaron": 600, "Iacute": 600, "plusminus": 600, "brokenbar": 600, "registered": 600, "Gbreve": 600, "Idotaccent": 600, "summation": 600, "Egrave": 600, "racute": 600, "omacron": 600, "Zacute": 600, "Zcaron": 600, "greaterequal": 600, "Eth": 600, "Ccedilla": 600, "lcommaaccent": 600, "tcaron": 600, "eogonek": 600, "Uogonek": 600, "Aacute": 600, "Adieresis": 600, "egrave": 600, "zacute": 600, "iogonek": 600, "Oacute": 600, "oacute": 600, "amacron": 600, "sacute": 600, "idieresis": 600, "Ocircumflex": 600, "Ugrave": 600, "Delta": 600, "thorn": 600, "twosuperior": 600, "Odieresis": 600, "mu": 600, "igrave": 600, "ohungarumlaut": 600, "Eogonek": 600, "dcroat": 600, "threequarters": 600, "Scedilla": 600, "lcaron": 600, "Kcommaaccent": 600, "Lacute": 600, "trademark": 600, "edotaccent": 600, "Igrave": 600, "Imacron": 600, "Lcaron": 600, "onehalf": 600, "lessequal": 600, "ocircumflex": 600, "ntilde": 600, "Uhungarumlaut": 600, "Eacute": 600, "emacron": 600, "gbreve": 600, "onequarter": 600, "Scaron": 600, "Scommaaccent": 600, "Ohungarumlaut": 600, "degree": 600, "ograve": 600, "Ccaron": 600, "ugrave": 600, "radical": 600, "Dcaron": 600, "rcommaaccent": 600, "Ntilde": 600, "otilde": 600, "Rcommaaccent": 600, "Lcommaaccent": 600, "Atilde": 600, "Aogonek": 600, "Aring": 600, "Otilde": 600, "zdotaccent": 600, "Ecaron": 600, "Iogonek": 600, "kcommaaccent": 600, "minus": 600, "Icircumflex": 600, "ncaron": 600, "tcommaaccent": 600, "logicalnot": 600, "odieresis": 600, "udieresis": 600, "notequal": 600, "gcommaaccent": 600, "eth": 600, "zcaron": 600, "ncommaaccent": 600, "onesuperior": 600, "imacron": 600, "Euro": 600},
	},
	"Courier": {
		NewRectangle(-23.0, -250.0, 715.0, 805.0),
		map[string]int{"space": 600, "exclam": 600, "quotedbl": 600, "numbersign": 600, "dollar": 600, "percent": 600, "ampersand": 600, "quoteright": 600, "parenleft": 600, "parenright": 600, "asterisk": 600, "plus": 600, "comma": 600, "hyphen": 600, "period": 600, "slash": 600, "zero": 600, "one": 600, "two": 600, "three": 600, "four": 600, "five": 600, "six": 600, "seven": 600, "eight": 600, "nine": 600, "colon": 600, "semicolon": 600, "less": 600, "equal": 600, "greater": 600, "question": 600, "at": 600, "A": 600, "B": 600, "C": 600, "D": 600, "E": 600, "F": 600, "G": 600, "H": 600, "I": 600, "J": 600, "K": 600, "L": 600, "M": 600, "N": 600, "O": 600, "P": 600, "Q": 600, "R": 600, "S": 600, "T": 600, "U": 600, "V": 600, "W": 600, "X": 600, "Y": 600, "Z": 600, "bracketleft": 600, "backslash": 600, "bracketright": 600, "asciicircum": 600, "underscore": 600, "quoteleft": 600, "a": 600, "b": 600, "c": 600, "d": 600, "e": 600, "f": 600, "g": 600, "h": 600, "i": 600, "j": 600, "k": 600, "l": 600, "m": 600, "n": 600, "o": 600, "p": 600, "q": 600, "r": 600, "s": 600, "t": 600, "u": 600, "v": 600, "w": 600, "x": 600, "y": 600, "z": 600, "braceleft": 600, "bar": 600, "braceright": 600, "asciitilde": 600, "exclamdown": 600, "cent": 600, "sterling": 600, "fraction": 600, "yen": 600, "florin": 600, "section": 600, "currency": 600, "quotesingle": 600, "quotedblleft": 600, "guillemotleft": 600, "guilsinglleft": 600, "guilsinglright": 600, "fi": 600, "fl": 600, "endash": 600, "dagger": 600, "daggerdbl": 600, "periodcentered": 600, "paragraph": 600, "bullet": 600, "quotesinglbase": 600, "quotedblbase": 600, "quotedblright": 600, "guillemotright": 600, "ellipsis": 600, "perthousand": 600, "questiondown": 600, "grave": 600, "acute": 600, "circumflex": 600, "tilde": 600, "macron": 600, "breve": 600, "dotaccent": 600, "dieresis": 600, "ring": 600, "cedilla": 600, "hungarumlaut": 600, "ogonek": 600, "caron": 600, "emdash": 600, "AE": 600, "ordfeminine": 600, "Lslash": 600, "Oslash": 600, "OE": 600, "ordmasculine": 600, "ae": 600, "dotlessi": 600, "lslash": 600, "oslash": 600, "oe": 600, "germandbls": 600, "Idieresis": 600, "eacute": 600, "abreve": 600, "uhungarumlaut": 600, "ecaron": 600, "Ydieresis": 600, "divide": 600, "Yacute": 600, "Acircumflex": 600, "aacute": 600, "Ucircumflex": 600, "yacute": 600, "scommaaccent": 600, "ecircumflex": 600, "Uring": 600, "Udieresis": 600, "aogonek": 600, "Uacute": 600, "uogonek": 600, "Edieresis": 600, "Dcroat": 600, "commaaccent": 600, "copyright": 600, "Emacron": 600, "ccaron": 600, "aring": 600, "Ncommaaccent": 600, "lacute": 600, "agrave": 600, "Tcommaaccent": 600, "Cacute": 600, "atilde": 600, "Edotaccent": 600, "scaron": 600, "scedilla": 600, "iacute": 600, "lozenge": 600, "Rcaron": 600, "Gcommaaccent": 600, "ucircumflex": 600, "acircumflex": 600, "Amacron": 600, "rcaron": 600, "ccedilla": 600, "Zdotaccent": 600, "Thorn": 600, "Omacron": 600, "Racute": 600, "Sacute": 600, "dcaron": 600, "Umacron": 600, "uring": 600, "threesuperior": 600, "Ograve": 600, "Agrave": 600, "Abreve": 600, "multiply": 600, "uacute": 600, "Tcaron": 600, "partialdiff": 600, "ydieresis": 600, "Nacute": 600, "icircumflex": 600, "Ecircumflex": 600, "adieresis": 600, "edieresis": 600, "cacute": 600, "nacute": 600, "umacron": 600, "Ncaron": 600, "Iacute": 600, "plusminus": 600, "brokenbar": 600, "registered": 600, "Gbreve": 600, "Idotaccent": 600, "summation": 600, "Egrave": 600, "racute": 600, "omacron": 600, "Zacute": 600, "Zcaron": 600, "greaterequal": 600, "Eth": 600, "Ccedilla": 600, "lcommaaccent": 600, "tcaron": 600, "eogonek": 600, "Uogonek": 600, "Aacute": 600, "Adieresis": 600, "egrave": 600, "zacute": 600, "iogonek": 600, "Oacute": 600, "oacute": 600, "amacron": 600, "sacute": 600, "idieresis": 600, "Ocircumflex": 600, "Ugrave": 600, "Delta": 600, "thorn": 600, "twosuperior": 600, "Odieresis": 600, "mu": 600, "igrave": 600, "ohungarumlaut": 600, "Eogonek": 600, "dcroat": 600, "threequarters": 600, "Scedilla": 600, "lcaron": 600, "Kcommaaccent": 600, "Lacute": 600, "trademark": 600, "edotaccent": 600, "Igrave": 600, "Imacron": 600, "Lcaron": 600, "onehalf": 600, "lessequal": 600, "ocircumflex": 600, "ntilde": 600, "Uhungarumlaut": 600, "Eacute": 600, "emacron": 600, "gbreve": 600, "onequarter": 600, "Scaron": 600, "Scommaaccent": 600, "Ohungarumlaut": 600, "degree": 600, "ograve": 600, "Ccaron": 600, "ugrave": 600, "radical": 600, "Dcaron": 600, "rcommaaccent": 600, "Ntilde": 600, "otilde": 600, "Rcommaaccent": 600, "Lcommaaccent": 600, "Atilde": 600, "Aogonek": 600, "Aring": 600, "Otilde": 600, "zdotaccent": 600, "Ecaron": 600, "Iogonek": 600, "kcommaaccent": 600, "minus": 600, "Icircumflex": 600, "ncaron": 600, "tcommaaccent": 600, "logicalnot": 600, "odieresis": 600, "udieresis": 600, "notequal": 600, "gcommaaccent": 600, "eth": 600, "zcaron": 600, "ncommaaccent": 600, "onesuperior": 600, "imacron": 600, "Euro": 600},
	},
	"Helvetica-Bold": {
		NewRectangle(-170.0, -228.0, 1003.0, 962.0),
		map[string]int{"space": 278, "exclam": 333, "quotedbl": 474, "numbersign": 556, "dollar": 556, "percent": 889, "ampersand": 722, "quoteright": 278, "parenleft": 333, "parenright": 333, "asterisk": 389, "plus": 584, "comma": 278, "hyphen": 333, "period": 278, "slash": 278, "zero": 556, "one": 556, "two": 556, "three": 556, "four": 556, "five": 556, "six": 556, "seven": 556, "eight": 556, "nine": 556, "colon": 333, "semicolon": 333, "less": 584, "equal": 584, "greater": 584, "question": 611, "at": 975, "A": 722, "B": 722, "C": 722, "D": 722, "E": 667, "F": 611, "G": 778, "H": 722, "I": 278, "J": 556, "K": 722, "L": 611, "M": 833, "N": 722, "O": 778, "P": 667, "Q": 778, "R": 722, "S": 667, "T": 611, "U": 722, "V": 667, "W": 944, "X": 667, "Y": 667, "Z": 611, "bracketleft": 333, "backslash": 278, "bracketright": 333, "asciicircum": 584, "underscore": 556, "quoteleft": 278, "a": 556, "b": 611, "c": 556, "d": 611, "e": 556, "f": 333, "g": 611, "h": 611, "i": 278, "j": 278, "k": 556, "l": 278, "m": 889, "n": 611, "o": 611, "p": 611, "q": 611, "r": 389, "s": 556, "t": 333, "u": 611, "v": 556, "w": 778, "x": 556, "y": 556, "z": 500, "braceleft": 389, "bar": 280, "braceright": 389, "asciitilde": 584, "exclamdown": 333, "cent": 556, "sterling": 556, "fraction": 167, "yen": 556, "florin": 556, "section": 556, "currency": 556, "quotesingle": 238, "quotedblleft": 500, "guillemotleft": 556, "guilsinglleft": 333, "guilsinglright": 333, "fi": 611, "fl": 611, "endash": 556, "dagger": 556, "daggerdbl": 556, "periodcentered": 278, "paragraph": 556, "bullet": 350, "quotesinglbase": 278, "quotedblbase": 500, "quotedblright": 500, "guillemotright": 556, "ellipsis": 1000, "perthousand": 1000, "questiondown": 611, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 1000, "ordfeminine": 370, "Lslash": 611, "Oslash": 778, "OE": 1000, "ordmasculine": 365, "ae": 889, "dotlessi": 278, "lslash": 278, "oslash": 611, "oe": 944, "germandbls": 611, "Idieresis": 278, "eacute": 556, "abreve": 556, "uhungarumlaut": 611, "ecaron": 556, "Ydieresis": 667, "divide": 584, "Yacute": 667, "Acircumflex": 722, "aacute": 556, "Ucircumflex": 722, "yacute": 556, "scommaaccent": 556, "ecircumflex": 556, "Uring": 722, "Udieresis": 722, "aogonek": 556, "Uacute": 722, "uogonek": 611, "Edieresis": 667, "Dcroat": 722, "commaaccent": 250, "copyright": 737, "Emacron": 667, "ccaron": 556, "aring": 556, "Ncommaaccent": 722, "lacute": 278, "agrave": 556, "Tcommaaccent": 611, "Cacute": 722, "atilde": 556, "Edotaccent": 667, "scaron": 556, "scedilla": 556, "iacute": 278, "lozenge": 494, "Rcaron": 722, "Gcommaaccent": 778, "ucircumflex": 611, "acircumflex": 556, "Amacron": 722, "rcaron": 389, "ccedilla": 556, "Zdotaccent": 611, "Thorn": 667, "Omacron": 778, "Racute": 722, "Sacute": 667, "dcaron": 743, "Umacron": 722, "uring": 611, "threesuperior": 333, "Ograve": 778, "Agrave": 722, "Abreve": 722, "multiply": 584, "uacute": 611, "Tcaron": 611, "partialdiff": 494, "ydieresis": 556, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 667, "adieresis": 556, "edieresis": 556, "cacute": 556, "nacute": 611, "umacron": 611, "Ncaron": 722, "Iacute": 278, "plusminus": 584, "brokenbar": 280, "registered": 737, "Gbreve": 778, "Idotaccent": 278, "summation": 600, "Egrave": 667, "racute": 389, "omacron": 611, "Zacute": 611, "Zcaron": 611, "greaterequal": 549, "Eth": 722, "Ccedilla": 722, "lcommaaccent": 278, "tcaron": 389, "eogonek": 556, "Uogonek": 722, "Aacute": 722, "Adieresis": 722, "egrave": 556, "zacute": 500, "iogonek": 278, "Oacute": 778, "oacute": 611, "amacron": 556, "sacute": 556, "idieresis": 278, "Ocircumflex": 778, "Ugrave": 722, "Delta": 612, "thorn": 611, "twosuperior": 333, "Odieresis": 778, "mu": 611, "igrave": 278, "ohungarumlaut": 611, "Eogonek": 667, "dcroat": 611, "threequarters": 834, "Scedilla": 667, "lcaron": 400, "Kcommaaccent": 722, "Lacute": 611, "trademark": 1000, "edotaccent": 556, "Igrave": 278, "Imacron": 278, "Lcaron": 611, "onehalf": 834, "lessequal": 549, "ocircumflex": 611, "ntilde": 611, "Uhungarumlaut": 722, "Eacute": 667, "emacron": 556, "gbreve": 611, "onequarter": 834, "Scaron": 667, "Scommaaccent": 667, "Ohungarumlaut": 778, "degree": 400, "ograve": 611, "Ccaron": 722, "ugrave": 611, "radical": 549, "Dcaron": 722, "rcommaaccent": 389, "Ntilde": 722, "otilde": 611, "Rcommaaccent": 722, "Lcommaaccent": 611, "Atilde": 722, "Aogonek": 722, "Aring": 722, "Otilde": 778, "zdotaccent": 500, "Ecaron": 667, "Iogonek": 278, "kcommaaccent": 556, "minus": 584, "Icircumflex": 278, "ncaron": 611, "tcommaaccent": 333, "logicalnot": 584, "odieresis": 611, "udieresis": 611, "notequal": 549, "gcommaaccent": 611, "eth": 611, "zcaron": 500, "ncommaaccent": 611, "onesuperior": 333, "imacron": 278, "Euro": 556},
	},
	"Helvetica-BoldOblique": {
		NewRectangle(-174.0, -228.0, 1114.0, 962.0),
		map[string]int{"space": 278, "exclam": 333, "quotedbl": 474, "numbersign": 556, "dollar": 556, "percent": 889, "ampersand": 722, "quoteright": 278, "parenleft": 333, "parenright": 333, "asterisk": 389, "plus": 584, "comma": 278, "hyphen": 333, "period": 278, "slash": 278, "zero": 556, "one": 556, "two": 556, "three": 556, "four": 556, "five": 556, "six": 556, "seven": 556, "eight": 556, "nine": 556, "colon": 333, "semicolon": 333, "less": 584, "equal": 584, "greater": 584, "question": 611, "at": 975, "A": 722, "B": 722, "C": 722, "D": 722, "E": 667, "F": 611, "G": 778, "H": 722, "I": 278, "J": 556, "K": 722, "L": 611, "M": 833, "N": 722, "O": 778, "P": 667, "Q": 778, "R": 722, "S": 667, "T": 611, "U": 722, "V": 667, "W": 944, "X": 667, "Y": 667, "Z": 611, "bracketleft": 333, "backslash": 278, "bracketright": 333, "asciicircum": 584, "underscore": 556, "quoteleft": 278, "a": 556, "b": 611, "c": 556, "d": 611, "e": 556, "f": 333, "g": 611, "h": 611, "i": 278, "j": 278, "k": 556, "l": 278, "m": 889, "n": 611, "o": 611, "p": 611, "q": 611, "r": 389, "s": 556, "t": 333, "u": 611, "v": 556, "w": 778, "x": 556, "y": 556, "z": 500, "braceleft": 389, "bar": 280, "braceright": 389, "asciitilde": 584, "exclamdown": 333, "cent": 556, "sterling": 556, "fraction": 167, "yen": 556, "florin": 556, "section": 556, "currency": 556, "quotesingle": 238, "quotedblleft": 500, "guillemotleft": 556, "guilsinglleft": 333, "guilsinglright": 333, "fi": 611, "fl": 611, "endash": 556, "dagger": 556, "daggerdbl": 556, "periodcentered": 278, "paragraph": 556, "bullet": 350, "quotesinglbase": 278, "quotedblbase": 500, "quotedblright": 500, "guillemotright": 556, "ellipsis": 1000, "perthousand": 1000, "questiondown": 611, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 1000, "ordfeminine": 370, "Lslash": 611, "Oslash": 778, "OE": 1000, "ordmasculine": 365, "ae": 889, "dotlessi": 278, "lslash": 278, "oslash": 611, "oe": 944, "germandbls": 611, "Idieresis": 278, "eacute": 556, "abreve": 556, "uhungarumlaut": 611, "ecaron": 556, "Ydieresis": 667, "divide": 584, "Yacute": 667, "Acircumflex": 722, "aacute": 556, "Ucircumflex": 722, "yacute": 556, "scommaaccent": 556, "ecircumflex": 556, "Uring": 722, "Udieresis": 722, "aogonek": 556, "Uacute": 722, "uogonek": 611, "Edieresis": 667, "Dcroat": 722, "commaaccent": 250, "copyright": 737, "Emacron": 667, "ccaron": 556, "aring": 556, "Ncommaaccent": 722, "lacute": 278, "agrave": 556, "Tcommaaccent": 611, "Cacute": 722, "atilde": 556, "Edotaccent": 667, "scaron": 556, "scedilla": 556, "iacute": 278, "lozenge": 494, "Rcaron": 722, "Gcommaaccent": 778, "ucircumflex": 611, "acircumflex": 556, "Amacron": 722, "rcaron": 389, "ccedilla": 556, "Zdotaccent": 611, "Thorn": 667, "Omacron": 778, "Racute": 722, "Sacute": 667, "dcaron": 743, "Umacron": 722, "uring": 611, "threesuperior": 333, "Ograve": 778, "Agrave": 722, "Abreve": 722, "multiply": 584, "uacute": 611, "Tcaron": 611, "partialdiff": 494, "ydieresis": 556, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 667, "adieresis": 556, "edieresis": 556, "cacute": 556, "nacute": 611, "umacron": 611, "Ncaron": 722, "Iacute": 278, "plusminus": 584, "brokenbar": 280, "registered": 737, "Gbreve": 778, "Idotaccent": 278, "summation": 600, "Egrave": 667, "racute": 389, "omacron": 611, "Zacute": 611, "Zcaron": 611, "greaterequal": 549, "Eth": 722, "Ccedilla": 722, "lcommaaccent": 278, "tcaron": 389, "eogonek": 556, "Uogonek": 722, "Aacute": 722, "Adieresis": 722, "egrave": 556, "zacute": 500, "iogonek": 278, "Oacute": 778, "oacute": 611, "amacron": 556, "sacute": 556, "idieresis": 278, "Ocircumflex": 778, "Ugrave": 722, "Delta": 612, "thorn": 611, "twosuperior": 333, "Odieresis": 778, "mu": 611, "igrave": 278, "ohungarumlaut": 611, "Eogonek": 667, "dcroat": 611, "threequarters": 834, "Scedilla": 667, "lcaron": 400, "Kcommaaccent": 722, "Lacute": 611, "trademark": 1000, "edotaccent": 556, "Igrave": 278, "Imacron": 278, "Lcaron": 611, "onehalf": 834, "lessequal": 549, "ocircumflex": 611, "ntilde": 611, "Uhungarumlaut": 722, "Eacute": 667, "emacron": 556, "gbreve": 611, "onequarter": 834, "Scaron": 667, "Scommaaccent": 667, "Ohungarumlaut": 778, "degree": 400, "ograve": 611, "Ccaron": 722, "ugrave": 611, "radical": 549, "Dcaron": 722, "rcommaaccent": 389, "Ntilde": 722, "otilde": 611, "Rcommaaccent": 722, "Lcommaaccent": 611, "Atilde": 722, "Aogonek": 722, "Aring": 722, "Otilde": 778, "zdotaccent": 500, "Ecaron": 667, "Iogonek": 278, "kcommaaccent": 556, "minus": 584, "Icircumflex": 278, "ncaron": 611, "tcommaaccent": 333, "logicalnot": 584, "odieresis": 611, "udieresis": 611, "notequal": 549, "gcommaaccent": 611, "eth": 611, "zcaron": 500, "ncommaaccent": 611, "onesuperior": 333, "imacron": 278, "Euro": 556},
	},
	"Helvetica-Oblique": {
		NewRectangle(-170.0, -225.0, 1116.0, 931.0),
		map[string]int{"space": 278, "exclam": 278, "quotedbl": 355, "numbersign": 556, "dollar": 556, "percent": 889, "ampersand": 667, "quoteright": 222, "parenleft": 333, "parenright": 333, "asterisk": 389, "plus": 584, "comma": 278, "hyphen": 333, "period": 278, "slash": 278, "zero": 556, "one": 556, "two": 556, "three": 556, "four": 556, "five": 556, "six": 556, "seven": 556, "eight": 556, "nine": 556, "colon": 278, "semicolon": 278, "less": 584, "equal": 584, "greater": 584, "question": 556, "at": 1015, "A": 667, "B": 667, "C": 722, "D": 722, "E": 667, "F": 611, "G": 778, "H": 722, "I": 278, "J": 500, "K": 667, "L": 556, "M": 833, "N": 722, "O": 778, "P": 667, "Q": 778, "R": 722, "S": 667, "T": 611, "U": 722, "V": 667, "W": 944, "X": 667, "Y": 667, "Z": 611, "bracketleft": 278, "backslash": 278, "bracketright": 278, "asciicircum": 469, "underscore": 556, "quoteleft": 222, "a": 556, "b": 556, "c": 500, "d": 556, "e": 556, "f": 278, "g": 556, "h": 556, "i": 222, "j": 222, "k": 500, "l": 222, "m": 833, "n": 556, "o": 556, "p": 556, "q": 556, "r": 333, "s": 500, "t": 278, "u": 556, "v": 500, "w": 722, "x": 500, "y": 500, "z": 500, "braceleft": 334, "bar": 260, "braceright": 334, "asciitilde": 584, "exclamdown": 333, "cent": 556, "sterling": 556, "fraction": 167, "yen": 556, "florin": 556, "section": 556, "currency": 556, "quotesingle": 191, "quotedblleft": 333, "guillemotleft": 556, "guilsinglleft": 333, "guilsinglright": 333, "fi": 500, "fl": 500, "endash": 556, "dagger": 556, "daggerdbl": 556, "periodcentered": 278, "paragraph": 537, "bullet": 350, "quotesinglbase": 222, "quotedblbase": 333, "quotedblright": 333, "guillemotright": 556, "ellipsis": 1000, "perthousand": 1000, "questiondown": 611, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 1000, "ordfeminine": 370, "Lslash": 556, "Oslash": 778, "OE": 1000, "ordmasculine": 365, "ae": 889, "dotlessi": 278, "lslash": 222, "oslash": 611, "oe": 944, "germandbls": 611, "Idieresis": 278, "eacute": 556, "abreve": 556, "uhungarumlaut": 556, "ecaron": 556, "Ydieresis": 667, "divide": 584, "Yacute": 667, "Acircumflex": 667, "aacute": 556, "Ucircumflex": 722, "yacute": 500, "scommaaccent": 500, "ecircumflex": 556, "Uring": 722, "Udieresis": 722, "aogonek": 556, "Uacute": 722, "uogonek": 556, "Edieresis": 667, "Dcroat": 722, "commaaccent": 250, "copyright": 737, "Emacron": 667, "ccaron": 500, "aring": 556, "Ncommaaccent": 722, "lacute": 222, "agrave": 556, "Tcommaaccent": 611, "Cacute": 722, "atilde": 556, "Edotaccent": 667, "scaron": 500, "scedilla": 500, "iacute": 278, "lozenge": 471, "Rcaron": 722, "Gcommaaccent": 778, "ucircumflex": 556, "acircumflex": 556, "Amacron": 667, "rcaron": 333, "ccedilla": 500, "Zdotaccent": 611, "Thorn": 667, "Omacron": 778, "Racute": 722, "Sacute": 667, "dcaron": 643, "Umacron": 722, "uring": 556, "threesuperior": 333, "Ograve": 778, "Agrave": 667, "Abreve": 667, "multiply": 584, "uacute": 556, "Tcaron": 611, "partialdiff": 476, "ydieresis": 500, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 667, "adieresis": 556, "edieresis": 556, "cacute": 500, "nacute": 556, "umacron": 556, "Ncaron": 722, "Iacute": 278, "plusminus": 584, "brokenbar": 260, "registered": 737, "Gbreve": 778, "Idotaccent": 278, "summation": 600, "Egrave": 667, "racute": 333, "omacron": 556, "Zacute": 611, "Zcaron": 611, "greaterequal": 549, "Eth": 722, "Ccedilla": 722, "lcommaaccent": 222, "tcaron": 317, "eogonek": 556, "Uogonek": 722, "Aacute": 667, "Adieresis": 667, "egrave": 556, "zacute": 500, "iogonek": 222, "Oacute": 778, "oacute": 556, "amacron": 556, "sacute": 500, "idieresis": 278, "Ocircumflex": 778, "Ugrave": 722, "Delta": 612, "thorn": 556, "twosuperior": 333, "Odieresis": 778, "mu": 556, "igrave": 278, "ohungarumlaut": 556, "Eogonek": 667, "dcroat": 556, "threequarters": 834, "Scedilla": 667, "lcaron": 299, "Kcommaaccent": 667, "Lacute": 556, "trademark": 1000, "edotaccent": 556, "Igrave": 278, "Imacron": 278, "Lcaron": 556, "onehalf": 834, "lessequal": 549, "ocircumflex": 556, "ntilde": 556, "Uhungarumlaut": 722, "Eacute": 667, "emacron": 556, "gbreve": 556, "onequarter": 834, "Scaron": 667, "Scommaaccent": 667, "Ohungarumlaut": 778, "degree": 400, "ograve": 556, "Ccaron": 722, "ugrave": 556, "radical": 453, "Dcaron": 722, "rcommaaccent": 333, "Ntilde": 722, "otilde": 556, "Rcommaaccent": 722, "Lcommaaccent": 556, "Atilde": 667, "Aogonek": 667, "Aring": 667, "Otilde": 778, "zdotaccent": 500, "Ecaron": 667, "Iogonek": 278, "kcommaaccent": 500, "minus": 584, "Icircumflex": 278, "ncaron": 556, "tcommaaccent": 278, "logicalnot": 584, "odieresis": 556, "udieresis": 556, "notequal": 549, "gcommaaccent": 556, "eth": 556, "zcaron": 500, "ncommaaccent": 556, "onesuperior": 333, "imacron": 278, "Euro": 556},
	},
	"Helvetica": {
		NewRectangle(-166.0, -225.0, 1000.0, 931.0),
		map[string]int{"space": 278, "exclam": 278, "quotedbl": 355, "numbersign": 556, "dollar": 556, "percent": 889, "ampersand": 667, "quoteright": 222, "parenleft": 333, "parenright": 333, "asterisk": 389, "plus": 584, "comma": 278, "hyphen": 333, "period": 278, "slash": 278, "zero": 556, "one": 556, "two": 556, "three": 556, "four": 556, "five": 556, "six": 556, "seven": 556, "eight": 556, "nine": 556, "colon": 278, "semicolon": 278, "less": 584, "equal": 584, "greater": 584, "question": 556, "at": 1015, "A": 667, "B": 667, "C": 722, "D": 722, "E": 667, "F": 611, "G": 778, "H": 722, "I": 278, "J": 500, "K": 667, "L": 556, "M": 833, "N": 722, "O": 778, "P": 667, "Q": 778, "R": 722, "S": 667, "T": 611, "U": 722, "V": 667, "W": 944, "X": 667, "Y": 667, "Z": 611, "bracketleft": 278, "backslash": 278, "bracketright": 278, "asciicircum": 469, "underscore": 556, "quoteleft": 222, "a": 556, "b": 556, "c": 500, "d": 556, "e": 556, "f": 278, "g": 556, "h": 556, "i": 222, "j": 222, "k": 500, "l": 222, "m": 833, "n": 556, "o": 556, "p": 556, "q": 556, "r": 333, "s": 500, "t": 278, "u": 556, "v": 500, "w": 722, "x": 500, "y": 500, "z": 500, "braceleft": 334, "bar": 260, "braceright": 334, "asciitilde": 584, "exclamdown": 333, "cent": 556, "sterling": 556, "fraction": 167, "yen": 556, "florin": 556, "section": 556, "currency": 556, "quotesingle": 191, "quotedblleft": 333, "guillemotleft": 556, "guilsinglleft": 333, "guilsinglright": 333, "fi": 500, "fl": 500, "endash": 556, "dagger": 556, "daggerdbl": 556, "periodcentered": 278, "paragraph": 537, "bullet": 350, "quotesinglbase": 222, "quotedblbase": 333, "quotedblright": 333, "guillemotright": 556, "ellipsis": 1000, "perthousand": 1000, "questiondown": 611, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 1000, "ordfeminine": 370, "Lslash": 556, "Oslash": 778, "OE": 1000, "ordmasculine": 365, "ae": 889, "dotlessi": 278, "lslash": 222, "oslash": 611, "oe": 944, "germandbls": 611, "Idieresis": 278, "eacute": 556, "abreve": 556, "uhungarumlaut": 556, "ecaron": 556, "Ydieresis": 667, "divide": 584, "Yacute": 667, "Acircumflex": 667, "aacute": 556, "Ucircumflex": 722, "yacute": 500, "scommaaccent": 500, "ecircumflex": 556, "Uring": 722, "Udieresis": 722, "aogonek": 556, "Uacute": 722, "uogonek": 556, "Edieresis": 667, "Dcroat": 722, "commaaccent": 250, "copyright": 737, "Emacron": 667, "ccaron": 500, "aring": 556, "Ncommaaccent": 722, "lacute": 222, "agrave": 556, "Tcommaaccent": 611, "Cacute": 722, "atilde": 556, "Edotaccent": 667, "scaron": 500, "scedilla": 500, "iacute": 278, "lozenge": 471, "Rcaron": 722, "Gcommaaccent": 778, "ucircumflex": 556, "acircumflex": 556, "Amacron": 667, "rcaron": 333, "ccedilla": 500, "Zdotaccent": 611, "Thorn": 667, "Omacron": 778, "Racute": 722, "Sacute": 667, "dcaron": 643, "Umacron": 722, "uring": 556, "threesuperior": 333, "Ograve": 778, "Agrave": 667, "Abreve": 667, "multiply": 584, "uacute": 556, "Tcaron": 611, "partialdiff": 476, "ydieresis": 500, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 667, "adieresis": 556, "edieresis": 556, "cacute": 500, "nacute": 556, "umacron": 556, "Ncaron": 722, "Iacute": 278, "plusminus": 584, "brokenbar": 260, "registered": 737, "Gbreve": 778, "Idotaccent": 278, "summation": 600, "Egrave": 667, "racute": 333, "omacron": 556, "Zacute": 611, "Zcaron": 611, "greaterequal": 549, "Eth": 722, "Ccedilla": 722, "lcommaaccent": 222, "tcaron": 317, "eogonek": 556, "Uogonek": 722, "Aacute": 667, "Adieresis": 667, "egrave": 556, "zacute": 500, "iogonek": 222, "Oacute": 778, "oacute": 556, "amacron": 556, "sacute": 500, "idieresis": 278, "Ocircumflex": 778, "Ugrave": 722, "Delta": 612, "thorn": 556, "twosuperior": 333, "Odieresis": 778, "mu": 556, "igrave": 278, "ohungarumlaut": 556, "Eogonek": 667, "dcroat": 556, "threequarters": 834, "Scedilla": 667, "lcaron": 299, "Kcommaaccent": 667, "Lacute": 556, "trademark": 1000, "edotaccent": 556, "Igrave": 278, "Imacron": 278, "Lcaron": 556, "onehalf": 834, "lessequal": 549, "ocircumflex": 556, "ntilde": 556, "Uhungarumlaut": 722, "Eacute": 667, "emacron": 556, "gbreve": 556, "onequarter": 834, "Scaron": 667, "Scommaaccent": 667, "Ohungarumlaut": 778, "degree": 400, "ograve": 556, "Ccaron": 722, "ugrave": 556, "radical": 453, "Dcaron": 722, "rcommaaccent": 333, "Ntilde": 722, "otilde": 556, "Rcommaaccent": 722, "Lcommaaccent": 556, "Atilde": 667, "Aogonek": 667, "Aring": 667, "Otilde": 778, "zdotaccent": 500, "Ecaron": 667, "Iogonek": 278, "kcommaaccent": 500, "minus": 584, "Icircumflex": 278, "ncaron": 556, "tcommaaccent": 278, "logicalnot": 584, "odieresis": 556, "udieresis": 556, "notequal": 549, "gcommaaccent": 556, "eth": 556, "zcaron": 500, "ncommaaccent": 556, "onesuperior": 333, "imacron": 278, "Euro": 556},
	},
	"Symbol": {
		NewRectangle(-180.0, -293.0, 1090.0, 1010.0),
		map[string]int{"space": 250, "exclam": 333, "universal": 713, "numbersign": 500, "existential": 549, "percent": 833, "ampersand": 778, "suchthat": 439, "parenleft": 333, "parenright": 333, "asteriskmath": 500, "plus": 549, "comma": 250, "minus": 549, "period": 250, "slash": 278, "zero": 500, "one": 500, "two": 500, "three": 500, "four": 500, "five": 500, "six": 500, "seven": 500, "eight": 500, "nine": 500, "colon": 278, "semicolon": 278, "less": 549, "equal": 549, "greater": 549, "question": 444, "congruent": 549, "Alpha": 722, "Beta": 667, "Chi": 722, "Delta": 612, "Epsilon": 611, "Phi": 763, "Gamma": 603, "Eta": 722, "Iota": 333, "theta1": 631, "Kappa": 722, "Lambda": 686, "Mu": 889, "Nu": 722, "Omicron": 722, "Pi": 768, "Theta": 741, "Rho": 556, "Sigma": 592, "Tau": 611, "Upsilon": 690, "sigma1": 439, "Omega": 768, "Xi": 645, "Psi": 795, "Zeta": 611, "bracketleft": 333, "therefore": 863, "bracketright": 333, "perpendicular": 658, "underscore": 500, "radicalex": 500, "alpha": 631, "beta": 549, "chi": 549, "delta": 494, "epsilon": 439, "phi": 521, "gamma": 411, "eta": 603, "iota": 329, "phi1": 603, "kappa": 549, "lambda": 549, "mu": 576, "nu": 521, "omicron": 549, "pi": 549, "theta": 521, "rho": 549, "sigma": 603, "tau": 439, "upsilon": 576, "omega1": 713, "omega": 686, "xi": 493, "psi": 686, "zeta": 494, "braceleft": 480, "bar": 200, "braceright": 480, "similar": 549, "Euro": 750, "Upsilon1": 620, "minute": 247, "lessequal": 549, "fraction": 167, "infinity": 713, "florin": 500, "club": 753, "diamond": 753, "heart": 753, "spade": 753, "arrowboth": 1042, "arrowleft": 987, "arrowup": 603, "arrowright": 987, "arrowdown": 603, "degree": 400, "plusminus": 549, "second": 411, "greaterequal": 549, "multiply": 549, "proportional": 713, "partialdiff": 494, "bullet": 460, "divide": 549, "notequal": 549, "equivalence": 549, "approxequal": 549, "ellipsis": 1000, "arrowvertex": 603, "arrowhorizex": 1000, "carriagereturn": 658, "aleph": 823, "Ifraktur": 686, "Rfraktur": 795, "weierstrass": 987, "circlemultiply": 768, "circleplus": 768, "emptyset": 823, "intersection": 768, "union": 768, "propersuperset": 713, "reflexsuperset": 713, "notsubset": 713, "propersubset": 713, "reflexsubset": 713, "element": 713, "notelement": 713, "angle": 768, "gradient": 713, "registerserif": 790, "copyrightserif": 790, "trademarkserif": 890, "product": 823, "radical": 549, "dotmath": 250, "logicalnot": 713, "logicaland": 603, "logicalor": 603, "arrowdblboth": 1042, "arrowdblleft": 987, "arrowdblup": 603, "arrowdblright": 987, "arrowdbldown": 603, "lozenge": 494, "angleleft": 329, "registersans": 790, "copyrightsans": 790, "trademarksans": 786, "summation": 713, "parenlefttp": 384, "parenleftex": 384, "parenleftbt": 384, "bracketlefttp": 384, "bracketleftex": 384, "bracketleftbt": 384, "bracelefttp": 494, "braceleftmid": 494, "braceleftbt": 494, "braceex": 494, "angleright": 329, "integral": 274, "integraltp": 686, "integralex": 686, "integralbt": 686, "parenrighttp": 384, "parenrightex": 384, "parenrightbt": 384, "bracketrighttp": 384, "bracketrightex": 384, "bracketrightbt": 384, "bracerighttp": 494, "bracerightmid": 494, "bracerightbt": 494, "apple": 790},
	},
	"Times-Bold": {
		NewRectangle(-168.0, -218.0, 1000.0, 935.0),
		map[string]int{"space": 250, "exclam": 333, "quotedbl": 555, "numbersign": 500, "dollar": 500, "percent": 1000, "ampersand": 833, "quoteright": 333, "parenleft": 333, "parenright": 333, "asterisk": 500, "plus": 570, "comma": 250, "hyphen": 333, "period": 250, "slash": 278, "zero": 500, "one": 500, "two": 500, "three": 500, "four": 500, "five": 500, "six": 500, "seven": 500, "eight": 500, "nine": 500, "colon": 333, "semicolon": 333, "less": 570, "equal": 570, "greater": 570, "question": 500, "at": 930, "A": 722, "B": 667, "C": 722, "D": 722, "E": 667, "F": 611, "G": 778, "H": 778, "I": 389, "J": 500, "K": 778, "L": 667, "M": 944, "N": 722, "O": 778, "P": 611, "Q": 778, "R": 722, "S": 556, "T": 667, "U": 722, "V": 722, "W": 1000, "X": 722, "Y": 722, "Z": 667, "bracketleft": 333, "backslash": 278, "bracketright": 333, "asciicircum": 581, "underscore": 500, "quoteleft": 333, "a": 500, "b": 556, "c": 444, "d": 556, "e": 444, "f": 333, "g": 500, "h": 556, "i": 278, "j": 333, "k": 556, "l": 278, "m": 833, "n": 556, "o": 500, "p": 556, "q": 556, "r": 444, "s": 389, "t": 333, "u": 556, "v": 500, "w": 722, "x": 500, "y": 500, "z": 444, "braceleft": 394, "bar": 220, "braceright": 394, "asciitilde": 520, "exclamdown": 333, "cent": 500, "sterling": 500, "fraction": 167, "yen": 500, "florin": 500, "section": 500, "currency": 500, "quotesingle": 278, "quotedblleft": 500, "guillemotleft": 500, "guilsinglleft": 333, "guilsinglright": 333, "fi": 556, "fl": 556, "endash": 500, "dagger": 500, "daggerdbl": 500, "periodcentered": 250, "paragraph": 540, "bullet": 350, "quotesinglbase": 333, "quotedblbase": 500, "quotedblright": 500, "guillemotright": 500, "ellipsis": 1000, "perthousand": 1000, "questiondown": 500, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 1000, "ordfeminine": 300, "Lslash": 667, "Oslash": 778, "OE": 1000, "ordmasculine": 330, "ae": 722, "dotlessi": 278, "lslash": 278, "oslash": 500, "oe": 722, "germandbls": 556, "Idieresis": 389, "eacute": 444, "abreve": 500, "uhungarumlaut": 556, "ecaron": 444, "Ydieresis": 722, "divide": 570, "Yacute": 722, "Acircumflex": 722, "aacute": 500, "Ucircumflex": 722, "yacute": 500, "scommaaccent": 389, "ecircumflex": 444, "Uring": 722, "Udieresis": 722, "aogonek": 500, "Uacute": 722, "uogonek": 556, "Edieresis": 667, "Dcroat": 722, "commaaccent": 250, "copyright": 747, "Emacron": 667, "ccaron": 444, "aring": 500, "Ncommaaccent": 722, "lacute": 278, "agrave": 500, "Tcommaaccent": 667, "Cacute": 722, "atilde": 500, "Edotaccent": 667, "scaron": 389, "scedilla": 389, "iacute": 278, "lozenge": 494, "Rcaron": 722, "Gcommaaccent": 778, "ucircumflex": 556, "acircumflex": 500, "Amacron": 722, "rcaron": 444, "ccedilla": 444, "Zdotaccent": 667, "Thorn": 611, "Omacron": 778, "Racute": 722, "Sacute": 556, "dcaron": 672, "Umacron": 722, "uring": 556, "threesuperior": 300, "Ograve": 778, "Agrave": 722, "Abreve": 722, "multiply": 570, "uacute": 556, "Tcaron": 667, "partialdiff": 494, "ydieresis": 500, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 667, "adieresis": 500, "edieresis": 444, "cacute": 444, "nacute": 556, "umacron": 556, "Ncaron": 722, "Iacute": 389, "plusminus": 570, "brokenbar": 220, "registered": 747, "Gbreve": 778, "Idotaccent": 389, "summation": 600, "Egrave": 667, "racute": 444, "omacron": 500, "Zacute": 667, "Zcaron": 667, "greaterequal": 549, "Eth": 722, "Ccedilla": 722, "lcommaaccent": 278, "tcaron": 416, "eogonek": 444, "Uogonek": 722, "Aacute": 722, "Adieresis": 722, "egrave": 444, "zacute": 444, "iogonek": 278, "Oacute": 778, "oacute": 500, "amacron": 500, "sacute": 389, "idieresis": 278, "Ocircumflex": 778, "Ugrave": 722, "Delta": 612, "thorn": 556, "twosuperior": 300, "Odieresis": 778, "mu": 556, "igrave": 278, "ohungarumlaut": 500, "Eogonek": 667, "dcroat": 556, "threequarters": 750, "Scedilla": 556, "lcaron": 394, "Kcommaaccent": 778, "Lacute": 667, "trademark": 1000, "edotaccent": 444, "Igrave": 389, "Imacron": 389, "Lcaron": 667, "onehalf": 750, "lessequal": 549, "ocircumflex": 500, "ntilde": 556, "Uhungarumlaut": 722, "Eacute": 667, "emacron": 444, "gbreve": 500, "onequarter": 750, "Scaron": 556, "Scommaaccent": 556, "Ohungarumlaut": 778, "degree": 400, "ograve": 500, "Ccaron": 722, "ugrave": 556, "radical": 549, "Dcaron": 722, "rcommaaccent": 444, "Ntilde": 722, "otilde": 500, "Rcommaaccent": 722, "Lcommaaccent": 667, "Atilde": 722, "Aogonek": 722, "Aring": 722, "Otilde": 778, "zdotaccent": 444, "Ecaron": 667, "Iogonek": 389, "kcommaaccent": 556, "minus": 570, "Icircumflex": 389, "ncaron": 556, "tcommaaccent": 333, "logicalnot": 570, "odieresis": 500, "udieresis": 556, "notequal": 549, "gcommaaccent": 500, "eth": 500, "zcaron": 444, "ncommaaccent": 556, "onesuperior": 300, "imacron": 278, "Euro": 500},
	},
	"Times-BoldItalic": {
		NewRectangle(-200.0, -218.0, 996.0, 921.0),
		map[string]int{"space": 250, "exclam": 389, "quotedbl": 555, "numbersign": 500, "dollar": 500, "percent": 833, "ampersand": 778, "quoteright": 333, "parenleft": 333, "parenright": 333, "asterisk": 500, "plus": 570, "comma": 250, "hyphen": 333, "period": 250, "slash": 278, "zero": 500, "one": 500, "two": 500, "three": 500, "four": 500, "five": 500, "six": 500, "seven": 500, "eight": 500, "nine": 500, "colon": 333, "semicolon": 333, "less": 570, "equal": 570, "greater": 570, "question": 500, "at": 832, "A": 667, "B": 667, "C": 667, "D": 722, "E": 667, "F": 667, "G": 722, "H": 778, "I": 389, "J": 500, "K": 667, "L": 611, "M": 889, "N": 722, "O": 722, "P": 611, "Q": 722, "R": 667, "S": 556, "T": 611, "U": 722, "V": 667, "W": 889, "X": 667, "Y": 611, "Z": 611, "bracketleft": 333, "backslash": 278, "bracketright": 333, "asciicircum": 570, "underscore": 500, "quoteleft": 333, "a": 500, "b": 500, "c": 444, "d": 500, "e": 444, "f": 333, "g": 500, "h": 556, "i": 278, "j": 278, "k": 500, "l": 278, "m": 778, "n": 556, "o": 500, "p": 500, "q": 500, "r": 389, "s": 389, "t": 278, "u": 556, "v": 444, "w": 667, "x": 500, "y": 444, "z": 389, "braceleft": 348, "bar": 220, "braceright": 348, "asciitilde": 570, "exclamdown": 389, "cent": 500, "sterling": 500, "fraction": 167, "yen": 500, "florin": 500, "section": 500, "currency": 500, "quotesingle": 278, "quotedblleft": 500, "guillemotleft": 500, "guilsinglleft": 333, "guilsinglright": 333, "fi": 556, "fl": 556, "endash": 500, "dagger": 500, "daggerdbl": 500, "periodcentered": 250, "paragraph": 500, "bullet": 350, "quotesinglbase": 333, "quotedblbase": 500, "quotedblright": 500, "guillemotright": 500, "ellipsis": 1000, "perthousand": 1000, "questiondown": 500, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 944, "ordfeminine": 266, "Lslash": 611, "Oslash": 722, "OE": 944, "ordmasculine": 300, "ae": 722, "dotlessi": 278, "lslash": 278, "oslash": 500, "oe": 722, "germandbls": 500, "Idieresis": 389, "eacute": 444, "abreve": 500, "uhungarumlaut": 556, "ecaron": 444, "Ydieresis": 611, "divide": 570, "Yacute": 611, "Acircumflex": 667, "aacute": 500, "Ucircumflex": 722, "yacute": 444, "scommaaccent": 389, "ecircumflex": 444, "Uring": 722, "Udieresis": 722, "aogonek": 500, "Uacute": 722, "uogonek": 556, "Edieresis": 667, "Dcroat": 722, "commaaccent": 250, "copyright": 747, "Emacron": 667, "ccaron": 444, "aring": 500, "Ncommaaccent": 722, "lacute": 278, "agrave": 500, "Tcommaaccent": 611, "Cacute": 667, "atilde": 500, "Edotaccent": 667, "scaron": 389, "scedilla": 389, "iacute": 278, "lozenge": 494, "Rcaron": 667, "Gcommaaccent": 722, "ucircumflex": 556, "acircumflex": 500, "Amacron": 667, "rcaron": 389, "ccedilla": 444, "Zdotaccent": 611, "Thorn": 611, "Omacron": 722, "Racute": 667, "Sacute": 556, "dcaron": 608, "Umacron": 722, "uring": 556, "threesuperior": 300, "Ograve": 722, "Agrave": 667, "Abreve": 667, "multiply": 570, "uacute": 556, "Tcaron": 611, "partialdiff": 494, "ydieresis": 444, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 667, "adieresis": 500, "edieresis": 444, "cacute": 444, "nacute": 556, "umacron": 556, "Ncaron": 722, "Iacute": 389, "plusminus": 570, "brokenbar": 220, "registered": 747, "Gbreve": 722, "Idotaccent": 389, "summation": 600, "Egrave": 667, "racute": 389, "omacron": 500, "Zacute": 611, "Zcaron": 611, "greaterequal": 549, "Eth": 722, "Ccedilla": 667, "lcommaaccent": 278, "tcaron": 366, "eogonek": 444, "Uogonek": 722, "Aacute": 667, "Adieresis": 667, "egrave": 444, "zacute": 389, "iogonek": 278, "Oacute": 722, "oacute": 500, "amacron": 500, "sacute": 389, "idieresis": 278, "Ocircumflex": 722, "Ugrave": 722, "Delta": 612, "thorn": 500, "twosuperior": 300, "Odieresis": 722, "mu": 576, "igrave": 278, "ohungarumlaut": 500, "Eogonek": 667, "dcroat": 500, "threequarters": 750, "Scedilla": 556, "lcaron": 382, "Kcommaaccent": 667, "Lacute": 611, "trademark": 1000, "edotaccent": 444, "Igrave": 389, "Imacron": 389, "Lcaron": 611, "onehalf": 750, "lessequal": 549, "ocircumflex": 500, "ntilde": 556, "Uhungarumlaut": 722, "Eacute": 667, "emacron": 444, "gbreve": 500, "onequarter": 750, "Scaron": 556, "Scommaaccent": 556, "Ohungarumlaut": 722, "degree": 400, "ograve": 500, "Ccaron": 667, "ugrave": 556, "radical": 549, "Dcaron": 722, "rcommaaccent": 389, "Ntilde": 722, "otilde": 500, "Rcommaaccent": 667, "Lcommaaccent": 611, "Atilde": 667, "Aogonek": 667, "Aring": 667, "Otilde": 722, "zdotaccent": 389, "Ecaron": 667, "Iogonek": 389, "kcommaaccent": 500, "minus": 606, "Icircumflex": 389, "ncaron": 556, "tcommaaccent": 278, "logicalnot": 606, "odieresis": 500, "udieresis": 556, "notequal": 549, "gcommaaccent": 500, "eth": 500, "zcaron": 389, "ncommaaccent": 556, "onesuperior": 300, "imacron": 278, "Euro": 500},
	},
	"Times-Italic": {
		NewRectangle(-169.0, -217.0, 1010.0, 883.0),
		map[string]int{"space": 250, "exclam": 333, "quotedbl": 420, "numbersign": 500, "dollar": 500, "percent": 833, "ampersand": 778, "quoteright": 333, "parenleft": 333, "parenright": 333, "asterisk": 500, "plus": 675, "comma": 250, "hyphen": 333, "period": 250, "slash": 278, "zero": 500, "one": 500, "two": 500, "three": 500, "four": 500, "five": 500, "six": 500, "seven": 500, "eight": 500, "nine": 500, "colon": 333, "semicolon": 333, "less": 675, "equal": 675, "greater": 675, "question": 500, "at": 920, "A": 611, "B": 611, "C": 667, "D": 722, "E": 611, "F": 611, "G": 722, "H": 722, "I": 333, "J": 444, "K": 667, "L": 556, "M": 833, "N": 667, "O": 722, "P": 611, "Q": 722, "R": 611, "S": 500, "T": 556, "U": 722, "V": 611, "W": 833, "X": 611, "Y": 556, "Z": 556, "bracketleft": 389, "backslash": 278, "bracketright": 389, "asciicircum": 422, "underscore": 500, "quoteleft": 333, "a": 500, "b": 500, "c": 444, "d": 500, "e": 444, "f": 278, "g": 500, "h": 500, "i": 278, "j": 278, "k": 444, "l": 278, "m": 722, "n": 500, "o": 500, "p": 500, "q": 500, "r": 389, "s": 389, "t": 278, "u": 500, "v": 444, "w": 667, "x": 444, "y": 444, "z": 389, "braceleft": 400, "bar": 275, "braceright": 400, "asciitilde": 541, "exclamdown": 389, "cent": 500, "sterling": 500, "fraction": 167, "yen": 500, "florin": 500, "section": 500, "currency": 500, "quotesingle": 214, "quotedblleft": 556, "guillemotleft": 500, "guilsinglleft": 333, "guilsinglright": 333, "fi": 500, "fl": 500, "endash": 500, "dagger": 500, "daggerdbl": 500, "periodcentered": 250, "paragraph": 523, "bullet": 350, "quotesinglbase": 333, "quotedblbase": 556, "quotedblright": 556, "guillemotright": 500, "ellipsis": 889, "perthousand": 1000, "questiondown": 500, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 889, "AE": 889, "ordfeminine": 276, "Lslash": 556, "Oslash": 722, "OE": 944, "ordmasculine": 310, "ae": 667, "dotlessi": 278, "lslash": 278, "oslash": 500, "oe": 667, "germandbls": 500, "Idieresis": 333, "eacute": 444, "abreve": 500, "uhungarumlaut": 500, "ecaron": 444, "Ydieresis": 556, "divide": 675, "Yacute": 556, "Acircumflex": 611, "aacute": 500, "Ucircumflex": 722, "yacute": 444, "scommaaccent": 389, "ecircumflex": 444, "Uring": 722, "Udieresis": 722, "aogonek": 500, "Uacute": 722, "uogonek": 500, "Edieresis": 611, "Dcroat": 722, "commaaccent": 250, "copyright": 760, "Emacron": 611, "ccaron": 444, "aring": 500, "Ncommaaccent": 667, "lacute": 278, "agrave": 500, "Tcommaaccent": 556, "Cacute": 667, "atilde": 500, "Edotaccent": 611, "scaron": 389, "scedilla": 389, "iacute": 278, "lozenge": 471, "Rcaron": 611, "Gcommaaccent": 722, "ucircumflex": 500, "acircumflex": 500, "Amacron": 611, "rcaron": 389, "ccedilla": 444, "Zdotaccent": 556, "Thorn": 611, "Omacron": 722, "Racute": 611, "Sacute": 500, "dcaron": 544, "Umacron": 722, "uring": 500, "threesuperior": 300, "Ograve": 722, "Agrave": 611, "Abreve": 611, "multiply": 675, "uacute": 500, "Tcaron": 556, "partialdiff": 476, "ydieresis": 444, "Nacute": 667, "icircumflex": 278, "Ecircumflex": 611, "adieresis": 500, "edieresis": 444, "cacute": 444, "nacute": 500, "umacron": 500, "Ncaron": 667, "Iacute": 333, "plusminus": 675, "brokenbar": 275, "registered": 760, "Gbreve": 722, "Idotaccent": 333, "summation": 600, "Egrave": 611, "racute": 389, "omacron": 500, "Zacute": 556, "Zcaron": 556, "greaterequal": 549, "Eth": 722, "Ccedilla": 667, "lcommaaccent": 278, "tcaron": 300, "eogonek": 444, "Uogonek": 722, "Aacute": 611, "Adieresis": 611, "egrave": 444, "zacute": 389, "iogonek": 278, "Oacute": 722, "oacute": 500, "amacron": 500, "sacute": 389, "idieresis": 278, "Ocircumflex": 722, "Ugrave": 722, "Delta": 612, "thorn": 500, "twosuperior": 300, "Odieresis": 722, "mu": 500, "igrave": 278, "ohungarumlaut": 500, "Eogonek": 611, "dcroat": 500, "threequarters": 750, "Scedilla": 500, "lcaron": 300, "Kcommaaccent": 667, "Lacute": 556, "trademark": 980, "edotaccent": 444, "Igrave": 333, "Imacron": 333, "Lcaron": 611, "onehalf": 750, "lessequal": 549, "ocircumflex": 500, "ntilde": 500, "Uhungarumlaut": 722, "Eacute": 611, "emacron": 444, "gbreve": 500, "onequarter": 750, "Scaron": 500, "Scommaaccent": 500, "Ohungarumlaut": 722, "degree": 400, "ograve": 500, "Ccaron": 667, "ugrave": 500, "radical": 453, "Dcaron": 722, "rcommaaccent": 389, "Ntilde": 667, "otilde": 500, "Rcommaaccent": 611, "Lcommaaccent": 556, "Atilde": 611, "Aogonek": 611, "Aring": 611, "Otilde": 722, "zdotaccent": 389, "Ecaron": 611, "Iogonek": 333, "kcommaaccent": 444, "minus": 675, "Icircumflex": 333, "ncaron": 500, "tcommaaccent": 278, "logicalnot": 675, "odieresis": 500, "udieresis": 500, "notequal": 549, "gcommaaccent": 500, "eth": 500, "zcaron": 389, "ncommaaccent": 500, "onesuperior": 300, "imacron": 278, "Euro": 500},
	},
	"Times-Roman": {
		NewRectangle(-168.0, -218.0, 1000.0, 898.0),
		map[string]int{"space": 250, "exclam": 333, "quotedbl": 408, "numbersign": 500, "dollar": 500, "percent": 833, "ampersand": 778, "quoteright": 333, "parenleft": 333, "parenright": 333, "asterisk": 500, "plus": 564, "comma": 250, "hyphen": 333, "period": 250, "slash": 278, "zero": 500, "one": 500, "two": 500, "three": 500, "four": 500, "five": 500, "six": 500, "seven": 500, "eight": 500, "nine": 500, "colon": 278, "semicolon": 278, "less": 564, "equal": 564, "greater": 564, "question": 444, "at": 921, "A": 722, "B": 667, "C": 667, "D": 722, "E": 611, "F": 556, "G": 722, "H": 722, "I": 333, "J": 389, "K": 722, "L": 611, "M": 889, "N": 722, "O": 722, "P": 556, "Q": 722, "R": 667, "S": 556, "T": 611, "U": 722, "V": 722, "W": 944, "X": 722, "Y": 722, "Z": 611, "bracketleft": 333, "backslash": 278, "bracketright": 333, "asciicircum": 469, "underscore": 500, "quoteleft": 333, "a": 444, "b": 500, "c": 444, "d": 500, "e": 444, "f": 333, "g": 500, "h": 500, "i": 278, "j": 278, "k": 500, "l": 278, "m": 778, "n": 500, "o": 500, "p": 500, "q": 500, "r": 333, "s": 389, "t": 278, "u": 500, "v": 500, "w": 722, "x": 500, "y": 500, "z": 444, "braceleft": 480, "bar": 200, "braceright": 480, "asciitilde": 541, "exclamdown": 333, "cent": 500, "sterling": 500, "fraction": 167, "yen": 500, "florin": 500, "section": 500, "currency": 500, "quotesingle": 180, "quotedblleft": 444, "guillemotleft": 500, "guilsinglleft": 333, "guilsinglright": 333, "fi": 556, "fl": 556, "endash": 500, "dagger": 500, "daggerdbl": 500, "periodcentered": 250, "paragraph": 453, "bullet": 350, "quotesinglbase": 333, "quotedblbase": 444, "quotedblright": 444, "guillemotright": 500, "ellipsis": 1000, "perthousand": 1000, "questiondown": 444, "grave": 333, "acute": 333, "circumflex": 333, "tilde": 333, "macron": 333, "breve": 333, "dotaccent": 333, "dieresis": 333, "ring": 333, "cedilla": 333, "hungarumlaut": 333, "ogonek": 333, "caron": 333, "emdash": 1000, "AE": 889, "ordfeminine": 276, "Lslash": 611, "Oslash": 722, "OE": 889, "ordmasculine": 310, "ae": 667, "dotlessi": 278, "lslash": 278, "oslash": 500, "oe": 722, "germandbls": 500, "Idieresis": 333, "eacute": 444, "abreve": 444, "uhungarumlaut": 500, "ecaron": 444, "Ydieresis": 722, "divide": 564, "Yacute": 722, "Acircumflex": 722, "aacute": 444, "Ucircumflex": 722, "yacute": 500, "scommaaccent": 389, "ecircumflex": 444, "Uring": 722, "Udieresis": 722, "aogonek": 444, "Uacute": 722, "uogonek": 500, "Edieresis": 611, "Dcroat": 722, "commaaccent": 250, "copyright": 760, "Emacron": 611, "ccaron": 444, "aring": 444, "Ncommaaccent": 722, "lacute": 278, "agrave": 444, "Tcommaaccent": 611, "Cacute": 667, "atilde": 444, "Edotaccent": 611, "scaron": 389, "scedilla": 389, "iacute": 278, "lozenge": 471, "Rcaron": 667, "Gcommaaccent": 722, "ucircumflex": 500, "acircumflex": 444, "Amacron": 722, "rcaron": 333, "ccedilla": 444, "Zdotaccent": 611, "Thorn": 556, "Omacron": 722, "Racute": 667, "Sacute": 556, "dcaron": 588, "Umacron": 722, "uring": 500, "threesuperior": 300, "Ograve": 722, "Agrave": 722, "Abreve": 722, "multiply": 564, "uacute": 500, "Tcaron": 611, "partialdiff": 476, "ydieresis": 500, "Nacute": 722, "icircumflex": 278, "Ecircumflex": 611, "adieresis": 444, "edieresis": 444, "cacute": 444, "nacute": 500, "umacron": 500, "Ncaron": 722, "Iacute": 333, "plusminus": 564, "brokenbar": 200, "registered": 760, "Gbreve": 722, "Idotaccent": 333, "summation": 600, "Egrave": 611, "racute": 333, "omacron": 500, "Zacute": 611, "Zcaron": 611, "greaterequal": 549, "Eth": 722, "Ccedilla": 667, "lcommaaccent": 278, "tcaron": 326, "eogonek": 444, "Uogonek": 722, "Aacute": 722, "Adieresis": 722, "egrave": 444, "zacute": 444, "iogonek": 278, "Oacute": 722, "oacute": 500, "amacron": 444, "sacute": 389, "idieresis": 278, "Ocircumflex": 722, "Ugrave": 722, "Delta": 612, "thorn": 500, "twosuperior": 300, "Odieresis": 722, "mu": 500, "igrave": 278, "ohungarumlaut": 500, "Eogonek": 611, "dcroat": 500, "threequarters": 750, "Scedilla": 556, "lcaron": 344, "Kcommaaccent": 722, "Lacute": 611, "trademark": 980, "edotaccent": 444, "Igrave": 333, "Imacron": 333, "Lcaron": 611, "onehalf": 750, "lessequal": 549, "ocircumflex": 500, "ntilde": 500, "Uhungarumlaut": 722, "Eacute": 611, "emacron": 444, "gbreve": 500, "onequarter": 750, "Scaron": 556, "Scommaaccent": 556, "Ohungarumlaut": 722, "degree": 400, "ograve": 500, "Ccaron": 667, "ugrave": 500, "radical": 453, "Dcaron": 722, "rcommaaccent": 333, "Ntilde": 722, "otilde": 500, "Rcommaaccent": 667, "Lcommaaccent": 611, "Atilde": 722, "Aogonek": 722, "Aring": 722, "Otilde": 722, "zdotaccent": 444, "Ecaron": 611, "Iogonek": 333, "kcommaaccent": 500, "minus": 564, "Icircumflex": 333, "ncaron": 500, "tcommaaccent": 278, "logicalnot": 564, "odieresis": 500, "udieresis": 500, "notequal": 549, "gcommaaccent": 500, "eth": 500, "zcaron": 444, "ncommaaccent": 500, "onesuperior": 300, "imacron": 278, "Euro": 500},
	},
	"ZapfDingbats": {
		NewRectangle(-1.0, -143.0, 981.0, 820.0),
		map[string]int{"space": 278, "a1": 974, "a2": 961, "a202": 974, "a3": 980, "a4": 719, "a5": 789, "a119": 790, "a118": 791, "a117": 690, "a11": 960, "a12": 939, "a13": 549, "a14": 855, "a15": 911, "a16": 933, "a105": 911, "a17": 945, "a18": 974, "a19": 755, "a20": 846, "a21": 762, "a22": 761, "a23": 571, "a24": 677, "a25": 763, "a26": 760, "a27": 759, "a28": 754, "a6": 494, "a7": 552, "a8": 537, "a9": 577, "a10": 692, "a29": 786, "a30": 788, "a31": 788, "a32": 790, "a33": 793, "a34": 794, "a35": 816, "a36": 823, "a37": 789, "a38": 841, "a39": 823, "a40": 833, "a41": 816, "a42": 831, "a43": 923, "a44": 744, "a45": 723, "a46": 749, "a47": 790, "a48": 792, "a49": 695, "a50": 776, "a51": 768, "a52": 792, "a53": 759, "a54": 707, "a55": 708, "a56": 682, "a57": 701, "a58": 826, "a59": 815, "a60": 789, "a61": 789, "a62": 707, "a63": 687, "a64": 696, "a65": 689, "a66": 786, "a67": 787, "a68": 713, "a69": 791, "a70": 785, "a71": 791, "a72": 873, "a73": 761, "a74": 762, "a203": 762, "a75": 759, "a204": 759, "a76": 892, "a77": 892, "a78": 788, "a79": 784, "a81": 438, "a82": 138, "a83": 277, "a84": 415, "a97": 392, "a98": 392, "a99": 668, "a100": 668, "a89": 390, "a90": 390, "a93": 317, "a94": 317, "a91": 276, "a92": 276, "a205": 509, "a85": 509, "a206": 410, "a86": 410, "a87": 234, "a88": 234, "a95": 334, "a96": 334, "a101": 732, "a102": 544, "a103": 544, "a104": 910, "a106": 667, "a107": 760, "a108": 760, "a112": 776, "a111": 595, "a110": 694, "a109": 626, "a120": 788, "a121": 788, "a122": 788, "a123": 788, "a124": 788, "a125": 788, "a126": 788, "a127": 788, "a128": 788, "a129": 788, "a130": 788, "a131": 788, "a132": 788, "a133": 788, "a134": 788, "a135": 788, "a136": 788, "a137": 788, "a138": 788, "a139": 788, "a140": 788, "a141": 788, "a142": 788, "a143": 788, "a144": 788, "a145": 788, "a146": 788, "a147": 788, "a148": 788, "a149": 788, "a150": 788, "a151": 788, "a152": 788, "a153": 788, "a154": 788, "a155": 788, "a156": 788, "a157": 788, "a158": 788, "a159": 788, "a160": 894, "a161": 838, "a163": 1016, "a164": 458, "a196": 748, "a165": 924, "a192": 748, "a166": 918, "a167": 927, "a168": 928, "a169": 928, "a170": 834, "a171": 873, "a172": 828, "a173": 924, "a162": 924, "a174": 917, "a175": 930, "a176": 931, "a177": 463, "a178": 883, "a179": 836, "a193": 836, "a180": 867, "a199": 867, "a181": 696, "a200": 696, "a182": 874, "a201": 874, "a183": 760, "a184": 946, "a197": 771, "a185": 865, "a194": 771, "a198": 888, "a186": 967, "a195": 888, "a187": 831, "a188": 873, "a189": 927, "a190": 970, "a191": 918},
	},
}

// IsCoreFont returns true for the 14 PDF standard Type 1 	fonts.
func IsCoreFont(fontName string) bool {
	_, ok := CoreFontMetrics[fontName]
	return ok
}

// EnsureFontDict ensures a font dict for fontName, lang, script.
func EnsureFontDict(xRefTable *XRefTable, fontName, lang, script string, field bool, indRef *IndirectRef) (*IndirectRef, error) {
	if IsCoreFont(fontName) {
		if indRef != nil {
			return indRef, nil
		}
		return coreFontDict(xRefTable, fontName)
	}
	if field && (script == "" || !CJK(script, lang)) {
		return trueTypeFontDict(xRefTable, fontName, lang)
	}
	return type0FontDict(xRefTable, fontName, lang, script, indRef)
}

// FontMap maps font names to font resources.
type FontMap map[string]FontResource

// FontResources returns a font resource dict for a font map.
func FontResources(xRefTable *XRefTable, fm FontMap) (Dict, error) {
	d := Dict{}

	for fontName, font := range fm {
		ir, err := EnsureFontDict(xRefTable, fontName, "", "", false, nil)
		if err != nil {
			return nil, err
		}
		d.Insert(font.Res.ID, *ir)
	}

	return d, nil
}

// Name evaluates the font name for a given font dict.
func Name(xRefTable *XRefTable, fontDict Dict, objNumber int) (prefix, fontName string, err error) {
	var found bool
	var o Object

	if *fontDict.Subtype() != "Type3" {

		o, found = fontDict.Find("BaseFont")
		if !found {
			o, found = fontDict.Find("Name")
			if !found {
				return "", "", errors.New("pdfcpu: fontName: missing fontDict entries \"BaseFont\" and \"Name\"")
			}
		}

	} else {

		// Type3 fonts only have Name in V1.0 else use generic name.

		o, found = fontDict.Find("Name")
		if !found {
			return "", fmt.Sprintf("Type3_%d", objNumber), nil
		}

	}

	o, err = xRefTable.Dereference(o)
	if err != nil {
		return "", "", err
	}

	baseFont, ok := o.(NameType)
	if !ok {
		return "", "", errors.New("pdfcpu: fontName: corrupt fontDict entry BaseFont")
	}

	n := string(baseFont)

	// Isolate Postscript prefix.
	var p string

	i := strings.Index(n, "+")

	if i > 0 {
		p = n[:i]
		n = n[i+1:]
	}

	return p, n, nil
}

// Lang detects the optional language indicator in a font dict.
func Lang(xRefTable *XRefTable, fontDict Dict) (string, error) {
	o, found := fontDict.Find("FontDescriptor")
	if found {
		fd, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return "", err
		}
		var s string
		n := fd.NameEntry("Lang")
		if n != nil {
			s = *n
		}
		return s, nil
	}

	o, found = fontDict.Find("DescendantFonts")
	if !found {
		return "", ErrCorruptFontDict
	}

	arr, err := xRefTable.DereferenceArray(o)
	if err != nil {
		return "", err
	}

	if len(arr) != 1 {
		return "", ErrCorruptFontDict
	}

	d1, err := xRefTable.DereferenceDict(arr[0])
	if err != nil {
		return "", err
	}
	o, found = d1.Find("FontDescriptor")
	if found {
		fd, err := xRefTable.DereferenceDict(o)
		if err != nil {
			return "", err
		}
		var s string
		n := fd.NameEntry("Lang")
		if n != nil {
			s = *n
		}
		return s, nil
	}

	return "", nil
}

func trivialFontDescriptor(xRefTable *XRefTable, fontDict Dict, objNr int) (Dict, error) {
	o, ok := fontDict.Find("FontDescriptor")
	if !ok {
		return nil, nil
	}

	// fontDescriptor directly available.

	d, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return nil, err
	}

	if d == nil {
		return nil, errors.Errorf("pdfcpu: trivialFontDescriptor: FontDescriptor is null for font object %d\n", objNr)
	}

	if d.Type() != nil && *d.Type() != "FontDescriptor" {
		return nil, errors.Errorf("pdfcpu: trivialFontDescriptor: FontDescriptor dict incorrect dict type for font object %d\n", objNr)
	}

	return d, nil
}

// FontDescriptor gets the font descriptor for this
func FontDescriptor(xRefTable *XRefTable, fontDict Dict, objNr int) (Dict, error) {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("fontDescriptor begin")
	// }

	d, err := trivialFontDescriptor(xRefTable, fontDict, objNr)
	if err != nil {
		return nil, err
	}
	if d != nil {
		return d, nil
	}

	// Try to access a fontDescriptor in a Descendent font for Type0 fonts.

	o, ok := fontDict.Find("DescendantFonts")
	if !ok {
		// logErrorOptimize.Printf("FontDescriptor: Neither FontDescriptor nor DescendantFonts for font object %d\n", objectNumber)
		return nil, nil
	}

	// A descendant font is contained in an array of size 1.

	a, err := xRefTable.DereferenceArray(o)
	if err != nil || a == nil {
		return nil, errors.Errorf("pdfcpu: fontDescriptor: DescendantFonts: IndirectRef or Array with length 1 expected for font object %d\n", objNr)
	}
	if len(a) != 1 {
		return nil, errors.Errorf("pdfcpu: fontDescriptor: DescendantFonts Array length <> 1 %v\n", a)
	}

	// dict is the fontDict of the descendant
	d, err = xRefTable.DereferenceDict(a[0])
	if err != nil {
		return nil, errors.Errorf("pdfcpu: fontDescriptor: No descendant font dict for %v\n", a)
	}
	if d == nil {
		return nil, errors.Errorf("pdfcpu: fontDescriptor: descendant font dict is null for %v\n", a)
	}

	if *d.Type() != "Font" {
		return nil, errors.Errorf("pdfcpu: fontDescriptor: font dict with incorrect dict type for %v\n", d)
	}

	o, ok = d.Find("FontDescriptor")
	if !ok {
		// log.Optimize.Printf("fontDescriptor: descendant font not embedded %s\n", d)
		return nil, nil
	}

	d, err = xRefTable.DereferenceDict(o)
	if err != nil {
		return nil, errors.Errorf("pdfcpu: fontDescriptor: No FontDescriptor dict for font object %d\n", objNr)
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("fontDescriptor end")
	// }

	return d, nil
}

func Embedded(xRefTable *XRefTable, fontDict Dict, objNr int) (bool, error) {
	fd, err := FontDescriptor(xRefTable, fontDict, objNr)
	if err != nil {
		return false, err
	}
	if _, ok := fd.Find("FontFile"); ok {
		return true, nil
	}
	if _, ok := fd.Find("FontFile2"); ok {
		return true, nil
	}
	if _, ok := fd.Find("FontFile3"); ok {
		return true, nil
	}
	return false, nil
}

// Get rid of redundant fonts for given fontResources dictionary.
func optimizeFontResourcesDict(ctx *Context, rDict Dict, pageNr int, rNamePrefix string) error {
	pageFonts := pageFonts(ctx, pageNr)

	// Iterate over font resource dict.
	for rName, v := range rDict {

		indRef, ok := v.(IndirectRef)
		if !ok {
			continue
		}

		objNr := int(indRef.ObjectNumber)

		qualifiedRName := rName
		if rNamePrefix != "" {
			qualifiedRName = rNamePrefix + "." + rName
		}

		if _, found := ctx.Optimize.FontObjects[objNr]; found {
			// This font has already been registered.
			// log.Optimize.Printf("optimizeFontResourcesDict: Fontobject %d already registered\n", objectNumber)
			pageFonts[objNr] = true
			continue
		}

		// We are dealing with a new
		fontDict, err := ctx.DereferenceFontDict(indRef)
		if err != nil {
			return err
		}
		if fontDict == nil {
			continue
		}

		// Get the unique font name.
		prefix, fName, err := Name(ctx.XRefTable, fontDict, objNr)
		if err != nil {
			return err
		}

		// Check if fontDict is a duplicate and if so return the object number of the original.
		originalObjNr, err := handleDuplicateFontObject(ctx, fontDict, fName, qualifiedRName, objNr, pageNr)
		if err != nil {
			return err
		}

		if originalObjNr != nil {
			// We have identified a redundant fontDict!
			// Update font resource dict so that rName points to the original.
			ir := NewIndirectRef(*originalObjNr, 0)
			rDict[rName] = *ir
			ctx.IncrementRefCount(ir)
			// if log.OptimizeEnabled() {
			// 	log.Optimize.Printf("optimizeFontResourcesDict: redundant fontDict prefix=%s name=%s (objNr#%d -> objNr#%d)\n", prefix, fName, objNr, originalObjNr)
			// }
			continue
		}

		registerFontDictObjNr(ctx, fName, objNr)

		fontObj := FontObject{
			ResourceNames: []string{qualifiedRName},
			Prefix:        prefix,
			FontName:      fName,
			FontDict:      fontDict,
		}

		// if log.StatsEnabled() || ctx.Cmd == LISTINFO || ctx.Cmd == EXTRACTFONTS {
		// 	fontObj.Embedded, err = pdfEmbedded(ctx.XRefTable, fontDict, objNr)
		// 	if err != nil {
		// 		return err
		// 	}
		// }

		ctx.Optimize.FontObjects[objNr] = &fontObj

		pageFonts[objNr] = true
	}

	return nil
}

// handleDuplicateImageObject returns nil or the object number of the registered image if it matches this image.
func handleDuplicateImageObject(ctx *Context, imageDict *StreamDict, resourceName string, objNr, pageNr int) (*int, bool, error) {
	// Get the set of image object numbers for pageNr.
	pageImages := ctx.Optimize.PageImages[pageNr]

	if duplImgObj, ok := ctx.Optimize.DuplicateImages[objNr]; ok {

		newObjNr := duplImgObj.NewObjNr
		// We have detected a redundant image dict.
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("handleDuplicateImageObject: redundant imageObj#:%d already registered with obj#:%d !\n", objNr, newObjNr)
		// }

		// Register new page image for pageNr.
		// The image for image object number is used instead of objNr.
		pageImages[newObjNr] = true

		// Add the resource name of this duplicate image to the list of registered resource names.
		ctx.Optimize.ImageObjects[newObjNr].AddResourceName(pageNr, resourceName)

		// Return the imageObjectNumber that will be used instead of objNr.
		return &newObjNr, false, nil
	}

	// Process image dict, check if this is a duplicate.
	for imageObjNr, imageObject := range ctx.Optimize.ImageObjects {

		if imageObjNr == objNr {
			// Add the resource name of this duplicate image to the list of registered resource names.
			imageObject.AddResourceName(pageNr, resourceName)
			return nil, true, nil
		}

		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("handleDuplicateImageObject: comparing with imagedict Obj %d\n", imageObjNr)
		// }

		// Check if the input imageDict matches the imageDict of this imageObject.
		ok, err := EqualStreamDicts(imageObject.ImageDict, imageDict, ctx.XRefTable)
		if err != nil {
			return nil, false, err
		}

		if !ok {
			// No match!
			continue
		}

		// We have detected a redundant image dict.
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("handleDuplicateImageObject: redundant imageObj#:%d already registered with obj#:%d !\n", objNr, imageObjNr)
		// }

		// Register new page image for pageNr.
		// The image for image object number is used instead of objNr.
		pageImages[imageObjNr] = true

		// Add the resource name of this duplicate image to the list of registered resource names.
		imageObject.AddResourceName(pageNr, resourceName)

		// Register imageDict as duplicate.
		ctx.Optimize.DuplicateImages[objNr] = &DuplicateImageObject{ImageDict: imageDict, NewObjNr: imageObjNr}

		// Return the imageObjectNumber that will be used instead of objNr.
		return &imageObjNr, false, nil
	}

	return nil, false, nil
}

func optimizeXObjectImage(ctx *Context, osd *StreamDict, rNamePrefix, rName string, rDict Dict, objNr, pageNr, pageObjNumber int, pageImages IntSet) error {
	qualifiedRName := rName
	if rNamePrefix != "" {
		qualifiedRName = rNamePrefix + "." + rName
	}

	// Check if image is a duplicate and if so return the object number of the original.
	originalObjNr, alreadyDupl, err := handleDuplicateImageObject(ctx, osd, qualifiedRName, objNr, pageNr)
	if err != nil {
		return err
	}

	if originalObjNr != nil {
		// We have identified a redundant image!
		// Update xobject resource dict so that rName points to the original.
		ir := NewIndirectRef(*originalObjNr, 0)
		ctx.IncrementRefCount(ir)
		rDict[rName] = *ir
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("optimizeXObjectImage: redundant xobject name=%s (objNr#%d -> objNr#%d)\n", qualifiedRName, objNr, originalObjNr)
		// }
		return nil
	}

	if !alreadyDupl {
		// Register new image dict.
		ctx.Optimize.ImageObjects[objNr] = &ImageObject{
			ResourceNames: map[int]string{pageNr: qualifiedRName},
			ImageDict:     osd,
		}
	}

	pageImages[objNr] = true
	return nil
}

func optimizeXObjectForm(ctx *Context, sd *StreamDict, objNr int) (*IndirectRef, error) {
	f := ctx.Optimize.FormStreamCache
	if len(f) == 0 {
		f[objNr] = sd
		return nil, nil
	}

	if f[objNr] != nil {
		return nil, nil
	}

	cachedObjNrs := []int{}
	for objNr, sd1 := range f {
		if *sd1.StreamLength == *sd.StreamLength {
			cachedObjNrs = append(cachedObjNrs, objNr)
		}
	}
	if len(cachedObjNrs) == 0 {
		f[objNr] = sd
		return nil, nil
	}

	for _, objNr1 := range cachedObjNrs {
		sd1 := f[objNr1]
		ok, err := EqualStreamDicts(sd, sd1, ctx.XRefTable)
		if err != nil {
			return nil, err
		}
		if ok {
			ir := NewIndirectRef(objNr1, 0)
			ctx.IncrementRefCount(ir)
			return ir, nil
		}
	}

	f[objNr] = sd
	return nil, nil
}

func optimizeFormResources(ctx *Context, o Object, pageNr, pageObjNumber int, rName string, visitedRes []Object) error {
	d, err := ctx.DereferenceDict(o)
	if err != nil {
		return err
	}
	if d != nil {
		// Optimize image and font resources.
		if err = optimizeResources(ctx, d, pageNr, pageObjNumber, rName, visitedRes); err != nil {
			return err
		}
	}
	return nil
}

func visited(o Object, visited []Object) bool {
	for _, obj := range visited {
		if obj == o {
			return true
		}
	}
	return false
}

func optimizeForm(ctx *Context, osd *StreamDict, rNamePrefix, rName string, rDict Dict, objNr, pageNr, pageObjNumber int, vis []Object) error {
	ir, err := optimizeXObjectForm(ctx, osd, objNr)
	if err != nil {
		return err
	}

	if ir != nil {
		rDict[rName] = *ir
		return nil
	}

	o, found := osd.Find("Resources")
	if !found {
		return nil
	}

	indRef, ok := o.(IndirectRef)
	if ok {
		if visited(indRef, vis) {
			return nil
		}
		vis = append(vis, indRef)
	}

	qualifiedRName := rName
	if rNamePrefix != "" {
		qualifiedRName = rNamePrefix + "." + rName
	}

	return optimizeFormResources(ctx, o, pageNr, pageObjNumber, qualifiedRName, vis)
}

func optimizeExtGStateResources(ctx *Context, rDict Dict, pageNr, pageObjNumber int, rNamePrefix string, vis []Object) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("optimizeExtGStateResources page#%dbegin: %s\n", pageObjNumber, rDict)
	// }

	pageImages := pageImages(ctx, pageNr)

	s, found := rDict.Find("SMask")
	if found {
		dict, ok := s.(Dict)
		if ok {
			if err := optimizeSMaskResources(dict, vis, rNamePrefix, ctx, rDict, pageNr, pageImages, pageObjNumber); err != nil {
				return err
			}
		}
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("optimizeExtGStateResources end")
	// }

	return nil
}

func optimizeSMaskResources(dict Dict, vis []Object, rNamePrefix string, ctx *Context, rDict Dict, pageNr int, pageImages IntSet, pageObjNumber int) error {
	indRef := dict.IndirectRefEntry("G")
	if indRef == nil {
		return nil
	}

	if visited(*indRef, vis) {
		return nil
	}

	vis = append(vis, indRef)

	objNr := int(indRef.ObjectNumber)

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("optimizeSMaskResources: processing \"G\", obj#=%d\n", objNr)
	// }

	sd, err := ctx.DereferenceXObjectDict(*indRef)
	if err != nil {
		return err
	}
	if sd == nil {
		return nil
	}

	if *sd.Subtype() == "Image" {
		if err := optimizeXObjectImage(ctx, sd, rNamePrefix, "G", rDict, objNr, pageNr, pageObjNumber, pageImages); err != nil {
			return err
		}
	}

	if *sd.Subtype() == "Form" {
		if err := optimizeForm(ctx, sd, rNamePrefix, "G", rDict, objNr, pageNr, pageObjNumber, vis); err != nil {
			return err
		}
	}

	return nil
}

func optimizeExtGStateResourcesDict(ctx *Context, rDict Dict, pageNr, pageObjNumber int, rNamePrefix string, vis []Object) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("optimizeExtGStateResourcesDict page#%dbegin: %s\n", pageObjNumber, rDict)
	// }

	for rName, v := range rDict {

		indRef, ok := v.(IndirectRef)
		if !ok {
			continue
		}

		if visited(indRef, vis) {
			continue
		}

		vis = append(vis, indRef)

		qualifiedRName := rName
		if rNamePrefix != "" {
			qualifiedRName = rNamePrefix + "." + rName
		}

		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("optimizeExtGStateResourcesDict: processing XObject: %s, obj#=%d\n", qualifiedRName, objNr)
		// }

		rDict, err := ctx.DereferenceDict(indRef)
		if err != nil {
			continue
		}
		if rDict == nil {
			continue
		}

		if err := optimizeExtGStateResources(ctx, rDict, pageNr, pageObjNumber, qualifiedRName, vis); err != nil {
			return err
		}

	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("optimizeXObjectResourcesDict end")
	// }

	return nil
}

func optimizeXObjectResourcesDict(ctx *Context, rDict Dict, pageNr, pageObjNumber int, rNamePrefix string, vis []Object) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("optimizeXObjectResourcesDict page#%dbegin: %s\n", pageObjNumber, rDict)
	// }

	pageImages := pageImages(ctx, pageNr)

	for rName, v := range rDict {

		indRef, ok := v.(IndirectRef)
		if !ok {
			continue
		}

		if visited(indRef, vis) {
			continue
		}

		vis = append(vis, indRef)

		objNr := int(indRef.ObjectNumber)

		// qualifiedRName := rName
		// if rNamePrefix != "" {
		// 	qualifiedRName = rNamePrefix + "." + rName
		// }

		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("optimizeXObjectResourcesDict: processing XObject: %s, obj#=%d\n", qualifiedRName, objNr)
		// }

		sd, err := ctx.DereferenceXObjectDict(indRef)
		if err != nil {
			return err
		}
		if sd == nil {
			continue
		}

		if *sd.Subtype() == "Image" {
			if err := optimizeXObjectImage(ctx, sd, rNamePrefix, rName, rDict, objNr, pageNr, pageObjNumber, pageImages); err != nil {
				return err
			}
		}

		if *sd.Subtype() == "Form" {
			// Get rid of PieceInfo dict from form XObjects.
			if err := ctx.DeleteDictEntry(sd.Dict, "PieceInfo"); err != nil {
				return err
			}
			if err := optimizeForm(ctx, sd, rNamePrefix, rName, rDict, objNr, pageNr, pageObjNumber, vis); err != nil {
				return err
			}
		}

	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("optimizeXObjectResourcesDict end")
	// }

	return nil
}

func processFontResources(ctx *Context, obj Object, pageNr, pageObjNumber int, rNamePrefix string) error {
	d, err := ctx.DereferenceDict(obj)
	if err != nil {
		return err
	}

	if d == nil {
		return errors.Errorf("pdfcpu: processFontResources: font resource dict is null for page %d pageObj %d\n", pageNr, pageObjNumber)
	}

	return optimizeFontResourcesDict(ctx, d, pageNr, rNamePrefix)
}

func processXObjectResources(ctx *Context, obj Object, pageNr, pageObjNumber int, rNamePrefix string, visitedRes []Object) error {
	d, err := ctx.DereferenceDict(obj)
	if err != nil {
		return err
	}

	if d == nil {
		return errors.Errorf("pdfcpu: processXObjectResources: xObject resource dict is null for page %d pageObj %d\n", pageNr, pageObjNumber)
	}

	return optimizeXObjectResourcesDict(ctx, d, pageNr, pageObjNumber, rNamePrefix, visitedRes)
}

func processExtGStateResources(ctx *Context, obj Object, pageNr, pageObjNumber int, rNamePrefix string, visitedRes []Object) error {
	d, err := ctx.DereferenceDict(obj)
	if err != nil {
		return err
	}

	if d == nil {
		return errors.Errorf("pdfcpu: processExtGStateResources: extGState resource dict is null for page %d pageObj %d\n", pageNr, pageObjNumber)
	}

	return optimizeExtGStateResourcesDict(ctx, d, pageNr, pageObjNumber, rNamePrefix, visitedRes)
}

// Optimize given resource dictionary by removing redundant fonts and images.
func optimizeResources(ctx *Context, resourcesDict Dict, pageNr, pageObjNumber int, rNamePrefix string, visitedRes []Object) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("optimizeResources begin: pageNr=%d pageObjNumber=%d\n", pageNr, pageObjNumber)
	// }

	if resourcesDict == nil {
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("optimizeResources end: No resources dict available")
		// }
		return nil
	}

	obj, found := resourcesDict.Find("Font")
	if found {
		// Process Font resource dict, get rid of redundant fonts.
		if err := processFontResources(ctx, obj, pageNr, pageObjNumber, rNamePrefix); err != nil {
			return err
		}
	}

	obj, found = resourcesDict.Find("XObject")
	if found {
		// Process XObject resource dict, get rid of redundant images.
		if err := processXObjectResources(ctx, obj, pageNr, pageObjNumber, rNamePrefix, visitedRes); err != nil {
			return err
		}
	}

	obj, found = resourcesDict.Find("ExtGState")
	if found {
		// An ExtGState resource dict may contain binary content in the following entries: "SMask", "HT".
		if err := processExtGStateResources(ctx, obj, pageNr, pageObjNumber, rNamePrefix, visitedRes); err != nil {
			return err
		}
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("optimizeResources end")
	// }

	return nil
}

// Process the resources dictionary for given page number and optimize by removing redundant resources.
func parseResourcesDict(ctx *Context, pageDict Dict, pageNr, pageObjNumber int) error {
	if ctx.Optimize.Cache[pageObjNumber] {
		return nil
	}
	ctx.Optimize.Cache[pageObjNumber] = true

	// The logical pageNr is pageNr+1.
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("parseResourcesDict begin page: %d, object:%d\n", pageNr+1, pageObjNumber)
	// }

	// Get resources dict for this page.
	d, err := resourcesDictForPageDict(ctx.XRefTable, pageDict, pageObjNumber)
	if err != nil {
		return err
	}

	// dict may be nil for inherited resource dicts.
	if d != nil {
		// Optimize image and font resources.
		if err = optimizeResources(ctx, d, pageNr, pageObjNumber, "", []Object{}); err != nil {
			return err
		}
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("parseResourcesDict end page: %d, object:%d\n", pageNr+1, pageObjNumber)
	// }

	return nil
}

// Iterate over all pages and optimize content & resources.
func parsePagesDict(ctx *Context, pagesDict Dict, pageNr int) (int, error) {
	// TODO Integrate resource consolidation based on content stream requirements.

	_, found := pagesDict.Find("Count")
	if !found {
		return pageNr, errors.New("pdfcpu: parsePagesDict: missing Count")
	}

	ctx.Optimize.Cache = map[int]bool{}

	// Iterate over page tree.
	o, found := pagesDict.Find("Kids")
	if !found {
		return pageNr, errors.Errorf("pdfcpu: corrupt \"Kids\" entry %s", pagesDict)
	}

	kids, err := ctx.DereferenceArray(o)
	if err != nil || kids == nil {
		return pageNr, errors.Errorf("pdfcpu: corrupt \"Kids\" entry: %s", pagesDict)
	}

	for _, v := range kids {

		// Dereference next page node dict.
		ir, _ := v.(IndirectRef)

		// if log.OptimizeEnabled() {
		// 	log.Optimize.Printf("parsePagesDict PageNode: %s\n", ir)
		// }

		d, err := ctx.DereferencePageNodeDict(ir)
		if err != nil {
			return 0, errors.Wrap(err, "parsePagesDict: can't locate Pagedict or Pagesdict")
		}

		dictType := d.Type()

		// Note: Resource dicts may be inherited.

		if *dictType == "Pages" {

			// Recurse over pagetree and optimize resources.
			pageNr, err = parsePagesDict(ctx, d, pageNr)
			if err != nil {
				return 0, err
			}

			continue
		}

		// Process page dict.

		if ctx.OptimizeDuplicateContentStreams {
			if err = optimizePageContent(ctx, d, int(ir.ObjectNumber)); err != nil {
				return 0, err
			}
		}

		// Get rid of PieceInfo dict from page dict.
		if err := ctx.DeleteDictEntry(d, "PieceInfo"); err != nil {
			return 0, err
		}

		// Parse and optimize resource dict for one page.
		if err = parseResourcesDict(ctx, d, pageNr, int(ir.ObjectNumber)); err != nil {
			return 0, err
		}

		pageNr++
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("parsePagesDict end: %s\n", pagesDict)
	// }

	return pageNr, nil
}

func traverse(xRefTable *XRefTable, value Object, duplObjs IntSet) error {
	if indRef, ok := value.(IndirectRef); ok {
		duplObjs[int(indRef.ObjectNumber)] = true
		o, err := xRefTable.Dereference(indRef)
		if err != nil {
			return err
		}
		traverseObjectGraphAndMarkDuplicates(xRefTable, o, duplObjs)
	}
	if d, ok := value.(Dict); ok {
		traverseObjectGraphAndMarkDuplicates(xRefTable, d, duplObjs)
	}
	if sd, ok := value.(StreamDict); ok {
		traverseObjectGraphAndMarkDuplicates(xRefTable, sd, duplObjs)
	}
	if a, ok := value.(Array); ok {
		traverseObjectGraphAndMarkDuplicates(xRefTable, a, duplObjs)
	}

	return nil
}

// Traverse the object graph for a Object and mark all objects as potential duplicates.
func traverseObjectGraphAndMarkDuplicates(xRefTable *XRefTable, obj Object, duplObjs IntSet) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Printf("traverseObjectGraphAndMarkDuplicates begin type=%T\n", obj)
	// }

	switch x := obj.(type) {

	case Dict:
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Println("traverseObjectGraphAndMarkDuplicates: dict")
		// }
		for _, value := range x {
			if err := traverse(xRefTable, value, duplObjs); err != nil {
				return err
			}
		}

	case StreamDict:
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Println("traverseObjectGraphAndMarkDuplicates: streamDict")
		// }
		for _, value := range x.Dict {
			if err := traverse(xRefTable, value, duplObjs); err != nil {
				return err
			}
		}

	case Array:
		// if log.OptimizeEnabled() {
		// 	log.Optimize.Println("traverseObjectGraphAndMarkDuplicates: arr")
		// }
		for _, value := range x {
			if err := traverse(xRefTable, value, duplObjs); err != nil {
				return err
			}
		}
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("traverseObjectGraphAndMarkDuplicates end")
	// }

	return nil
}

// Identify and mark all potential duplicate objects.
func calcRedundantObjects(ctx *Context) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("calcRedundantObjects begin")
	// }

	for i, fontDict := range ctx.Optimize.DuplicateFonts {
		ctx.Optimize.DuplicateFontObjs[i] = true
		// Identify and mark all involved potential duplicate objects for a redundant
		if err := traverseObjectGraphAndMarkDuplicates(ctx.XRefTable, fontDict, ctx.Optimize.DuplicateFontObjs); err != nil {
			return err
		}
	}

	for i, obj := range ctx.Optimize.DuplicateImages {
		ctx.Optimize.DuplicateImageObjs[i] = true
		// Identify and mark all involved potential duplicate objects for a redundant image.
		if err := traverseObjectGraphAndMarkDuplicates(ctx.XRefTable, *obj.ImageDict, ctx.Optimize.DuplicateImageObjs); err != nil {
			return err
		}
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("calcRedundantObjects end")
	// }

	return nil
}

// Iterate over all pages and optimize resources.
// Get rid of duplicate embedded fonts and images.
func optimizeFontAndImages(ctx *Context) error {
	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("optimizeFontAndImages begin")
	// }

	// Get a reference to the PDF indirect reference of the page tree root dict.
	indRefPages, err := ctx.Pages()
	if err != nil {
		return err
	}

	// Dereference and get a reference to the page tree root dict.
	pageTreeRootDict, err := ctx.XRefTable.DereferenceDict(*indRefPages)
	if err != nil {
		return err
	}

	// Prepare optimization environment.
	ctx.Optimize.PageFonts = make([]IntSet, ctx.PageCount)
	ctx.Optimize.PageImages = make([]IntSet, ctx.PageCount)

	// Iterate over page dicts and optimize resources.
	_, err = parsePagesDict(ctx, pageTreeRootDict, 0)
	if err != nil {
		return err
	}

	ctx.Optimize.ContentStreamCache = map[int]*StreamDict{}
	ctx.Optimize.FormStreamCache = map[int]*StreamDict{}

	// Identify all duplicate objects.
	if err = calcRedundantObjects(ctx); err != nil {
		return err
	}

	// if log.OptimizeEnabled() {
	// 	log.Optimize.Println("optimizeFontAndImages end")
	// }

	return nil
}

func fixDeepDict(ctx *Context, d Dict) error {
	for k, v := range d {
		ir, err := fixDeepObject(ctx, v)
		if err != nil {
			return err
		}
		if ir != nil {
			d[k] = *ir
		}
	}

	return nil
}

func fixDeepArray(ctx *Context, a Array) error {
	for i, v := range a {
		ir, err := fixDeepObject(ctx, v)
		if err != nil {
			return err
		}
		if ir != nil {
			a[i] = *ir
		}
	}

	return nil
}

func fixDirectObject(ctx *Context, o Object) error {
	switch o := o.(type) {
	case Dict:
		for k, v := range o {
			ir, err := fixDeepObject(ctx, v)
			if err != nil {
				return err
			}
			if ir != nil {
				o[k] = *ir
			}
		}
	case Array:
		for i, v := range o {
			ir, err := fixDeepObject(ctx, v)
			if err != nil {
				return err
			}
			if ir != nil {
				o[i] = *ir
			}
		}
	}

	return nil
}

func fixIndirectObject(ctx *Context, ir *IndirectRef) error {
	objNr := int(ir.ObjectNumber)

	if ctx.Optimize.Cache[objNr] {
		return nil
	}
	ctx.Optimize.Cache[objNr] = true

	entry, found := ctx.Find(objNr)
	if !found {
		return nil
	}

	if entry.Free {
		// This is a reference to a free object that needs to be fixed.

		// fmt.Printf("fixNullObject: #%d g%d\n", objNr, genNr)

		if ctx.Optimize.NullObjNr == nil {
			nr, err := ctx.InsertObject(nil)
			if err != nil {
				return err
			}
			ctx.Optimize.NullObjNr = &nr
		}

		ir.ObjectNumber = Integer(*ctx.Optimize.NullObjNr)

		return nil
	}

	var err error

	switch o := entry.Object.(type) {

	case Dict:
		err = fixDeepDict(ctx, o)

	case StreamDict:
		err = fixDeepDict(ctx, o.Dict)

	case Array:
		err = fixDeepArray(ctx, o)

	}

	return err
}

func fixDeepObject(ctx *Context, o Object) (*IndirectRef, error) {
	ir, ok := o.(IndirectRef)
	if !ok {
		return nil, fixDirectObject(ctx, o)
	}

	err := fixIndirectObject(ctx, &ir)
	return &ir, err
}

func fixReferencesToFreeObjects(ctx *Context) error {
	return fixDirectObject(ctx, ctx.RootDict)
}

func optimizeResourceDicts(ctx *Context) error {
	for i := 1; i <= ctx.PageCount; i++ {
		d, _, inhPAttrs, err := ctx.PageDict(i, true)
		if err != nil {
			return err
		}
		if d == nil {
			continue
		}
		if len(inhPAttrs.Resources) > 0 {
			d["Resources"] = inhPAttrs.Resources
		}
	}
	// TODO Remove resource dicts from inner nodes.
	return nil
}

func resolveWidth(ctx *Context, sd *StreamDict) error {
	if obj, ok := sd.Find("Width"); ok {
		w, err := ctx.DereferenceNumber(obj)
		if err != nil {
			return err
		}
		sd.Dict["Width"] = Integer(w)
	}
	return nil
}

func ensureDirectWidthForXObjs(ctx *Context) error {
	for _, imgObjs := range ctx.Optimize.PageImages {
		for objNr, v := range imgObjs {
			if v {
				imageObj := ctx.Optimize.ImageObjects[objNr]
				if err := resolveWidth(ctx, imageObj.ImageDict); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

// OptimizeXRefTable optimizes an xRefTable by locating and getting rid of redundant embedded fonts and images.
func OptimizeXRefTable(ctx *Context) error {
	if ctx.PageCount == 0 {
		return nil
	}

	// Sometimes free objects are used although they are part of the free object list.
	// Replace references to free xref table entries with a reference to a NULL object.
	if err := fixReferencesToFreeObjects(ctx); err != nil {
		return err
	}

	if (ctx.Cmd == VALIDATE ||
		ctx.Cmd == OPTIMIZE ||
		ctx.Cmd == LISTIMAGES ||
		ctx.Cmd == EXTRACTIMAGES ||
		ctx.Cmd == UPDATEIMAGES) &&
		ctx.Conf.OptimizeResourceDicts {
		// Extra step with potential for performance hit when processing large files.
		if err := optimizeResourceDicts(ctx); err != nil {
			return err
		}
	}

	// Get rid of duplicate embedded fonts and images.
	if err := optimizeFontAndImages(ctx); err != nil {
		return err
	}

	if err := ensureDirectWidthForXObjs(ctx); err != nil {
		return err
	}

	// Get rid of PieceInfo dict from root.
	if err := ctx.DeleteDictEntry(ctx.RootDict, "PieceInfo"); err != nil {
		return err
	}

	// Calculate memory usage of binary content for stats.
	// if log.StatsEnabled() {
	// 	if err := calcBinarySizes(ctx); err != nil {
	// 		return err
	// }
	// }

	ctx.Optimized = true

	return nil
}

// OptimizeContext optimizes ctx.
func OptimizeContext(ctx *Context) error {
	// if log.CLIEnabled() {
	// 	log.CLI.Println("optimizing...")
	// }
	return OptimizeXRefTable(ctx)
}

func ReadValidateAndOptimize(rs io.ReadSeeker, conf *Configuration) (ctx *Context, err error) {
	if conf == nil {
		return nil, errors.New("pdfcpu: ReadValidateAndOptimize: missing conf")
	}

	ctx, err = ReadAndValidate(rs, conf)
	if err != nil {
		return nil, err
	}

	// With the exception of commands utilizing structs provided the Optimize step
	// command optimization of the cross reference table is optional but usually recommended.
	// For large or complex files it may make sense to skip optimization and set conf.Optimize = false.
	if cmdAssumingOptimization(conf.Cmd) || conf.Optimize {
		if err = OptimizeContext(ctx); err != nil {
			return nil, err
		}
	}

	return ctx, nil
}

func extractAuthor(ctx *Context, obj Object) (err error) {
	// Record for stats.
	if ctx.Author, err = ctx.DereferenceText(obj); err != nil {
		return err
	}
	ctx.Author = CSVSafeString(ctx.Author)
	return nil
}

func extractCreator(ctx *Context, obj Object) (err error) {
	// Record for stats.
	ctx.Creator, err = ctx.DereferenceText(obj)
	if err != nil {
		return err
	}
	ctx.Creator = CSVSafeString(ctx.Creator)
	return nil
}

// handleInfoDict extracts relevant infoDict fields into the context.
func handleInfoDict(ctx *Context, d Dict) (err error) {
	for key, value := range d {
		switch key {

		case "Title":

		case "Author":
			if err = extractAuthor(ctx, value); err != nil {
				return err
			}

		case "Subject":

		case "Keywords":

		case "Creator":
			if err = extractCreator(ctx, value); err != nil {
				return err
			}

		case "Producer", "CreationDate", "ModDate":
			// pdfcpu will modify these as direct dict entries.
			if indRef, ok := value.(IndirectRef); ok {
				// Get rid of these extra objects.
				ctx.Optimize.DuplicateInfoObjects[int(indRef.ObjectNumber)] = true
			}

		case "Trapped":

		default:
			// if log.WriteEnabled() {
			// 	log.Write.Printf("handleInfoDict: found out of spec entry %s %v\n", key, value)
			// }

		}
	}

	return nil
}

func ensureInfoDict(ctx *Context) error {
	// => 14.3.3 Document Information Dictionary

	// Optional:
	// Title                -
	// Author               -
	// Subject              -
	// Keywords             -
	// Creator              -
	// Producer		        modified by pdfcpu
	// CreationDate	        modified by pdfcpu
	// ModDate		        modified by pdfcpu
	// Trapped              -

	now := DateString(time.Now())

	v := "pdfcpu " + VersionStr

	if ctx.Info == nil {

		d := NewDict()
		d.InsertString("Producer", v)
		d.InsertString("CreationDate", now)
		d.InsertString("ModDate", now)

		ir, err := ctx.IndRefForNewObject(d)
		if err != nil {
			return err
		}

		ctx.Info = ir

		return nil
	}

	d, err := ctx.DereferenceDict(*ctx.Info)
	if err != nil || d == nil {
		return err
	}

	if err = handleInfoDict(ctx, d); err != nil {
		return err
	}

	d.Update("CreationDate", StringLiteral(now))
	d.Update("ModDate", StringLiteral(now))
	d.Update("Producer", StringLiteral(v))

	return nil
}

func fileID(ctx *Context) (HexLiteral, error) {
	// see also 14.4 File Identifiers.

	// The calculation of the file identifier need not be reproducible;
	// all that matters is that the identifier is likely to be unique.
	// For example, two implementations of the preceding algorithm might use different formats for the current time,
	// causing them to produce different file identifiers for the same file created at the same time,
	// but the uniqueness of the identifier is not affected.

	h := md5.New()

	// Current timestamp.
	h.Write([]byte(time.Now().String()))

	// File location - ignore, we don't have this.

	// File size.
	h.Write([]byte(strconv.Itoa(ctx.Read.ReadFileSize())))

	// All values of the info dict which is assumed to be there at this point.
	if ctx.XRefTable.Version() < V20 {
		d, err := ctx.DereferenceDict(*ctx.Info)
		if err != nil {
			return "", err
		}
		for _, v := range d {
			o, err := ctx.Dereference(v)
			if err != nil {
				return "", err
			}
			h.Write([]byte(o.String()))
		}
	}

	m := h.Sum(nil)

	return HexLiteral(hex.EncodeToString(m)), nil
}

func ensureFileID(ctx *Context) error {
	fid, err := fileID(ctx)
	if err != nil {
		return err
	}

	if ctx.ID == nil {
		// Ensure ctx.ID
		ctx.ID = Array{fid, fid}
		return nil
	}

	// Update ctx.ID
	a := ctx.ID
	if len(a) != 2 {
		return errors.New("pdfcpu: ID must be an array with 2 elements")
	}

	a[1] = fid

	return nil
}

func ensureInfoDictAndFileID(ctx *Context) error {
	if ctx.XRefTable.Version() < V20 {
		if err := ensureInfoDict(ctx); err != nil {
			return err
		}
	}

	return ensureFileID(ctx)
}

// NewEncryptDict creates a new EncryptDict using the standard security handler.
func newEncryptDict(v Version, needAES bool, keyLength int, permissions int16) Dict {
	d := NewDict()

	d.Insert("Filter", NameType("Standard"))

	if keyLength >= 128 {
		d.Insert("Length", Integer(keyLength))
		i := 4
		if keyLength == 256 {
			i = 5
		}
		d.Insert("V", Integer(i))
		if v == V20 {
			i++
		}
		d.Insert("R", Integer(i))
	} else {
		d.Insert("R", Integer(2))
		d.Insert("V", Integer(1))
	}

	// Set user access permission flags.
	d.Insert("P", Integer(permissions))

	d.Insert("StmF", NameType("StdCF"))
	d.Insert("StrF", NameType("StdCF"))

	d1 := NewDict()
	d1.Insert("AuthEvent", NameType("DocOpen"))

	if needAES {
		n := "AESV2"
		if keyLength == 256 {
			n = "AESV3"
		}
		d1.Insert("CFM", NameType(n))
	} else {
		d1.Insert("CFM", NameType("V2"))
	}

	d1.Insert("Length", Integer(keyLength/8))

	d2 := NewDict()
	d2.Insert("StdCF", d1)

	d.Insert("CF", d2)

	if keyLength == 256 {
		d.Insert("U", NewHexLiteral(make([]byte, 48)))
		d.Insert("O", NewHexLiteral(make([]byte, 48)))
		d.Insert("UE", NewHexLiteral(make([]byte, 32)))
		d.Insert("OE", NewHexLiteral(make([]byte, 32)))
		d.Insert("Perms", NewHexLiteral(make([]byte, 16)))
	} else {
		d.Insert("U", NewHexLiteral(make([]byte, 32)))
		d.Insert("O", NewHexLiteral(make([]byte, 32)))
	}

	return d
}

func calcFileEncKey(ctx *Context) error {
	ctx.EncKey = make([]byte, 32)
	_, err := io.ReadFull(rand.Reader, ctx.EncKey)
	return err
}

func calcOAndUAES256(ctx *Context, d Dict) (err error) {
	b := make([]byte, 16)
	_, err = io.ReadFull(rand.Reader, b)
	if err != nil {
		return err
	}

	u := append(make([]byte, 32), b...)
	upw := []byte(ctx.UserPW)
	h := sha256.Sum256(append(upw, validationSalt(u)...))

	ctx.E.U = append(h[:], b...)
	d.Update("U", HexLiteral(hex.EncodeToString(ctx.E.U)))

	///////////////////////////////////

	b = make([]byte, 16)
	_, err = io.ReadFull(rand.Reader, b)
	if err != nil {
		return err
	}

	o := append(make([]byte, 32), b...)
	opw := []byte(ctx.OwnerPW)
	c := append(opw, validationSalt(o)...)
	h = sha256.Sum256(append(c, ctx.E.U...))
	ctx.E.O = append(h[:], b...)
	d.Update("O", HexLiteral(hex.EncodeToString(ctx.E.O)))

	//////////////////////////////////

	if err := calcFileEncKey(ctx); err != nil {
		return err
	}

	//////////////////////////////////

	h = sha256.Sum256(append(upw, keySalt(u)...))
	cb, err := aes.NewCipher(h[:])
	if err != nil {
		return err
	}

	iv := make([]byte, 16)
	mode := cipher.NewCBCEncrypter(cb, iv)
	mode.CryptBlocks(ctx.E.UE, ctx.EncKey)
	d.Update("UE", HexLiteral(hex.EncodeToString(ctx.E.UE)))

	//////////////////////////////////

	c = append(opw, keySalt(o)...)
	h = sha256.Sum256(append(c, ctx.E.U...))
	cb, err = aes.NewCipher(h[:])
	if err != nil {
		return err
	}

	mode = cipher.NewCBCEncrypter(cb, iv)
	mode.CryptBlocks(ctx.E.OE, ctx.EncKey)
	d.Update("OE", HexLiteral(hex.EncodeToString(ctx.E.OE)))

	return nil
}

func calcOAndUAES256Rev6(ctx *Context, d Dict) (err error) {
	b := make([]byte, 16)
	_, err = io.ReadFull(rand.Reader, b)
	if err != nil {
		return err
	}

	u := append(make([]byte, 32), b...)
	upw := []byte(ctx.UserPW)
	h, _, err := hashRev6(append(upw, validationSalt(u)...), upw, nil)
	if err != nil {
		return err
	}

	ctx.E.U = append(h[:], b...)
	d.Update("U", HexLiteral(hex.EncodeToString(ctx.E.U)))

	///////////////////////////

	b = make([]byte, 16)
	_, err = io.ReadFull(rand.Reader, b)
	if err != nil {
		return err
	}

	o := append(make([]byte, 32), b...)
	opw := []byte(ctx.OwnerPW)
	c := append(opw, validationSalt(o)...)
	h, _, err = hashRev6(append(c, ctx.E.U...), opw, ctx.E.U)
	if err != nil {
		return err
	}

	ctx.E.O = append(h[:], b...)
	d.Update("O", HexLiteral(hex.EncodeToString(ctx.E.O)))

	///////////////////////////

	if err := calcFileEncKey(ctx); err != nil {
		return err
	}

	///////////////////////////

	h, _, err = hashRev6(append(upw, keySalt(u)...), upw, nil)
	if err != nil {
		return err
	}

	cb, err := aes.NewCipher(h[:])
	if err != nil {
		return err
	}

	iv := make([]byte, 16)
	mode := cipher.NewCBCEncrypter(cb, iv)
	mode.CryptBlocks(ctx.E.UE, ctx.EncKey)
	d.Update("UE", HexLiteral(hex.EncodeToString(ctx.E.UE)))

	//////////////////////////////

	c = append(opw, keySalt(o)...)
	h, _, err = hashRev6(append(c, ctx.E.U...), opw, ctx.E.U)
	if err != nil {
		return err
	}

	cb, err = aes.NewCipher(h[:])
	if err != nil {
		return err
	}

	mode = cipher.NewCBCEncrypter(cb, iv)
	mode.CryptBlocks(ctx.E.OE, ctx.EncKey)
	d.Update("OE", HexLiteral(hex.EncodeToString(ctx.E.OE)))

	return nil
}

func calcOAndU(ctx *Context, d Dict) (err error) {
	if ctx.E.R == 5 {
		return calcOAndUAES256(ctx, d)
	}

	if ctx.E.R == 6 {
		return calcOAndUAES256Rev6(ctx, d)
	}

	ctx.E.O, err = o(ctx)
	if err != nil {
		return err
	}

	ctx.E.U, ctx.EncKey, err = u(ctx)
	if err != nil {
		return err
	}

	d.Update("U", HexLiteral(hex.EncodeToString(ctx.E.U)))
	d.Update("O", HexLiteral(hex.EncodeToString(ctx.E.O)))

	return nil
}

func setupEncryption(ctx *Context) error {
	var err error

	if ok := validateAlgorithm(ctx); !ok {
		return errors.New("pdfcpu: unsupported encryption algorithm (PDF 2.0 assumes AES/256)")
	}

	d := newEncryptDict(
		ctx.XRefTable.Version(),
		ctx.EncryptUsingAES,
		ctx.EncryptKeyLength,
		int16(ctx.Permissions),
	)

	if ctx.E, err = supportedEncryption(ctx, d); err != nil {
		return err
	}

	if ctx.ID == nil {
		return errors.New("pdfcpu: encrypt: missing ID")
	}

	if ctx.E.ID, err = ctx.IDFirstElement(); err != nil {
		return err
	}

	if err = calcOAndU(ctx, d); err != nil {
		return err
	}

	if err = writePermissions(ctx, d); err != nil {
		return err
	}

	xRefTableEntry := NewXRefTableEntryGen0(d)

	// Reuse free objects (including recycled objects from this run).
	objNumber, err := ctx.InsertAndUseRecycled(*xRefTableEntry)
	if err != nil {
		return err
	}

	ctx.Encrypt = NewIndirectRef(objNumber, 0)

	return nil
}

// O calculates the owner password digest.
func o(ctx *Context) ([]byte, error) {
	ownerpw := ctx.OwnerPW
	userpw := ctx.UserPW

	e := ctx.E

	// 3a-d
	key := key(ownerpw, userpw, e.R, e.L)

	// 3e
	o := []byte(userpw)
	if len(o) >= 32 {
		o = o[:32]
	} else {
		o = append(o, padArr[:32-len(o)]...)
	}

	// 3f
	c, err := rc4.NewCipher(key)
	if err != nil {
		return nil, err
	}
	c.XORKeyStream(o, o)

	// 3g
	if e.R >= 3 {
		for i := 1; i <= 19; i++ {
			keynew := make([]byte, len(key))
			copy(keynew, key)

			for j := range keynew {
				keynew[j] ^= byte(i)
			}

			c, err := rc4.NewCipher(keynew)
			if err != nil {
				return nil, err
			}
			c.XORKeyStream(o, o)
		}
	}

	return o, nil
}

func updateEncryption(ctx *Context) error {
	if ctx.Encrypt == nil {
		return errors.New("pdfcpu: This file is not encrypted - nothing written.")
	}

	d, err := ctx.EncryptDict()
	if err != nil {
		return err
	}

	if ctx.Cmd == SETPERMISSIONS {
		// fmt.Printf("updating permissions to: %v\n", ctx.UserAccessPermissions)
		ctx.E.P = int(ctx.Permissions)
		d.Update("P", Integer(ctx.E.P))
		// and moving on, U is dependent on P
	}

	// ctx.Cmd == CHANGEUPW or CHANGE OPW

	if ctx.UserPWNew != nil {
		// fmt.Printf("change upw from <%s> to <%s>\n", ctx.UserPW, *ctx.UserPWNew)
		ctx.UserPW = *ctx.UserPWNew
	}

	if ctx.OwnerPWNew != nil {
		// fmt.Printf("change opw from <%s> to <%s>\n", ctx.OwnerPW, *ctx.OwnerPWNew)
		ctx.OwnerPW = *ctx.OwnerPWNew
	}

	if ctx.E.R == 5 || ctx.E.R == 6 {

		if err = calcOAndU(ctx, d); err != nil {
			return err
		}

		// Calc Perms for rev 5, 6.
		return writePermissions(ctx, d)
	}

	// fmt.Printf("opw before: length:%d <%s>\n", len(ctx.E.O), ctx.E.O)
	if ctx.E.O, err = o(ctx); err != nil {
		return err
	}
	// fmt.Printf("opw after: length:%d <%s> %0X\n", len(ctx.E.O), ctx.E.O, ctx.E.O)
	d.Update("O", HexLiteral(hex.EncodeToString(ctx.E.O)))

	// fmt.Printf("upw before: length:%d <%s>\n", len(ctx.E.U), ctx.E.U)
	if ctx.E.U, ctx.EncKey, err = u(ctx); err != nil {
		return err
	}
	// fmt.Printf("upw after: length:%d <%s> %0X\n", len(ctx.E.U), ctx.E.U, ctx.E.U)
	// fmt.Printf("encKey = %0X\n", ctx.EncKey)
	d.Update("U", HexLiteral(hex.EncodeToString(ctx.E.U)))

	return nil
}

func handleEncryption(ctx *Context) error {
	if ctx.Cmd == ENCRYPT || ctx.Cmd == DECRYPT {
		if ctx.Cmd == DECRYPT {
			// Remove encryption.
			ctx.EncKey = nil
		} else {
			if err := setupEncryption(ctx); err != nil {
				return err
			}

			// alg := "RC4"
			// if ctx.EncryptUsingAES {
			// 	alg = "AES"
			// }
			// if log.CLIEnabled() {
			// 	log.CLI.Printf("using %s-%d\n", alg, ctx.EncryptKeyLength)
			// }
		}
	} else if ctx.UserPWNew != nil || ctx.OwnerPWNew != nil || ctx.Cmd == SETPERMISSIONS {
		if err := updateEncryption(ctx); err != nil {
			return err
		}
	}

	// write xrefstream if using xrefstream only.
	if ctx.Encrypt != nil && ctx.EncKey != nil && !ctx.Read.UsingXRefStreams {
		ctx.WriteObjectStream = false
		ctx.WriteXRefStream = false
	}

	return nil
}

func prepareContextForWriting(ctx *Context) error {
	if err := ensureInfoDictAndFileID(ctx); err != nil {
		return err
	}

	return handleEncryption(ctx)
}

func writeCommentLine(w *WriteContext, comment string) (int, error) {
	return w.WriteString(fmt.Sprintf("%%%s%s", comment, w.Eol))
}

// Write root entry to disk.
func writeRootEntry(ctx *Context, d Dict, dictName, entryName string, statsAttr int) error {
	_, err := writeEntry(ctx, d, dictName, entryName)
	if err != nil {
		return err
	}

	// if o != nil {
	// 	ctx.Stats.AddRootAttr(statsAttr)
	// }

	return nil
}

func writeHeader(w *WriteContext, v Version) error {
	i, err := writeCommentLine(w, "PDF-"+v.String())
	if err != nil {
		return err
	}

	j, err := writeCommentLine(w, "\xe2\xe3\xcf\xD3")
	if err != nil {
		return err
	}

	w.Offset += int64(i + j)

	return nil
}

func pageNodeDict(ctx *Context, o Object) (Dict, *IndirectRef, error) {
	if o == nil {
		// if log.WriteEnabled() {
		// 	log.Write.Println("pageNodeDict: is nil")
		// }
		return nil, nil, nil
	}

	// Dereference next page node dict.
	indRef, ok := o.(IndirectRef)
	if !ok {
		return nil, nil, errors.New("pdfcpu: pageNodeDict: missing indirect reference")
	}
	// if log.WriteEnabled() {
	// 	log.Write.Printf("pageNodeDict: PageNode: %s\n", indRef)
	// }

	d, err := ctx.DereferenceDict(indRef)
	if err != nil {
		return nil, nil, errors.New("pdfcpu: pageNodeDict: cannot dereference, pageNodeDict")
	}
	if d == nil {
		return nil, nil, errors.New("pdfcpu: pageNodeDict: pageNodeDict is null")
	}

	dictType := d.Type()
	if dictType == nil {
		return nil, nil, errors.New("pdfcpu: pageNodeDict: missing pageNodeDict type")
	}

	return d, &indRef, nil
}

// The PDF page object fields.
const (
	PageLastModified = iota
	PageResources
	PageMediaBox
	PageCropBox
	PageBleedBox
	PageTrimBox
	PageArtBox
	PageBoxColorInfo
	PageContents
	PageRotate
	PageGroup
	PageThumb
	PageB
	PageDur
	PageTrans
	PageAnnots
	PageAA
	PageMetadata
	PagePieceInfo
	PageStructParents
	PageID
	PagePZ
	PageSeparationInfo
	PageTabs
	PageTemplateInstantiated
	PagePresSteps
	PageUserUnit
	PageVP
)

// Write page entry to disk.
func writePageEntry(ctx *Context, d Dict, dictName, entryName string, statsAttr int) error {
	_, err := writeEntry(ctx, d, dictName, entryName)
	if err != nil {
		return err
	}

	// if o != nil {
	// 	ctx.Stats.AddPageAttr(statsAttr)
	// }

	return nil
}

func writePageDict(ctx *Context, indRef *IndirectRef, pageDict Dict, pageNr int) error {
	objNr := indRef.ObjectNumber.Value()
	genNr := indRef.GenerationNumber.Value()

	if ctx.Write.HasWriteOffset(objNr) {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writePageDict: object #%d already written.\n", objNr)
		// }
		return nil
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writePageDict: logical pageNr=%d object #%d gets writeoffset: %d\n", pageNr, objNr, ctx.Write.Offset)
	// }

	dictName := "pageDict"

	if err := writeDictObject(ctx, objNr, genNr, pageDict); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writePageDict: new offset = %d\n", ctx.Write.Offset)
	// }

	if indRef := pageDict.IndirectRefEntry("Parent"); indRef == nil {
		return errors.New("pdfcpu: writePageDict: missing parent")
	}

	ctx.WritingPages = true

	for _, e := range []struct {
		entryName string
		statsAttr int
	}{
		{"Contents", PageContents},
		{"Resources", PageResources},
		{"MediaBox", PageMediaBox},
		{"CropBox", PageCropBox},
		{"BleedBox", PageBleedBox},
		{"TrimBox", PageTrimBox},
		{"ArtBox", PageArtBox},
		{"BoxColorInfo", PageBoxColorInfo},
		{"PieceInfo", PagePieceInfo},
		{"LastModified", PageLastModified},
		{"Rotate", PageRotate},
		{"Group", PageGroup},
		{"Annots", PageAnnots},
		{"Thumb", PageThumb},
		{"B", PageB},
		{"Dur", PageDur},
		{"Trans", PageTrans},
		{"AA", PageAA},
		{"Metadata", PageMetadata},
		{"StructParents", PageStructParents},
		{"ID", PageID},
		{"PZ", PagePZ},
		{"SeparationInfo", PageSeparationInfo},
		{"Tabs", PageTabs},
		{"TemplateInstantiated", PageTemplateInstantiated},
		{"PresSteps", PagePresSteps},
		{"UserUnit", PageUserUnit},
		{"VP", PageVP},
	} {
		if err := writePageEntry(ctx, pageDict, dictName, e.entryName, e.statsAttr); err != nil {
			return err
		}
	}

	ctx.WritingPages = false

	// if log.WriteEnabled() {
	// 	log.Write.Printf("*** writePageDict end: obj#%d offset=%d ***\n", objNr, ctx.Write.Offset)
	// }

	return nil
}

func writeKids(ctx *Context, a Array, pageNr *int) (Array, int, error) {
	kids := Array{}
	count := 0

	for _, o := range a {

		d, ir, err := pageNodeDict(ctx, o)
		if err != nil {
			return nil, 0, err
		}
		if d == nil {
			continue
		}

		switch *d.Type() {

		case "Pages":
			// Recurse over pagetree
			skip, c, err := writePagesDict(ctx, ir, pageNr)
			if err != nil {
				return nil, 0, err
			}
			if !skip {
				kids = append(kids, o)
				count += c
			}

		case "Page":
			*pageNr++
			if len(ctx.Write.SelectedPages) > 0 {
				// if log.WriteEnabled() {
				// 	log.Write.Printf("selectedPages: %v\n", ctx.Write.SelectedPages)
				// }
				writePage := ctx.Write.SelectedPages[*pageNr]
				if ctx.Cmd == REMOVEPAGES {
					writePage = !writePage
				}
				if writePage {
					// if log.WriteEnabled() {
					// 	log.Write.Printf("writeKids: writing page:%d\n", *pageNr)
					// }
					err = writePageDict(ctx, ir, d, *pageNr)
					kids = append(kids, o)
					count++
				} else {
					// if log.WriteEnabled() {
					// 	log.Write.Printf("writeKids: skipping page:%d\n", *pageNr)
					// }
				}
			} else {
				// if log.WriteEnabled() {
				// 	log.Write.Printf("writeKids: writing page anyway:%d\n", *pageNr)
				// }
				err = writePageDict(ctx, ir, d, *pageNr)
				kids = append(kids, o)
				count++
			}

		default:
			err = errors.Errorf("pdfcpu: writeKids: Unexpected dict type: %s", *d.Type())

		}

		if err != nil {
			return nil, 0, err
		}

	}

	return kids, count, nil
}

func writePageEntries(ctx *Context, d Dict, dictName string) error {
	// TODO Check inheritance rules.
	for _, e := range []struct {
		entryName string
		statsAttr int
	}{
		{"Resources", PageResources},
		{"MediaBox", PageMediaBox},
		{"CropBox", PageCropBox},
		{"Rotate", PageRotate},
	} {
		if err := writePageEntry(ctx, d, dictName, e.entryName, e.statsAttr); err != nil {
			return err
		}
	}

	return nil
}

func writePagesDict(ctx *Context, indRef *IndirectRef, pageNr *int) (skip bool, writtenPages int, err error) {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writePagesDict: begin pageNr=%d\n", *pageNr)
	// }

	dictName := "pagesDict"
	objNr := int(indRef.ObjectNumber)
	genNr := int(indRef.GenerationNumber)

	d, err := ctx.DereferenceDict(*indRef)
	if err != nil {
		return false, 0, errors.Wrapf(err, "writePagesDict: unable to dereference indirect object #%d", objNr)
	}

	// Push count, kids.
	countOrig, _ := d.Find("Count")
	kidsOrig := d.ArrayEntry("Kids")

	// Iterate over page tree.
	kidsArray := d.ArrayEntry("Kids")
	kidsNew, countNew, err := writeKids(ctx, kidsArray, pageNr)
	if err != nil {
		return false, 0, err
	}

	d.Update("Kids", kidsNew)
	d.Update("Count", Integer(countNew))
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writePagesDict: writing pageDict for obj=%d page=%d\n%s", objNr, *pageNr, d)
	// }

	if err = writeDictObject(ctx, objNr, genNr, d); err != nil {
		return false, 0, err
	}

	if err := writePageEntries(ctx, d, dictName); err != nil {
		return false, 0, err
	}

	// Pop kids, count.
	d.Update("Kids", kidsOrig)
	d.Update("Count", countOrig)

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writePagesDict: end pageNr=%d\n", *pageNr)
	// }

	return false, countNew, nil
}

// Write page tree.
func writePages(ctx *Context, rootDict Dict) error {
	// Page tree root (the top "Pages" dict) must be indirect reference.
	indRef := rootDict.IndirectRefEntry("Pages")
	if indRef == nil {
		return errors.New("pdfcpu: writePages: missing indirect obj for pages dict")
	}

	// Embed all page tree objects into objects stream.
	ctx.Write.WriteToObjectStream = true

	// Write page tree.
	p := 0
	if _, _, err := writePagesDict(ctx, indRef, &p); err != nil {
		return err
	}

	return stopObjectStream(ctx)
}

func sigDictPDFString(d Dict) string {
	s := []string{}
	s = append(s, "<<")
	s = append(s, fmt.Sprintf("/ByteRange%-62v", d["ByteRange"].PDFString()))
	s = append(s, fmt.Sprintf("/Contents%s", d["Contents"].PDFString()))
	s = append(s, fmt.Sprintf("/Type%s", d["Type"].PDFString()))
	s = append(s, fmt.Sprintf("/Filter%s", d["Filter"].PDFString()))
	s = append(s, fmt.Sprintf("/SubFilter%s", d["SubFilter"].PDFString()))
	s = append(s, ">>")
	return strings.Join(s, "")
}

func writeSigDict(ctx *Context, ir IndirectRef) error {
	// 	<<
	// 		<ByteRange, []>
	// 		<Contents, <00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000>>
	// 		<Filter, Adobe.PPKLite>
	// 		<SubFilter, adbe.pkcs7.detached>
	// 		<Type, Sig>
	// >>

	d, err := ctx.DereferenceDict(ir)
	if err != nil {
		return err
	}

	typ := d.NameEntry("Type")
	if typ == nil || *typ != "Sig" {
		return errors.New("corrupt sig dict")
	}

	f := d.NameEntry("Filter")
	if f == nil || *f != "Adobe.PPKLite" {
		return errors.Errorf("sig dict: unexpected Filter: %s", *f)
	}

	f = d.NameEntry("SubFilter")
	if f == nil || *f != "adbe.pkcs7.detached" {
		return errors.Errorf("sig dict: unexpected SubFilter: %s", *f)
	}

	objNr := ir.ObjectNumber.Value()
	genNr := ir.GenerationNumber.Value()

	// Set write-offset for this object.
	w := ctx.Write
	w.SetWriteOffset(objNr)

	written, err := writeObjectHeader(w, objNr, genNr)
	if err != nil {
		return err
	}

	// <</ByteRange[]
	w.OffsetSigByteRange = w.Offset + int64(written) + 2 + 10
	// 2 for "<<"
	// 10 for "/ByteRange"

	// [...]/Contents<00..... maxSigContentsBytes>
	w.OffsetSigContents = w.OffsetSigByteRange + 1 + 60 + 1 + 9
	// 1 for "["
	// 60 for max 60 chars within this array PDF string.
	// 1 for "]"
	// 9 for "/Contents<"

	i, err := w.WriteString(sigDictPDFString(d))
	if err != nil {
		return err
	}

	j, err := writeObjectTrailer(w)
	if err != nil {
		return err
	}

	// Write-offset for next object.
	w.Offset += int64(written + i + j)

	// Record writeOffset for first and last char of Contents.

	// Record writeOffset for ByteArray...

	return nil
}

func writeSigFieldDict(ctx *Context, d Dict, objNr, genNr int) error {
	// 	<<
	// 		<DA, (/Courier 0 Tf)>
	// 		<FT, Sig>
	// 		<Rect, [0.00 0.00 0.00 0.00]>
	// 		<Subtype, Widget>
	// 		<T, (Signature)>
	// 		<Type, Annot>
	// 		<V, (21 0 R)>
	// >>

	if err := writeDictObject(ctx, objNr, genNr, d); err != nil {
		return err
	}

	ir := d.IndirectRefEntry("V")
	if ir == nil {
		return errors.New("sig field dict: missing V")
	}

	return writeSigDict(ctx, *ir)
}

func writeBlankSignature(ctx *Context, d Dict, objNr, genNr int) error {
	// <<
	// 	<DR, <<
	// 		<Font, <<
	// 			<Courier, (19 0 R)>
	// 		>>>
	// 	>>>
	// 	<Fields, [(20 0 R)]>
	// 	<SigFlags, 3>
	// >>

	if err := writeDictObject(ctx, objNr, genNr, d); err != nil {
		return err
	}

	// Write font resource
	resDict := d.DictEntry("DR")
	fontResDict := resDict.DictEntry("Font")
	ir := fontResDict.IndirectRefEntry("Courier")
	if err := writeIndirectObject(ctx, *ir); err != nil {
		return err
	}

	// Write fields
	a := d.ArrayEntry("Fields")
	if a == nil {
		return errors.New("acroform dict: missing Fields")
	}
	for _, o := range a {
		ir, ok := o.(IndirectRef)
		if !ok {
			return errors.New("acroform dict fields: expecting indRef")
		}
		d, err := ctx.DereferenceDict(ir)
		if err != nil {
			return err
		}
		ft := d.NameEntry("FT")
		if ft == nil || *ft != "Sig" {
			if err := writeIndirectObject(ctx, ir); err != nil {
				return err
			}
			continue
		}
		objNr := ir.ObjectNumber.Value()
		genNr := ir.GenerationNumber.Value()
		writeSigFieldDict(ctx, d, objNr, genNr)
	}
	return nil
}

// The PDF root object fields.
const (
	RootVersion = iota
	RootExtensions
	RootPageLabels
	RootNames
	RootDests
	RootViewerPrefs
	RootPageLayout
	RootPageMode
	RootOutlines
	RootThreads
	RootOpenAction
	RootAA
	RootURI
	RootAcroForm
	RootMetadata
	RootStructTreeRoot
	RootMarkInfo
	RootLang
	RootSpiderInfo
	RootOutputIntents
	RootPieceInfo
	RootOCProperties
	RootPerms
	RootLegal
	RootRequirements
	RootCollection
	RootNeedsRendering
)

func writeAcroFormRootEntry(ctx *Context, d Dict, dictName string) error {
	o, found := d.Find("AcroForm")
	if !found || o == nil {
		return nil
	}

	if ctx.Cmd != ADDSIGNATURE {
		if err := writeRootEntry(ctx, d, dictName, "AcroForm", RootAcroForm); err != nil {
			return err
		}
		// ctx.Stats.AddRootAttr(RootAcroForm)
		return nil
	}

	// TODO distinguish between
	// 		A) PDF is not signed      => write new Acroform with single SigField
	//		B) Acroform is not signed => add Sigfield to existing Acroform
	//      C) PDF is already signed  => add Sigfield to existing Acroform via incremental update

	// Handle A)
	indRef, ok := o.(IndirectRef)
	if !ok {
		return errors.New("pdfcpu: add signature: missing Acroform object")
	}

	d1, err := ctx.DereferenceDict(indRef)
	if err != nil {
		return err
	}

	objNr := indRef.ObjectNumber.Value()
	genNr := indRef.GenerationNumber.Value()

	if err := writeBlankSignature(ctx, d1, objNr, genNr); err != nil {
		return err
	}

	// ctx.Stats.AddRootAttr(RootAcroForm)

	return nil
}

func writeRootAttrsBatch1(ctx *Context, d Dict, dictName string) error {
	if err := writeAcroFormRootEntry(ctx, d, dictName); err != nil {
		return err
	}

	for _, e := range []struct {
		entryName string
		statsAttr int
	}{
		{"Extensions", RootExtensions},
		{"PageLabels", RootPageLabels},
		{"Names", RootNames},
		{"Dests", RootDests},
		{"ViewerPreferences", RootViewerPrefs},
		{"PageLayout", RootPageLayout},
		{"PageMode", RootPageMode},
		{"Outlines", RootOutlines},
		{"Threads", RootThreads},
		{"OpenAction", RootOpenAction},
		{"AA", RootAA},
		{"URI", RootURI},
		//{"AcroForm", RootAcroForm},
		{"Metadata", RootMetadata},
	} {
		if err := writeRootEntry(ctx, d, dictName, e.entryName, e.statsAttr); err != nil {
			return err
		}
	}

	return nil
}

// Write root entry to object stream.
func writeRootEntryToObjStream(ctx *Context, d Dict, dictName, entryName string, statsAttr int) error {
	ctx.Write.WriteToObjectStream = true

	if err := writeRootEntry(ctx, d, dictName, entryName, statsAttr); err != nil {
		return err
	}

	return stopObjectStream(ctx)
}

func writeRootAttrsBatch2(ctx *Context, d Dict, dictName string) error {
	for _, e := range []struct {
		entryName string
		statsAttr int
	}{
		{"MarkInfo", RootMarkInfo},
		{"Lang", RootLang},
		{"SpiderInfo", RootSpiderInfo},
		{"OutputIntents", RootOutputIntents},
		{"PieceInfo", RootPieceInfo},
		{"OCProperties", RootOCProperties},
		{"Perms", RootPerms},
		{"Legal", RootLegal},
		{"Requirements", RootRequirements},
		{"Collection", RootCollection},
		{"NeedsRendering", RootNeedsRendering},
	} {
		if err := writeRootEntry(ctx, d, dictName, e.entryName, e.statsAttr); err != nil {
			return err
		}
	}

	return nil
}

func writeRootObject(ctx *Context) error {
	// => 7.7.2 Document Catalog

	xRefTable := ctx.XRefTable
	catalog := *xRefTable.Root
	objNumber := int(catalog.ObjectNumber)
	genNumber := int(catalog.GenerationNumber)

	// if log.WriteEnabled() {
	// 	log.Write.Printf("*** writeRootObject: begin offset=%d *** %s\n", ctx.Write.Offset, catalog)
	// }

	// Ensure corresponding and accurate name tree object graphs.
	if !ctx.ApplyReducedFeatureSet() {
		if err := ctx.BindNameTrees(); err != nil {
			return err
		}
	}

	d, err := xRefTable.DereferenceDict(catalog)
	if err != nil {
		return err
	}

	if d == nil {
		return errors.Errorf("pdfcpu: writeRootObject: unable to dereference root dict")
	}

	dictName := "rootDict"

	if ctx.ApplyReducedFeatureSet() {
		// log.Write.Println("writeRootObject - reducedFeatureSet:exclude complex entries.")
		d.Delete("Names")
		d.Delete("Dests")
		d.Delete("Outlines")
		d.Delete("OpenAction")
		d.Delete("StructTreeRoot")
		d.Delete("OCProperties")
	}

	if err = writeDictObject(ctx, objNumber, genNumber, d); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeRootObject: %s\n", d)
	// 	log.Write.Printf("writeRootObject: new offset after rootDict = %d\n", ctx.Write.Offset)
	// }

	if err = writeRootEntry(ctx, d, dictName, "Version", RootVersion); err != nil {
		return err
	}

	if err = writePages(ctx, d); err != nil {
		return err
	}

	if err := writeRootAttrsBatch1(ctx, d, dictName); err != nil {
		return err
	}

	if err = writeRootEntryToObjStream(ctx, d, dictName, "StructTreeRoot", RootStructTreeRoot); err != nil {
		return err
	}

	if err := writeRootAttrsBatch2(ctx, d, dictName); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("*** writeRootObject: end offset=%d ***\n", ctx.Write.Offset)
	// }

	return nil
}

func writeDirectObject(ctx *Context, o Object) error {
	switch o := o.(type) {

	case Dict:
		for k, v := range o {
			if ctx.WritingPages && (k == "Dest" || k == "D") {
				ctx.Dest = true
			}
			if _, _, err := writeDeepObject(ctx, v); err != nil {
				return err
			}
			ctx.Dest = false
		}
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeDirectObject: end offset=%d\n", ctx.Write.Offset)
		// }

	case Array:
		for i, v := range o {
			if ctx.Dest && i == 0 {
				continue
			}
			if _, _, err := writeDeepObject(ctx, v); err != nil {
				return err
			}
		}
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeDirectObject: end offset=%d\n", ctx.Write.Offset)
		// }

	default:
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeDirectObject: end, direct obj - nothing written: offset=%d\n%v\n", ctx.Write.Offset, o)
		// }
	}

	return nil
}

func writeObjectHeader(w *WriteContext, objNumber, genNumber int) (int, error) {
	return w.WriteString(fmt.Sprintf("%d %d obj%s", objNumber, genNumber, w.Eol))
}

func writeObjectTrailer(w *WriteContext) (int, error) {
	return w.WriteString(fmt.Sprintf("%sendobj%s", w.Eol, w.Eol))
}

func writeObject(ctx *Context, objNumber, genNumber int, s string) error {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeObject begin, obj#:%d gen#:%d <%s>\n", objNumber, genNumber, s)
	// }

	w := ctx.Write

	// Cleanup entry (necessary for split command)
	// TODO This is not the right place to check for an existing obj since we maybe writing NULL.
	entry, ok := ctx.FindTableEntry(objNumber, genNumber)
	if ok {
		entry.Compressed = false
	}

	// Set write-offset for this object.
	w.SetWriteOffset(objNumber)

	written, err := writeObjectHeader(w, objNumber, genNumber)
	if err != nil {
		return err
	}

	// Note: Lines that are not part of stream object data are limited to no more than 255 characters.
	i, err := w.WriteString(s)
	if err != nil {
		return err
	}

	j, err := writeObjectTrailer(w)
	if err != nil {
		return err
	}

	// Write-offset for next object.
	w.Offset += int64(written + i + j)

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeObject end, %d bytes written\n", written+i+j)
	// }

	return nil
}

const (

	// ObjectStreamMaxObjects limits the number of objects within an object stream written.
	ObjectStreamMaxObjects = 100
)

func writeTrailer(w *WriteContext) error {
	_, err := w.WriteString("%%EOF" + w.Eol)
	return err
}

func startObjectStream(ctx *Context) error {
	// See 7.5.7 Object streams
	// When new object streams and compressed objects are created, they shall always be assigned new object numbers.

	// if log.WriteEnabled() {
	// 	log.Write.Println("startObjectStream begin")
	// }

	objStreamDict := NewObjectStreamDict()

	objNr, err := ctx.InsertObject(*objStreamDict)
	if err != nil {
		return err
	}

	ctx.Write.CurrentObjStream = &objNr

	// if log.WriteEnabled() {
	// 	log.Write.Printf("startObjectStream end: %d\n", objNr)
	// }

	return nil
}

func stopObjectStream(ctx *Context) error {
	// if log.WriteEnabled() {
	// 	log.Write.Println("stopObjectStream begin")
	// }

	xRefTable := ctx.XRefTable

	if !ctx.Write.WriteToObjectStream {
		return errors.Errorf("stopObjectStream: Not writing to object stream.")
	}

	if ctx.Write.CurrentObjStream == nil {
		ctx.Write.WriteToObjectStream = false
		// if log.WriteEnabled() {
		// 	log.Write.Println("stopObjectStream end (no content)")
		// }
		return nil
	}

	entry, _ := xRefTable.FindTableEntry(*ctx.Write.CurrentObjStream, 0)
	osd, _ := (entry.Object).(ObjectStreamDictType)

	// When we are ready to write: append prolog and content
	osd.Finalize()

	// Encode objStreamDict.Content -> objStreamDict.Raw
	// and wipe (decoded) content to free up memory.
	if err := osd.StreamDict.Encode(); err != nil {
		return err
	}

	// Release memory.
	osd.Content = nil

	osd.StreamDict.Insert("First", Integer(osd.FirstObjOffset))
	osd.StreamDict.Insert("N", Integer(osd.ObjCount))

	// for each objStream execute at the end right before xRefStreamDict gets written.
	// if log.WriteEnabled() {
	// 	log.Write.Printf("stopObjectStream: objStreamDict: %s\n", osd)
	// }

	if err := writeStreamDictObject(ctx, *ctx.Write.CurrentObjStream, 0, osd.StreamDict); err != nil {
		return err
	}

	// Release memory.
	osd.Raw = nil

	ctx.Write.CurrentObjStream = nil
	ctx.Write.WriteToObjectStream = false

	// if log.WriteEnabled() {
	// 	log.Write.Println("stopObjectStream end")
	// }

	return nil
}

// SetWriteOffset saves the current write offset to the PDFDestination.
func (wc *WriteContext) SetWriteOffset(objNumber int) {
	wc.Table[objNumber] = wc.Offset
}

// HasWriteOffset returns true if an object has already been written to PDFDestination.
func (wc *WriteContext) HasWriteOffset(objNumber int) bool {
	_, found := wc.Table[objNumber]
	return found
}

func writeToObjectStream(ctx *Context, objNumber, genNumber int) (ok bool, err error) {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("addToObjectStream begin, obj#:%d gen#:%d\n", objNumber, genNumber)
	// }

	w := ctx.Write

	if ctx.WriteXRefStream && // object streams assume an xRefStream to be generated.
		ctx.WriteObjectStream && // signal for compression into object stream is on.
		ctx.Write.WriteToObjectStream && // currently writing to object stream.
		genNumber == 0 {

		if w.CurrentObjStream == nil {
			// Create new objects stream on first write.
			if err = startObjectStream(ctx); err != nil {
				return false, err
			}
		}

		objStrEntry, _ := ctx.FindTableEntry(*ctx.Write.CurrentObjStream, 0)
		objStreamDict, _ := (objStrEntry.Object).(ObjectStreamDictType)

		// Get next free index in object stream.
		i := objStreamDict.ObjCount

		// Locate the xref table entry for the object to be added to this object stream.
		entry, _ := ctx.FindTableEntry(objNumber, genNumber)

		// Turn entry into a compressed entry located in object stream at index i.
		entry.Compressed = true
		entry.ObjectStream = ctx.Write.CurrentObjStream // !
		entry.ObjectStreamInd = &i
		w.SetWriteOffset(objNumber) // for a compressed obj this is supposed to be a fake offset. value does not matter.

		// Append to prolog & content
		s := entry.Object.PDFString()
		if err = objStreamDict.AddObject(objNumber, s); err != nil {
			return false, err
		}

		objStrEntry.Object = objStreamDict

		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeObject end, obj#%d written to objectStream #%d\n", objNumber, *ctx.Write.CurrentObjStream)
		// }

		if objStreamDict.ObjCount == ObjectStreamMaxObjects {
			if err = stopObjectStream(ctx); err != nil {
				return false, err
			}
			w.WriteToObjectStream = true
		}

		ok = true

	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("addToObjectStream end, obj#:%d gen#:%d\n", objNumber, genNumber)
	// }

	return ok, nil
}

func writePDFNullObject(ctx *Context, objNumber, genNumber int) error {
	return writeObject(ctx, objNumber, genNumber, "null")
}

func writeBooleanObject(ctx *Context, objNumber, genNumber int, boolean Boolean) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	return writeObject(ctx, objNumber, genNumber, boolean.PDFString())
}

func writeNameObject(ctx *Context, objNumber, genNumber int, name NameType) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	return writeObject(ctx, objNumber, genNumber, name.PDFString())
}

func encryptAESBytes(b, key []byte) ([]byte, error) {
	// pad b to aes.Blocksize
	l := len(b) % aes.BlockSize
	c := 0x10
	if l > 0 {
		c = aes.BlockSize - l
	}
	b = append(b, bytes.Repeat([]byte{byte(c)}, aes.BlockSize-l)...)

	if len(b) < aes.BlockSize {
		return nil, errors.New("pdfcpu: encryptAESBytes: Ciphertext too short")
	}

	if len(b)%aes.BlockSize > 0 {
		return nil, errors.New("pdfcpu: encryptAESBytes: Ciphertext not a multiple of block size")
	}

	data := make([]byte, aes.BlockSize+len(b))
	iv := data[:aes.BlockSize]

	_, err := io.ReadFull(rand.Reader, iv)
	if err != nil {
		return nil, err
	}

	cb, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	mode := cipher.NewCBCEncrypter(cb, iv)
	mode.CryptBlocks(data[aes.BlockSize:], b)

	return data, nil
}

// EncryptBytes encrypts s using RC4 or AES.
func encryptBytes(b []byte, objNr, genNr int, encKey []byte, needAES bool, r int) ([]byte, error) {
	if needAES {
		k := encKey
		if r != 5 && r != 6 {
			k = decryptKey(objNr, genNr, encKey, needAES)
		}
		return encryptAESBytes(b, k)
	}

	return applyRC4CipherBytes(b, objNr, genNr, encKey, needAES)
}

func encryptStringLiteral(sl StringLiteral, objNr, genNr int, key []byte, needAES bool, r int) (*StringLiteral, error) {
	bb, err := Unescape(sl.Value())
	if err != nil {
		return nil, err
	}

	bb, err = encryptBytes(bb, objNr, genNr, key, needAES, r)
	if err != nil {
		return nil, err
	}

	s, err := Escape(string(bb))
	if err != nil {
		return nil, err
	}

	sl = StringLiteral(*s)

	return &sl, nil
}

func writeStringLiteralObject(ctx *Context, objNumber, genNumber int, sl StringLiteral) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	if ctx.EncKey != nil {
		sl1, err := encryptStringLiteral(sl, objNumber, genNumber, ctx.EncKey, ctx.AES4Strings, ctx.E.R)
		if err != nil {
			return err
		}

		sl = *sl1
	}

	return writeObject(ctx, objNumber, genNumber, sl.PDFString())
}

func encryptHexLiteral(hl HexLiteral, objNr, genNr int, key []byte, needAES bool, r int) (*HexLiteral, error) {
	bb, err := hl.Bytes()
	if err != nil {
		return nil, err
	}

	bb, err = encryptBytes(bb, objNr, genNr, key, needAES, r)
	if err != nil {
		return nil, err
	}

	hl = NewHexLiteral(bb)

	return &hl, nil
}

func writeHexLiteralObject(ctx *Context, objNumber, genNumber int, hl HexLiteral) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	if ctx.EncKey != nil {
		hl1, err := encryptHexLiteral(hl, objNumber, genNumber, ctx.EncKey, ctx.AES4Strings, ctx.E.R)
		if err != nil {
			return err
		}

		hl = *hl1
	}

	return writeObject(ctx, objNumber, genNumber, hl.PDFString())
}

func writeIntegerObject(ctx *Context, objNumber, genNumber int, integer Integer) error {
	return writeObject(ctx, objNumber, genNumber, integer.PDFString())
}

func writeFloatObject(ctx *Context, objNumber, genNumber int, float Float) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	return writeObject(ctx, objNumber, genNumber, float.PDFString())
}

func encrypt(m map[string]Object, k string, v Object, objNr, genNr int, key []byte, needAES bool, r int) error {
	s, err := encryptDeepObject(v, objNr, genNr, key, needAES, r)
	if err != nil {
		return err
	}

	if s != nil {
		m[k] = s
	}

	return nil
}

func encryptDict(d Dict, objNr, genNr int, key []byte, needAES bool, r int) error {
	isSig := false
	ft := d["FT"]
	if ft == nil {
		ft = d["Type"]
	}
	if ft != nil {
		if ftv, ok := ft.(NameType); ok && (ftv == "Sig" || ftv == "DocTimeStamp") {
			isSig = true
		}
	}
	for k, v := range d {
		if isSig && k == "Contents" {
			continue
		}
		err := encrypt(d, k, v, objNr, genNr, key, needAES, r)
		if err != nil {
			return err
		}
	}

	return nil
}

// EncryptDeepObject recurses over non trivial PDF objects and encrypts all strings encountered.
func encryptDeepObject(objIn Object, objNr, genNr int, key []byte, needAES bool, r int) (Object, error) {
	_, ok := objIn.(IndirectRef)
	if ok {
		return nil, nil
	}

	switch obj := objIn.(type) {

	case StreamDict:
		err := encryptDict(obj.Dict, objNr, genNr, key, needAES, r)
		if err != nil {
			return nil, err
		}

	case Dict:
		err := encryptDict(obj, objNr, genNr, key, needAES, r)
		if err != nil {
			return nil, err
		}

	case Array:
		for i, v := range obj {
			s, err := encryptDeepObject(v, objNr, genNr, key, needAES, r)
			if err != nil {
				return nil, err
			}
			if s != nil {
				obj[i] = s
			}
		}

	case StringLiteral:
		sl, err := encryptStringLiteral(obj, objNr, genNr, key, needAES, r)
		if err != nil {
			return nil, err
		}
		return *sl, nil

	case HexLiteral:
		hl, err := encryptHexLiteral(obj, objNr, genNr, key, needAES, r)
		if err != nil {
			return nil, err
		}
		return *hl, nil

	default:

	}

	return nil, nil
}

func writeDictObject(ctx *Context, objNumber, genNumber int, d Dict) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	if ctx.EncKey != nil {
		_, err := encryptDeepObject(d, objNumber, genNumber, ctx.EncKey, ctx.AES4Strings, ctx.E.R)
		if err != nil {
			return err
		}
	}

	return writeObject(ctx, objNumber, genNumber, d.PDFString())
}

func writeArrayObject(ctx *Context, objNumber, genNumber int, a Array) error {
	ok, err := writeToObjectStream(ctx, objNumber, genNumber)
	if err != nil {
		return err
	}

	if ok {
		return nil
	}

	if ctx.EncKey != nil {
		if _, err := encryptDeepObject(a, objNumber, genNumber, ctx.EncKey, ctx.AES4Strings, ctx.E.R); err != nil {
			return err
		}
	}

	return writeObject(ctx, objNumber, genNumber, a.PDFString())
}

func writeStream(w *WriteContext, sd StreamDict) (int64, error) {
	b, err := w.WriteString(fmt.Sprintf("%sstream%s", w.Eol, w.Eol))
	if err != nil {
		return 0, errors.Wrapf(err, "writeStream: failed to write raw content")
	}

	c, err := w.Write(sd.Raw)
	if err != nil {
		return 0, errors.Wrapf(err, "writeStream: failed to write raw content")
	}
	if int64(c) != *sd.StreamLength {
		return 0, errors.Errorf("writeStream: failed to write raw content: %d bytes written - streamlength:%d", c, *sd.StreamLength)
	}

	e, err := w.WriteString(fmt.Sprintf("%sendstream", w.Eol))
	if err != nil {
		return 0, errors.Wrapf(err, "writeStream: failed to write raw content")
	}

	written := int64(b+e) + *sd.StreamLength

	return written, nil
}

func handleIndirectLength(ctx *Context, ir *IndirectRef) error {
	objNr := int(ir.ObjectNumber)
	genNr := int(ir.GenerationNumber)

	if ctx.Write.HasWriteOffset(objNr) {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("*** handleIndirectLength: object #%d already written offset=%d ***\n", objNr, ctx.Write.Offset)
		// }
	} else {
		length, err := ctx.DereferenceInteger(*ir)
		if err != nil || length == nil {
			return err
		}
		if err = writeIntegerObject(ctx, objNr, genNr, *length); err != nil {
			return err
		}
	}

	return nil
}

func writeStreamObject(ctx *Context, objNr, genNr int, sd StreamDict, pdfString string) (int, int64, int, error) {
	h, err := writeObjectHeader(ctx.Write, objNr, genNr)
	if err != nil {
		return 0, 0, 0, err
	}

	// Note: Lines that are not part of stream object data are limited to no more than 255 characters.
	if _, err = ctx.Write.WriteString(pdfString); err != nil {
		return 0, 0, 0, err
	}

	b, err := writeStream(ctx.Write, sd)
	if err != nil {
		return 0, 0, 0, err
	}

	t, err := writeObjectTrailer(ctx.Write)
	if err != nil {
		return 0, 0, 0, err
	}

	return h, b, t, nil
}

// EncryptStream encrypts a stream buffer using RC4 or AES.
func encryptStream(buf []byte, objNr, genNr int, encKey []byte, needAES bool, r int) ([]byte, error) {
	k := encKey
	if r != 5 && r != 6 {
		k = decryptKey(objNr, genNr, encKey, needAES)
	}

	if needAES {
		return encryptAESBytes(buf, k)
	}

	return applyRC4Bytes(buf, k)
}

func writeStreamDictObject(ctx *Context, objNr, genNr int, sd StreamDict) error {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeStreamDictObject begin: object #%d\n%v", objNr, sd)
	// }

	var inObjStream bool

	if ctx.Write.WriteToObjectStream {
		inObjStream = true
		ctx.Write.WriteToObjectStream = false
	}

	// Sometimes a streamDicts length is a reference.
	if ir := sd.IndirectRefEntry("Length"); ir != nil {
		if err := handleIndirectLength(ctx, ir); err != nil {
			return err
		}
	}

	var err error

	// Unless the "Identity" crypt filter is used we have to encrypt.
	isXRefStreamDict := sd.Type() != nil && *sd.Type() == "XRef"
	if ctx.EncKey != nil &&
		!isXRefStreamDict &&
		!(len(sd.FilterPipeline) == 1 && sd.FilterPipeline[0].Name == "Crypt") {

		if sd.Raw, err = encryptStream(sd.Raw, objNr, genNr, ctx.EncKey, ctx.AES4Streams, ctx.E.R); err != nil {
			return err
		}

		l := int64(len(sd.Raw))
		sd.StreamLength = &l
		sd.Update("Length", Integer(l))
	}

	ctx.Write.SetWriteOffset(objNr)

	pdfString := sd.PDFString()

	h, b, t, err := writeStreamObject(ctx, objNr, genNr, sd, pdfString)
	if err != nil {
		return err
	}

	written := b + int64(h+len(pdfString)+t)

	ctx.Write.Offset += written
	ctx.Write.BinaryTotalSize += *sd.StreamLength

	if inObjStream {
		ctx.Write.WriteToObjectStream = true
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeStreamDictObject end: object #%d written=%d\n", objNr, written)
	// }

	return nil
}

func writeNullObject(ctx *Context, objNumber, genNumber int) error {
	// An indirect reference to nil is a corner case.
	// Still, it is an object that will be written.
	if err := writePDFNullObject(ctx, objNumber, genNumber); err != nil {
		return err
	}

	// Ensure no entry in free list.
	return ctx.UndeleteObject(objNumber)
}

func writeDeepDict(ctx *Context, d Dict, objNr, genNr int) error {
	if d.IsPage() {
		valid, err := ctx.IsObjValid(objNr, genNr)
		if err != nil {
			return err
		}
		if !valid {
			return nil
		}
	}

	if err := writeDictObject(ctx, objNr, genNr, d); err != nil {
		return err
	}

	for k, v := range d {
		if ctx.WritingPages && (k == "Dest" || k == "D") {
			ctx.Dest = true
		}
		if _, _, err := writeDeepObject(ctx, v); err != nil {
			return err
		}
		ctx.Dest = false
	}

	return nil
}

func writeDeepStreamDict(ctx *Context, sd *StreamDict, objNr, genNr int) error {
	if ctx.EncKey != nil {
		if _, err := encryptDeepObject(*sd, objNr, genNr, ctx.EncKey, ctx.AES4Strings, ctx.E.R); err != nil {
			return err
		}
	}

	if err := writeStreamDictObject(ctx, objNr, genNr, *sd); err != nil {
		return err
	}

	for _, v := range sd.Dict {
		if _, _, err := writeDeepObject(ctx, v); err != nil {
			return err
		}
	}

	return nil
}

func writeDeepArray(ctx *Context, a Array, objNr, genNr int) error {
	if err := writeArrayObject(ctx, objNr, genNr, a); err != nil {
		return err
	}

	for i, v := range a {
		if ctx.Dest && i == 0 {
			continue
		}
		if _, _, err := writeDeepObject(ctx, v); err != nil {
			return err
		}
	}

	return nil
}

func writeLazyObjectStreamObject(ctx *Context, objNr, genNr int, o LazyObjectStreamObject) error {
	data, err := o.GetData()
	if err != nil {
		return err
	}

	return writeObject(ctx, objNr, genNr, string(data))
}

func writeObjectGeneric(ctx *Context, o Object, objNr, genNr int) (err error) {
	switch o := o.(type) {

	case Dict:
		err = writeDeepDict(ctx, o, objNr, genNr)

	case StreamDict:
		err = writeDeepStreamDict(ctx, &o, objNr, genNr)

	case Array:
		err = writeDeepArray(ctx, o, objNr, genNr)

	case Integer:
		err = writeIntegerObject(ctx, objNr, genNr, o)

	case Float:
		err = writeFloatObject(ctx, objNr, genNr, o)

	case StringLiteral:
		err = writeStringLiteralObject(ctx, objNr, genNr, o)

	case HexLiteral:
		err = writeHexLiteralObject(ctx, objNr, genNr, o)

	case Boolean:
		err = writeBooleanObject(ctx, objNr, genNr, o)

	case NameType:
		err = writeNameObject(ctx, objNr, genNr, o)

	case LazyObjectStreamObject:
		err = writeLazyObjectStreamObject(ctx, objNr, genNr, o)

	default:
		err = errors.Errorf("writeIndirectObject: undefined PDF object #%d %T\n", objNr, o)
	}

	return err
}

func writeEntry(ctx *Context, d Dict, dictName, entryName string) (Object, error) {
	o, found := d.Find(entryName)
	if !found || o == nil {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeEntry end: entry %s is nil\n", entryName)
		// }
		return nil, nil
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeEntry begin: dict=%s entry=%s offset=%d\n", dictName, entryName, ctx.Write.Offset)
	// }

	o, _, err := writeDeepObject(ctx, o)
	if err != nil {
		return nil, err
	}

	if o == nil {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeEntry end: dict=%s entry=%s resolved to nil, offset=%d\n", dictName, entryName, ctx.Write.Offset)
		// }
		return nil, nil
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeEntry end: dict=%s entry=%s offset=%d\n", dictName, entryName, ctx.Write.Offset)
	// }

	return o, nil
}

func writeIndirectObject(ctx *Context, ir IndirectRef) error {
	objNr := int(ir.ObjectNumber)
	genNr := int(ir.GenerationNumber)

	if ctx.Write.HasWriteOffset(objNr) {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeIndirectObject end: object #%d already written.\n", objNr)
		// }
		return nil
	}

	o, err := ctx.DereferenceForWrite(ir)
	if err != nil {
		return errors.Wrapf(err, "writeIndirectObject: unable to dereference indirect object #%d", objNr)
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeIndirectObject: object #%d gets writeoffset: %d\n", objNr, ctx.Write.Offset)
	// }

	if o == nil {

		if err = writeNullObject(ctx, objNr, genNr); err != nil {
			return err
		}

		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeIndirectObject: end, obj#%d resolved to nil, offset=%d\n", objNr, ctx.Write.Offset)
		// }

		return nil
	}

	if err := writeObjectGeneric(ctx, o, objNr, genNr); err != nil {
		return err
	}

	return err
}

func writeDeepObject(ctx *Context, objIn Object) (objOut Object, written bool, err error) {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeDeepObject: begin offset=%d\n%s\n", ctx.Write.Offset, objIn)
	// }

	ir, ok := objIn.(IndirectRef)
	if !ok {
		return objIn, written, writeDirectObject(ctx, objIn)
	}

	if err = writeIndirectObject(ctx, ir); err == nil {
		written = true
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeDeepObject: end offset=%d\n", ctx.Write.Offset)
		// }
	}

	return objOut, written, err
}

// Write the document info object for this PDF file.
func writeDocumentInfoDict(ctx *Context) error {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("*** writeDocumentInfoDict begin: offset=%d ***\n", ctx.Write.Offset)
	// }

	// Note: The document info object is optional but pdfcpu ensures one.

	if ctx.Info == nil {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("writeDocumentInfoObject end: No info object present, offset=%d\n", ctx.Write.Offset)
		// }
		return nil
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeDocumentInfoObject: %s\n", *ctx.Info)
	// }

	o := *ctx.Info

	d, err := ctx.DereferenceDict(o)
	if err != nil || d == nil {
		return err
	}

	if _, _, err = writeDeepObject(ctx, o); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("*** writeDocumentInfoDict end: offset=%d ***\n", ctx.Write.Offset)
	// }

	return nil
}

func writeAdditionalStreams(ctx *Context) error {
	if ctx.AdditionalStreams == nil {
		return nil
	}

	if _, _, err := writeDeepObject(ctx, ctx.AdditionalStreams); err != nil {
		return err
	}

	return nil
}

func writeEncryptDict(ctx *Context) error {
	// Bail out unless we really have to write encrypted.
	if ctx.Encrypt == nil || ctx.EncKey == nil {
		return nil
	}

	indRef := *ctx.Encrypt
	objNumber := int(indRef.ObjectNumber)
	genNumber := int(indRef.GenerationNumber)

	d, err := ctx.DereferenceDict(indRef)
	if err != nil {
		return err
	}

	return writeObject(ctx, objNumber, genNumber, d.PDFString())
}

func writeObjects(ctx *Context) error {
	// Write root object(aka the document catalog) and page tree.
	if err := writeRootObject(ctx); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("offset after writeRootObject: %d\n", ctx.Write.Offset)
	// }

	// Write document information dictionary.
	if err := writeDocumentInfoDict(ctx); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("offset after writeInfoObject: %d\n", ctx.Write.Offset)
	// }

	// Write offspec additional streams as declared in pdf trailer.
	if err := writeAdditionalStreams(ctx); err != nil {
		return err
	}

	return writeEncryptDict(ctx)
}

// IsDuplicateFontObject returns true if object #i is a duplicate font object.
func (oc *OptimizationContext) IsDuplicateFontObject(i int) bool {
	return oc.DuplicateFontObjs[i]
}

// IsDuplicateImageObject returns true if object #i is a duplicate image object.
func (oc *OptimizationContext) IsDuplicateImageObject(i int) bool {
	return oc.DuplicateImageObjs[i]
}

// IsDuplicateInfoObject returns true if object #i is a duplicate info object.
func (oc *OptimizationContext) IsDuplicateInfoObject(i int) bool {
	return oc.DuplicateInfoObjects[i]
}

func deleteRedundantObject(ctx *Context, objNr int) {
	if len(ctx.Write.SelectedPages) == 0 &&
		(ctx.Optimize.IsDuplicateFontObject(objNr) || ctx.Optimize.IsDuplicateImageObject(objNr)) {
		ctx.FreeObject(objNr)
	}

	if ctx.IsLinearizationObject(objNr) || ctx.Optimize.IsDuplicateInfoObject(objNr) ||
		ctx.Read.IsObjectStreamObject(objNr) {
		ctx.FreeObject(objNr)
	}
}

func detectLinearizationObjs(xRefTable *XRefTable, entry *XRefTableEntry, i int) {
	if _, ok := entry.Object.(StreamDict); ok {

		if *entry.Offset == *xRefTable.OffsetPrimaryHintTable {
			xRefTable.LinearizationObjs[i] = true
			// if log.WriteEnabled() {
			// 	log.Write.Printf("detectLinearizationObjs: primaryHintTable at obj #%d\n", i)
			// }
		}

		if xRefTable.OffsetOverflowHintTable != nil &&
			*entry.Offset == *xRefTable.OffsetOverflowHintTable {
			xRefTable.LinearizationObjs[i] = true
			// if log.WriteEnabled() {
			// 	log.Write.Printf("detectLinearizationObjs: overflowHintTable at obj #%d\n", i)
			// }
		}

	}
}

func deleteRedundantObjects(ctx *Context) {
	if ctx.Optimize == nil {
		return
	}

	xRefTable := ctx.XRefTable

	// if log.WriteEnabled() {
	// 	log.Write.Printf("deleteRedundantObjects begin: Size=%d\n", *xRefTable.Size)
	// }

	for i := 0; i < *xRefTable.Size; i++ {

		// Missing object remains missing.
		entry, found := xRefTable.Find(i)
		if !found {
			continue
		}

		// Free object
		if entry.Free {
			continue
		}

		// Object written
		if ctx.Write.HasWriteOffset(i) {
			// Resources may be cross referenced from different objects
			// eg. font descriptors may be shared by different font dicts.
			// Try to remove this object from the list of the potential duplicate objects.
			// if log.WriteEnabled() {
			// 	log.Write.Printf("deleteRedundantObjects: remove duplicate obj #%d\n", i)
			// }
			delete(ctx.Optimize.DuplicateFontObjs, i)
			delete(ctx.Optimize.DuplicateImageObjs, i)
			delete(ctx.Optimize.DuplicateInfoObjects, i)
			continue
		}

		// Object not written

		if ctx.Read.Linearized && entry.Offset != nil {
			// This block applies to pre existing objects only.
			// Since there is no type entry for stream dicts associated with linearization dicts
			// we have to check every StreamDict that has not been written.
			detectLinearizationObjs(xRefTable, entry, i)
		}

		deleteRedundantObject(ctx, i)
	}

	// if log.WriteEnabled() {
	// 	log.Write.Println("deleteRedundantObjects end")
	// }
}

func sortedWritableKeys(ctx *Context) []int {
	var keys []int

	for i, e := range ctx.Table {
		if !ctx.Write.Increment && e.Free || ctx.Write.HasWriteOffset(i) {
			keys = append(keys, i)
		}
	}

	sort.Ints(keys)

	return keys
}

// NewXRefStreamDict creates a new PDFXRefStreamDict object.
func newXRefStreamDict(ctx *Context) *XRefStreamDict {
	sd := StreamDict{Dict: NewDict()}
	sd.Insert("Type", NameType("XRef"))
	sd.Insert("Filter", NameType(Flate))
	sd.FilterPipeline = []PDFFilter{{Name: Flate, DecodeParms: nil}}
	sd.Insert("Root", *ctx.Root)
	if ctx.Info != nil {
		sd.Insert("Info", *ctx.Info)
	}
	if ctx.ID != nil {
		sd.Insert("ID", ctx.ID)
	}
	if ctx.Encrypt != nil && ctx.EncKey != nil {
		sd.Insert("Encrypt", *ctx.Encrypt)
	}
	if ctx.Write.Increment {
		sd.Insert("Prev", Integer(*ctx.Write.OffsetPrevXRef))
	}
	return &XRefStreamDict{StreamDict: sd}
}

// int64ToBuf returns a byte slice with length byteCount representing integer i.
func int64ToBuf(i int64, byteCount int) (buf []byte) {
	j := 0
	var b []byte

	for k := i; k > 0; {
		b = append(b, byte(k&0xff))
		k >>= 8
		j++
	}

	// Swap byte order
	for i, j := 0, len(b)-1; i < j; i, j = i+1, j-1 {
		b[i], b[j] = b[j], b[i]
	}

	if j < byteCount {
		buf = append(bytes.Repeat([]byte{0}, byteCount-j), b...)
	} else {
		buf = b
	}

	return
}

func createXRefStream(ctx *Context, i1, i2, i3 int, objNrs []int) ([]byte, *Array, error) {
	// if log.WriteEnabled() {
	// 	log.Write.Println("createXRefStream begin")
	// }

	xRefTable := ctx.XRefTable

	var (
		buf []byte
		a   Array
	)

	// objCount := len(objNrs)
	// if log.WriteEnabled() {
	// 	log.Write.Printf("createXRefStream: xref has %d entries\n", objCount)
	// }

	start := objNrs[0]
	size := 0

	for i := 0; i < len(objNrs); i++ {

		j := objNrs[i]
		entry := xRefTable.Table[j]
		var s1, s2, s3 []byte

		if entry.Free {

			// unused
			// if log.WriteEnabled() {
			// 	log.Write.Printf("createXRefStream: unused i=%d nextFreeAt:%d gen:%d\n", j, int(*entry.Offset), int(*entry.Generation))
			// }

			s1 = int64ToBuf(0, i1)
			s2 = int64ToBuf(*entry.Offset, i2)
			s3 = int64ToBuf(int64(*entry.Generation), i3)

		} else if entry.Compressed {

			// in use, compressed into object stream
			// if log.WriteEnabled() {
			// 	log.Write.Printf("createXRefStream: compressed i=%d at objstr %d[%d]\n", j, int(*entry.ObjectStream), int(*entry.ObjectStreamInd))
			// }

			s1 = int64ToBuf(2, i1)
			s2 = int64ToBuf(int64(*entry.ObjectStream), i2)
			s3 = int64ToBuf(int64(*entry.ObjectStreamInd), i3)

		} else {

			off, found := ctx.Write.Table[j]
			if !found {
				return nil, nil, errors.Errorf("pdfcpu: createXRefStream: missing write offset for obj #%d\n", i)
			}

			// in use, uncompressed
			// if log.WriteEnabled() {
			// 	log.Write.Printf("createXRefStream: used i=%d offset:%d gen:%d\n", j, int(off), int(*entry.Generation))
			// }

			s1 = int64ToBuf(1, i1)
			s2 = int64ToBuf(off, i2)
			s3 = int64ToBuf(int64(*entry.Generation), i3)

		}

		// if log.WriteEnabled() {
		// 	log.Write.Printf("createXRefStream: written: %x %x %x \n", s1, s2, s3)
		// }

		buf = append(buf, s1...)
		buf = append(buf, s2...)
		buf = append(buf, s3...)

		if i > 0 && (objNrs[i]-objNrs[i-1] > 1) {

			a = append(a, Integer(start))
			a = append(a, Integer(size))

			start = objNrs[i]
			size = 1
			continue
		}

		size++
	}

	a = append(a, Integer(start))
	a = append(a, Integer(size))

	// if log.WriteEnabled() {
	// 	log.Write.Println("createXRefStream end")
	// }

	return buf, &a, nil
}

// WriteEol writes an end of line sequence.
func (wc *WriteContext) WriteEol() error {
	_, err := wc.WriteString(wc.Eol)

	return err
}

func writeXRefStream(ctx *Context) error {
	// if log.WriteEnabled() {
	// 	log.Write.Println("writeXRefStream begin")
	// }

	xRefTable := ctx.XRefTable
	xRefStreamDict := newXRefStreamDict(ctx)
	xRefTableEntry := NewXRefTableEntryGen0(*xRefStreamDict)

	// Reuse free objects (including recycled objects from this run).
	objNumber, err := xRefTable.InsertAndUseRecycled(*xRefTableEntry)
	if err != nil {
		return err
	}

	xRefStreamDict.Insert("Size", Integer(*xRefTable.Size))

	// Include xref stream dict obj within xref stream dict.
	offset := ctx.Write.Offset
	ctx.Write.SetWriteOffset(objNumber)

	i2Base := int64(*ctx.Size)
	if offset > i2Base {
		i2Base = offset
	}

	i1 := 1 // 0, 1 or 2 always fit into 1 byte.

	i2 := func(i int64) (byteCount int) {
		for i > 0 {
			i >>= 8
			byteCount++
		}
		return byteCount
	}(i2Base)

	i3 := 2 // scale for max objectstream index <= 0x ff ff

	wArr := Array{Integer(i1), Integer(i2), Integer(i3)}
	xRefStreamDict.Insert("W", wArr)

	// Generate xRefStreamDict data = xref entries -> xRefStreamDict.Content
	objNrs := sortedWritableKeys(ctx)
	content, indArr, err := createXRefStream(ctx, i1, i2, i3, objNrs)
	if err != nil {
		return err
	}

	xRefStreamDict.Content = content
	xRefStreamDict.Insert("Index", *indArr)

	// Encode xRefStreamDict.Content -> xRefStreamDict.Raw
	if err = xRefStreamDict.StreamDict.Encode(); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeXRefStream: xRefStreamDict: %s\n", xRefStreamDict)
	// }

	if err = writeStreamDictObject(ctx, objNumber, 0, xRefStreamDict.StreamDict); err != nil {
		return err
	}

	w := ctx.Write

	if _, err = w.WriteString("startxref"); err != nil {
		return err
	}

	if err = w.WriteEol(); err != nil {
		return err
	}

	if _, err = w.WriteString(fmt.Sprintf("%d", offset)); err != nil {
		return err
	}

	if err = w.WriteEol(); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Println("writeXRefStream end")
	// }

	return nil
}

func writeXRefSubsection(ctx *Context, start int, size int) error {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeXRefSubsection: start=%d size=%d\n", start, size)
	// }

	w := ctx.Write

	if _, err := w.WriteString(fmt.Sprintf("%d %d%s", start, size, w.Eol)); err != nil {
		return err
	}

	// var lines []string

	for i := start; i < start+size; i++ {

		entry := ctx.XRefTable.Table[i]

		if entry.Compressed {
			return errors.New("pdfcpu: writeXRefSubsection: compressed entries present")
		}

		var s string

		if entry.Free {
			s = fmt.Sprintf("%010d %05d f%2s", *entry.Offset, *entry.Generation, w.Eol)
		} else {
			var off int64
			writeOffset, found := ctx.Write.Table[i]
			if found {
				off = writeOffset
			}
			s = fmt.Sprintf("%010d %05d n%2s", off, *entry.Generation, w.Eol)
		}

		// lines = append(lines, fmt.Sprintf("%d: %s", i, s))

		if _, err := w.WriteString(s); err != nil {
			return err
		}
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("\n%s\n", strings.Join(lines, ""))
	// 	log.Write.Printf("writeXRefSubsection: end\n")
	// }

	return nil
}

func writeTrailerDict(ctx *Context) error {
	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeTrailerDict begin\n")
	// }

	w := ctx.Write
	xRefTable := ctx.XRefTable

	if _, err := w.WriteString("trailer"); err != nil {
		return err
	}

	if err := w.WriteEol(); err != nil {
		return err
	}

	d := NewDict()
	d.Insert("Size", Integer(*xRefTable.Size))
	d.Insert("Root", *xRefTable.Root)

	if xRefTable.Info != nil {
		d.Insert("Info", *xRefTable.Info)
	}

	if ctx.Encrypt != nil && ctx.EncKey != nil {
		d.Insert("Encrypt", *ctx.Encrypt)
	}

	if xRefTable.ID != nil {
		d.Insert("ID", xRefTable.ID)
	}

	if ctx.Write.Increment {
		d.Insert("Prev", Integer(*ctx.Write.OffsetPrevXRef))
	}

	if _, err := w.WriteString(d.PDFString()); err != nil {
		return err
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("writeTrailerDict end\n")
	// }

	return nil
}

// After inserting the last object write the cross reference table to disk.
func writeXRefTable(ctx *Context) error {
	keys := sortedWritableKeys(ctx)

	// objCount := len(keys)
	// if log.WriteEnabled() {
	// 	log.Write.Printf("xref has %d entries\n", objCount)
	// }

	if _, err := ctx.Write.WriteString("xref"); err != nil {
		return err
	}

	if err := ctx.Write.WriteEol(); err != nil {
		return err
	}

	start := keys[0]
	size := 1

	for i := 1; i < len(keys); i++ {

		if keys[i]-keys[i-1] > 1 {

			if err := writeXRefSubsection(ctx, start, size); err != nil {
				return err
			}

			start = keys[i]
			size = 1
			continue
		}

		size++
	}

	if err := writeXRefSubsection(ctx, start, size); err != nil {
		return err
	}

	if err := writeTrailerDict(ctx); err != nil {
		return err
	}

	if err := ctx.Write.WriteEol(); err != nil {
		return err
	}

	if _, err := ctx.Write.WriteString("startxref"); err != nil {
		return err
	}

	if err := ctx.Write.WriteEol(); err != nil {
		return err
	}

	if _, err := ctx.Write.WriteString(fmt.Sprintf("%d", ctx.Write.Offset)); err != nil {
		return err
	}

	return ctx.Write.WriteEol()
}

func writeXRef(ctx *Context) error {
	if ctx.WriteXRefStream {
		// Write cross reference stream and generate objectstreams.
		return writeXRefStream(ctx)
	}

	// Write cross reference table section.
	return writeXRefTable(ctx)
}

// NonReferencedObjsString returns a formatted string and the number of objs.
func (oc *OptimizationContext) NonReferencedObjsString() (int, string) {
	var s []string
	for _, o := range oc.NonReferencedObjs {
		s = append(s, fmt.Sprintf("%d", o))
	}

	return len(oc.NonReferencedObjs), strings.Join(s, ",")
}

func setFileSizeOfWrittenFile(w *WriteContext) error {
	if err := w.Flush(); err != nil {
		return err
	}

	// For in-memory/WASM-compatible operations, use the current write offset as file size
	w.FileSize = w.Offset

	return nil
}

// DuplicateInfoObjectsString returns a formatted string and the number of objs.
func (oc *OptimizationContext) DuplicateInfoObjectsString() (int, string) {
	var objs []int
	for k := range oc.DuplicateInfoObjects {
		if oc.DuplicateInfoObjects[k] {
			objs = append(objs, k)
		}
	}
	sort.Ints(objs)

	var dupInfos []string
	for _, i := range objs {
		dupInfos = append(dupInfos, fmt.Sprintf("%d", i))
	}

	return len(dupInfos), strings.Join(dupInfos, ",")
}

// DuplicateFontObjectsString returns a formatted string and the number of objs.
func (oc *OptimizationContext) DuplicateFontObjectsString() (int, string) {
	var objs []int
	for k := range oc.DuplicateFontObjs {
		if oc.DuplicateFontObjs[k] {
			objs = append(objs, k)
		}
	}
	sort.Ints(objs)

	var dupFonts []string
	for _, i := range objs {
		dupFonts = append(dupFonts, fmt.Sprintf("%d", i))
	}

	return len(dupFonts), strings.Join(dupFonts, ",")
}

// DuplicateImageObjectsString returns a formatted string and the number of objs.
func (oc *OptimizationContext) DuplicateImageObjectsString() (int, string) {
	var objs []int
	for k := range oc.DuplicateImageObjs {
		if oc.DuplicateImageObjs[k] {
			objs = append(objs, k)
		}
	}
	sort.Ints(objs)

	var dupImages []string
	for _, i := range objs {
		dupImages = append(dupImages, fmt.Sprintf("%d", i))
	}

	return len(dupImages), strings.Join(dupImages, ",")
}

// WriteContext generates a PDF file for the cross reference table contained in Context.
func CoreWriteContext(ctx *Context) (err error) {
	// Create a writer for dirname and filename if not already supplied.
	if ctx.Write.Writer == nil {
		// fileName := filepath.Join(ctx.Write.DirName, ctx.Write.FileName)
		// if log.CLIEnabled() {
		// 	log.CLI.Printf("writing to %s\n", fileName)
		// }

		// file, err := os.Create(fileName)
		// if err != nil {
		// 	return errors.Wrapf(err, "can't create %s\n%s", fileName, err)
		// }

		// ctx.Write.Writer = bufio.NewWriter(file)

		// defer func() {
		// 	// The underlying bufio.Writer has already been flushed.

		// 	// Processing error takes precedence.
		// 	if err != nil {
		// 		file.Close()
		// 		return
		// 	}

		// 	// Do not miss out on closing errors.
		// 	err = file.Close()
		// }()
	}

	if err = prepareContextForWriting(ctx); err != nil {
		return err
	}

	// if exists metadata, update from info dict
	// else if v2 create from scratch
	// else nothing just write info dict

	// We support PDF Collections (since V1.7) for file attachments
	v := V17

	if ctx.XRefTable.Version() == V20 {
		v = V20
	}

	if err = writeHeader(ctx.Write, v); err != nil {
		return err
	}

	// Ensure there is no root version.
	if ctx.RootVersion != nil {
		ctx.RootDict.Delete("Version")
	}

	// if log.WriteEnabled() {
	// 	log.Write.Printf("offset after writeHeader: %d\n", ctx.Write.Offset)
	// }

	if err := writeObjects(ctx); err != nil {
		return err
	}

	// Mark redundant objects as free.
	// eg. duplicate resources, compressed objects, linearization dicts..
	deleteRedundantObjects(ctx)

	if err = writeXRef(ctx); err != nil {
		return err
	}

	// Write pdf trailer.
	if err = writeTrailer(ctx.Write); err != nil {
		return err
	}

	if err = setFileSizeOfWrittenFile(ctx.Write); err != nil {
		return err
	}

	if ctx.Read != nil {
		ctx.Write.BinaryImageSize = ctx.Read.BinaryImageSize
		ctx.Write.BinaryFontSize = ctx.Read.BinaryFontSize
	}

	return nil
}

func WriteContextF(ctx *Context, w io.Writer) error {
	ctx.Write.Writer = bufio.NewWriter(w)
	defer ctx.Write.Flush()
	return CoreWriteContext(ctx)
}

// Optimize optimizes a PDF represented as a byte slice and returns the optimized byte slice.
func Optimize(input []byte, conf *Configuration) ([]byte, error) {
	if len(input) == 0 {
		return nil, errors.New("pdfcpu: Optimize: empty input")
	}

	if conf == nil {
		conf = NewDefaultConfiguration()
	}

	// Create reader from byte slice
	reader := bytes.NewReader(input)

	// Process PDF (read, validate, optimize)
	ctx, err := ReadValidateAndOptimize(reader, conf)
	if err != nil {
		return nil, err
	}

	// Create output buffer
	var output bytes.Buffer

	// Write optimized PDF to buffer
	if err = WriteContextF(ctx, &output); err != nil {
		return nil, err
	}

	return output.Bytes(), nil
}
