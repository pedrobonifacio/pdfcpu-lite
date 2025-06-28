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
	"compress/zlib"
	_ "embed"
	"encoding/ascii85"
	"encoding/gob"
	"encoding/hex"
	"encoding/json"
	"encoding/xml"
	"fmt"
	"image/jpeg"
	"io"
	"math"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unicode"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/hhrutter/lzw"
	"github.com/pkg/errors"
	"golang.org/x/image/ccitt"
	"golang.org/x/text/unicode/norm"
)

func RemoveControlChars(s string) string {
	return strings.Map(func(r rune) rune {
		switch r {
		case '\n', '\r', '\t', '\b', '\f':
			return -1
		default:
			return r
		}
	}, s)
}

// NewStringSet returns a new StringSet for slice.
func NewStringSet(slice []string) StringSet {
	strSet := StringSet{}
	if slice == nil {
		return strSet
	}
	for _, s := range slice {
		strSet[s] = true
	}
	return strSet
}

// Convert a 1,2 or 3 digit unescaped octal string into the corresponding byte value.
func ByteForOctalString(octalBytes string) (b byte) {
	i, _ := strconv.ParseInt(octalBytes, 8, 64)
	return byte(i)
}

// Escape applies all defined escape sequences to s.
func Escape(s string) (*string, error) {
	var b bytes.Buffer

	for i := 0; i < len(s); i++ {

		c := s[i]

		switch c {
		case 0x0A:
			c = 'n'
		case 0x0D:
			c = 'r'
		case 0x09:
			c = 't'
		case 0x08:
			c = 'b'
		case 0x0C:
			c = 'f'
		case '\\', '(', ')':
		default:
			b.WriteByte(c)
			continue
		}

		b.WriteByte('\\')
		b.WriteByte(c)
	}

	s1 := b.String()

	return &s1, nil
}

func escaped(c byte) (bool, byte) {
	switch c {
	case 'n':
		c = 0x0A
	case 'r':
		c = 0x0D
	case 't':
		c = 0x09
	case 'b':
		c = 0x08
	case 'f':
		c = 0x0C
	case '(', ')':
	case '0', '1', '2', '3', '4', '5', '6', '7':
		return true, c
	}

	return false, c
}

func regularChar(c byte, esc bool) bool {
	return c != 0x5c && !esc
}

// Unescape resolves all escape sequences of s.
func Unescape(s string) ([]byte, error) {
	var esc bool
	var longEol bool
	var octalCode string
	var b bytes.Buffer

	for i := 0; i < len(s); i++ {

		c := s[i]

		if longEol {
			esc = false
			longEol = false
			// c is completing a 0x5C0D0A line break.
			if c == 0x0A {
				continue
			}
		}

		if len(octalCode) > 0 {
			if strings.ContainsRune("01234567", rune(c)) {
				octalCode = octalCode + string(c)
				if len(octalCode) == 3 {
					b.WriteByte(ByteForOctalString(octalCode))
					octalCode = ""
					esc = false
				}
				continue
			}
			b.WriteByte(ByteForOctalString(octalCode))
			octalCode = ""
			esc = false
		}

		if regularChar(c, esc) {
			b.WriteByte(c)
			continue
		}

		if c == 0x5c { // '\'
			if !esc { // Start escape sequence.
				esc = true
			} else { // Escaped \
				if len(octalCode) > 0 {
					return nil, errors.Errorf("Unescape: illegal \\ in octal code sequence detected %X", octalCode)
				}
				b.WriteByte(c)
				esc = false
			}
			continue
		}

		// escaped = true && any other than \

		// Ignore \eol line breaks.
		if c == 0x0A {
			esc = false
			continue
		}

		if c == 0x0D {
			longEol = true
			continue
		}

		// Relax for issue 305 and also accept "\ ".
		//if !enc && !strings.ContainsRune(" nrtbf()01234567", rune(c)) {
		//	return nil, errors.Errorf("Unescape: illegal escape sequence \\%c detected: <%s>", c, s)
		//}

		var octal bool
		octal, c = escaped(c)
		if octal {
			octalCode += string(c)
			continue
		}

		b.WriteByte(c)
		esc = false
	}

	if len(octalCode) > 0 {
		b.WriteByte(ByteForOctalString(octalCode))
	}

	return b.Bytes(), nil
}

// UTF8ToCP1252 converts UTF-8 to CP1252. Unused
func UTF8ToCP1252(s string) string {
	bb := []byte{}
	for _, r := range s {
		bb = append(bb, byte(r))
	}
	return string(bb)
}

// CP1252ToUTF8 converts CP1252 to UTF-8. Unused
func CP1252ToUTF8(s string) string {
	utf8Buf := make([]byte, utf8.UTFMax)
	bb := []byte{}
	for i := 0; i < len(s); i++ {
		n := utf8.EncodeRune(utf8Buf, rune(s[i]))
		bb = append(bb, utf8Buf[:n]...)
	}
	return string(bb)
}

// Reverse reverses the runes within s.
func Reverse(s string) string {
	inRunes := []rune(norm.NFC.String(s))
	outRunes := make([]rune, len(inRunes))
	iMax := len(inRunes) - 1
	for i, r := range inRunes {
		outRunes[iMax-i] = r
	}
	return string(outRunes)
}

// needsHexSequence checks if a given character must be hex-encoded.
// See "7.3.5 Name Objects" for details.
func needsHexSequence(c byte) bool {
	switch c {
	case '(', ')', '<', '>', '[', ']', '{', '}', '/', '%', '#':
		// Delimiter characters (see "7.2.2 Character Set")
		return true
	}
	return c < '!' || c > '~'
}

// EncodeName applies name encoding according to PDF spec.
func EncodeName(s string) string {
	replaced := false
	var sb strings.Builder // will be used only if replacements are necessary
	for i := 0; i < len(s); i++ {
		ch := s[i]
		// TODO: Handle invalid character 0x00, 2nd error return value
		if needsHexSequence(ch) {
			if !replaced {
				sb.WriteString(s[:i])
			}
			sb.WriteByte('#')
			sb.WriteString(hex.EncodeToString([]byte{ch}))
			replaced = true
		} else if replaced {
			sb.WriteByte(ch)
		}
	}
	if !replaced {
		return s
	}
	return sb.String()
}

// DecodeName applies name decoding according to PDF spec.
func DecodeName(s string) (string, error) {
	replaced := false
	var sb strings.Builder // will be used only if replacements are necessary
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c == 0 {
			return "", errors.New("a name may not contain a null byte")
		} else if c != '#' {
			if replaced {
				sb.WriteByte(c)
			}
			continue
		}

		// # detected, next 2 chars have to exist.
		if len(s) < i+3 {
			return "", errors.New("not enough characters after #")
		}

		s1 := s[i+1 : i+3]

		// And they have to be hex characters.
		decoded, err := hex.DecodeString(s1)
		if err != nil {
			return "", err
		}

		if decoded[0] == 0 {
			return "", errors.New("a name may not contain a null byte")
		}

		if !replaced {
			sb.WriteString(s[:i])
			replaced = true
		}
		sb.Write(decoded)
		i += 2
	}
	if !replaced {
		return s, nil
	}
	return sb.String(), nil
}

// Dict represents a PDF dict object.
type Dict map[string]Object

// NewDict returns a new PDFDict object.
func NewDict() Dict {
	return map[string]Object{}
}

// Len returns the length of this PDFDict.
func (d Dict) Len() int {
	return len(d)
}

// Clone returns a clone of d.
func (d Dict) Clone() Object {
	d1 := NewDict()
	for k, v := range d {
		if v != nil {
			v = v.Clone()
		}
		d1.Insert(k, v)
	}
	return d1
}

// Insert adds a new entry to this PDFDict.
func (d Dict) Insert(k string, v Object) bool {
	if _, found := d.Find(k); !found {
		d[k] = v
		return true
	}
	return false
}

// InsertBool adds a new bool entry to this PDFDict.
func (d Dict) InsertBool(key string, value bool) {
	d.Insert(key, Boolean(value))
}

// InsertInt adds a new int entry to this PDFDict.
func (d Dict) InsertInt(key string, value int) {
	d.Insert(key, Integer(value))
}

// InsertFloat adds a new float entry to this PDFDict.
func (d Dict) InsertFloat(key string, value float32) {
	d.Insert(key, Float(value))
}

// InsertString adds a new string entry to this PDFDict.
func (d Dict) InsertString(key, value string) {
	d.Insert(key, StringLiteral(value))
}

// InsertName adds a new name entry to this PDFDict.
func (d Dict) InsertName(key, value string) {
	d.Insert(key, NameType(value))
}

// Update modifies an existing entry of this PDFDict.
func (d Dict) Update(key string, value Object) {
	if value != nil {
		d[key] = value
	}
}

// Find returns the Object for given key and PDFDict.
func (d Dict) Find(key string) (Object, bool) {
	v, found := d[key]
	if found {
		return v, found
	}
	for n, v := range d {
		k, err := DecodeName(n)
		if err != nil {
			return nil, false
		}
		if k == key {
			return v, true
		}
	}
	return nil, false
}

// Delete deletes the Object for given key.
func (d Dict) Delete(key string) (value Object) {
	value, found := d.Find(key)
	if !found {
		return nil
	}
	// TODO Take encoded names into account.
	delete(d, key)
	return value
}

// NewIDForPrefix returns next id with prefix.
func (d Dict) NewIDForPrefix(prefix string, i int) string {
	var id string
	found := true
	for j := i; found; j++ {
		id = prefix + strconv.Itoa(j)
		_, found = d.Find(id)
	}
	return id
}

// Entry returns the value for a given key and if the entry was found.
func (d Dict) Entry(dictName, key string, required bool) (Object, bool, error) {
	obj, found := d.Find(key)
	if !found {
		if required {
			return nil, false, errors.Errorf("dict=%s required entry=%s missing", dictName, key)
		}
		return nil, false, nil
	}

	if obj == nil {
		if required {
			return nil, true, errors.Errorf("dict=%s required entry=%s corrupt", dictName, key)
		}
	}

	return obj, found, nil
}

// BooleanEntry expects and returns a BooleanEntry for given key.
func (d Dict) BooleanEntry(key string) *bool {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	bb, ok := value.(Boolean)
	if ok {
		b := bb.Value()
		return &b
	}

	return nil
}

// StringEntry expects and returns a StringLiteral entry for given key.
func (d Dict) StringEntry(key string) *string {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	pdfStr, ok := value.(StringLiteral)
	if ok {
		s := string(pdfStr)
		return &s
	}

	return nil
}

// NameEntry expects and returns a Name entry for given key.
func (d Dict) NameEntry(key string) *string {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	name, ok := value.(NameType)
	if ok {
		s := name.Value()
		return &s
	}

	return nil
}

// IntEntry expects and returns a Integer entry for given key.
func (d Dict) IntEntry(key string) *int {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	pdfInt, ok := value.(Integer)
	if ok {
		i := int(pdfInt)
		return &i
	}

	return nil
}

// Int64Entry expects and returns a Integer entry representing an int64 value for given key.
func (d Dict) Int64Entry(key string) *int64 {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	pdfInt, ok := value.(Integer)
	if ok {
		i := int64(pdfInt)
		return &i
	}

	return nil
}

// IndirectRefEntry returns an indirectRefEntry for given key for this dictionary.
func (d Dict) IndirectRefEntry(key string) *IndirectRef {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	pdfIndRef, ok := value.(IndirectRef)
	if ok {
		return &pdfIndRef
	}

	// return err?
	return nil
}

// DictEntry expects and returns a PDFDict entry for given key.
func (d Dict) DictEntry(key string) Dict {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	// TODO resolve indirect ref.

	d, ok := value.(Dict)
	if ok {
		return d
	}

	return nil
}

// PDFFilter represents a PDF stream filter object.
type PDFFilter struct {
	Name        string
	DecodeParms Dict
}

// StreamDict represents a PDF stream dict object.
type StreamDict struct {
	Dict
	StreamOffset      int64
	StreamLength      *int64
	StreamLengthObjNr *int
	FilterPipeline    []PDFFilter
	Raw               []byte // Encoded
	Content           []byte // Decoded
	// DCTImage          image.Image
	IsPageContent bool
	CSComponents  int
}

// NewStreamDict creates a new PDFStreamDict for given PDFDict, stream offset and length.
func NewStreamDict(d Dict, streamOffset int64, streamLength *int64, streamLengthObjNr *int, filterPipeline []PDFFilter) StreamDict {
	return StreamDict{
		d,
		streamOffset,
		streamLength,
		streamLengthObjNr,
		filterPipeline,
		nil,
		nil,
		// nil,
		false,
		0,
	}
}

// Clone returns a clone of sd.
func (sd StreamDict) Clone() Object {
	sd1 := sd
	sd1.Dict = sd.Dict.Clone().(Dict)
	pl := make([]PDFFilter, len(sd.FilterPipeline))
	for k, v := range sd.FilterPipeline {
		f := PDFFilter{}
		f.Name = v.Name
		if v.DecodeParms != nil {
			f.DecodeParms = v.DecodeParms.Clone().(Dict)
		}
		pl[k] = f
	}
	sd1.FilterPipeline = pl
	return sd1
}

// HasSoleFilterNamed returns true if sd has a
// filterPipeline with 1 filter named filterName.
func (sd StreamDict) HasSoleFilterNamed(filterName string) bool {
	fpl := sd.FilterPipeline
	if fpl == nil || len(fpl) != 1 {
		return false
	}
	return fpl[0].Name == filterName
}

func (sd StreamDict) Image() bool {
	s := sd.Type()
	if s == nil || *s != "XObject" {
		return false
	}
	s = sd.Subtype()
	if s == nil || *s != "Image" {
		return false
	}
	return true
}

type DecodeLazyObjectStreamObjectFunc func(c ContextContext, s string) (Object, error)

type LazyObjectStreamObject struct {
	osd         *ObjectStreamDictType
	startOffset int
	endOffset   int

	decodeFunc    DecodeLazyObjectStreamObjectFunc
	decodedObject Object
	decodedError  error
}

func NewLazyObjectStreamObject(osd *ObjectStreamDictType, startOffset, endOffset int, decodeFunc DecodeLazyObjectStreamObjectFunc) Object {
	return LazyObjectStreamObject{
		osd:         osd,
		startOffset: startOffset,
		endOffset:   endOffset,

		decodeFunc: decodeFunc,
	}
}

func (l LazyObjectStreamObject) Clone() Object {
	return LazyObjectStreamObject{
		osd:         l.osd,
		startOffset: l.startOffset,
		endOffset:   l.endOffset,

		decodeFunc:    l.decodeFunc,
		decodedObject: l.decodedObject,
		decodedError:  l.decodedError,
	}
}

func (l LazyObjectStreamObject) PDFString() string {
	data, err := l.GetData()
	if err != nil {
		panic(err)
	}

	return string(data)
}

func (l LazyObjectStreamObject) String() string {
	return l.PDFString()
}

func (l *LazyObjectStreamObject) GetData() ([]byte, error) {
	if err := l.osd.Decode(); err != nil {
		return nil, err
	}

	var data []byte
	if l.endOffset == -1 {
		data = l.osd.Content[l.startOffset:]
	} else {
		data = l.osd.Content[l.startOffset:l.endOffset]
	}
	return data, nil
}

func (l *LazyObjectStreamObject) DecodedObject(c ContextContext) (Object, error) {
	if l.decodedObject == nil && l.decodedError == nil {
		data, err := l.GetData()
		if err != nil {
			return nil, err
		}

		l.decodedObject, l.decodedError = l.decodeFunc(c, string(data))
		if l.decodedError != nil {
			return nil, l.decodedError
		}
	}
	return l.decodedObject, l.decodedError
}

// ObjectStreamDictType represents a object stream dictionary.
type ObjectStreamDictType struct {
	StreamDict
	Prolog         []byte
	ObjCount       int
	FirstObjOffset int
	ObjArray       Array
}

type ascii85Decode struct {
	baseFilter
}

const eodASCII85 = "~>"

// Encode implements encoding for an ASCII85Decode
func (f ascii85Decode) Encode(r io.Reader) (io.Reader, error) {
	b2 := &bytes.Buffer{}
	encoder := ascii85.NewEncoder(b2)
	if _, err := io.Copy(encoder, r); err != nil {
		return nil, err
	}
	encoder.Close()

	// Add eod sequence
	b2.WriteString(eodASCII85)

	return b2, nil
}

// Decode implements decoding for an ASCII85Decode
func (f ascii85Decode) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f ascii85Decode) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	bb, err := getReaderBytes(r)
	if err != nil {
		return nil, err
	}

	// fmt.Printf("dump:\n%s", hex.Dump(bb))

	l := len(bb)
	if bb[l-1] == 0x0A || bb[l-1] == 0x0D {
		bb = bb[:l-1]
	}

	if !bytes.HasSuffix(bb, []byte(eodASCII85)) {
		return nil, errors.New("pdfcpu: Decode: missing eod marker")
	}

	// Strip eod sequence: "~>"
	bb = bb[:len(bb)-2]

	decoder := ascii85.NewDecoder(bytes.NewReader(bb))

	var b2 bytes.Buffer
	if maxLen < 0 {
		if _, err := io.Copy(&b2, decoder); err != nil {
			return nil, err
		}
	} else {
		if _, err := io.CopyN(&b2, decoder, maxLen); err != nil {
			return nil, err
		}
	}

	return &b2, nil
}

type asciiHexDecode struct {
	baseFilter
}

const eodHexDecode = '>'

// Encode implements encoding for an ASCIIHexDecode
func (f asciiHexDecode) Encode(r io.Reader) (io.Reader, error) {
	bb, err := getReaderBytes(r)
	if err != nil {
		return nil, err
	}

	dst := make([]byte, hex.EncodedLen(len(bb)))
	hex.Encode(dst, bb)

	// eod marker
	dst = append(dst, eodHexDecode)

	return bytes.NewBuffer(dst), nil
}

// Decode implements decoding for an ASCIIHexDecode
func (f asciiHexDecode) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f asciiHexDecode) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	bb, err := getReaderBytes(r)
	if err != nil {
		return nil, err
	}

	var p []byte

	// Remove any white space and cut off on eod
	for i := 0; i < len(bb); i++ {
		if bb[i] == eodHexDecode {
			break
		}
		if !bytes.ContainsRune([]byte{0x09, 0x0A, 0x0C, 0x0D, 0x20}, rune(bb[i])) {
			p = append(p, bb[i])
		}
	}

	// if len == odd add "0"
	if len(p)%2 == 1 {
		p = append(p, '0')
	}

	if maxLen < 0 {
		maxLen = int64(hex.DecodedLen(len(p)))
	}
	dst := make([]byte, maxLen)

	if _, err := hex.Decode(dst, p[:maxLen*2]); err != nil {
		return nil, err
	}

	return bytes.NewBuffer(dst), nil
}

// PDF defines the following filters. See also 7.4 in the PDF spec.
const (
	ASCII85   = "ASCII85Decode"
	ASCIIHex  = "ASCIIHexDecode"
	RunLength = "RunLengthDecode"
	LZW       = "LZWDecode"
	Flate     = "FlateDecode"
	CCITTFax  = "CCITTFaxDecode"
	JBIG2     = "JBIG2Decode"
	DCT       = "DCTDecode"
	JPX       = "JPXDecode"
)

// ErrUnsupportedFilter signals unsupported filter encountered.
var ErrUnsupportedFilter = errors.New("pdfcpu: filter not supported")

// Filter defines an interface for encoding/decoding PDF object streams.
type Filter interface {
	Encode(r io.Reader) (io.Reader, error)
	Decode(r io.Reader) (io.Reader, error)
	// DecodeLength will decode at least maxLen bytes. For filters where decoding
	// parts doesn't make sense (e.g. DCT), the whole stream is decoded.
	// If maxLen < 0 is passed, the whole stream is decoded.
	DecodeLength(r io.Reader, maxLen int64) (io.Reader, error)
}

type runLengthDecode struct {
	baseFilter
}

func (f runLengthDecode) decode(w io.ByteWriter, src []byte, maxLen int64) {
	var written int64

	for i := 0; i < len(src); {
		b := src[i]
		if b == 0x80 {
			// eod
			break
		}
		i++
		if b < 0x80 {
			c := int(b) + 1
			for j := 0; j < c; j++ {
				if maxLen >= 0 && maxLen == written {
					break
				}

				w.WriteByte(src[i])
				written++
				i++
			}
			continue
		}
		c := 257 - int(b)
		for j := 0; j < c; j++ {
			if maxLen >= 0 && maxLen == written {
				break
			}

			w.WriteByte(src[i])
			written++
		}
		i++
	}
}

func (f runLengthDecode) encode(w io.ByteWriter, src []byte) {
	const maxLen = 0x80
	const eod = 0x80

	i := 0
	b := src[i]
	start := i

	for {

		// Detect constant run eg. 0x1414141414141414
		for i < len(src) && src[i] == b && (i-start < maxLen) {
			i++
		}
		c := i - start
		if c > 1 {
			// Write constant run with length=c
			w.WriteByte(byte(257 - c))
			w.WriteByte(b)
			if i == len(src) {
				w.WriteByte(eod)
				return
			}
			b = src[i]
			start = i
			continue
		}

		// Detect variable run eg. 0x20FFD023335BCC12
		for i < len(src) && src[i] != b && (i-start < maxLen) {
			b = src[i]
			i++
		}
		if i == len(src) || i-start == maxLen {
			c = i - start
			w.WriteByte(byte(c - 1))
			for j := 0; j < c; j++ {
				w.WriteByte(src[start+j])
			}
			if i == len(src) {
				w.WriteByte(eod)
				return
			}
		} else {
			c = i - 1 - start
			// Write variable run with length=c
			w.WriteByte(byte(c - 1))
			for j := 0; j < c; j++ {
				w.WriteByte(src[start+j])
			}
			i--
		}
		b = src[i]
		start = i
	}
}

// Encode implements encoding for a RunLengthDecode
func (f runLengthDecode) Encode(r io.Reader) (io.Reader, error) {
	b1, err := getReaderBytes(r)
	if err != nil {
		return nil, err
	}

	var b2 bytes.Buffer
	f.encode(&b2, b1)

	return &b2, nil
}

// Decode implements decoding for an RunLengthDecode
func (f runLengthDecode) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f runLengthDecode) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	b1, err := getReaderBytes(r)
	if err != nil {
		return nil, err
	}

	var b2 bytes.Buffer
	f.decode(&b2, b1, maxLen)

	return &b2, nil
}

type lzwDecode struct {
	baseFilter
}

// Encode implements encoding for an LZWDecode
func (f lzwDecode) Encode(r io.Reader) (io.Reader, error) {
	var b bytes.Buffer

	ec, ok := f.parms["EarlyChange"]
	if !ok {
		ec = 1
	}

	wc := lzw.NewWriter(&b, ec == 1)
	defer wc.Close()

	_, err := io.Copy(wc, r)
	if err != nil {
		return nil, err
	}

	return &b, nil
}

// Decode implements decoding for an LZWDecode
func (f lzwDecode) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f lzwDecode) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	p, found := f.parms["Predictor"]
	if found && p > 1 {
		return nil, errors.Errorf("DecodeLZW: unsupported predictor %d", p)
	}

	ec, ok := f.parms["EarlyChange"]
	if !ok {
		ec = 1
	}

	rc := lzw.NewReader(r, ec == 1)
	defer rc.Close()

	var b bytes.Buffer
	var err error
	if maxLen < 0 {
		_, err = io.Copy(&b, rc)
	} else {
		_, err = io.CopyN(&b, rc, maxLen)
	}
	if err != nil {
		return nil, err
	}

	return &b, nil
}

// Portions of this code are based on ideas of image/png: reader.go:readImagePass
// PNG is documented here: www.w3.org/TR/PNG-Filters.html

// PDF allows a prediction step prior to compression applying TIFF or PNG prediction.
// Predictor algorithm.
const (
	PredictorNo      = 1  // No prediction.
	PredictorTIFF    = 2  // Use TIFF prediction for all rows.
	PredictorNone    = 10 // Use PNGNone for all rows.
	PredictorSub     = 11 // Use PNGSub for all rows.
	PredictorUp      = 12 // Use PNGUp for all rows.
	PredictorAverage = 13 // Use PNGAverage for all rows.
	PredictorPaeth   = 14 // Use PNGPaeth for all rows.
	PredictorOptimum = 15 // Use the optimum PNG prediction for each row.
)

// For predictor > 2 PNG filters (see RFC 2083) get applied and the first byte of each pixelrow defines
// the prediction algorithm used for all pixels of this row.
const (
	PNGNone    = 0x00
	PNGSub     = 0x01
	PNGUp      = 0x02
	PNGAverage = 0x03
	PNGPaeth   = 0x04
)

type flate struct {
	baseFilter
}

// Encode implements encoding for a Flate
func (f flate) Encode(r io.Reader) (io.Reader, error) {
	var b bytes.Buffer
	w := zlib.NewWriter(&b)
	defer w.Close()

	_, err := io.Copy(w, r)
	if err != nil {
		return nil, err
	}

	return &b, nil
}

// Decode implements decoding for a Flate
func (f flate) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f flate) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	rc, err := zlib.NewReader(r)
	if err != nil {
		return nil, err
	}
	defer rc.Close()

	// Optional decode parameters need postprocessing.
	return f.decodePostProcess(rc, maxLen)
}

func passThru(rin io.Reader, maxLen int64) (*bytes.Buffer, error) {
	var b bytes.Buffer
	var err error
	if maxLen < 0 {
		_, err = io.Copy(&b, rin)
	} else {
		_, err = io.CopyN(&b, rin, maxLen)
	}
	if err == io.ErrUnexpectedEOF {
		// Workaround for missing support for partial flush in compress/flate.
		// See also https://github.com/golang/go/issues/31514
		err = nil
	}
	return &b, err
}

func intMemberOf(i int, list []int) bool {
	for _, v := range list {
		if i == v {
			return true
		}
	}
	return false
}

// Each prediction value implies (a) certain row filter(s).
// func validateRowFilter(f, p int) error {

// 	switch p {

// 	case PredictorNone:
// 		if !intMemberOf(f, []int{PNGNone, PNGSub, PNGUp, PNGAverage, PNGPaeth}) {
// 			return errors.Errorf("pdfcpu: validateRowFilter: PredictorOptimum, unexpected row filter #%02x", f)
// 		}
// 		// if f != PNGNone {
// 		// 	return errors.Errorf("validateRowFilter: expected row filter #%02x, got: #%02x", PNGNone, f)
// 		// }

// 	case PredictorSub:
// 		if f != PNGSub {
// 			return errors.Errorf("pdfcpu: validateRowFilter: expected row filter #%02x, got: #%02x", PNGSub, f)
// 		}

// 	case PredictorUp:
// 		if f != PNGUp {
// 			return errors.Errorf("pdfcpu: validateRowFilter: expected row filter #%02x, got: #%02x", PNGUp, f)
// 		}

// 	case PredictorAverage:
// 		if f != PNGAverage {
// 			return errors.Errorf("pdfcpu: validateRowFilter: expected row filter #%02x, got: #%02x", PNGAverage, f)
// 		}

// 	case PredictorPaeth:
// 		if f != PNGPaeth {
// 			return errors.Errorf("pdfcpu: validateRowFilter: expected row filter #%02x, got: #%02x", PNGPaeth, f)
// 		}

// 	case PredictorOptimum:
// 		if !intMemberOf(f, []int{PNGNone, PNGSub, PNGUp, PNGAverage, PNGPaeth}) {
// 			return errors.Errorf("pdfcpu: validateRowFilter: PredictorOptimum, unexpected row filter #%02x", f)
// 		}

// 	default:
// 		return errors.Errorf("pdfcpu: validateRowFilter: unexpected predictor #%02x", p)

// 	}

// 	return nil
// }

func applyHorDiff(row []byte, colors int) ([]byte, error) {
	// This works for 8 bits per color only.
	for i := 1; i < len(row)/colors; i++ {
		for j := 0; j < colors; j++ {
			row[i*colors+j] += row[(i-1)*colors+j]
		}
	}
	return row, nil
}

// intSize is either 32 or 64.
// Disabled intSize 64 for govet.
const intSize = 32 //<< (^uint(0) >> 63)

func abs(x int) int {
	// m := -1 if x < 0. m := 0 otherwise.
	m := x >> (intSize - 1)

	// In two's complement representation, the negative number
	// of any number (except the smallest one) can be computed
	// by flipping all the bits and add 1. This is faster than
	// code with a branch.
	// See Hacker's Delight, section 2-4.
	return (x ^ m) - m
}

// filterPaeth applies the Paeth filter to the cdat slice.
// cdat is the current row's data, pdat is the previous row's data.
func filterPaeth(cdat, pdat []byte, bytesPerPixel int) {
	var a, b, c, pa, pb, pc int
	for i := 0; i < bytesPerPixel; i++ {
		a, c = 0, 0
		for j := i; j < len(cdat); j += bytesPerPixel {
			b = int(pdat[j])
			pa = b - c
			pb = a - c
			pc = abs(pa + pb)
			pa = abs(pa)
			pb = abs(pb)
			if pa <= pb && pa <= pc {
				// No-op.
			} else if pb <= pc {
				a = b
			} else {
				a = c
			}
			a += int(cdat[j])
			a &= 0xff
			cdat[j] = uint8(a)
			c = b
		}
	}
}

func processRow(pr, cr []byte, p, colors, bytesPerPixel int) ([]byte, error) {
	// fmt.Printf("pr(%v) =\n%s\n", &pr, hex.Dump(pr))
	// fmt.Printf("cr(%v) =\n%s\n", &cr, hex.Dump(cr))

	if p == PredictorTIFF {
		return applyHorDiff(cr, colors)
	}

	// Apply the
	cdat := cr[1:]
	pdat := pr[1:]

	// Get row filter from 1st byte
	f := int(cr[0])

	// The value of Predictor supplied by the decoding filter need not match the value
	// used when the data was encoded if they are both greater than or equal to 10.

	switch f {

	case PNGNone:
		// No operation.

	case PNGSub:
		for i := bytesPerPixel; i < len(cdat); i++ {
			cdat[i] += cdat[i-bytesPerPixel]
		}

	case PNGUp:
		for i, p := range pdat {
			cdat[i] += p
		}

	case PNGAverage:
		// The average of the two neighboring pixels (left and above).
		// Raw(x) - floor((Raw(x-bpp)+Prior(x))/2)
		for i := 0; i < bytesPerPixel; i++ {
			cdat[i] += pdat[i] / 2
		}
		for i := bytesPerPixel; i < len(cdat); i++ {
			cdat[i] += uint8((int(cdat[i-bytesPerPixel]) + int(pdat[i])) / 2)
		}

	case PNGPaeth:
		filterPaeth(cdat, pdat, bytesPerPixel)

	}

	return cdat, nil
}

func (f flate) parameters() (colors, bpc, columns int, err error) {
	// Colors, int
	// The number of interleaved colour components per sample.
	// Valid values are 1 to 4 (PDF 1.0) and 1 or greater (PDF 1.3). Default value: 1.
	// Used by PredictorTIFF only.
	colors, found := f.parms["Colors"]
	if !found {
		colors = 1
	} else if colors == 0 {
		return 0, 0, 0, errors.Errorf("pdfcpu: filter FlateDecode: \"Colors\" must be > 0")
	}

	// BitsPerComponent, int
	// The number of bits used to represent each colour component in a sample.
	// Valid values are 1, 2, 4, 8, and (PDF 1.5) 16. Default value: 8.
	// Used by PredictorTIFF only.
	bpc, found = f.parms["BitsPerComponent"]
	if !found {
		bpc = 8
	} else if !intMemberOf(bpc, []int{1, 2, 4, 8, 16}) {
		return 0, 0, 0, errors.Errorf("pdfcpu: filter FlateDecode: Unexpected \"BitsPerComponent\": %d", bpc)
	}

	// Columns, int
	// The number of samples in each row. Default value: 1.
	columns, found = f.parms["Columns"]
	if !found {
		columns = 1
	}

	return colors, bpc, columns, nil
}

func checkBufLen(b bytes.Buffer, maxLen int64) bool {
	return maxLen < 0 || int64(b.Len()) < maxLen
}

func process(w io.Writer, pr, cr []byte, predictor, colors, bytesPerPixel int) error {
	d, err := processRow(pr, cr, predictor, colors, bytesPerPixel)
	if err != nil {
		return err
	}

	_, err = w.Write(d)

	return err
}

// decodePostProcess
func (f flate) decodePostProcess(r io.Reader, maxLen int64) (io.Reader, error) {
	predictor, found := f.parms["Predictor"]
	if !found || predictor == PredictorNo {
		return passThru(r, maxLen)
	}

	if !intMemberOf(
		predictor,
		[]int{
			PredictorTIFF,
			PredictorNone,
			PredictorSub,
			PredictorUp,
			PredictorAverage,
			PredictorPaeth,
			PredictorOptimum,
		}) {
		return nil, errors.Errorf("pdfcpu: filter FlateDecode: undefined \"Predictor\" %d", predictor)
	}

	colors, bpc, columns, err := f.parameters()
	if err != nil {
		return nil, err
	}

	bytesPerPixel := (bpc*colors + 7) / 8
	rowSize := (bpc*colors*columns + 7) / 8

	m := rowSize
	if predictor != PredictorTIFF {
		// PNG prediction uses a row filter byte prefixing the pixelbytes of a row.
		m++
	}

	// cr and pr are the bytes for the current and previous row.
	cr := make([]byte, m)
	pr := make([]byte, m)

	// Output buffer
	var b bytes.Buffer

	for checkBufLen(b, maxLen) {

		// Read decompressed bytes for one pixel row.
		n, err := io.ReadFull(r, cr)
		if err != nil {
			if err != io.EOF {
				return nil, err
			}
			// eof
			if n == 0 {
				break
			}
		}

		if n != m {
			return nil, errors.Errorf("pdfcpu: filter FlateDecode: read error, expected %d bytes, got: %d", m, n)
		}

		if err := process(&b, pr, cr, predictor, colors, bytesPerPixel); err != nil {
			return nil, err
		}

		if err == io.EOF {
			break
		}

		pr, cr = cr, pr
	}

	if maxLen < 0 && b.Len()%rowSize > 0 {
		return nil, errors.New("pdfcpu: filter FlateDecode: postprocessing failed")
	}

	return &b, nil
}

type ccittDecode struct {
	baseFilter
}

// Encode implements encoding for a CCITTDecode
func (f ccittDecode) Encode(r io.Reader) (io.Reader, error) {
	// TODO
	return nil, nil
}

// Decode implements decoding for a CCITTDecode
func (f ccittDecode) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f ccittDecode) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	var ok bool

	// <0 : Pure two-dimensional encoding (Group 4)
	// =0 : Pure one-dimensional encoding (Group 3, 1-D)
	// >0 : Mixed one- and two-dimensional encoding (Group 3, 2-D)
	k := 0
	k, ok = f.parms["K"]
	if ok && k > 0 {
		return nil, errors.New("pdfcpu: filter CCITTFax k > 0 currently unsupported")
	}

	cols := 1728
	col, ok := f.parms["Columns"]
	if ok {
		cols = col
	}

	rows, ok := f.parms["Rows"]
	if !ok {
		return nil, errors.New("pdfcpu: ccitt: missing DecodeParam \"Rows\"")
	}

	blackIs1 := false
	v, ok := f.parms["BlackIs1"]
	if ok && v == 1 {
		blackIs1 = true
	}

	encodedByteAlign := false
	v, ok = f.parms["EncodedByteAlign"]
	if ok && v == 1 {
		encodedByteAlign = true
	}

	opts := &ccitt.Options{Invert: blackIs1, Align: encodedByteAlign}

	mode := ccitt.Group3
	if k < 0 {
		mode = ccitt.Group4
	}
	rd := ccitt.NewReader(r, ccitt.MSB, mode, cols, rows, opts)

	var b bytes.Buffer
	_, err := io.Copy(&b, rd)
	if err != nil {
		return nil, err
	}

	return &b, nil
}

type dctDecode struct {
	baseFilter
}

// Encode implements encoding for a DCTDecode
func (f dctDecode) Encode(r io.Reader) (io.Reader, error) {
	return nil, nil
}

// Decode implements decoding for a DCTDecode
func (f dctDecode) Decode(r io.Reader) (io.Reader, error) {
	return f.DecodeLength(r, -1)
}

func (f dctDecode) DecodeLength(r io.Reader, maxLen int64) (io.Reader, error) {
	im, err := jpeg.Decode(r)
	if err != nil {
		return nil, err
	}

	var b bytes.Buffer

	enc := gob.NewEncoder(&b)

	if err := enc.Encode(im); err != nil {
		return nil, err
	}

	return &b, nil
}

// NewFilter returns a filter for given filterName and an optional parameter dictionary.
func NewFilter(filterName string, parms map[string]int) (filter Filter, err error) {
	switch filterName {

	case ASCII85:
		filter = ascii85Decode{baseFilter{}}

	case ASCIIHex:
		filter = asciiHexDecode{baseFilter{}}

	case RunLength:
		filter = runLengthDecode{baseFilter{parms}}

	case LZW:
		filter = lzwDecode{baseFilter{parms}}

	case Flate:
		filter = flate{baseFilter{parms}}

	case CCITTFax:
		filter = ccittDecode{baseFilter{parms}}

	case DCT:
		filter = dctDecode{baseFilter{parms}}

	case JBIG2:
		// Unsupported
		fallthrough

	case JPX:
		// Unsupported
		err = ErrUnsupportedFilter

	default:
		err = errors.Errorf("Invalid filter: <%s>", filterName)
	}

	return filter, err
}

// List return the list of all supported PDF filters.
func List() []string {
	// Exclude CCITTFax, DCT, JBIG2 & JPX since they only makes sense in the context of image processing.
	return []string{ASCII85, ASCIIHex, RunLength, LZW, Flate}
}

type baseFilter struct {
	parms map[string]int
}

func SupportsDecodeParms(f string) bool {
	return f == CCITTFax || f == LZW || f == Flate
}

func getReaderBytes(r io.Reader) ([]byte, error) {
	var bb []byte
	if buf, ok := r.(*bytes.Buffer); ok {
		bb = buf.Bytes()
	} else {
		var buf bytes.Buffer
		if _, err := io.Copy(&buf, r); err != nil {
			return nil, err
		}

		bb = buf.Bytes()
	}

	return bb, nil
}

// NewObjectStreamDict creates a new ObjectStreamDictType object.
func NewObjectStreamDict() *ObjectStreamDictType {
	sd := StreamDict{Dict: NewDict()}
	sd.Insert("Type", NameType("ObjStm"))
	sd.Insert("Filter", NameType(Flate))
	sd.FilterPipeline = []PDFFilter{{Name: Flate, DecodeParms: nil}}
	return &ObjectStreamDictType{StreamDict: sd}
}

func parmsForFilter(d Dict) map[string]int {
	m := map[string]int{}

	if d == nil {
		return m
	}

	for k, v := range d {

		i, ok := v.(Integer)
		if ok {
			m[k] = i.Value()
			continue
		}

		// Encode boolean values: false -> 0, true -> 1
		b, ok := v.(Boolean)
		if ok {
			m[k] = 0
			if b.Value() {
				m[k] = 1
			}
			continue
		}

	}

	return m
}

// Encode applies sd's filter pipeline to sd.Content in order to produce sd.Raw.
func (sd *StreamDict) Encode() error {
	if sd.Content == nil && sd.Raw != nil {
		// Not decoded yet, no need to encode.
		return nil
	}

	// No filter specified, nothing to encode.
	if sd.FilterPipeline == nil {
		sd.Raw = sd.Content
		streamLength := int64(len(sd.Raw))
		sd.StreamLength = &streamLength
		sd.Update("Length", Integer(streamLength))
		return nil
	}

	var b, c io.Reader
	b = bytes.NewReader(sd.Content)

	// Apply each filter in the pipeline to result of preceding

	for i := len(sd.FilterPipeline) - 1; i >= 0; i-- {
		f := sd.FilterPipeline[i]

		// Make parms map[string]int
		parms := parmsForFilter(f.DecodeParms)

		fi, err := NewFilter(f.Name, parms)
		if err != nil {
			return err
		}

		c, err = fi.Encode(b)
		if err != nil {
			return err
		}

		b = c
	}

	if bb, ok := c.(*bytes.Buffer); ok {
		sd.Raw = bb.Bytes()
	} else {
		var buf bytes.Buffer
		if _, err := io.Copy(&buf, c); err != nil {
			return err
		}

		sd.Raw = buf.Bytes()
	}

	streamLength := int64(len(sd.Raw))
	sd.StreamLength = &streamLength
	sd.Update("Length", Integer(streamLength))

	return nil
}

func fixParms(f PDFFilter, parms map[string]int, sd *StreamDict) error {
	if f.Name == CCITTFax {
		// x/image/ccitt needs the optional decode parameter "Rows"
		// if not available we supply image "Height".
		_, ok := parms["Rows"]
		if !ok {
			ip := sd.IntEntry("Height")
			if ip == nil {
				return errors.New("pdfcpu: ccitt: \"Height\" required")
			}
			parms["Rows"] = *ip
		}
	}
	return nil
}

// Decode applies sd's filter pipeline to sd.Raw in order to produce sd.Content.
func (sd *StreamDict) Decode() error {
	_, err := sd.DecodeLength(-1)
	return err
}

func (sd *StreamDict) decodeLength(maxLen int64) ([]byte, error) {
	var b, c io.Reader
	b = bytes.NewReader(sd.Raw)

	// Apply each filter in the pipeline to result of preceding
	for idx, f := range sd.FilterPipeline {

		if f.Name == JPX {
			break
		}

		if f.Name == DCT {
			if sd.CSComponents != 4 {
				break
			}
			// if sd.CSComponents == 4 {
			// 	// Special case where we have to do real JPG decoding.
			// 	// Another option is using a dctDecode filter using gob - performance hit?

			// 	im, err := jpeg.Decode(b)
			//  if err != nil {
			// 	 	return err
			// 	}
			// 	sd.DCTImage = im // hacky
			// 	return nil
			// }
		}

		parms := parmsForFilter(f.DecodeParms)
		if err := fixParms(f, parms, sd); err != nil {
			return nil, err
		}

		fi, err := NewFilter(f.Name, parms)
		if err != nil {
			return nil, err
		}

		if maxLen >= 0 && idx == len(sd.FilterPipeline)-1 {
			c, err = fi.DecodeLength(b, maxLen)
		} else {
			c, err = fi.Decode(b)
		}
		if err != nil {
			return nil, err
		}

		// fmt.Printf("decodedStream after:%s\n%s\n", f.Name, hex.Dump(c.Bytes()))
		b = c
	}

	var data []byte
	if bb, ok := c.(*bytes.Buffer); ok {
		data = bb.Bytes()
	} else {
		var buf bytes.Buffer
		if _, err := io.Copy(&buf, c); err != nil {
			return nil, err
		}

		data = buf.Bytes()
	}

	if maxLen < 0 {
		sd.Content = data
		return data, nil
	}

	return data[:maxLen], nil
}

func (sd *StreamDict) DecodeLength(maxLen int64) ([]byte, error) {
	if sd.Content != nil {
		// This stream has already been decoded.
		if maxLen < 0 {
			return sd.Content, nil
		}

		return sd.Content[:maxLen], nil
	}

	fpl := sd.FilterPipeline

	// No filter or sole filter DTC && !CMYK or JPX - nothing to decode.
	if fpl == nil || len(fpl) == 1 && ((fpl[0].Name == DCT && sd.CSComponents != 4) || fpl[0].Name == JPX) {
		sd.Content = sd.Raw
		// fmt.Printf("decodedStream returning %d(#%02x)bytes: \n%s\n", len(sd.Content), len(sd.Content), hex.Dump(sd.Content))
		if maxLen < 0 {
			return sd.Content, nil
		}

		return sd.Content[:maxLen], nil
	}

	// fmt.Printf("decodedStream before:\n%s\n", hex.Dump(sd.Raw))

	return sd.decodeLength(maxLen)
}

// IndexedObject returns the object at given index from a ObjectStreamDictType.
func (osd *ObjectStreamDictType) IndexedObject(index int) (Object, error) {
	if osd.ObjArray == nil || index < 0 || index >= len(osd.ObjArray) {
		return nil, errors.Errorf("IndexedObject(%d): object not available", index)
	}
	return osd.ObjArray[index], nil
}

// AddObject adds another object to this object stream.
// Relies on decoded content!
func (osd *ObjectStreamDictType) AddObject(objNumber int, pdfString string) error {
	offset := len(osd.Content)
	s := ""
	if osd.ObjCount > 0 {
		s = " "
	}
	s = s + fmt.Sprintf("%d %d", objNumber, offset)
	osd.Prolog = append(osd.Prolog, []byte(s)...)
	// pdfString := entry.Object.PDFString()
	osd.Content = append(osd.Content, []byte(pdfString)...)
	osd.ObjCount++
	return nil
}

// Finalize prepares the final content of the objectstream.
func (osd *ObjectStreamDictType) Finalize() {
	osd.Content = append(osd.Prolog, osd.Content...)
	osd.FirstObjOffset = len(osd.Prolog)
}

// XRefStreamDict represents a cross reference stream dictionary.
type XRefStreamDict struct {
	StreamDict
	Size           int
	Objects        []int
	W              [3]int
	PreviousOffset *int64
}

// StreamDictEntry expects and returns a StreamDict entry for given key.
// unused.
func (d Dict) StreamDictEntry(key string) *StreamDict {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	sd, ok := value.(StreamDict)
	if ok {
		return &sd
	}

	return nil
}

// ArrayEntry expects and returns a Array entry for given key.
func (d Dict) ArrayEntry(key string) Array {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	a, ok := value.(Array)
	if ok {
		return a
	}

	return nil
}

// StringLiteralEntry returns a StringLiteral object for given key.
func (d Dict) StringLiteralEntry(key string) *StringLiteral {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	s, ok := value.(StringLiteral)
	if ok {
		return &s
	}

	return nil
}

// ErrInvalidUTF16BE represents an error that gets raised for invalid UTF-16BE byte sequences.
var ErrInvalidUTF16BE = errors.New("pdfcpu: invalid UTF-16BE detected")

// IsStringUTF16BE checks a string for Big Endian byte order BOM.
func IsStringUTF16BE(s string) bool {
	s1 := fmt.Sprint(s)
	ok := strings.HasPrefix(s1, "\376\377") // 0xFE 0xFF
	return ok
}

// IsUTF16BE checks for Big Endian byte order mark and valid length.
func IsUTF16BE(b []byte) bool {
	if len(b) == 0 || len(b)%2 != 0 {
		return false
	}
	// Check BOM
	return b[0] == 0xFE && b[1] == 0xFF
}

func decodeUTF16String(b []byte) (string, error) {
	// Convert UTF-16 to UTF-8
	// We only accept big endian byte order.
	if !IsUTF16BE(b) {
		return "", ErrInvalidUTF16BE
	}

	// Strip BOM.
	b = b[2:]

	// code points
	u16 := make([]uint16, 0, len(b))

	// Collect code points.
	for i := 0; i < len(b); {

		val := (uint16(b[i]) << 8) + uint16(b[i+1])

		if val <= 0xD7FF || val > 0xE000 {
			// Basic Multilingual Plane
			u16 = append(u16, val)
			i += 2
			continue
		}

		// Ensure bytes needed in order to decode surrogate pair.
		if i+2 >= len(b) {
			return "", errors.Errorf("decodeUTF16String: corrupt UTF16BE byte length on unicode point 1: %v", b)
		}

		// Ensure high surrogate is leading in possible surrogate pair.
		if val >= 0xDC00 && val <= 0xDFFF {
			return "", errors.Errorf("decodeUTF16String: corrupt UTF16BE on unicode point 1: %v", b)
		}

		// Supplementary Planes
		u16 = append(u16, val)
		val = (uint16(b[i+2]) << 8) + uint16(b[i+3])
		if val < 0xDC00 || val > 0xDFFF {
			return "", errors.Errorf("decodeUTF16String: corrupt UTF16BE on unicode point 2: %v", b)
		}

		u16 = append(u16, val)
		i += 4
	}

	decb := []byte{}
	utf8Buf := make([]byte, utf8.UTFMax)

	for _, rune := range utf16.Decode(u16) {
		n := utf8.EncodeRune(utf8Buf, rune)
		decb = append(decb, utf8Buf[:n]...)
	}

	return string(decb), nil
}

// DecodeUTF16String decodes a UTF16BE string from a hex string.
func DecodeUTF16String(s string) (string, error) {
	return decodeUTF16String([]byte(s))
}

func EncodeUTF16String(s string) string {
	rr := utf16.Encode([]rune(s))
	bb := []byte{0xFE, 0xFF}
	for _, r := range rr {
		bb = append(bb, byte(r>>8), byte(r&0xFF))
	}
	return string(bb)
}

func EscapedUTF16String(s string) (*string, error) {
	return Escape(EncodeUTF16String(s))
}

// StringLiteralToString returns the best possible string rep for a string literal.
func StringLiteralToString(sl StringLiteral) (string, error) {
	bb, err := Unescape(sl.Value())
	if err != nil {
		return "", err
	}
	if IsUTF16BE(bb) {
		return decodeUTF16String(bb)
	}
	// if no acceptable UTF16 encoding found, ensure utf8 encoding.
	bb = bytes.TrimPrefix(bb, []byte{239, 187, 191})
	s := string(bb)
	if !utf8.ValidString(s) {
		s = CP1252ToUTF8(s)
	}
	return s, nil
}

// HexLiteralToString returns a possibly UTF16 encoded string for a hex string.
func HexLiteralToString(hl HexLiteral) (string, error) {
	bb, err := hl.Bytes()
	if err != nil {
		return "", err
	}
	if IsUTF16BE(bb) {
		return decodeUTF16String(bb)
	}

	bb, err = Unescape(string(bb))
	if err != nil {
		return "", err
	}

	bb = bytes.TrimPrefix(bb, []byte{239, 187, 191})

	return string(bb), nil
}

func StringOrHexLiteral(obj Object) (*string, error) {
	if sl, ok := obj.(StringLiteral); ok {
		s, err := StringLiteralToString(sl)
		return &s, err
	}
	if hl, ok := obj.(HexLiteral); ok {
		s, err := HexLiteralToString(hl)
		return &s, err
	}
	return nil, errors.New("pdfcpu: expected StringLiteral or HexLiteral")
}

// HexLiteralEntry returns a HexLiteral object for given key.
func (d Dict) HexLiteralEntry(key string) *HexLiteral {
	value, found := d.Find(key)
	if !found {
		return nil
	}

	s, ok := value.(HexLiteral)
	if ok {
		return &s
	}

	return nil
}

func (d Dict) StringOrHexLiteralEntry(key string) (*string, error) {
	if obj, ok := d.Find(key); ok {
		return StringOrHexLiteral(obj)
	}
	return nil, nil
}

// Length returns a *int64 for entry with key "Length".
// Stream length may be referring to an indirect object.
func (d Dict) Length() (*int64, *int) {
	val := d.Int64Entry("Length")
	if val != nil {
		return val, nil
	}

	indirectRef := d.IndirectRefEntry("Length")
	if indirectRef == nil {
		return nil, nil
	}

	intVal := indirectRef.ObjectNumber.Value()

	return nil, &intVal
}

// Type returns the value of the name entry for key "Type".
func (d Dict) Type() *string {
	return d.NameEntry("Type")
}

// Subtype returns the value of the name entry for key "Subtype".
func (d Dict) Subtype() *string {
	return d.NameEntry("Subtype")
}

// Size returns the value of the int entry for key "Size"
func (d Dict) Size() *int {
	return d.IntEntry("Size")
}

func (d Dict) IsPage() bool {
	return d.Type() != nil && *d.Type() == "Page"
}

// IsObjStm returns true if given PDFDict is an object stream.
func (d Dict) IsObjStm() bool {
	return d.Type() != nil && *d.Type() == "ObjStm"
}

// W returns a *Array for key "W".
func (d Dict) W() Array {
	return d.ArrayEntry("W")
}

// Prev returns the previous offset.
func (d Dict) Prev() *int64 {
	return d.Int64Entry("Prev")
}

// Index returns a *Array for key "Index".
func (d Dict) Index() Array {
	return d.ArrayEntry("Index")
}

// N returns a *int for key "N".
func (d Dict) N() *int {
	return d.IntEntry("N")
}

// First returns a *int for key "First".
func (d Dict) First() *int {
	return d.IntEntry("First")
}

// IsLinearizationParmDict returns true if this dict has an int entry for key "Linearized".
func (d Dict) IsLinearizationParmDict() bool {
	return d.IntEntry("Linearized") != nil
}

// IncrementBy increments the integer value for given key by i.
func (d *Dict) IncrementBy(key string, i int) error {
	v := d.IntEntry(key)
	if v == nil {
		return errors.Errorf("IncrementBy: unknown key: %s", key)
	}
	*v += i
	d.Update(key, Integer(*v))
	return nil
}

// Increment increments the integer value for given key.
func (d *Dict) Increment(key string) error {
	return d.IncrementBy(key, 1)
}

func (d Dict) indentedString(level int) string {
	logstr := []string{"<<\n"}
	tabstr := strings.Repeat("\t", level)

	var keys []string
	for k := range d {
		keys = append(keys, k)
	}
	sort.Strings(keys)

	for _, k := range keys {

		v := d[k]

		switch v := v.(type) {
		case Dict:
			dictStr := v.indentedString(level + 1)
			logstr = append(logstr, fmt.Sprintf("%s<%s, %s>\n", tabstr, k, dictStr))
		case Array:
			arrStr := v.indentedString(level + 1)
			logstr = append(logstr, fmt.Sprintf("%s<%s, %s>\n", tabstr, k, arrStr))
		default:
			val := "null"
			if v != nil {
				val = v.String()
				if n, ok := v.(NameType); ok {
					val, _ = DecodeName(string(n))
				}
			}

			logstr = append(logstr, fmt.Sprintf("%s<%s, %v>\n", tabstr, k, val))
		}
	}

	logstr = append(logstr, fmt.Sprintf("%s%s", strings.Repeat("\t", level-1), ">>"))

	return strings.Join(logstr, "")
}

// PDFString returns a string representation as found in and written to a PDF file.
func (d Dict) PDFString() string {
	logstr := []string{} // make([]string, 20)
	logstr = append(logstr, "<<")

	var keys []string
	for k := range d {
		keys = append(keys, k)
	}
	sort.Strings(keys)

	for _, k := range keys {

		v := d[k]
		keyName := EncodeName(k)

		switch v := v.(type) {
		case nil:
			logstr = append(logstr, fmt.Sprintf("/%s null", keyName))
		case Dict:
			logstr = append(logstr, fmt.Sprintf("/%s%s", keyName, v.PDFString()))
		case Array:
			logstr = append(logstr, fmt.Sprintf("/%s%s", keyName, v.PDFString()))
		case IndirectRef:
			logstr = append(logstr, fmt.Sprintf("/%s %s", keyName, v.PDFString()))
		case NameType:
			logstr = append(logstr, fmt.Sprintf("/%s%s", keyName, v.PDFString()))
		case Integer:
			logstr = append(logstr, fmt.Sprintf("/%s %s", keyName, v.PDFString()))
		case Float:
			logstr = append(logstr, fmt.Sprintf("/%s %s", keyName, v.PDFString()))
		case Boolean:
			logstr = append(logstr, fmt.Sprintf("/%s %s", keyName, v.PDFString()))
		case StringLiteral:
			logstr = append(logstr, fmt.Sprintf("/%s%s", keyName, v.PDFString()))
		case HexLiteral:
			logstr = append(logstr, fmt.Sprintf("/%s%s", keyName, v.PDFString()))
		default:
			// if log.InfoEnabled() {
			// 	log.Info.Fatalf("PDFDict.PDFString(): entry of unknown object type: %T %[1]v\n", v)
			// }
		}
	}

	logstr = append(logstr, ">>")
	return strings.Join(logstr, "")
}

func (d Dict) String() string {
	return d.indentedString(1)
}

// StringEntryBytes returns the byte slice representing the string value for key.
func (d Dict) StringEntryBytes(key string) ([]byte, error) {
	s := d.StringLiteralEntry(key)
	if s != nil {
		bb, err := Unescape(s.Value())
		if err != nil {
			return nil, err
		}
		return bb, nil
	}

	h := d.HexLiteralEntry(key)
	if h != nil {
		return h.Bytes()
	}

	return nil, nil
}

// Array represents a PDF array object.
type Array []Object

// NewStringLiteralArray returns a PDFArray with StringLiteral entries.
func NewStringLiteralArray(sVars ...string) Array {
	a := Array{}

	for _, s := range sVars {
		a = append(a, StringLiteral(s))
	}

	return a
}

// NewHexLiteralArray returns a PDFArray with HexLiteralLiteral entries.
func NewHexLiteralArray(sVars ...string) Array {
	a := Array{}

	for _, s := range sVars {
		a = append(a, NewHexLiteral([]byte(s)))
	}

	return a
}

// NewNameArray returns a PDFArray with Name entries.
func NewNameArray(sVars ...string) Array {
	a := Array{}

	for _, s := range sVars {
		a = append(a, NameType(s))
	}

	return a
}

// NewNumberArray returns a PDFArray with Float entries.
func NewNumberArray(fVars ...float64) Array {
	a := Array{}

	for _, f := range fVars {
		a = append(a, Float(f))
	}

	return a
}

// NewIntegerArray returns a PDFArray with Integer entries.
func NewIntegerArray(fVars ...int) Array {
	a := Array{}

	for _, f := range fVars {
		a = append(a, Integer(f))
	}

	return a
}

// Clone returns a clone of a.
func (a Array) Clone() Object {
	a1 := Array(make([]Object, len(a)))
	for k, v := range a {
		if v != nil {
			v = v.Clone()
		}
		a1[k] = v
	}
	return a1
}

func (a Array) indentedString(level int) string {
	logstr := []string{"["}
	tabstr := strings.Repeat("\t", level)
	first := true
	sepstr := ""

	for _, entry := range a {

		if first {
			first = false
			sepstr = ""
		} else {
			sepstr = " "
		}

		switch entry := entry.(type) {
		case Dict:
			dictstr := entry.indentedString(level + 1)
			logstr = append(logstr, fmt.Sprintf("\n%[1]s%[2]s\n%[1]s", tabstr, dictstr))
			first = true
		case Array:
			arrstr := entry.indentedString(level + 1)
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, arrstr))
		default:
			v := "null"
			if entry != nil {
				v = entry.String()
				if n, ok := entry.(NameType); ok {
					v, _ = DecodeName(string(n))
				}
			}

			logstr = append(logstr, fmt.Sprintf("%s%v", sepstr, v))
		}
	}

	logstr = append(logstr, "]")

	return strings.Join(logstr, "")
}

func (a Array) String() string {
	return a.indentedString(1)
}

// PDFString returns a string representation as found in and written to a PDF file.
func (a Array) PDFString() string {
	logstr := []string{}
	logstr = append(logstr, "[")
	first := true
	var sepstr string

	for _, entry := range a {

		if first {
			first = false
			sepstr = ""
		} else {
			sepstr = " "
		}

		switch entry := entry.(type) {
		case nil:
			logstr = append(logstr, fmt.Sprintf("%snull", sepstr))
		case Dict:
			logstr = append(logstr, entry.PDFString())
		case Array:
			logstr = append(logstr, entry.PDFString())
		case IndirectRef:
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, entry.PDFString()))
		case NameType:
			logstr = append(logstr, entry.PDFString())
		case Integer:
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, entry.PDFString()))
		case Float:
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, entry.PDFString()))
		case Boolean:
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, entry.PDFString()))
		case StringLiteral:
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, entry.PDFString()))
		case HexLiteral:
			logstr = append(logstr, fmt.Sprintf("%s%s", sepstr, entry.PDFString()))
		default:
			// if log.InfoEnabled() {
			// 	log.Info.Fatalf("PDFArray.PDFString(): entry of unknown object type: %[1]T %[1]v\n", entry)
			// }
		}
	}

	logstr = append(logstr, "]")

	return strings.Join(logstr, "")
}

// See table 22 - User access permissions
type PermissionFlags int

// DisplayUnit is the metric unit used to output paper sizes.
type DisplayUnit int

// Supported line delimiters
const (
	EolLF   = "\x0A"
	EolCR   = "\x0D"
	EolCRLF = "\x0D\x0A"
)

// FreeHeadGeneration is the predefined generation number for the head of the free list.
const FreeHeadGeneration = 65535

// ByteSize represents the various terms for storage space.
type ByteSize float64

// Storage space terms.
const (
	_           = iota // ignore first value by assigning to blank identifier
	KB ByteSize = 1 << (10 * iota)
	MB
	GB
)

func (b ByteSize) String() string {
	switch {
	case b >= GB:
		return fmt.Sprintf("%.2f GB", b/GB)
	case b >= MB:
		return fmt.Sprintf("%.1f MB", b/MB)
	case b >= KB:
		return fmt.Sprintf("%.0f KB", b/KB)
	}

	return fmt.Sprintf("%.0f", b)
}

// IntSet is a set of integers.
type IntSet map[int]bool

// StringSet is a set of strings.
type StringSet map[string]bool

// Object defines an interface for all Objects.
type Object interface {
	fmt.Stringer
	Clone() Object
	PDFString() string
}

// Boolean represents a PDF boolean object.
type Boolean bool

// Clone returns a clone of boolean.
func (boolean Boolean) Clone() Object {
	return boolean
}

func (boolean Boolean) String() string {
	return fmt.Sprintf("%v", bool(boolean))
}

// PDFString returns a string representation as found in and written to a PDF file.
func (boolean Boolean) PDFString() string {
	return boolean.String()
}

// Value returns a bool value for this PDF object.
func (boolean Boolean) Value() bool {
	return bool(boolean)
}

///////////////////////////////////////////////////////////////////////////////////

// Float represents a PDF float object.
type Float float64

// Clone returns a clone of f.
func (f Float) Clone() Object {
	return f
}

func (f Float) String() string {
	// Use a precision of 2 for logging readability.
	return fmt.Sprintf("%.2f", float64(f))
}

// PDFString returns a string representation as found in and written to a PDF file.
func (f Float) PDFString() string {
	// The max precision encountered so far has been 12 (fontType3 fontmatrix components).
	return strconv.FormatFloat(f.Value(), 'f', 12, 64)
}

// Value returns a float64 value for this PDF object.
func (f Float) Value() float64 {
	return float64(f)
}

///////////////////////////////////////////////////////////////////////////////////

// Integer represents a PDF integer object.
type Integer int

// Clone returns a clone of i.
func (i Integer) Clone() Object {
	return i
}

func (i Integer) String() string {
	return strconv.Itoa(int(i))
}

// PDFString returns a string representation as found in and written to a PDF file.
func (i Integer) PDFString() string {
	return i.String()
}

// Value returns an int value for this PDF object.
func (i Integer) Value() int {
	return int(i)
}

///////////////////////////////////////////////////////////////////////////////////

// Point represents a user space location.
type Point struct {
	X float64 `json:"x"`
	Y float64 `json:"y"`
}

func NewPoint(x, y float64) Point {
	return Point{X: x, Y: y}
}

// Translate modifies p's coordinates.
func (p *Point) Translate(dx, dy float64) {
	p.X += dx
	p.Y += dy
}

func (p Point) String() string {
	return fmt.Sprintf("(%.2f,%.2f)\n", p.X, p.Y)
}

// Rectangle represents a rectangular region in userspace.
type Rectangle struct {
	LL Point `json:"ll"`
	UR Point `json:"ur"`
}

// NewRectangle returns a new rectangle for given corner coordinates.
func NewRectangle(llx, lly, urx, ury float64) *Rectangle {
	return &Rectangle{LL: Point{llx, lly}, UR: Point{urx, ury}}
}

func decodeFloat(number Object) float64 {
	var f float64
	switch v := number.(type) {
	case Float:
		f = v.Value()
	case Integer:
		f = float64(v.Value())
	}
	return f
}

func RectForArray(arr Array) *Rectangle {
	if len(arr) != 4 {
		return nil
	}

	llx := decodeFloat(arr[0])
	lly := decodeFloat(arr[1])
	urx := decodeFloat(arr[2])
	ury := decodeFloat(arr[3])

	return NewRectangle(llx, lly, urx, ury)
}

// RectForDim returns a new rectangle for given dimensions.
func RectForDim(width, height float64) *Rectangle {
	return NewRectangle(0.0, 0.0, width, height)
}

// RectForWidthAndHeight returns a new rectangle for given dimensions.
func RectForWidthAndHeight(llx, lly, width, height float64) *Rectangle {
	return NewRectangle(llx, lly, llx+width, lly+height)
}

// PaperSize is a map of known paper sizes in user units (=72 dpi pixels).
var PaperSize = map[string]*Dim{
	// ISO 216:1975 A
	"4A0": {4768, 6741}, // 66 1/4" x 93 5/8"	1682 x 2378 mm
	"2A0": {3370, 4768}, // 46 3/4" x 66 1/4"	1189 x 1682 mm
	"A0":  {2384, 3370}, //     33" x 46 3/4"	 841 x 1189 mm
	"A1":  {1684, 2384}, // 23 3/8" x 33"		 594 x 841 mm
	"A2":  {1191, 1684}, // 16 1/2" x 23 3/8"	 420 x 594 mm
	"A3":  {842, 1191},  // 11 3/4" x 16 1/2"	 297 x 420 mm
	"A4":  {595, 842},   //  8 1/4" x 11 3/4"	 210 x 297 mm
	"A5":  {420, 595},   //  5 7/8" x 8 1/4"	 148 x 210 mm
	"A6":  {298, 420},   //  4 1/8" x 5 7/8"	 105 x 148 mm
	"A7":  {210, 298},   //  2 7/8" x 4 1/8"	  74 x 105 mm
	"A8":  {147, 210},   //      2" x 2 7/8"	  52 x 74 mm
	"A9":  {105, 147},   //  1 1/2" x 2"		  37 x 52 mm
	"A10": {74, 105},    //      1" x 1 1/2"	  26 x 37 mm

	// ISO 216:1975 B
	"B0+": {3170, 4479}, //     44" x 62 1/4"	1118 x 1580 mm
	"B0":  {2835, 4008}, // 39 3/8" x 55 3/4"	1000 x 1414 mm
	"B1+": {2041, 2892}, // 28 3/8" x 40 1/8"	 720 x 1020 mm
	"B1":  {2004, 2835}, // 27 3/4" x 39 3/8"	 707 x 1000 mm
	"B2+": {1474, 2041}, // 20 1/2" x 28 3/8"	 520 x 720 mm
	"B2":  {1417, 2004}, // 19 3/4" x 27 3/4"	 500 x 707 mm
	"B3":  {1001, 1417}, // 13 7/8" x 19 3/4"	 353 x 500 mm
	"B4":  {709, 1001},  //  9 7/8" x 13 7/8"	 250 x 353 mm
	"B5":  {499, 709},   //      7" x 9 7/8"	 176 x 250 mm
	"B6":  {354, 499},   //  4 7/8" x 7"		 125 x 176 mm
	"B7":  {249, 354},   //  3 1/2" x 4 7/8"	  88 x 125 mm
	"B8":  {176, 249},   //  2 1/2" x 3 1/2"	  62 x 88 mm
	"B9":  {125, 176},   //  1 3/4" x 2 1/2"	  44 x 62 mm
	"B10": {88, 125},    //  1 1/4" x 1 3/4"	  31 x 44 mm

	// ISO 269:1985 envelopes aka ISO C
	"C0":  {2599, 3677}, //     36" x 51"		917 x 1297 mm
	"C1":  {1837, 2599}, // 25 1/2" x 36"		648 x 917 mm
	"C2":  {1298, 1837}, //     18" x 25 1/2"	458 x 648 mm
	"C3":  {918, 1298},  // 12 3/4" x 18"		324 x 458 mm
	"C4":  {649, 918},   //      9" x 12 3/4"	229 x 324 mm
	"C5":  {459, 649},   //  6 3/8" x 9"		162 x 229 mm
	"C6":  {323, 459},   //  4 1/2" x 6 3/8"	114 x 162 mm
	"C7":  {230, 323},   // 3 3/16" x 4 1/2"	 81 x 114 mm
	"C8":  {162, 230},   //  2 1/4" x 3 3/16	 57 x 81 mm
	"C9":  {113, 162},   //  1 5/8" x 2 1/4"	 40 x 57 mm
	"C10": {79, 113},    //  1 1/8" x 1 5/8"	 28 x 40 mm

	// ISO 217:2013 untrimmed raw paper
	"RA0": {2438, 3458}, // 33.9" x 48.0"		860 x 1220 mm
	"RA1": {1729, 2438}, // 24.0" x 33.9"		610 x 860 mm
	"RA2": {1219, 1729}, // 16.9" x 24.0"		430 x 610 mm
	"RA3": {865, 1219},  // 12.0" x 16.9"		305 x 430 mm
	"RA4": {610, 865},   //  8.5" x 12.0"		215 x 305 mm

	"SRA0": {2551, 3628}, // 35.4" x 50.4"		900 x 1280 mm
	"SRA1": {1814, 2551}, // 25.2" x 35.4"		640 x 900 mm
	"SRA2": {1276, 1814}, // 17.7" x 25.2"		450 x 640 mm
	"SRA3": {907, 1276},  // 12.6" x 17.7"		320 x 450 mm
	"SRA4": {638, 907},   //  8.9" x 12.6"		225 x 320 mm

	"SRA1+":  {2835, 4008}, // 26.0" x 36.2"	660 x 920 mm
	"SRA2+":  {1361, 1843}, // 18.9" x 25.6"	480 x 650 mm
	"SRA3+":  {907, 1304},  // 12.6" x 18.1"	320 x 460 mm
	"SRA3++": {2835, 4008}, // 12.6" x 18.3"	320 x 464 mm

	// American
	"SuperB": {936, 1368}, // 13" x 19"
	"B+":     {936, 1368},

	"Tabloid":      {792, 1224}, //    11" x 17" 		ANSIB, DobleCarta
	"ExtraTabloid": {864, 1296}, //    12" x 18"		ARCHB, Arch2
	"Ledger":       {1224, 792}, //    17" x 11" 		ANSIB
	"Legal":        {612, 1008}, // 8 1/2" x 14"

	"GovLegal": {612, 936}, // 8 1/2" x 13"
	"Oficio":   {612, 936},
	"Folio":    {612, 936},

	"Letter":         {612, 792}, // 8 1/2" x 11"		ANSIA
	"Carta":          {612, 792},
	"AmericanQuarto": {612, 792},

	"DobleCarta": {792, 1224}, // 11" x 17"			Tabloid, ANSIB

	"GovLetter": {576, 756}, //     8" x 10 1/2"
	"Executive": {522, 756}, // 7 1/4" x 10 1/2"

	"HalfLetter": {396, 612}, // 5 1/2" x 8 1/2"
	"Memo":       {396, 612},
	"Statement":  {396, 612},
	"Stationary": {396, 612},

	"JuniorLegal": {360, 576}, // 5" x 8"
	"IndexCard":   {360, 576},

	"Photo": {288, 432}, // 4" x 6"

	// ANSI/ASME Y14.1
	"ANSIA": {612, 792},   // 8 1/2" x 11" Letter, Carta, AmericanQuarto
	"ANSIB": {792, 1224},  //    11" x 17" Ledger, Tabloid, DobleCarta
	"ANSIC": {1224, 1584}, //    17" x 22"
	"ANSID": {1584, 2448}, //    22" x 34"
	"ANSIE": {2448, 3168}, //    34" x 44"
	"ANSIF": {2016, 2880}, //    28" x 40"

	// ANSI/ASME Y14.1 Architectural series
	"ARCHA":  {649, 865},   //  9" x 12"	Arch 1
	"ARCHB":  {865, 1296},  // 12" x 18"	Arch 2, ExtraTabloide
	"ARCHC":  {1296, 1729}, // 18" x 24"	Arch 3
	"ARCHD":  {1729, 2591}, // 24" x 36"	Arch 4
	"ARCHE":  {2591, 3456}, // 36" x 48"	Arch 6
	"ARCHE1": {2160, 3025}, // 30" x 42"	Arch 5
	"ARCHE2": {1871, 2736}, // 26" x 38"
	"ARCHE3": {1945, 2809}, // 27" x 39"

	"Arch1": {648, 864},   //  9" x 12"	ARCHA
	"Arch2": {864, 1296},  // 12" x 18"	ARCHB, ExtraTabloide
	"Arch3": {1296, 1728}, // 18" x 24"	ARCHC
	"Arch4": {1728, 2592}, // 24" x 36"	ARCHD
	"Arch5": {2160, 3024}, // 30" x 42"	ARCHE1
	"Arch6": {2592, 3456}, // 36" x 48"	ARCHE

	// American Uncut
	"Bond":  {1584, 1224}, //     22" x 17"
	"Book":  {2736, 1800}, //     38" x 25"
	"Cover": {1872, 1440}, //     26" x 20"
	"Index": {2196, 1836}, // 30 1/2" x 25 1/2"

	"Newsprint": {2592, 1728}, // 36" x 24"
	"Tissue":    {2592, 1728},

	"Offset": {2736, 1800}, // 38" x 25"
	"Text":   {2736, 1800},

	// English Uncut
	"Crown":          {1170, 1512}, // 16 1/4" x 21"
	"DoubleCrown":    {1440, 2160}, //     20" x 30"
	"Quad":           {2160, 2880}, //     30" x 40"
	"Demy":           {1278, 1620}, // 17 3/4" x 22 1/2"
	"DoubleDemy":     {1620, 2556}, // 22 1/2" x 35 1/2"
	"Medium":         {1314, 1656}, // 18 1/4" x 23"
	"Royal":          {1440, 1804}, //     20" x 25 1/16"
	"SuperRoyal":     {1512, 1944}, //     21" x 27"
	"DoublePott":     {1080, 1800}, //     15" x 25"
	"DoublePost":     {1368, 2196}, //     19" x 30 1/2"
	"Foolscap":       {972, 1224},  // 13 1/2" x 17"
	"DoubleFoolscap": {1224, 1944}, //     17" x 27"

	"F4": {594, 936}, // 8 1/4" x 13"

	// GB/T 148-1997 D Series China
	"D0": {2166, 3016}, // 29.9" x 41.9"	764 x 1064 mm
	"D1": {1508, 2155}, // 20.9" x 29.9"	532 x 760 mm
	"D2": {1077, 1497}, // 15.0" x 20.8"	380 x 528 mm
	"D3": {748, 1066},  // 10.4" x 14.8"	264 x 376 mm
	"D4": {533, 737},   //  7.4" x 10.2"	188 x 260 mm
	"D5": {369, 522},   //  5.1" x 7.2"		130 x 184 mm
	"D6": {261, 357},   //  3.6" x 5.0"		 92 x 126 mm

	"RD0": {2231, 3096}, // 31.0" x 43.0"	787 x 1092 mm
	"RD1": {1548, 2231}, // 21.5" x 31.0"	546 x 787 mm
	"RD2": {1114, 1548}, // 15.5" x 21.5"	393 x 546 mm
	"RD3": {774, 1114},  // 10.7" x 15.5"	273 x 393 mm
	"RD4": {556, 774},   //  7.7" x 10.7"	196 x 273 mm
	"RD5": {386, 556},   //  5.4" x 7.7"	136 x 196 mm
	"RD6": {278, 386},   //  3.9" x 5.4"	 98 x 136 mm

	// Japanese B-series variant
	"JIS-B0":      {2920, 4127}, // 40.55" x 57.32"		1030 x 1456 mm
	"JIS-B1":      {2064, 2920}, // 28.66" x 40.55"	 	 728 x 1030 mm
	"JIS-B2":      {1460, 2064}, // 20.28" x 28.66"	 	 515 x 728 mm
	"JIS-B3":      {1032, 1460}, // 14.33" x 20.28"	 	 364 x 515 mm
	"JIS-B4":      {729, 1032},  // 10.12" x 14.33"	 	 257 x 364 mm
	"JIS-B5":      {516, 729},   //  7.17" x 10.12"	 	 182 x 257 mm
	"JIS-B6":      {363, 516},   //  5.04" x 7.17"		 128 x 182 mm
	"JIS-B7":      {258, 363},   //  3.58" x 5.04"		  91 x 128 mm
	"JIS-B8":      {181, 258},   //  2.52" x 3.58"		  64 x 91 mm
	"JIS-B9":      {127, 181},   //  1.77" x 2.52"		  45 x 64 mm
	"JIS-B10":     {91, 127},    //  1.26" x 1.77"		  32 x 45 mm
	"JIS-B11":     {63, 91},     //  0.87" x 1.26"		  22 x 32 mm
	"JIS-B12":     {45, 63},     //  0.63" x 0.87"		  16 x 22 mm
	"Shirokuban4": {748, 1074},  // 10.39" x 14.92"		 264 x 379 mm
	"Shirokuban5": {536, 742},   //  7.44" x 10.31"		 189 x 262 mm
	"Shirokuban6": {360, 533},   //  5.00" x 7.40"		 127 x 188 mm
	"Kiku4":       {644, 868},   //  8.94" x 12.05"		 227 x 306 mm
	"Kiku5":       {428, 644},   //  5.95" x 8.94"		 151 x 227 mm
	"AB":          {595, 729},   //  8.27" x 10.12"	 	 210 x 257 mm
	"B40":         {292, 516},   //  4.06" x 7.17"		 103 x 182 mm
	"Shikisen":    {238, 420},   //  3.31" x 5.83"		  84 x 148 mm
}

// RectForFormat returns a new rectangle for given format.
func RectForFormat(f string) *Rectangle {
	d := PaperSize[f]
	return RectForDim(d.Width, d.Height)
}

// Width returns the horizontal span of a rectangle in userspace.
func (r Rectangle) Width() float64 {
	return r.UR.X - r.LL.X
}

// Height returns the vertical span of a rectangle in userspace.
func (r Rectangle) Height() float64 {
	return r.UR.Y - r.LL.Y
}

func (r Rectangle) Equals(r2 Rectangle) bool {
	return r.LL == r2.LL && r.UR == r2.UR
}

// FitsWithin returns true if rectangle r fits within rectangle r2.
func (r Rectangle) FitsWithin(r2 *Rectangle) bool {
	return r.Width() <= r2.Width() && r.Height() <= r2.Height()
}

func (r Rectangle) Visible() bool {
	return r.Width() != 0 && r.Height() != 0
}

// AspectRatio returns the relation between width and height of a rectangle.
func (r Rectangle) AspectRatio() float64 {
	return r.Width() / r.Height()
}

// Landscape returns true if r is in landscape mode.
func (r Rectangle) Landscape() bool {
	return r.AspectRatio() > 1
}

// Portrait returns true if r is in portrait mode.
func (r Rectangle) Portrait() bool {
	return r.AspectRatio() < 1
}

// Contains returns true if rectangle r contains point p.
func (r Rectangle) Contains(p Point) bool {
	return p.X >= r.LL.X && p.X <= r.UR.X && p.Y >= r.LL.Y && p.Y <= r.LL.Y
}

// ScaledWidth returns the width for given height according to r's aspect ratio.
func (r Rectangle) ScaledWidth(h float64) float64 {
	return r.AspectRatio() * h
}

// ScaledHeight returns the height for given width according to r's aspect ratio.
func (r Rectangle) ScaledHeight(w float64) float64 {
	return w / r.AspectRatio()
}

// Dimensions returns r's dimensions.
func (r Rectangle) Dimensions() Dim {
	return Dim{r.Width(), r.Height()}
}

// Translate moves r by dx and dy.
func (r *Rectangle) Translate(dx, dy float64) {
	r.LL.Translate(dx, dy)
	r.UR.Translate(dx, dy)
}

// Center returns the center point of a rectangle.
func (r Rectangle) Center() Point {
	return Point{(r.UR.X - r.Width()/2), (r.UR.Y - r.Height()/2)}
}

func (r Rectangle) String() string {
	return fmt.Sprintf("(%3.2f, %3.2f, %3.2f, %3.2f) w=%.2f h=%.2f ar=%.2f", r.LL.X, r.LL.Y, r.UR.X, r.UR.Y, r.Width(), r.Height(), r.AspectRatio())
}

// ShortString returns a compact string representation for r.
func (r Rectangle) ShortString() string {
	return fmt.Sprintf("(%3.0f, %3.0f, %3.0f, %3.0f)", r.LL.X, r.LL.Y, r.UR.X, r.UR.Y)
}

// Array returns the PDF representation of a rectangle.
func (r Rectangle) Array() Array {
	return NewNumberArray(r.LL.X, r.LL.Y, r.UR.X, r.UR.Y)
}

// Clone returns a clone of r.
func (r Rectangle) Clone() *Rectangle {
	return NewRectangle(r.LL.X, r.LL.Y, r.UR.X, r.UR.Y)
}

// CroppedCopy returns a copy of r with applied margin..
func (r Rectangle) CroppedCopy(margin float64) *Rectangle {
	return NewRectangle(r.LL.X+margin, r.LL.Y+margin, r.UR.X-margin, r.UR.Y-margin)
}

// ToInches converts r to inches.
func (r Rectangle) ToInches() *Rectangle {
	return NewRectangle(r.LL.X*userSpaceToInch, r.LL.Y*userSpaceToInch, r.UR.X*userSpaceToInch, r.UR.Y*userSpaceToInch)
}

// ToCentimetres converts r to centimetres.
func (r Rectangle) ToCentimetres() *Rectangle {
	return NewRectangle(r.LL.X*userSpaceToCm, r.LL.Y*userSpaceToCm, r.UR.X*userSpaceToCm, r.UR.Y*userSpaceToCm)
}

// ToMillimetres converts r to millimetres.
func (r Rectangle) ToMillimetres() *Rectangle {
	return NewRectangle(r.LL.X*userSpaceToMm, r.LL.Y*userSpaceToMm, r.UR.X*userSpaceToMm, r.UR.Y*userSpaceToMm)
}

// ConvertToUnit converts r to unit.
func (r *Rectangle) ConvertToUnit(unit DisplayUnit) *Rectangle {
	switch unit {
	case INCHES:
		return r.ToInches()
	case CENTIMETRES:
		return r.ToCentimetres()
	case MILLIMETRES:
		return r.ToMillimetres()
	}
	return r
}

func (r Rectangle) formatToInches() string {
	return fmt.Sprintf("(%3.2f, %3.2f, %3.2f, %3.2f) w=%.2f h=%.2f ar=%.2f",
		r.LL.X*userSpaceToInch,
		r.LL.Y*userSpaceToInch,
		r.UR.X*userSpaceToInch,
		r.UR.Y*userSpaceToInch,
		r.Width()*userSpaceToInch,
		r.Height()*userSpaceToInch,
		r.AspectRatio())
}

func (r Rectangle) formatToCentimetres() string {
	return fmt.Sprintf("(%3.2f, %3.2f, %3.2f, %3.2f) w=%.2f h=%.2f ar=%.2f",
		r.LL.X*userSpaceToCm,
		r.LL.Y*userSpaceToCm,
		r.UR.X*userSpaceToCm,
		r.UR.Y*userSpaceToCm,
		r.Width()*userSpaceToCm,
		r.Height()*userSpaceToCm,
		r.AspectRatio())
}

func (r Rectangle) formatToMillimetres() string {
	return fmt.Sprintf("(%3.2f, %3.2f, %3.2f, %3.2f) w=%.2f h=%.2f ar=%.2f",
		r.LL.X*userSpaceToMm,
		r.LL.Y*userSpaceToMm,
		r.UR.X*userSpaceToMm,
		r.UR.Y*userSpaceToMm,
		r.Width()*userSpaceToMm,
		r.Height()*userSpaceToMm,
		r.AspectRatio())
}

// Format returns r's details converted into unit.
func (r Rectangle) Format(unit DisplayUnit) string {
	switch unit {
	case INCHES:
		return r.formatToInches()
	case CENTIMETRES:
		return r.formatToCentimetres()
	case MILLIMETRES:
		return r.formatToMillimetres()
	}
	return r.String()
}

///////////////////////////////////////////////////////////////////////////////////

// QuadLiteral is a polygon with four edges and four vertices.
// The four vertices are assumed to be specified in counter clockwise order.
type QuadLiteral struct {
	P1, P2, P3, P4 Point
}

func NewQuadLiteralForRect(r *Rectangle) *QuadLiteral {
	// p1 := Point{X: r.LL.X, Y: r.LL.Y}
	// p2 := Point{X: r.UR.X, Y: r.LL.Y}
	// p3 := Point{X: r.UR.X, Y: r.UR.Y}
	// p4 := Point{X: r.LL.X, Y: r.UR.Y}

	p3 := Point{X: r.LL.X, Y: r.LL.Y}
	p4 := Point{X: r.UR.X, Y: r.LL.Y}
	p2 := Point{X: r.UR.X, Y: r.UR.Y}
	p1 := Point{X: r.LL.X, Y: r.UR.Y}

	return &QuadLiteral{P1: p1, P2: p2, P3: p3, P4: p4}
}

// Array returns the PDF representation of ql.
func (ql QuadLiteral) Array() Array {
	return NewNumberArray(ql.P1.X, ql.P1.Y, ql.P2.X, ql.P2.Y, ql.P3.X, ql.P3.Y, ql.P4.X, ql.P4.Y)
}

// EnclosingRectangle calculates the rectangle enclosing ql's vertices at a distance f.
func (ql QuadLiteral) EnclosingRectangle(f float64) *Rectangle {
	xmin, xmax := ql.P1.X, ql.P1.X
	ymin, ymax := ql.P1.Y, ql.P1.Y
	for _, p := range []Point{ql.P2, ql.P3, ql.P4} {
		if p.X < xmin {
			xmin = p.X
		} else if p.X > xmax {
			xmax = p.X
		}
		if p.Y < ymin {
			ymin = p.Y
		} else if p.Y > ymax {
			ymax = p.Y
		}
	}
	return NewRectangle(xmin-f, ymin-f, xmax+f, ymax+f)
}

// QuadPoints is an array of 8 × n numbers specifying the coordinates of n quadrilaterals in default user space.
type QuadPoints []QuadLiteral

// AddQuadLiteral adds a quadliteral to qp.
func (qp *QuadPoints) AddQuadLiteral(ql QuadLiteral) {
	*qp = append(*qp, ql)
}

// Array returns the PDF representation of qp.
func (qp *QuadPoints) Array() Array {
	a := Array{}
	for _, ql := range *qp {
		a = append(a, ql.Array()...)
	}
	return a
}

///////////////////////////////////////////////////////////////////////////////////

// Name represents a PDF name object.
type NameType string

// Clone returns a clone of nameObject.
func (nameObject NameType) Clone() Object {
	return nameObject
}

func (nameObject NameType) String() string {
	return string(nameObject)
}

// PDFString returns a string representation as found in and written to a PDF file.
func (nameObject NameType) PDFString() string {
	s := " "
	if len(nameObject) > 0 {
		s = EncodeName(string(nameObject))
	}
	return fmt.Sprintf("/%s", s)
}

// Value returns a string value for this PDF object.
func (nameObject NameType) Value() string {
	return nameObject.String()
}

///////////////////////////////////////////////////////////////////////////////////

// StringLiteral represents a PDF string literal object.
type StringLiteral string

// Clone returns a clone of stringLiteral.
func (stringliteral StringLiteral) Clone() Object {
	return stringliteral
}

func (stringliteral StringLiteral) String() string {
	return fmt.Sprintf("(%s)", string(stringliteral))
}

// PDFString returns a string representation as found in and written to a PDF file.
func (stringliteral StringLiteral) PDFString() string {
	return stringliteral.String()
}

// Value returns a string value for this PDF object.
func (stringliteral StringLiteral) Value() string {
	return string(stringliteral)
}

///////////////////////////////////////////////////////////////////////////////////

// HexLiteral represents a PDF hex literal object.
type HexLiteral string

// NewHexLiteral creates a new HexLiteral for b..
func NewHexLiteral(b []byte) HexLiteral {
	return HexLiteral(hex.EncodeToString(b))
}

// Clone returns a clone of hexliteral.
func (hexliteral HexLiteral) Clone() Object {
	return hexliteral
}

func (hexliteral HexLiteral) String() string {
	return fmt.Sprintf("<%s>", string(hexliteral))
}

// PDFString returns the string representation as found in and written to a PDF file.
func (hexliteral HexLiteral) PDFString() string {
	return hexliteral.String()
}

// Value returns a string value for this PDF object.
func (hexliteral HexLiteral) Value() string {
	return string(hexliteral)
}

// Bytes returns the byte representation.
func (hexliteral HexLiteral) Bytes() ([]byte, error) {
	return hex.DecodeString(hexliteral.Value())
}

///////////////////////////////////////////////////////////////////////////////////

// IndirectRef represents a PDF indirect object.
type IndirectRef struct {
	ObjectNumber     Integer
	GenerationNumber Integer
}

// NewIndirectRef returns a new PDFIndirectRef object.
func NewIndirectRef(objectNumber, generationNumber int) *IndirectRef {
	return &IndirectRef{
		ObjectNumber:     Integer(objectNumber),
		GenerationNumber: Integer(generationNumber),
	}
}

// Clone returns a clone of ir.
func (ir IndirectRef) Clone() Object {
	ir2 := ir
	return ir2
}

func (ir IndirectRef) String() string {
	return fmt.Sprintf("(%s)", ir.PDFString())
}

// PDFString returns a string representation as found in and written to a PDF file.
func (ir IndirectRef) PDFString() string {
	return fmt.Sprintf("%d %d R", ir.ObjectNumber, ir.GenerationNumber)
}

/////////////////////////////////////////////////////////////////////////////////////

// Options for display unit in effect.
const (
	POINTS DisplayUnit = iota
	INCHES
	CENTIMETRES
	MILLIMETRES
)

const (
	userSpaceToInch = float64(1) / 72
	userSpaceToCm   = 2.54 / 72
	userSpaceToMm   = userSpaceToCm * 10

	inchToUserSpace = 1 / userSpaceToInch
	cmToUserSpace   = 1 / userSpaceToCm
	mmToUserSpace   = 1 / userSpaceToMm
)

func ToUserSpace(f float64, unit DisplayUnit) float64 {
	switch unit {
	case INCHES:
		return f * inchToUserSpace
	case CENTIMETRES:
		return f * cmToUserSpace
	case MILLIMETRES:
		return f * mmToUserSpace

	}
	return f
}

// Dim represents the dimensions of a rectangular view medium
// like a PDF page, a sheet of paper or an image grid
// in user space, inches, centimetres or millimetres.
type Dim struct {
	Width  float64 `json:"width"`
	Height float64 `json:"height"`
}

// ToInches converts d to inches.
func (d Dim) ToInches() Dim {
	return Dim{d.Width * userSpaceToInch, d.Height * userSpaceToInch}
}

// ToCentimetres converts d to centimetres.
func (d Dim) ToCentimetres() Dim {
	return Dim{d.Width * userSpaceToCm, d.Height * userSpaceToCm}
}

// ToMillimetres converts d to millimetres.
func (d Dim) ToMillimetres() Dim {
	return Dim{d.Width * userSpaceToMm, d.Height * userSpaceToMm}
}

// ConvertToUnit converts d to unit.
func (d Dim) ConvertToUnit(unit DisplayUnit) Dim {
	switch unit {
	case INCHES:
		return d.ToInches()
	case CENTIMETRES:
		return d.ToCentimetres()
	case MILLIMETRES:
		return d.ToMillimetres()
	}
	return d
}

// AspectRatio returns the relation between width and height.
func (d Dim) AspectRatio() float64 {
	return d.Width / d.Height
}

// Landscape returns true if d is in landscape mode.
func (d Dim) Landscape() bool {
	return d.AspectRatio() > 1
}

// Portrait returns true if d is in portrait mode.
func (d Dim) Portrait() bool {
	return d.AspectRatio() < 1
}

func (d Dim) String() string {
	return fmt.Sprintf("%fx%f", d.Width, d.Height)
}

var errNameTreeDuplicateKey = errors.New("pdfcpu: name: duplicate key")

const maxEntries = 3

// Node is an opinionated implementation of the PDF name tree.
// pdfcpu caches all name trees found in the PDF catalog with this data structure.
// The PDF spec does not impose any rules regarding a strategy for the creation of nodes.
// A binary tree was chosen where each leaf node has a limited number of entries (maxEntries).
// Once maxEntries has been reached a leaf node turns into an intermediary node with two kids,
// which are leaf nodes each of them holding half of the sorted entries of the original leaf node.
type Node struct {
	Kids       []*Node // Mirror of the name tree's Kids array, an array of indirect references.
	Names      []entry // Mirror of the name tree's Names array.
	Kmin, Kmax string  // Mirror of the name tree's Limit array[Kmin,Kmax].
	D          Dict    // The PDF dict representing this name tree node.
}

// entry is a key value pair.
type entry struct {
	k string
	v Object
}

func (n Node) leaf() bool {
	return n.Kids == nil
}

func keyLess(k, s string) bool {
	return k < s
}

func keyLessOrEqual(k, s string) bool {
	return k == s || keyLess(k, s)
}

func (n Node) withinLimits(k string) bool {
	return keyLessOrEqual(n.Kmin, k) && keyLessOrEqual(k, n.Kmax)
}

// Value returns the value for given key
func (n Node) Value(k string) (Object, bool) {
	if !n.withinLimits(k) {
		return nil, false
	}

	if n.leaf() {

		// names are sorted by key.
		for _, v := range n.Names {

			if v.k < k {
				continue
			}

			if v.k == k {
				return v.v, true
			}

			return nil, false
		}

		return nil, false
	}

	// kids are sorted by key ranges.
	for _, v := range n.Kids {
		if v.withinLimits(k) {
			return v.Value(k)
		}
	}

	return nil, false
}

// AppendToNames adds an entry to a leaf node (for internalizing name trees).
func (n *Node) AppendToNames(k string, v Object) {
	// fmt.Printf("AddToLeaf: %s %v (%v)\n\n", k, v, &v)

	if n.Names == nil {
		n.Names = make([]entry, 0, maxEntries)
	}

	arr, ok := v.(Array)
	if ok {
		arr1 := make(Array, len(arr))
		for i, v := range arr {
			if indRef, ok := v.(IndirectRef); ok {
				arr1[i] = *NewIndirectRef(indRef.ObjectNumber.Value(), indRef.GenerationNumber.Value())
			} else {
				arr1[i] = v
			}
		}
		n.Names = append(n.Names, entry{k, arr1})
	} else {
		n.Names = append(n.Names, entry{k, v})
	}
}

type NameMap map[string][]Dict

func (m NameMap) Add(k string, d Dict) {
	dd, ok := m[k]
	if !ok {
		m[k] = []Dict{d}
		return
	}
	m[k] = append(dd, d)
}

func (n *Node) insertIntoLeaf(k string, v Object, m NameMap) error {
	for i, e := range n.Names {
		if keyLess(e.k, k) {
			continue
		}
		if e.k == k {
			return errNameTreeDuplicateKey
		}
		// Insert entry(k,v) at i
		n.Names = append(n.Names, entry{})
		copy(n.Names[i+1:], n.Names[i:])
		n.Names[i] = entry{k, v}
		return nil
	}
	n.Kmax = k
	n.Names = append(n.Names, entry{k, v})
	return nil
}

func updateNameRef(d Dict, keys []string, nameOld, nameNew string) error {
	for _, k := range keys {
		s, err := d.StringOrHexLiteralEntry(k)
		if err != nil {
			return err
		}
		if s != nil {
			if *s != nameOld {
				return errors.Errorf("invalid Name ref detected for: %s", nameOld)
			}
			d[k] = NewHexLiteral([]byte(nameNew))
		}
	}
	return nil
}

func updateNameRefDicts(dd []Dict, nameRefDictKeys []string, nameOld, nameNew string) error {
	// eg.
	// "Dests": "D", "Dest"    		[]string{"D", "Dest"}
	// "EmbeddedFiles": F", "UF"	[]string{"F", "UF"}

	for _, d := range dd {
		if err := updateNameRef(d, nameRefDictKeys, nameOld, nameNew); err != nil {
			return err
		}
	}

	return nil
}

func (n *Node) insertUniqueIntoLeaf(k string, v Object, m NameMap, nameRefDictKeys []string) (bool, error) {
	var err error
	kOrig := k
	for first := true; first || err == errNameTreeDuplicateKey; first = false {
		err = n.insertIntoLeaf(k, v, m)
		if err == nil {
			break
		}
		if err != errNameTreeDuplicateKey {
			return false, err
		}
		if len(m) == 0 {
			return true, nil
		}
		kNew := k + "\x01"
		dd, ok := m[kOrig]
		if !ok {
			return true, nil
		}
		if err := updateNameRefDicts(dd, nameRefDictKeys, k, kNew); err != nil {
			return false, err
		}
		k = kNew
	}

	return false, nil
}

var ErrNoContent = errors.New("pdfcpu: page without content")

var zero int64 = 0

// XRefTableEntry represents an entry in the PDF cross reference table.
//
// This may wrap a free object, a compressed object or any in use PDF object:
//
// Dict, StreamDict, ObjectStreamDictType, PDFXRefStreamDict,
// Array, Integer, Float, Name, StringLiteral, HexLiteral, Boolean
type XRefTableEntry struct {
	Free            bool
	Offset          *int64
	Generation      *int
	Incr            int
	RefCount        int
	Object          Object
	Compressed      bool
	ObjectStream    *int
	ObjectStreamInd *int
	Valid           bool
	BeingValidated  bool
}

// NewXRefTableEntryGen0 returns a cross reference table entry for an object with generation 0.
func NewXRefTableEntryGen0(obj Object) *XRefTableEntry {
	zero := 0
	return &XRefTableEntry{Generation: &zero, Object: obj}
}

// NewFreeHeadXRefTableEntry returns the xref table entry for object 0
// which is per definition the head of the free list (list of free objects).
func NewFreeHeadXRefTableEntry() *XRefTableEntry {
	freeHeadGeneration := FreeHeadGeneration

	return &XRefTableEntry{
		Free:       true,
		Generation: &freeHeadGeneration,
		Offset:     &zero,
	}
}

// Enc wraps around all defined encryption attributes.
type Enc struct {
	O, U       []byte
	OE, UE     []byte
	Perms      []byte
	L, P, R, V int
	Emd        bool // encrypt meta data
	ID         []byte
}

// AnnotationFlags represents the PDF annotation flags.
type AnnotationFlags int

const ( // See table 165
	AnnInvisible AnnotationFlags = 1 << iota
	AnnHidden
	AnnPrint
	AnnNoZoom
	AnnNoRotate
	AnnNoView
	AnnReadOnly
	AnnLocked
	AnnToggleNoView
	AnnLockedContents
)

// AnnotationType represents the various PDF annotation
type AnnotationType int

const (
	AnnText AnnotationType = iota
	AnnLink
	AnnFreeText
	AnnLine
	AnnSquare
	AnnCircle
	AnnPolygon
	AnnPolyLine
	AnnHighLight
	AnnUnderline
	AnnSquiggly
	AnnStrikeOut
	AnnStamp
	AnnCaret
	AnnInk
	AnnPopup
	AnnFileAttachment
	AnnSound
	AnnMovie
	AnnWidget
	AnnScreen
	AnnPrinterMark
	AnnTrapNet
	AnnWatermark
	Ann3D
	AnnRedact
	AnnCustom
)

var AnnotTypes = map[string]AnnotationType{
	"Text":           AnnText,
	"Link":           AnnLink,
	"FreeText":       AnnFreeText,
	"Line":           AnnLine,
	"Square":         AnnSquare,
	"Circle":         AnnCircle,
	"Polygon":        AnnPolygon,
	"PolyLine":       AnnPolyLine,
	"Highlight":      AnnHighLight,
	"Underline":      AnnUnderline,
	"Squiggly":       AnnSquiggly,
	"StrikeOut":      AnnStrikeOut,
	"Stamp":          AnnStamp,
	"Caret":          AnnCaret,
	"Ink":            AnnInk,
	"Popup":          AnnPopup,
	"FileAttachment": AnnFileAttachment,
	"Sound":          AnnSound,
	"Movie":          AnnMovie,
	"Widget":         AnnWidget,
	"Screen":         AnnScreen,
	"PrinterMark":    AnnPrinterMark,
	"TrapNet":        AnnTrapNet,
	"Watermark":      AnnWatermark,
	"3D":             Ann3D,
	"Redact":         AnnRedact,
	"Custom":         AnnCustom,
}

// AnnotTypeStrings manages string representations for annotation
var AnnotTypeStrings = map[AnnotationType]string{
	AnnText:           "Text",
	AnnLink:           "Link",
	AnnFreeText:       "FreeText",
	AnnLine:           "Line",
	AnnSquare:         "Square",
	AnnCircle:         "Circle",
	AnnPolygon:        "Polygon",
	AnnPolyLine:       "PolyLine",
	AnnHighLight:      "Highlight",
	AnnUnderline:      "Underline",
	AnnSquiggly:       "Squiggly",
	AnnStrikeOut:      "StrikeOut",
	AnnStamp:          "Stamp",
	AnnCaret:          "Caret",
	AnnInk:            "Ink",
	AnnPopup:          "Popup",
	AnnFileAttachment: "FileAttachment",
	AnnSound:          "Sound",
	AnnMovie:          "Movie",
	AnnWidget:         "Widget",
	AnnScreen:         "Screen",
	AnnPrinterMark:    "PrinterMark",
	AnnTrapNet:        "TrapNet",
	AnnWatermark:      "Watermark",
	Ann3D:             "3D",
	AnnRedact:         "Redact",
	AnnCustom:         "Custom",
}

// BorderStyle (see table 168)
type BorderStyle int

const (
	BSSolid BorderStyle = iota
	BSDashed
	BSBeveled
	BSInset
	BSUnderline
)

func borderStyleDict(width float64, style BorderStyle) Dict {
	d := Dict(map[string]Object{
		"Type": NameType("Border"),
		"W":    Float(width),
	})

	var s string

	switch style {
	case BSSolid:
		s = "S"
	case BSDashed:
		s = "D"
	case BSBeveled:
		s = "B"
	case BSInset:
		s = "I"
	case BSUnderline:
		s = "U"
	}

	d["S"] = NameType(s)

	return d
}

func borderEffectDict(cloudyBorder bool, intensity int) Dict {
	s := "S"
	if cloudyBorder {
		s = "C"
	}

	return Dict(map[string]Object{
		"S": NameType(s),
		"I": Integer(intensity),
	})
}

func borderArray(rx, ry, width float64) Array {
	return NewNumberArray(rx, ry, width)
}

// LineEndingStyle (see table 179)
type LineEndingStyle int

const (
	LESquare LineEndingStyle = iota
	LECircle
	LEDiamond
	LEOpenArrow
	LEClosedArrow
	LENone
	LEButt
	LEROpenArrow
	LERClosedArrow
	LESlash
)

func LineEndingStyleName(les LineEndingStyle) string {
	var s string
	switch les {
	case LESquare:
		s = "Square"
	case LECircle:
		s = "Circle"
	case LEDiamond:
		s = "Diamond"
	case LEOpenArrow:
		s = "OpenArrow"
	case LEClosedArrow:
		s = "ClosedArrow"
	case LENone:
		s = "None"
	case LEButt:
		s = "Butt"
	case LEROpenArrow:
		s = "ROpenArrow"
	case LERClosedArrow:
		s = "RClosedArrow"
	case LESlash:
		s = "Slash"
	}
	return s
}

// AnnotationRenderer is the interface for PDF annotations.
type AnnotationRenderer interface {
	RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error)
	Type() AnnotationType
	RectString() string
	APObjNrInt() int
	ID() string
	ContentString() string
	CustomTypeString() string
}

// Some popular colors.
var (
	Black     = SimpleColor{}
	White     = SimpleColor{R: 1, G: 1, B: 1}
	LightGray = SimpleColor{.9, .9, .9}
	Gray      = SimpleColor{.5, .5, .5}
	DarkGray  = SimpleColor{.3, .3, .3}
	Red       = SimpleColor{1, 0, 0}
	Green     = SimpleColor{0, 1, 0}
	Blue      = SimpleColor{0, 0, 1}
	Yellow    = SimpleColor{.5, .5, 0}
)

var ErrInvalidColor = errors.New("pdfcpu: invalid color constant")

// SimpleColor is a simple rgb wrapper.
type SimpleColor struct {
	R, G, B float32 // intensities between 0 and 1.
}

func (sc SimpleColor) String() string {
	return fmt.Sprintf("r=%1.1f g=%1.1f b=%1.1f", sc.R, sc.G, sc.B)
}

func (sc SimpleColor) Array() Array {
	return NewNumberArray(float64(sc.R), float64(sc.G), float64(sc.B))
}

// NewSimpleColor returns a SimpleColor for rgb in the form 0x00RRGGBB
func NewSimpleColor(rgb uint32) SimpleColor {
	r := float32((rgb>>16)&0xFF) / 255
	g := float32((rgb>>8)&0xFF) / 255
	b := float32(rgb&0xFF) / 255
	return SimpleColor{r, g, b}
}

// NewSimpleColorForArray returns a SimpleColor for an r,g,b array.
func NewSimpleColorForArray(arr Array) SimpleColor {
	var r, g, b float32

	if f, ok := arr[0].(Float); ok {
		r = float32(f.Value())
	} else {
		r = float32(arr[0].(Integer))
	}

	if f, ok := arr[1].(Float); ok {
		g = float32(f.Value())
	} else {
		g = float32(arr[1].(Integer))
	}

	if f, ok := arr[2].(Float); ok {
		b = float32(f.Value())
	} else {
		b = float32(arr[2].(Integer))
	}

	return SimpleColor{r, g, b}
}

// NewSimpleColorForHexCode returns a SimpleColor for a #FFFFFF type hexadecimal rgb color representation.
func NewSimpleColorForHexCode(hexCol string) (SimpleColor, error) {
	var sc SimpleColor
	if len(hexCol) != 7 || hexCol[0] != '#' {
		return sc, errors.Errorf("pdfcpu: invalid hex color string: #FFFFFF, %s\n", hexCol)
	}
	b, err := hex.DecodeString(hexCol[1:])
	if err != nil || len(b) != 3 {
		return sc, errors.Errorf("pdfcpu: invalid hex color string: #FFFFFF, %s\n", hexCol)
	}
	return SimpleColor{float32(b[0]) / 255, float32(b[1]) / 255, float32(b[2]) / 255}, nil
}

func internalSimpleColor(s string) (SimpleColor, error) {
	var (
		sc  SimpleColor
		err error
	)
	switch strings.ToLower(s) {
	case "black":
		sc = Black
	case "darkgray":
		sc = DarkGray
	case "gray":
		sc = Gray
	case "lightgray":
		sc = LightGray
	case "white":
		sc = White
	case "red":
		sc = Red
	case "green":
		sc = Green
	case "blue":
		sc = Blue
	default:
		err = ErrInvalidColor
	}
	return sc, err
}

// ParseColor turns a color string into a SimpleColor.
func ParseColor(s string) (SimpleColor, error) {
	var sc SimpleColor

	cs := strings.Split(s, " ")
	if len(cs) != 1 && len(cs) != 3 {
		return sc, errors.Errorf("pdfcpu: illegal color string: 3 intensities 0.0 <= i <= 1.0 or #FFFFFF, %s\n", s)
	}

	if len(cs) == 1 {
		if len(cs[0]) == 7 && cs[0][0] == '#' {
			// #FFFFFF to uint32
			return NewSimpleColorForHexCode(cs[0])
		}
		return internalSimpleColor(cs[0])
	}

	r, err := strconv.ParseFloat(cs[0], 32)
	if err != nil {
		return sc, errors.Errorf("red must be a float value: %s\n", cs[0])
	}
	if r < 0 || r > 1 {
		return sc, errors.New("pdfcpu: red: a color value is an intensity between 0.0 and 1.0")
	}
	sc.R = float32(r)

	g, err := strconv.ParseFloat(cs[1], 32)
	if err != nil {
		return sc, errors.Errorf("pdfcpu: green must be a float value: %s\n", cs[1])
	}
	if g < 0 || g > 1 {
		return sc, errors.New("pdfcpu: green: a color value is an intensity between 0.0 and 1.0")
	}
	sc.G = float32(g)

	b, err := strconv.ParseFloat(cs[2], 32)
	if err != nil {
		return sc, errors.Errorf("pdfcpu: blue must be a float value: %s\n", cs[2])
	}
	if b < 0 || b > 1 {
		return sc, errors.New("pdfcpu: blue: a color value is an intensity between 0.0 and 1.0")
	}
	sc.B = float32(b)

	return sc, nil
}

// AnnotationInterface represents a PDF annotation.
type AnnotationInterface struct {
	SubType          AnnotationType  // The type of annotation that this dictionary describes.
	CustomSubType    string          // Out of spec annot type.
	Rect             Rectangle       // The annotation rectangle, defining the location of the annotation on the page in default user space units.
	APObjNr          int             // The objNr of the appearance stream dict.
	Contents         string          // Text that shall be displayed for the annotation.
	NM               string          // (Since V1.4) The annotation name, a text string uniquely identifying it among all the annotations on its page.
	ModificationDate string          // M - The date and time when the annotation was most recently modified.
	P                *IndirectRef    // An indirect reference to the page object with which this annotation is associated.
	F                AnnotationFlags // A set of flags specifying various characteristics of the annotation.
	C                *SimpleColor    // The background color of the annotation’s icon when closed, pop up title bar color, link ann border
	BorderRadX       float64         // Border radius X
	BorderRadY       float64         // Border radius Y
	BorderWidth      float64         // Border width
	Hash             uint32
	// StructParent int
	// OC dict
}

// NewAnnotation returns a new annotation.
func NewAnnotation(
	typ AnnotationType,
	customTyp string,
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
) AnnotationInterface {
	return AnnotationInterface{
		SubType:          typ,
		CustomSubType:    customTyp,
		Rect:             rect,
		APObjNr:          apObjNr,
		Contents:         contents,
		NM:               id,
		ModificationDate: modDate,
		F:                f,
		C:                col,
		BorderRadX:       borderRadX,
		BorderRadY:       borderRadY,
		BorderWidth:      borderWidth,
	}
}

// NewAnnotationForRawType returns a new annotation of a specific type.
func NewAnnotationForRawType(
	typ string,
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,

	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
) AnnotationInterface {
	annType, ok := AnnotTypes[typ]
	if !ok {
		annType = AnnotTypes["Custom"]
	} else {
		typ = ""
	}

	return NewAnnotation(annType, typ, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth)
}

// ID returns the annotation id.
func (ann AnnotationInterface) ID() string {
	return ann.NM
}

// ContentString returns a string representation of ann's contents.
func (ann AnnotationInterface) ContentString() string {
	return ann.Contents
}

// ContentString returns a string representation of ann's contents.
func (ann AnnotationInterface) CustomTypeString() string {
	return ann.CustomSubType
}

// RectString returns ann's positioning rectangle.
func (ann AnnotationInterface) RectString() string {
	return ann.Rect.ShortString()
}

func (ann AnnotationInterface) APObjNrInt() int {
	return ann.APObjNr
}

// Type returns ann's type.
func (ann AnnotationInterface) Type() AnnotationType {
	return ann.SubType
}

// TypeString returns a string representation of ann's type.
func (ann AnnotationInterface) TypeString() string {
	return AnnotTypeStrings[ann.SubType]
}

// HashString returns the annotation hash.
func (ann AnnotationInterface) HashString() uint32 {
	return ann.Hash
}

// DateString returns a string representation of t.
func DateString(t time.Time) string {
	_, tz := t.Zone()
	tzm := tz / 60
	sign := "+"
	if tzm < 0 {
		sign = "-"
		tzm = -tzm
	}

	return fmt.Sprintf("D:%d%02d%02d%02d%02d%02d%s%02d'%02d'",
		t.Year(), t.Month(), t.Day(),
		t.Hour(), t.Minute(), t.Second(),
		sign, tzm/60, tzm%60)
}

func prevalidateDate(s string, relaxed bool) (string, bool) {
	// utf16 conversion if applicable.
	if IsStringUTF16BE(s) {
		utf16s, err := DecodeUTF16String(s)
		if err != nil {
			return "", false
		}
		s = utf16s
	}

	s = strings.TrimPrefix(s, "\xEF\xBB\xBF")

	// Remove trailing 0x00
	s = strings.TrimRight(s, "\x00")

	if relaxed {
		// Accept missing "D:" prefix.
		// "YYYY" is mandatory
		s = strings.TrimPrefix(s, "D:")
		s = strings.TrimSpace(s)
		s = strings.ReplaceAll(s, ".", "")
		s = strings.ReplaceAll(s, "\\", "")
		return s, len(s) >= 4
	}

	// "D:YYYY" is mandatory
	if len(s) < 6 {
		return "", false
	}

	return s[2:], strings.HasPrefix(s, "D:")
}

func parseTimezoneHours(s string, o byte) (int, bool) {
	tzh, err := strconv.Atoi(s)
	if err != nil {
		return 0, false
	}

	// Opinionated hack.
	tzh = tzh % 24

	if o == 'Z' && tzh != 0 {
		return 0, false
	}

	return tzh, true
}

func parseTimezoneMinutes(s string, o byte) (int, bool) {
	tzm, err := strconv.Atoi(s)
	if err != nil {
		return 0, false
	}

	if tzm > 59 {
		return 0, false
	}

	if o == 'Z' && tzm != 0 {
		return 0, false
	}

	return tzm, true
}

func timezoneSeparator(c byte) bool {
	return c == '+' || c == '-' || c == 'Z'
}

// func validateTimezoneSeparator(c byte) bool {
// 	return c == '+' || c == '-' || c == 'Z'
// }

func parseTimezone(s string, off int, relaxed bool) (h, m int, ok bool) {
	o := s[off] // 14

	if !timezoneSeparator(o) {
		// Ignore timezone on corrupt timezone separator if relaxed.
		return 0, 0, relaxed
	}

	// local time equal to UT.
	// "YYYYMMDDHHmmSSZ" or
	// if relaxed
	// 		"YYYYMMDDHHmmSSZ'"
	// 		"YYYYMMDDHHmmSSZ'0"

	off++

	if o == 'Z' {
		t := s[off:]
		if t == "" || relaxed && (t == "'" || t == "'0") {
			return 0, 0, true
		}
	}

	// HH'mm
	s = s[off:]
	if s[0] == '-' {
		s = s[1:]
	}
	s = strings.ReplaceAll(s, " ", "0")
	ss := strings.Split(s, "'")
	if len(ss) == 0 {
		return 0, 0, false
	}

	neg := o == '-'

	tzh, ok := parseTimezoneHours(ss[0], o)
	if !ok {
		return 0, 0, false
	}

	if neg {
		tzh *= -1
	}

	if len(ss) == 1 || len(ss) == 2 && len(ss[1]) == 0 {
		// Ignore missing timezone minutes.
		return tzh, 0, true
	}

	tzm, ok := parseTimezoneMinutes(ss[1], o)
	if !ok {
		return 0, 0, false
	}

	return tzh, tzm, true
}

func parseYear(s string) (y int, finished, ok bool) {
	year := s[0:4]

	y, err := strconv.Atoi(year)
	if err != nil {
		return 0, false, false
	}

	// "YYYY"
	if len(s) == 4 {
		return y, true, true
	}

	if len(s) == 5 {
		return 0, false, false
	}

	return y, false, true
}

func parseMonth(s string) (m int, finished, ok bool) {
	month := s[4:6]

	var err error
	m, err = strconv.Atoi(month)
	if err != nil {
		return 0, false, false
	}

	if m < 1 || m > 12 {
		return 0, false, false
	}

	// "YYYYMM"
	if len(s) == 6 {
		return m, true, true
	}

	if len(s) == 7 {
		return 0, false, false
	}

	return m, false, true
}

func parseDay(s string, y, m int) (d int, finished, ok bool) {
	day := s[6:8]

	d, err := strconv.Atoi(day)
	if err != nil {
		return 0, false, false
	}

	if d < 1 || d > 31 {
		return 0, false, false
	}

	// check valid Date(year,month,day)
	// The day before the first day of next month:
	t := time.Date(y, time.Month(m+1), 0, 0, 0, 0, 0, time.UTC)
	if d > t.Day() {
		return 0, false, false
	}

	// "YYYYMMDD"
	if len(s) == 8 {
		return d, true, true
	}

	if len(s) == 9 {
		return 0, false, false
	}

	return d, false, true
}

func parseHour(s string) (h int, finished, ok bool) {
	hour := s[8:10]

	h, err := strconv.Atoi(hour)
	if err != nil {
		return 0, false, false
	}

	if h > 23 {
		return 0, false, false
	}

	// "YYYYMMDDHH"
	if len(s) == 10 {
		return h, true, true
	}

	if len(s) == 11 {
		return 0, false, false
	}

	return h, false, true
}

func parseMinute(s string) (min int, finished, ok bool) {
	minute := s[10:12]

	min, err := strconv.Atoi(minute)
	if err != nil {
		return 0, false, false
	}

	if min > 59 {
		return 0, false, false
	}

	// "YYYYMMDDHHmm"
	if len(s) == 12 {
		return min, true, true
	}

	if len(s) == 13 {
		return 0, false, false
	}

	return min, false, true
}

func parseSecond(s string) (sec int, finished bool, off int, ok bool) {
	off = 14

	second := s[12:14]
	if len(second) == 2 && timezoneSeparator(second[1]) {
		second = second[:1]
		off = 13
	}

	sec, err := strconv.Atoi(second)
	if err != nil {
		return 0, false, off, false
	}

	if sec > 59 {
		return 0, false, off, false
	}

	// "YYYYMMDDHHmmSS"
	if len(s) == 14 {
		return sec, true, off, true
	}

	return sec, false, off, true
}

func digestPopularOutOfSpecDates(s string) (time.Time, bool) {
	// Mon Jan 2 15:04:05 2006
	// Monday, January 02, 2006 3:04:05 PM
	// 1/2/2006 15:04:05
	// Mon, Jan 2, 2006

	t, err := time.Parse("Mon Jan 2 15:04:05 2006", s)
	if err == nil {
		return t, true
	}

	t, err = time.Parse("Monday, January 02, 2006 3:04:05 PM", s)
	if err == nil {
		return t, true
	}

	t, err = time.Parse("1/2/2006 15:04:05", s)
	if err == nil {
		return t, true
	}

	t, err = time.Parse("Mon, Jan 2, 2006", s)
	if err == nil {
		return t, true
	}

	return t, false
}

// DateTime decodes s into a time.Time.
func DateTime(s string, relaxed bool) (time.Time, bool) {
	// 7.9.4 Dates
	// (D:YYYYMMDDHHmmSSOHH'mm)

	var d time.Time

	var ok bool
	s, ok = prevalidateDate(s, relaxed)
	if !ok {
		return d, false
	}

	y, finished, ok := parseYear(s)
	if !ok {
		// Try workaround
		return digestPopularOutOfSpecDates(s)
	}

	// Construct time for yyyy 01 01 00:00:00
	d = time.Date(y, 1, 1, 0, 0, 0, 0, time.UTC)
	if finished {
		return d, true
	}

	m, finished, ok := parseMonth(s)
	if !ok {
		return d, false
	}

	d = d.AddDate(0, m-1, 0)
	if finished {
		return d, true
	}

	day, finished, ok := parseDay(s, y, m)
	if !ok {
		return d, false
	}

	d = d.AddDate(0, 0, day-1)
	if finished {
		return d, true
	}

	h, finished, ok := parseHour(s)
	if !ok {
		return d, false
	}

	d = d.Add(time.Duration(h) * time.Hour)
	if finished {
		return d, true
	}

	min, finished, ok := parseMinute(s)
	if !ok {
		return d, false
	}

	d = d.Add(time.Duration(min) * time.Minute)
	if finished {
		return d, true
	}

	sec, finished, off, ok := parseSecond(s)
	if !ok {
		return d, false
	}

	d = d.Add(time.Duration(sec) * time.Second)
	if finished {
		return d, true
	}

	// Process timezone
	tzh, tzm, ok := parseTimezone(s, off, relaxed)
	if !ok {
		return d, false
	}

	loc := time.FixedZone("", tzh*60*60+tzm*60)
	d = time.Date(y, time.Month(m), day, h, min, sec, 0, loc)

	return d, true
}

const (
	// ValidationStrict ensures 100% compliance with the spec (PDF 32000-1:2008).
	ValidationStrict int = iota

	// ValidationRelaxed ensures PDF compliance based on frequently encountered validation errors.
	ValidationRelaxed
)

// See table 22 - User access permissions

const (
	UnusedFlag1              PermissionFlags = 1 << iota // Bit 1:  unused
	UnusedFlag2                                          // Bit 2:  unused
	PermissionPrintRev2                                  // Bit 3:  Print (security handlers rev.2), draft print (security handlers >= rev.3)
	PermissionModify                                     // Bit 4:  Modify contents by operations other than controlled by bits 6, 9, 11.
	PermissionExtract                                    // Bit 5:  Copy, extract text & graphics
	PermissionModAnnFillForm                             // Bit 6:  Add or modify annotations, fill form fields, in conjunction with bit 4 create/mod form fields.
	UnusedFlag7                                          // Bit 7:  unused
	UnusedFlag8                                          // Bit 8:  unused
	PermissionFillRev3                                   // Bit 9:  Fill form fields (security handlers >= rev.3)
	PermissionExtractRev3                                // Bit 10: Copy, extract text & graphics (security handlers >= rev.3) (unused since PDF 2.0)
	PermissionAssembleRev3                               // Bit 11: Assemble document (security handlers >= rev.3)
	PermissionPrintRev3                                  // Bit 12: Print (security handlers >= rev.3)
)

const (
	PermissionsNone  = PermissionFlags(0xF0C3)
	PermissionsPrint = PermissionsNone + PermissionPrintRev2 + PermissionPrintRev3
	PermissionsAll   = PermissionFlags(0xFFFF)
)

const (

	// StatsFileNameDefault is the standard stats filename.
	StatsFileNameDefault = "stats.csv"
)

// CommandMode specifies the operation being executed.
type CommandMode int

// The available commands.
const (
	VALIDATE CommandMode = iota
	LISTINFO
	OPTIMIZE
	SPLIT
	SPLITBYPAGENR
	MERGECREATE
	MERGECREATEZIP
	MERGEAPPEND
	EXTRACTIMAGES
	EXTRACTFONTS
	EXTRACTPAGES
	EXTRACTCONTENT
	EXTRACTMETADATA
	TRIM
	LISTATTACHMENTS
	EXTRACTATTACHMENTS
	ADDATTACHMENTS
	ADDATTACHMENTSPORTFOLIO
	REMOVEATTACHMENTS
	LISTPERMISSIONS
	SETPERMISSIONS
	ADDWATERMARKS
	REMOVEWATERMARKS
	IMPORTIMAGES
	INSERTPAGESBEFORE
	INSERTPAGESAFTER
	REMOVEPAGES
	LISTKEYWORDS
	ADDKEYWORDS
	REMOVEKEYWORDS
	LISTPROPERTIES
	ADDPROPERTIES
	REMOVEPROPERTIES
	COLLECT
	CROP
	LISTBOXES
	ADDBOXES
	REMOVEBOXES
	LISTANNOTATIONS
	ADDANNOTATIONS
	REMOVEANNOTATIONS
	ROTATE
	NUP
	BOOKLET
	LISTBOOKMARKS
	ADDBOOKMARKS
	REMOVEBOOKMARKS
	IMPORTBOOKMARKS
	EXPORTBOOKMARKS
	LISTIMAGES
	UPDATEIMAGES
	CREATE
	DUMP
	LISTFORMFIELDS
	REMOVEFORMFIELDS
	LOCKFORMFIELDS
	UNLOCKFORMFIELDS
	RESETFORMFIELDS
	EXPORTFORMFIELDS
	FILLFORMFIELDS
	MULTIFILLFORMFIELDS
	ENCRYPT
	DECRYPT
	CHANGEUPW
	CHANGEOPW
	CHEATSHEETSFONTS
	INSTALLFONTS
	LISTFONTS
	RESIZE
	POSTER
	NDOWN
	CUT
	LISTPAGELAYOUT
	SETPAGELAYOUT
	RESETPAGELAYOUT
	LISTPAGEMODE
	SETPAGEMODE
	RESETPAGEMODE
	LISTVIEWERPREFERENCES
	SETVIEWERPREFERENCES
	RESETVIEWERPREFERENCES
	ZOOM
	ADDSIGNATURE
	VALIDATESIGNATURE
	LISTCERTIFICATES
	INSPECTCERTIFICATES
	IMPORTCERTIFICATES
	VALIDATESIGNATURES
)

// Configuration of a ContextContext.
type Configuration struct {
	// Location of corresponding config.yml
	Path string

	CreationDate string

	Version string

	// Check filename extensions.
	CheckFileNameExt bool

	// Enables PDF V1.5 compatible processing of object streams, xref streams, hybrid PDF files.
	Reader15 bool

	// Enables decoding of all streams (fontfiles, images..) for logging purposes.
	DecodeAllStreams bool

	// Validate against ISO-32000: strict or relaxed.
	ValidationMode int

	// Enable validation right before writing.
	PostProcessValidate bool

	// Check for broken links in LinkedAnnotations/URIActions.
	ValidateLinks bool

	// End of line char sequence for writing.
	Eol string

	// Turns on object stream generation.
	// A signal for compressing any new non-stream-object into an object stream.
	// true enforces WriteXRefStream to true.
	// false does not prevent xRefStream generation.
	WriteObjectStream bool

	// Switches between xRefSection (<=V1.4) and objectStream/xRefStream (>=V1.5) writing.
	WriteXRefStream bool

	// Turns on stats collection.
	// TODO Decision - unused.
	CollectStats bool

	// A CSV-filename holding the statistics.
	StatsFileName string

	// Supplied user password.
	UserPW    string
	UserPWNew *string

	// Supplied owner password.
	OwnerPW    string
	OwnerPWNew *string

	// EncryptUsingAES ensures AES encryption.
	// true: AES encryption
	// false: RC4 encryption.
	EncryptUsingAES bool

	// AES:40,128,256 RC4:40,128
	EncryptKeyLength int

	// Supplied user access permissions, see Table 22.
	Permissions PermissionFlags // int16

	// Command being executed.
	Cmd CommandMode

	// Display unit in effect.
	Unit DisplayUnit

	// Timestamp format.
	TimestampFormat string

	// Date format.
	DateFormat string

	// Optimize after reading and validating the xreftable but before processing.
	Optimize bool

	// Optimize after processing but before writing.
	// TODO add to config.yml
	OptimizeBeforeWriting bool

	// Optimize page resources via content stream analysis. (assuming Optimize == true || OptimizeBeforeWriting == true)
	OptimizeResourceDicts bool

	// Optimize duplicate content streams across pages. (assuming Optimize == true || OptimizeBeforeWriting == true)
	OptimizeDuplicateContentStreams bool

	// Merge creates bookmarks.
	CreateBookmarks bool

	// PDF Viewer is expected to supply appearance streams for form fields.
	NeedAppearances bool

	// Internet availability.
	Offline bool

	// HTTP timeout in seconds.
	Timeout int

	// Http timeout in seconds for CRL revocation checking.
	TimeoutCRL int

	// Http timeout in seconds for OCSP revocation checking.
	TimeoutOCSP int

	// Preferred certificate revocation checking mechanism: CRL, OSCP
	PreferredCertRevocationChecker int
}

// ConfigPath defines the location of pdfcpu's configuration directory.
// If set to a file path, pdfcpu will ensure the config dir at this location.
// Other possible values:
//
//	default:	Ensure config dir at default location
//	disable:	Disable config dir usage
//
// If you want to disable config dir usage in a multi threaded environment
// you are encouraged to use api.DisableConfigDir().
var ConfigPath string = "default"

// VersionStr is the current pdfcpu version.
var VersionStr = "v0.11.0 dev"

func newDefaultConfiguration() *Configuration {
	// NOTE: Needs to stay in sync with config.yml
	//
	// Takes effect whenever the installed config.yml is disabled:
	// 		cli: supply -conf disable
	// 		api: call api.DisableConfigDir()
	return &Configuration{
		CreationDate:                    time.Now().Format("2006-01-02 15:04"),
		Version:                         VersionStr,
		CheckFileNameExt:                true,
		Reader15:                        true,
		DecodeAllStreams:                false,
		ValidationMode:                  1,
		ValidateLinks:                   false,
		Eol:                             EolLF,
		WriteObjectStream:               true,
		WriteXRefStream:                 true,
		EncryptUsingAES:                 true,
		EncryptKeyLength:                256,
		Permissions:                     PermissionsPrint,
		TimestampFormat:                 "2006-01-02 15:04",
		DateFormat:                      "2006-01-02",
		Optimize:                        true,
		OptimizeBeforeWriting:           true,
		OptimizeResourceDicts:           true,
		OptimizeDuplicateContentStreams: false,
		CreateBookmarks:                 true,
		NeedAppearances:                 false,
		Offline:                         false,
		Timeout:                         5,
		PreferredCertRevocationChecker:  CRL,
	}
}

// NewDefaultConfiguration returns the default pdfcpu configuration.
func NewDefaultConfiguration() *Configuration {
	return newDefaultConfiguration()
}

// NewAESConfiguration returns a default configuration for AES encryption.
func NewAESConfiguration(userPW, ownerPW string, keyLength int) *Configuration {
	c := NewDefaultConfiguration()
	c.UserPW = userPW
	c.OwnerPW = ownerPW
	c.EncryptUsingAES = true
	c.EncryptKeyLength = keyLength
	return c
}

// NewRC4Configuration returns a default configuration for RC4 encryption.
func NewRC4Configuration(userPW, ownerPW string, keyLength int) *Configuration {
	c := NewDefaultConfiguration()
	c.UserPW = userPW
	c.OwnerPW = ownerPW
	c.EncryptUsingAES = false
	c.EncryptKeyLength = keyLength
	return c
}

// EolString returns a string rep for the eol in effect.
func (c *Configuration) EolString() string {
	var s string
	switch c.Eol {
	case EolLF:
		s = "EolLF"
	case EolCR:
		s = "EolCR"
	case EolCRLF:
		s = "EolCRLF"
	}
	return s
}

// ValidationModeString returns a string rep for the validation mode in effect.
func (c *Configuration) ValidationModeString() string {
	if c.ValidationMode == ValidationStrict {
		return "strict"
	}
	return "relaxed"
}

// PreferredCertRevocationCheckerString returns a string rep for the preferred certificate revocation checker in effect.
func (c *Configuration) PreferredCertRevocationCheckerString() string {
	if c.PreferredCertRevocationChecker == CRL {
		return "CRL"
	}
	return "OSCP"
}

// UnitString returns a string rep for the display unit in effect.
func (c *Configuration) UnitString() string {
	var s string
	switch c.Unit {
	case POINTS:
		s = "points"
	case INCHES:
		s = "inches"
	case CENTIMETRES:
		s = "cm"
	case MILLIMETRES:
		s = "mm"
	}
	return s
}

// SetUnit configures the display unit.
func (c *Configuration) SetUnit(s string) {
	switch s {
	case "points":
		c.Unit = POINTS
	case "inches":
		c.Unit = INCHES
	case "cm":
		c.Unit = CENTIMETRES
	case "mm":
		c.Unit = MILLIMETRES
	}
}

// ApplyReducedFeatureSet returns true if complex entries like annotations shall not be written.
func (c *Configuration) ApplyReducedFeatureSet() bool {
	switch c.Cmd {
	case SPLIT, TRIM, EXTRACTPAGES, IMPORTIMAGES:
		return true
	}
	return false
}

func (ann AnnotationInterface) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d := Dict(map[string]Object{
		"Type":    NameType("Annot"),
		"Subtype": NameType(ann.TypeString()),
		"Rect":    ann.Rect.Array(),
	})

	if pageIndRef != nil {
		d["P"] = *pageIndRef
	}

	if ann.Contents != "" {
		s, err := EscapedUTF16String(ann.Contents)
		if err != nil {
			return nil, err
		}
		d.InsertString("Contents", *s)
	}

	if ann.NM != "" {
		d.InsertString("NM", ann.NM)
	}

	modDate := DateString(time.Now())
	if ann.ModificationDate != "" {
		_, ok := DateTime(ann.ModificationDate, xRefTable.ValidationMode == ValidationRelaxed)
		if !ok {
			return nil, errors.Errorf("pdfcpu: annotation renderDict - validateDateEntry: <%s> invalid date", ann.ModificationDate)
		}
		modDate = ann.ModificationDate
	}
	d.InsertString("ModDate", modDate)

	if ann.F != 0 {
		d["F"] = Integer(ann.F)
	}

	if ann.C != nil {
		d["C"] = ann.C.Array()
	}

	if ann.BorderWidth > 0 {
		d["Border"] = borderArray(ann.BorderRadX, ann.BorderRadY, ann.BorderWidth)
	}

	return d, nil
}

// PopupAnnotation represents PDF Popup annotations.
type PopupAnnotation struct {
	AnnotationInterface
	ParentIndRef *IndirectRef // The optional parent markup annotation with which this pop-up annotation shall be associated.
	Open         bool         // A flag specifying whether the annotation shall initially be displayed open.
}

// NewPopupAnnotation returns a new popup annotation.
func NewPopupAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,

	parentIndRef *IndirectRef,
	displayOpen bool,
) PopupAnnotation {
	ann := NewAnnotation(AnnPopup, "", rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth)

	return PopupAnnotation{
		AnnotationInterface: ann,
		ParentIndRef:        parentIndRef,
		Open:                displayOpen,
	}
}

// ContentString returns a string representation of ann's content.
func (ann PopupAnnotation) ContentString() string {
	s := "\"" + ann.Contents + "\""
	if ann.ParentIndRef != nil {
		s = "-> #" + ann.ParentIndRef.ObjectNumber.String()
	}
	return s
}

func (ann PopupAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.AnnotationInterface.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.ParentIndRef != nil {
		d["Parent"] = *ann.ParentIndRef
	}

	d["Open"] = Boolean(ann.Open)

	return d, nil
}

// DestinationType represents the various PDF destination
type DestinationType int

// See table 151
const (
	DestXYZ   DestinationType = iota // [page /XYZ left top zoom]
	DestFit                          // [page /Fit]
	DestFitH                         // [page /FitH top]
	DestFitV                         // [page /FitV left]
	DestFitR                         // [page /FitR left bottom right top]
	DestFitB                         // [page /FitB]
	DestFitBH                        // [page /FitBH top]
	DestFitBV                        // [page /FitBV left]
)

// DestinationTypeStrings manages string representations for destination
var DestinationTypeStrings = map[DestinationType]string{
	DestXYZ:   "XYZ",   // Position (left, top) at upper-left corner of window.
	DestFit:   "Fit",   // Fit entire page within window.
	DestFitH:  "FitH",  // Position with (top) at top edge of window.
	DestFitV:  "FitV",  // Position with (left) positioned at left edge of window.
	DestFitR:  "FitR",  // Fit (left, bottom, right, top) entirely within window.
	DestFitB:  "FitB",  // Magnify content just enough to fit its bounding box entirely within window.
	DestFitBH: "FitBH", // Position with (top) at top edge of window and contents fit bounding box width within window.
	DestFitBV: "FitBV", // Position with (left) at left edge of window and contents fit bounding box height within window.
}

// Destination represents a PDF destination.
type Destination struct {
	Typ                      DestinationType
	PageNr                   int
	Left, Bottom, Right, Top int
	Zoom                     float32
}

func (dest Destination) String() string {
	return DestinationTypeStrings[dest.Typ]
}

func (dest Destination) Name() NameType {
	return NameType(DestinationTypeStrings[dest.Typ])
}

func (dest Destination) Array(indRef IndirectRef) Array {
	arr := Array{indRef, dest.Name()}
	switch dest.Typ {
	case DestXYZ:
		arr = append(arr, Integer(dest.Left), Integer(dest.Top), Float(dest.Zoom))
	case DestFitH:
		arr = append(arr, Integer(dest.Top))
	case DestFitV:
		arr = append(arr, Integer(dest.Left))
	case DestFitR:
		arr = append(arr, Integer(dest.Left), Integer(dest.Bottom), Integer(dest.Right), Integer(dest.Top))
	case DestFitBH:
		arr = append(arr, Integer(dest.Top))
	case DestFitBV:
		arr = append(arr, Integer(dest.Left))
	}
	return arr
}

// LinkAnnotation represents a PDF link annotation.
type LinkAnnotation struct {
	AnnotationInterface
	Dest        *Destination // internal link
	URI         string       // external link
	Quad        QuadPoints   // shall be ignored if any coordinate lies outside the region specified by Rect.
	Border      bool         // render border using borderColor.
	BorderWidth float64
	BorderStyle BorderStyle
}

// NewLinkAnnotation returns a new link annotation.
func NewLinkAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	borderCol *SimpleColor,

	dest *Destination, // supply dest or uri, dest takes precedence
	uri string,
	quad QuadPoints,
	border bool,
	borderWidth float64,
	borderStyle BorderStyle,
) LinkAnnotation {
	ann := NewAnnotation(AnnLink, "", rect, apObjNr, contents, id, modDate, f, borderCol, 0, 0, 0)

	return LinkAnnotation{
		AnnotationInterface: ann,
		Dest:                dest,
		URI:                 uri,
		Quad:                quad,
		Border:              border,
		BorderWidth:         borderWidth,
		BorderStyle:         borderStyle,
	}
}

// ContentString returns a string representation of ann's content.
func (ann LinkAnnotation) ContentString() string {
	if len(ann.URI) > 0 {
		return ann.URI
	}
	if ann.Dest != nil {
		// eg. page /XYZ left top zoom
		return fmt.Sprintf("Page %d %s", ann.Dest.PageNr, ann.Dest)
	}
	return "internal link"
}

// RenderDict renders ann into a page annotation dict.
func (ann LinkAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.AnnotationInterface.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.Dest != nil {
		dest := ann.Dest
		if dest.Zoom == 0 {
			dest.Zoom = 1
		}
		_, indRef, pAttr, err := xRefTable.PageDict(dest.PageNr, false)
		if err != nil {
			return nil, err
		}
		if dest.Typ == DestXYZ && dest.Left < 0 && dest.Top < 0 {
			// Show top left corner of destination page.
			dest.Left = int(pAttr.MediaBox.LL.X)
			dest.Top = int(pAttr.MediaBox.UR.Y)
			if pAttr.CropBox != nil {
				dest.Left = int(pAttr.CropBox.LL.X)
				dest.Top = int(pAttr.CropBox.UR.Y)
			}
		}
		d["Dest"] = dest.Array(*indRef)
	} else {
		actionDict := Dict(map[string]Object{
			"Type": NameType("Action"),
			"S":    NameType("URI"),
			"URI":  StringLiteral(ann.URI),
		})
		d["A"] = actionDict
	}

	if ann.Quad != nil {
		d.Insert("QuadPoints", ann.Quad.Array())
	}

	if !ann.Border {
		d["Border"] = NewIntegerArray(0, 0, 0)
	} else {
		if ann.C != nil {
			d["C"] = ann.C.Array()
		}
	}

	d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)

	return d, nil
}

// MarkupAnnotation represents a PDF markup annotation.
type MarkupAnnotation struct {
	AnnotationInterface
	T            string       // The text label that shall be displayed in the title bar of the annotation’s pop-up window when open and active. This entry shall identify the user who added the annotation.
	PopupIndRef  *IndirectRef // An indirect reference to a pop-up annotation for entering or editing the text associated with this annotation.
	CA           *float64     // (Default: 1.0) The constant opacity value that shall be used in painting the annotation.
	RC           string       // A rich text string that shall be displayed in the pop-up window when the annotation is opened.
	CreationDate string       // The date and time when the annotation was created.
	Subj         string       // Text representing a short description of the subject being addressed by the annotation.
}

// NewMarkupAnnotation returns a new markup annotation.
func NewMarkupAnnotation(
	subType AnnotationType,
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,

	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,
) MarkupAnnotation {
	ann := NewAnnotation(subType, "", rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth)

	return MarkupAnnotation{
		AnnotationInterface: ann,
		T:                   title,
		PopupIndRef:         popupIndRef,
		CA:                  ca,
		RC:                  rc,
		CreationDate:        DateString(time.Now()),
		Subj:                subject,
	}
}

// ContentString returns a string representation of ann's content.
func (ann MarkupAnnotation) ContentString() string {
	s := "\"" + ann.Contents + "\""
	if ann.PopupIndRef != nil {
		s += "-> #" + ann.PopupIndRef.ObjectNumber.String()
	}
	return s
}

func (ann MarkupAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.AnnotationInterface.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.T != "" {
		s, err := EscapedUTF16String(ann.T)
		if err != nil {
			return nil, err
		}
		d.InsertString("T", *s)
	}

	if ann.PopupIndRef != nil {
		d.Insert("Popup", *ann.PopupIndRef)
	}

	if ann.CA != nil {
		d.Insert("CA", Float(*ann.CA))
	}

	if ann.RC != "" {
		s, err := EscapedUTF16String(ann.RC)
		if err != nil {
			return nil, err
		}
		d.InsertString("RC", *s)
	}

	d.InsertString("CreationDate", ann.CreationDate)

	if ann.Subj != "" {
		s, err := EscapedUTF16String(ann.Subj)
		if err != nil {
			return nil, err
		}
		d.InsertString("Subj", *s)
	}

	return d, nil
}

// TextAnnotation represents a PDF text annotation aka "Sticky Note".
type TextAnnotation struct {
	MarkupAnnotation
	Open bool   // A flag specifying whether the annotation shall initially be displayed open.
	Name string // The name of an icon that shall be used in displaying the annotation. Comment, Key, (Note), Help, NewParagraph, Paragraph, Insert
}

// NewTextAnnotation returns a new text annotation.
func NewTextAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,

	displayOpen bool,
	name string,
) TextAnnotation {
	ma := NewMarkupAnnotation(AnnText, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject)

	return TextAnnotation{
		MarkupAnnotation: ma,
		Open:             displayOpen,
		Name:             name,
	}
}

// RenderDict renders ann into a PDF annotation dict.
func (ann TextAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	d["Open"] = Boolean(ann.Open)

	if ann.Name != "" {
		d.InsertName("Name", ann.Name)
	}

	return d, nil
}

// FreeTextIntent represents the various free text annotation intents.
type FreeTextIntent int

const (
	IntentFreeText FreeTextIntent = 1 << iota
	IntentFreeTextCallout
	IntentFreeTextTypeWriter
)

func FreeTextIntentName(fti FreeTextIntent) string {
	var s string
	switch fti {
	case IntentFreeText:
		s = "FreeText"
	case IntentFreeTextCallout:
		s = "FreeTextCallout"
	case IntentFreeTextTypeWriter:
		s = "FreeTextTypeWriter"
	}
	return s
}

// Corner represents one of four rectangle corners.
type Corner int

// The four corners of a rectangle.
const (
	LowerLeft Corner = iota
	LowerRight
	UpperLeft
	UpperRight
)

// HAlignment represents the horizontal alignment of text.
type HAlignment int

// These are the options for horizontal aligned text.
const (
	AlignLeft HAlignment = iota
	AlignCenter
	AlignRight
	AlignJustify
)

// VAlignment represents the vertical alignment of text.
type VAlignment int

// These are the options for vertical aligned text.
const (
	AlignBaseline VAlignment = iota
	AlignTop
	AlignMiddle
	AlignBottom
)

// LineJoinStyle represents the shape to be used at the corners of paths that are stroked (see 8.4.3.4)
type LineJoinStyle int

// Render mode
const (
	LJMiter LineJoinStyle = iota
	LJRound
	LJBevel
)

func ParseHorAlignment(s string) (HAlignment, error) {
	var a HAlignment
	switch strings.ToLower(s) {
	case "l", "left":
		a = AlignLeft
	case "r", "right":
		a = AlignRight
	case "c", "center":
		a = AlignCenter
	case "j", "justify":
		a = AlignJustify
	default:
		return a, errors.Errorf("pdfcpu: unknown textfield alignment (left, center, right, justify): %s", s)
	}
	return a, nil
}

func ParseOrigin(s string) (Corner, error) {
	var c Corner
	switch strings.ToLower(s) {
	case "ll", "lowerleft":
		c = LowerLeft
	case "lr", "lowerright":
		c = LowerRight
	case "ul", "upperleft":
		c = UpperLeft
	case "ur", "upperright":
		c = UpperRight
	default:
		return c, errors.Errorf("pdfcpu: unknown origin (ll, lr, ul, ur): %s", s)
	}
	return c, nil
}

// Anchor represents symbolic positions within a rectangular region.
type Anchor int

func (a Anchor) String() string {
	switch a {

	case TopLeft:
		return "top left"

	case TopCenter:
		return "top center"

	case TopRight:
		return "top right"

	case Left:
		return "left"

	case Center:
		return "center"

	case Right:
		return "right"

	case BottomLeft:
		return "bottom left"

	case BottomCenter:
		return "bottom center"

	case BottomRight:
		return "bottom right"

	case Full:
		return "full"

	}

	return ""
}

// These are the defined anchors for relative positioning.
const (
	TopLeft Anchor = iota
	TopCenter
	TopRight
	Left
	Center // default
	Right
	BottomLeft
	BottomCenter
	BottomRight
	Full // special case, no anchor needed, imageSize = pageSize
)

func ParseAnchor(s string) (Anchor, error) {
	var a Anchor
	switch strings.ToLower(s) {
	case "tl", "topleft":
		a = TopLeft
	case "tc", "topcenter":
		a = TopCenter
	case "tr", "topright":
		a = TopRight
	case "l", "left":
		a = Left
	case "c", "center":
		a = Center
	case "r", "right":
		a = Right
	case "bl", "bottomleft":
		a = BottomLeft
	case "bc", "bottomcenter":
		a = BottomCenter
	case "br", "bottomright":
		a = BottomRight
	default:
		return a, errors.Errorf("pdfcpu: unknown anchor: %s", s)
	}
	return a, nil
}

func ParsePositionAnchor(s string) (Anchor, error) {
	var a Anchor
	switch s {
	case "tl", "topleft", "top-left":
		a = TopLeft
	case "tc", "topcenter", "top-center":
		a = TopCenter
	case "tr", "topright", "top-right":
		a = TopRight
	case "l", "left":
		a = Left
	case "c", "center":
		a = Center
	case "r", "right":
		a = Right
	case "bl", "bottomleft", "bottom-left":
		a = BottomLeft
	case "bc", "bottomcenter", "bottom-center":
		a = BottomCenter
	case "br", "bottomright", "bottom-right":
		a = BottomRight
	case "f", "full":
		a = Full
	default:
		return a, errors.Errorf("pdfcpu: unknown position anchor: %s", s)
	}
	return a, nil
}

func AnchorPosition(a Anchor, r *Rectangle, w, h float64) (x float64, y float64) {
	switch a {
	case TopLeft:
		x, y = 0, r.Height()-h
	case TopCenter:
		x, y = r.Width()/2-w/2, r.Height()-h
	case TopRight:
		x, y = r.Width()-w, r.Height()-h
	case Left:
		x, y = 0, r.Height()/2-h/2
	case Center:
		x, y = r.Width()/2-w/2, r.Height()/2-h/2
	case Right:
		x, y = r.Width()-w, r.Height()/2-h/2
	case BottomLeft:
		x, y = 0, 0
	case BottomCenter:
		x, y = r.Width()/2-w/2, 0
	case BottomRight:
		x, y = r.Width()-w, 0
	}
	return
}

// TODO Refactor because of orientation in nup.go
type Orientation int

const (
	Horizontal Orientation = iota
	Vertical
)

// RelPosition represents the relative position of a text field's label.
type RelPosition int

// These are the options for relative label positions.
const (
	RelPosLeft RelPosition = iota
	RelPosRight
	RelPosTop
	RelPosBottom
)

func ParseRelPosition(s string) (RelPosition, error) {
	var p RelPosition
	switch strings.ToLower(s) {
	case "l", "left":
		p = RelPosLeft
	case "r", "right":
		p = RelPosRight
	case "t", "top":
		p = RelPosTop
	case "b", "bottom":
		p = RelPosBottom
	default:
		return p, errors.Errorf("pdfcpu: unknown textfield alignment (left, right, top, bottom): %s", s)
	}
	return p, nil
}

// NormalizeCoord transfers P(x,y) from pdfcpu user space into PDF user space,
// which uses a coordinate system with origin in the lower left corner of r.
//
// pdfcpu user space coordinate systems have the origin in one of four corners of r:
//
// LowerLeft corner (default = PDF user space)
//
//	x extends to the right,
//	y extends upward
//
// LowerRight corner:
//
//	x extends to the left,
//	y extends upward
//
// UpperLeft corner:
//
//	x extends to the right,
//	y extends downward
//
// UpperRight corner:
//
//	x extends to the left,
//	y extends downward
func NormalizeCoord(x, y float64, r *Rectangle, origin Corner, absolute bool) (float64, float64) {
	switch origin {
	case UpperLeft:
		if y >= 0 {
			y = r.Height() - y
			if y < 0 {
				y = 0
			}
		}
	case LowerRight:
		if x >= 0 {
			x = r.Width() - x
			if x < 0 {
				x = 0
			}
		}
	case UpperRight:
		if x >= 0 {
			x = r.Width() - x
			if x < 0 {
				x = 0
			}
		}
		if y >= 0 {
			y = r.Height() - y
			if y < 0 {
				y = 0
			}
		}
	}
	if absolute {
		if x >= 0 {
			x += r.LL.X
		}
		if y >= 0 {
			y += r.LL.Y
		}
	}
	return x, y
}

// Normalize offset transfers x and y into offsets in the PDF user space.
func NormalizeOffset(x, y float64, origin Corner) (float64, float64) {
	switch origin {
	case UpperLeft:
		y = -y
	case LowerRight:
		x = -x
	case UpperRight:
		x = -x
		y = -y
	}
	return x, y
}

func BestFitRectIntoRect(rSrc, rDest *Rectangle, enforceOrient, scaleUp bool) (w, h, dx, dy, rot float64) {
	if !scaleUp && rSrc.FitsWithin(rDest) {
		// Translate rSrc into center of rDest without scaling.
		w = rSrc.Width()
		h = rSrc.Height()
		dx = rDest.Width()/2 - rSrc.Width()/2
		dy = rDest.Height()/2 - rSrc.Height()/2
		return
	}

	if rSrc.Landscape() {
		if rDest.Landscape() {
			if rSrc.AspectRatio() > rDest.AspectRatio() {
				w = rDest.Width()
				h = rSrc.ScaledHeight(w)
				dy = (rDest.Height() - h) / 2
			} else {
				h = rDest.Height()
				w = rSrc.ScaledWidth(h)
				dx = (rDest.Width() - w) / 2
			}
		} else {
			if enforceOrient {
				rot = 90
				if 1/rSrc.AspectRatio() < rDest.AspectRatio() {
					w = rDest.Height()
					h = rSrc.ScaledHeight(w)
					dx = (rDest.Width() - h) / 2
				} else {
					h = rDest.Width()
					w = rSrc.ScaledWidth(h)
					dy = (rDest.Height() - w) / 2
				}
				return
			}
			w = rDest.Width()
			h = rSrc.ScaledHeight(w)
			dy = (rDest.Height() - h) / 2
		}
		return
	}

	if rSrc.Portrait() {
		if rDest.Portrait() {
			if rSrc.AspectRatio() < rDest.AspectRatio() {
				h = rDest.Height()
				w = rSrc.ScaledWidth(h)
				dx = (rDest.Width() - w) / 2
			} else {
				w = rDest.Width()
				h = rSrc.ScaledHeight(w)
				dy = (rDest.Height() - h) / 2
			}
		} else {
			if enforceOrient {
				rot = 90
				if 1/rSrc.AspectRatio() > rDest.AspectRatio() {
					h = rDest.Width()
					w = rSrc.ScaledWidth(h)
					dy = (rDest.Height() - w) / 2
				} else {
					w = rDest.Height()
					h = rSrc.ScaledHeight(w)
					dx = (rDest.Width() - h) / 2
				}
				return
			}
			h = rDest.Height()
			w = rSrc.ScaledWidth(h)
			dx = (rDest.Width() - w) / 2
		}
		return
	}

	if rDest.Portrait() {
		w = rDest.Width()
		dy = rDest.Height()/2 - rSrc.ScaledHeight(w)/2
		h = w
	} else {
		h = rDest.Height()
		dx = rDest.Width()/2 - rSrc.ScaledWidth(h)/2
		w = h
	}

	return
}

func ParsePageFormat(v string) (*Dim, string, error) {
	// Optional: appended last letter L indicates landscape mode.
	// Optional: appended last letter P indicates portrait mode.
	// eg. A4L means A4 in landscape mode whereas A4 defaults to A4P
	// The default mode is defined implicitly via PaperSize dimensions.

	portrait := true

	if strings.HasSuffix(v, "L") {
		v = v[:len(v)-1]
		portrait = false
	} else {
		v = strings.TrimSuffix(v, "P")
	}

	d, ok := PaperSize[v]
	if !ok {
		return nil, v, errors.Errorf("pdfcpu: page format %s is unsupported.\n", v)
	}

	dim := Dim{d.Width, d.Height}
	if (d.Portrait() && !portrait) || (d.Landscape() && portrait) {
		dim.Width, dim.Height = dim.Height, dim.Width
	}

	return &dim, v, nil
}

// FreeText AnnotationInterface displays text directly on the page.
type FreeTextAnnotation struct {
	MarkupAnnotation
	Text                   string       // Rich text string, see XFA 3.3
	HAlign                 HAlignment   // Code specifying the form of quadding (justification)
	FontName               string       // font name
	FontSize               int          // font size
	FontCol                *SimpleColor // font color
	DS                     string       // Default style string
	Intent                 string       // Description of the intent of the free text annotation
	CallOutLine            Array        // if intent is FreeTextCallout
	CallOutLineEndingStyle string
	Margins                Array
	BorderWidth            float64
	BorderStyle            BorderStyle
	CloudyBorder           bool
	CloudyBorderIntensity  int // 0,1,2
}

// XFA conform rich text string examples:
// The<b> second </b>and<span style="font-weight:bold"> fourth </span> words are bold.
// The<i> second </i>and<span style="font-style:italic"> fourth </span> words are italicized.
// For more information see <a href="http://www.example.com/">this</a> web site.

// NewFreeTextAnnotation returns a new free text annotation.
func NewFreeTextAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	text string,
	hAlign HAlignment,
	fontName string,
	fontSize int,
	fontCol *SimpleColor,
	ds string,
	intent *FreeTextIntent,
	callOutLine Array,
	callOutLineEndingStyle *LineEndingStyle,
	MLeft, MTop, MRight, MBot float64,
	borderWidth float64,
	borderStyle BorderStyle,
	cloudyBorder bool,
	cloudyBorderIntensity int,
) FreeTextAnnotation {
	// validate required DA, DS

	// validate callOutline: 2 or 3 points => array of 4 or 6 numbers.

	ma := NewMarkupAnnotation(AnnFreeText, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	if cloudyBorderIntensity < 0 || cloudyBorderIntensity > 2 {
		cloudyBorderIntensity = 0
	}

	freeTextIntent := ""
	if intent != nil {
		freeTextIntent = FreeTextIntentName(*intent)
	}

	leStyle := ""
	if callOutLineEndingStyle != nil {
		leStyle = LineEndingStyleName(*callOutLineEndingStyle)
	}

	freeTextAnn := FreeTextAnnotation{
		MarkupAnnotation:       ma,
		Text:                   text,
		HAlign:                 hAlign,
		FontName:               fontName,
		FontSize:               fontSize,
		FontCol:                fontCol,
		DS:                     ds,
		Intent:                 freeTextIntent,
		CallOutLine:            callOutLine,
		CallOutLineEndingStyle: leStyle,
		BorderWidth:            borderWidth,
		BorderStyle:            borderStyle,
		CloudyBorder:           cloudyBorder,
		CloudyBorderIntensity:  cloudyBorderIntensity,
	}

	if MLeft > 0 || MTop > 0 || MRight > 0 || MBot > 0 {
		freeTextAnn.Margins = NewNumberArray(MLeft, MTop, MRight, MBot)
	}

	return freeTextAnn
}

// RenderDict renders ann into a PDF annotation dict.
func (ann FreeTextAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	da := ""

	// TODO Implement Tf operator

	// fontID, err := xRefTable.EnsureFont(ann.FontName) // in root page Resources?
	// if err != nil {
	// 	return nil, err
	// }

	// da := fmt.Sprintf("/%s %d Tf", fontID, ann.FontSize)

	if ann.FontCol != nil {
		da += fmt.Sprintf(" %.2f %.2f %.2f rg", ann.FontCol.R, ann.FontCol.G, ann.FontCol.B)
	}
	d["DA"] = StringLiteral(da)

	d.InsertInt("Q", int(ann.HAlign))

	if ann.Text == "" {
		if ann.Contents == "" {
			return nil, errors.New("pdfcpu: FreeTextAnnotation missing \"text\"")
		}
		ann.Text = ann.Contents
	}
	s, err := EscapedUTF16String(ann.Text)
	if err != nil {
		return nil, err
	}
	d.InsertString("RC", *s)

	if ann.DS != "" {
		d.InsertString("DS", ann.DS)
	}

	if ann.Intent != "" {
		d.InsertName("IT", ann.Intent)
		if ann.Intent == "FreeTextCallout" {
			if len(ann.CallOutLine) > 0 {
				d["CL"] = ann.CallOutLine
				d.InsertName("LE", ann.CallOutLineEndingStyle)
			}
		}
	}

	if ann.Margins != nil {
		d["RD"] = ann.Margins
	}

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	if ann.CloudyBorder && ann.CloudyBorderIntensity > 0 {
		d["BE"] = borderEffectDict(ann.CloudyBorder, ann.CloudyBorderIntensity)
	}

	return d, nil
}

// LineIntent represents the various line annotation intents.
type LineIntent int

const (
	IntentLineArrow LineIntent = 1 << iota
	IntentLineDimension
)

func LineIntentName(li LineIntent) string {
	var s string
	switch li {
	case IntentLineArrow:
		s = "LineArrow"
	case IntentLineDimension:
		s = "LineDimension"
	}
	return s
}

// LineAnnotation represents a line annotation.
type LineAnnotation struct {
	MarkupAnnotation
	P1, P2                    Point   // Two points in default user space.
	LineEndings               Array   // Optional array of two names that shall specify the line ending styles.
	LeaderLineLength          float64 // Length of leader lines in default user space that extend from each endpoint of the line perpendicular to the line itself.
	LeaderLineOffset          float64 // Non-negative number that shall represent the length of the leader line offset, which is the amount of empty space between the endpoints of the annotation and the beginning of the leader lines.
	LeaderLineExtensionLength float64 // Non-negative number that shall represents the length of leader line extensions that extend from the line proper 180 degrees from the leader lines,
	Intent                    string  // Optional description of the intent of the line annotation.
	Measure                   Dict    // Optional measure dictionary that shall specify the scale and units that apply to the line annotation.
	Caption                   bool    // Use text specified by "Contents" or "RC" as caption.
	CaptionPositionTop        bool    // if true the caption shall be on top of the line else caption shall be centred inside the line.
	CaptionOffsetX            float64
	CaptionOffsetY            float64
	FillCol                   *SimpleColor
	BorderWidth               float64
	BorderStyle               BorderStyle
}

// NewLineAnnotation returns a new line annotation.
func NewLineAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	p1, p2 Point,
	beginLineEndingStyle *LineEndingStyle,
	endLineEndingStyle *LineEndingStyle,
	leaderLineLength float64,
	leaderLineOffset float64,
	leaderLineExtensionLength float64,
	intent *LineIntent,
	measure Dict,
	caption bool,
	captionPosTop bool,
	captionOffsetX float64,
	captionOffsetY float64,
	fillCol *SimpleColor,
	borderWidth float64,
	borderStyle BorderStyle,
) LineAnnotation {
	ma := NewMarkupAnnotation(AnnLine, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	lineIntent := ""
	if intent != nil {
		lineIntent = LineIntentName(*intent)
	}

	lineAnn := LineAnnotation{
		MarkupAnnotation:          ma,
		P1:                        p1,
		P2:                        p2,
		LeaderLineLength:          leaderLineLength,
		LeaderLineOffset:          leaderLineOffset,
		LeaderLineExtensionLength: leaderLineExtensionLength,
		Intent:                    lineIntent,
		Measure:                   measure,
		Caption:                   caption,
		CaptionPositionTop:        captionPosTop,
		CaptionOffsetX:            captionOffsetX,
		CaptionOffsetY:            captionOffsetY,
		FillCol:                   fillCol,
		BorderWidth:               borderWidth,
		BorderStyle:               borderStyle,
	}

	if beginLineEndingStyle != nil && endLineEndingStyle != nil {
		lineAnn.LineEndings = NewNameArray(
			LineEndingStyleName(*beginLineEndingStyle),
			LineEndingStyleName(*endLineEndingStyle),
		)
	}

	return lineAnn
}

func (ann LineAnnotation) validateLeaderLineAttrs() error {
	if ann.LeaderLineExtensionLength < 0 {
		return errors.New("pdfcpu: LineAnnotation leader line extension length must not be negative.")
	}

	if ann.LeaderLineExtensionLength > 0 && ann.LeaderLineLength == 0 {
		return errors.New("pdfcpu: LineAnnotation leader line length missing.")
	}

	if ann.LeaderLineOffset < 0 {
		return errors.New("pdfcpu: LineAnnotation leader line offset must not be negative.")
	}

	return nil
}

// RenderDict renders ann into a PDF annotation dict.
func (ann LineAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if err := ann.validateLeaderLineAttrs(); err != nil {
		return nil, err
	}

	d["L"] = NewNumberArray(ann.P1.X, ann.P1.Y, ann.P2.X, ann.P2.Y)

	if ann.LeaderLineExtensionLength > 0 {
		d["LLE"] = Float(ann.LeaderLineExtensionLength)
	}

	if ann.LeaderLineLength > 0 {
		d["LL"] = Float(ann.LeaderLineLength)
		if ann.LeaderLineOffset > 0 {
			d["LLO"] = Float(ann.LeaderLineOffset)
		}
	}

	if len(ann.Measure) > 0 {
		d["Measure"] = ann.Measure
	}

	if ann.Intent != "" {
		d.InsertName("IT", ann.Intent)
	}

	d["Cap"] = Boolean(ann.Caption)
	if ann.Caption {
		if ann.CaptionPositionTop {
			d["CP"] = NameType("Top")
		}
		d["CO"] = NewNumberArray(ann.CaptionOffsetX, ann.CaptionOffsetY)
	}

	if ann.FillCol != nil {
		d["IC"] = ann.FillCol.Array()
	}

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	if len(ann.LineEndings) == 2 {
		d["LE"] = ann.LineEndings
	}

	return d, nil
}

// SquareAnnotation represents a square annotation.
type SquareAnnotation struct {
	MarkupAnnotation
	FillCol               *SimpleColor
	Margins               Array
	BorderWidth           float64
	BorderStyle           BorderStyle
	CloudyBorder          bool
	CloudyBorderIntensity int // 0,1,2
}

// NewSquareAnnotation returns a new square annotation.
func NewSquareAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	fillCol *SimpleColor,
	MLeft, MTop, MRight, MBot float64,
	borderWidth float64,
	borderStyle BorderStyle,
	cloudyBorder bool,
	cloudyBorderIntensity int,
) SquareAnnotation {
	ma := NewMarkupAnnotation(AnnSquare, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	if cloudyBorderIntensity < 0 || cloudyBorderIntensity > 2 {
		cloudyBorderIntensity = 0
	}

	squareAnn := SquareAnnotation{
		MarkupAnnotation:      ma,
		FillCol:               fillCol,
		BorderWidth:           borderWidth,
		BorderStyle:           borderStyle,
		CloudyBorder:          cloudyBorder,
		CloudyBorderIntensity: cloudyBorderIntensity,
	}

	if MLeft > 0 || MTop > 0 || MRight > 0 || MBot > 0 {
		squareAnn.Margins = NewNumberArray(MLeft, MTop, MRight, MBot)
	}

	return squareAnn
}

// RenderDict renders ann into a page annotation dict.
func (ann SquareAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.FillCol != nil {
		d["IC"] = ann.FillCol.Array()
	}

	if ann.Margins != nil {
		d["RD"] = ann.Margins
	}

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	if ann.CloudyBorder && ann.CloudyBorderIntensity > 0 {
		d["BE"] = borderEffectDict(ann.CloudyBorder, ann.CloudyBorderIntensity)
	}

	return d, nil
}

// CircleAnnotation represents a square annotation.
type CircleAnnotation struct {
	MarkupAnnotation
	FillCol               *SimpleColor
	Margins               Array
	BorderWidth           float64
	BorderStyle           BorderStyle
	CloudyBorder          bool
	CloudyBorderIntensity int // 0,1,2
}

// NewCircleAnnotation returns a new circle annotation.
func NewCircleAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	fillCol *SimpleColor,
	MLeft, MTop, MRight, MBot float64,
	borderWidth float64,
	borderStyle BorderStyle,
	cloudyBorder bool,
	cloudyBorderIntensity int,
) CircleAnnotation {
	ma := NewMarkupAnnotation(AnnCircle, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	if cloudyBorderIntensity < 0 || cloudyBorderIntensity > 2 {
		cloudyBorderIntensity = 0
	}

	circleAnn := CircleAnnotation{
		MarkupAnnotation:      ma,
		FillCol:               fillCol,
		BorderWidth:           borderWidth,
		BorderStyle:           borderStyle,
		CloudyBorder:          cloudyBorder,
		CloudyBorderIntensity: cloudyBorderIntensity,
	}

	if MLeft > 0 || MTop > 0 || MRight > 0 || MBot > 0 {
		circleAnn.Margins = NewNumberArray(MLeft, MTop, MRight, MBot)
	}

	return circleAnn
}

// RenderDict renders ann into a page annotation dict.
func (ann CircleAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.FillCol != nil {
		d["IC"] = ann.FillCol.Array()
	}

	if ann.Margins != nil {
		d["RD"] = ann.Margins
	}

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	if ann.CloudyBorder && ann.CloudyBorderIntensity > 0 {
		d["BE"] = borderEffectDict(ann.CloudyBorder, ann.CloudyBorderIntensity)
	}

	return d, nil
}

// PolygonIntent represents the various polygon annotation intents.
type PolygonIntent int

const (
	IntentPolygonCloud PolygonIntent = 1 << iota
	IntentPolygonDimension
)

func PolygonIntentName(pi PolygonIntent) string {
	var s string
	switch pi {
	case IntentPolygonCloud:
		s = "PolygonCloud"
	case IntentPolygonDimension:
		s = "PolygonDimension"
	}
	return s
}

// PolygonAnnotation represents a polygon annotation.
type PolygonAnnotation struct {
	MarkupAnnotation
	Vertices              Array  // Array of numbers specifying the alternating horizontal and vertical coordinates, respectively, of each vertex, in default user space.
	Path                  Array  // Array of n arrays, each supplying the operands for a path building operator (m, l or c).
	Intent                string // Optional description of the intent of the polygon annotation.
	Measure               Dict   // Optional measure dictionary that shall specify the scale and units that apply to the annotation.
	FillCol               *SimpleColor
	BorderWidth           float64
	BorderStyle           BorderStyle
	CloudyBorder          bool
	CloudyBorderIntensity int // 0,1,2
}

// NewPolygonAnnotation returns a new polygon annotation.
func NewPolygonAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	vertices Array,
	path Array,
	intent *PolygonIntent,
	measure Dict,
	fillCol *SimpleColor,
	borderWidth float64,
	borderStyle BorderStyle,
	cloudyBorder bool,
	cloudyBorderIntensity int,
) PolygonAnnotation {
	ma := NewMarkupAnnotation(AnnPolygon, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	polygonIntent := ""
	if intent != nil {
		polygonIntent = PolygonIntentName(*intent)
	}

	if cloudyBorderIntensity < 0 || cloudyBorderIntensity > 2 {
		cloudyBorderIntensity = 0
	}

	polygonAnn := PolygonAnnotation{
		MarkupAnnotation:      ma,
		Vertices:              vertices,
		Path:                  path,
		Intent:                polygonIntent,
		Measure:               measure,
		FillCol:               fillCol,
		BorderWidth:           borderWidth,
		BorderStyle:           borderStyle,
		CloudyBorder:          cloudyBorder,
		CloudyBorderIntensity: cloudyBorderIntensity,
	}

	return polygonAnn
}

// RenderDict renders ann into a PDF annotation dict.
func (ann PolygonAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if len(ann.Measure) > 0 {
		d["Measure"] = ann.Measure
	}

	if len(ann.Vertices) > 0 && len(ann.Path) > 0 {
		return nil, errors.New("pdfcpu: PolygonAnnotation supports \"Vertices\" or \"Path\" only")
	}

	if len(ann.Vertices) > 0 {
		d["Vertices"] = ann.Vertices
	} else {
		d["Path"] = ann.Path
	}

	if ann.Intent != "" {
		d.InsertName("IT", ann.Intent)
	}

	if ann.FillCol != nil {
		d["IC"] = ann.FillCol.Array()
	}

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	if ann.CloudyBorder && ann.CloudyBorderIntensity > 0 {
		d["BE"] = borderEffectDict(ann.CloudyBorder, ann.CloudyBorderIntensity)
	}

	return d, nil
}

// PolyLineIntent represents the various polyline annotation intents.
type PolyLineIntent int

const (
	IntentPolyLinePolygonCloud PolyLineIntent = 1 << iota
	IntentPolyLineDimension
)

func PolyLineIntentName(pi PolyLineIntent) string {
	var s string
	switch pi {
	case IntentPolyLineDimension:
		s = "PolyLineDimension"
	}
	return s
}

type PolyLineAnnotation struct {
	MarkupAnnotation
	Vertices    Array  // Array of numbers specifying the alternating horizontal and vertical coordinates, respectively, of each vertex, in default user space.
	Path        Array  // Array of n arrays, each supplying the operands for a path building operator (m, l or c).
	Intent      string // Optional description of the intent of the polyline annotation.
	Measure     Dict   // Optional measure dictionary that shall specify the scale and units that apply to the annotation.
	FillCol     *SimpleColor
	BorderWidth float64
	BorderStyle BorderStyle
	LineEndings Array // Optional array of two names that shall specify the line ending styles.
}

// NewPolyLineAnnotation returns a new polyline annotation.
func NewPolyLineAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	vertices Array,
	path Array,
	intent *PolyLineIntent,
	measure Dict,
	fillCol *SimpleColor,
	borderWidth float64,
	borderStyle BorderStyle,
	beginLineEndingStyle *LineEndingStyle,
	endLineEndingStyle *LineEndingStyle,
) PolyLineAnnotation {
	ma := NewMarkupAnnotation(AnnPolyLine, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	polyLineIntent := ""
	if intent != nil {
		polyLineIntent = PolyLineIntentName(*intent)
	}

	polyLineAnn := PolyLineAnnotation{
		MarkupAnnotation: ma,
		Vertices:         vertices,
		Path:             path,
		Intent:           polyLineIntent,
		Measure:          measure,
		FillCol:          fillCol,
		BorderWidth:      borderWidth,
		BorderStyle:      borderStyle,
	}

	if beginLineEndingStyle != nil && endLineEndingStyle != nil {
		polyLineAnn.LineEndings = NewNameArray(
			LineEndingStyleName(*beginLineEndingStyle),
			LineEndingStyleName(*endLineEndingStyle),
		)
	}

	return polyLineAnn
}

// RenderDict renders ann into a PDF annotation dict.
func (ann PolyLineAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if len(ann.Measure) > 0 {
		d["Measure"] = ann.Measure
	}

	if len(ann.Vertices) > 0 && len(ann.Path) > 0 {
		return nil, errors.New("pdfcpu: PolyLineAnnotation supports \"Vertices\" or \"Path\" only")
	}

	if len(ann.Vertices) > 0 {
		d["Vertices"] = ann.Vertices
	} else {
		d["Path"] = ann.Path
	}

	if ann.Intent != "" {
		d.InsertName("IT", ann.Intent)
	}

	if ann.FillCol != nil {
		d["IC"] = ann.FillCol.Array()
	}

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	if len(ann.LineEndings) == 2 {
		d["LE"] = ann.LineEndings
	}

	return d, nil
}

type TextMarkupAnnotation struct {
	MarkupAnnotation
	Quad QuadPoints
}

func NewTextMarkupAnnotation(
	subType AnnotationType,
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	quad QuadPoints,
) TextMarkupAnnotation {
	ma := NewMarkupAnnotation(subType, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject)

	return TextMarkupAnnotation{
		MarkupAnnotation: ma,
		Quad:             quad,
	}
}

func (ann TextMarkupAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.Quad != nil {
		d.Insert("QuadPoints", ann.Quad.Array())
	}

	return d, nil
}

type HighlightAnnotation struct {
	TextMarkupAnnotation
}

func NewHighlightAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	quad QuadPoints,
) HighlightAnnotation {
	return HighlightAnnotation{
		NewTextMarkupAnnotation(AnnHighLight, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject, quad),
	}
}

type UnderlineAnnotation struct {
	TextMarkupAnnotation
}

func NewUnderlineAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	quad QuadPoints,
) UnderlineAnnotation {
	return UnderlineAnnotation{
		NewTextMarkupAnnotation(AnnUnderline, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject, quad),
	}
}

type SquigglyAnnotation struct {
	TextMarkupAnnotation
}

func NewSquigglyAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	quad QuadPoints,
) SquigglyAnnotation {
	return SquigglyAnnotation{
		NewTextMarkupAnnotation(AnnSquiggly, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject, quad),
	}
}

type StrikeOutAnnotation struct {
	TextMarkupAnnotation
}

func NewStrikeOutAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	quad QuadPoints,
) StrikeOutAnnotation {
	return StrikeOutAnnotation{
		NewTextMarkupAnnotation(AnnStrikeOut, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject, quad),
	}
}

type CaretAnnotation struct {
	MarkupAnnotation
	RD        *Rectangle // A set of four numbers that shall describe the numerical differences between two rectangles: the Rect entry of the annotation and the actual boundaries of the underlying caret.
	Paragraph bool       // A new paragraph symbol (¶) shall be associated with the caret.
}

func NewCaretAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	borderRadX float64,
	borderRadY float64,
	borderWidth float64,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	rd *Rectangle,
	paragraph bool,
) CaretAnnotation {
	ma := NewMarkupAnnotation(AnnCaret, rect, apObjNr, contents, id, modDate, f, col, borderRadX, borderRadY, borderWidth, title, popupIndRef, ca, rc, subject)

	return CaretAnnotation{
		MarkupAnnotation: ma,
		RD:               rd,
		Paragraph:        paragraph,
	}
}

func (ann CaretAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	if ann.RD != nil {
		d["RD"] = ann.RD.Array()
	}

	if ann.Paragraph {
		d["Sy"] = NameType("P")
	}

	return d, nil
}

// A series of alternating x and y coordinates in PDF user space, specifying points along the path.
type InkPath []float64

type InkAnnotation struct {
	MarkupAnnotation
	InkList     []InkPath // Array of n arrays, each representing a stroked path of points in user space.
	BorderWidth float64
	BorderStyle BorderStyle
}

func NewInkAnnotation(
	rect Rectangle,
	apObjNr int,
	contents, id string,
	modDate string,
	f AnnotationFlags,
	col *SimpleColor,
	title string,
	popupIndRef *IndirectRef,
	ca *float64,
	rc, subject string,

	ink []InkPath,
	borderWidth float64,
	borderStyle BorderStyle,
) InkAnnotation {
	ma := NewMarkupAnnotation(AnnInk, rect, apObjNr, contents, id, modDate, f, col, 0, 0, 0, title, popupIndRef, ca, rc, subject)

	return InkAnnotation{
		MarkupAnnotation: ma,
		InkList:          ink,
		BorderWidth:      borderWidth,
		BorderStyle:      borderStyle,
	}
}

func (ann InkAnnotation) RenderDict(xRefTable *XRefTable, pageIndRef *IndirectRef) (Dict, error) {
	d, err := ann.MarkupAnnotation.RenderDict(xRefTable, pageIndRef)
	if err != nil {
		return nil, err
	}

	ink := Array{}
	for i := range ann.InkList {
		ink = append(ink, NewNumberArray(ann.InkList[i]...))
	}
	d["InkList"] = ink

	if ann.BorderWidth > 0 {
		d["BS"] = borderStyleDict(ann.BorderWidth, ann.BorderStyle)
	}

	return d, nil
}

// AnnotMap represents annotations by object number of the corresponding annotation dict.
type AnnotMap map[int]AnnotationRenderer

type Annot struct {
	IndRefs *[]IndirectRef
	Map     AnnotMap
}

// PgAnnots represents a map of page annotations by type.
type PgAnnots map[AnnotationType]Annot

// Version is a type for the internal representation of PDF versions.
type Version int

const (
	V10 Version = iota
	V11
	V12
	V13
	V14
	V15
	V16
	V17
	V20
)

// PDFVersion returns the PDFVersion for a version string.
func PDFVersion(versionStr string) (Version, error) {
	switch versionStr {
	case "1.0":
		return V10, nil
	case "1.1":
		return V11, nil
	case "1.2":
		return V12, nil
	case "1.3":
		return V13, nil
	case "1.4":
		return V14, nil
	case "1.5":
		return V15, nil
	case "1.6":
		return V16, nil
	case "1.7":
		return V17, nil
	case "2.0":
		return V20, nil
	}

	return -1, errors.New(versionStr)
}

// String returns a string representation for a given PDFVersion.
func (v Version) String() string {
	if v == V20 {
		return "2.0"
	}
	return "1." + fmt.Sprintf("%d", v)
}

func identicalMajorAndMinorVersions(v1, v2 string) bool {
	ss1 := strings.Split(v1, ".")
	if len(ss1) < 2 {
		return false
	}

	ss2 := strings.Split(v2, ".")
	if len(ss2) < 2 {
		return false
	}

	return ss1[0] == ss2[0] && ss1[1] == ss2[1]
}

// CheckConfigVersion prints a warning if the configuration is outdated.
func CheckConfigVersion(v string) {
	if identicalMajorAndMinorVersions(v, VersionStr) {
		return
	}
}

type UserDate time.Time

const (
	userDateFormatNoTimeZone  = "2006-01-02T15:04:05Z"
	userDateFormatNegTimeZone = "2006-01-02T15:04:05-07:00"
	userDateFormatPosTimeZone = "2006-01-02T15:04:05+07:00"
)

func (ud *UserDate) UnmarshalXML(d *xml.Decoder, start xml.StartElement) error {
	dateString := ""
	err := d.DecodeElement(&dateString, &start)
	if err != nil {
		return err
	}
	dat, err := time.Parse(userDateFormatNoTimeZone, dateString)
	if err == nil {
		*ud = UserDate(dat)
		return nil
	}
	dat, err = time.Parse(userDateFormatPosTimeZone, dateString)
	if err == nil {
		*ud = UserDate(dat)
		return nil
	}
	dat, err = time.Parse(userDateFormatNegTimeZone, dateString)
	if err == nil {
		*ud = UserDate(dat)
		return nil
	}
	return err
}

type Alt struct {
	// XMLName xml.Name `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# Alt"`
	Entries []string `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# li"`
}

type Seq struct {
	// XMLName xml.Name `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# Seq"`
	Entries []string `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# li"`
}

type Title struct {
	// XMLName xml.Name `xml:"http://purl.org/dc/elements/1.1/ title"`
	Alt Alt `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# Alt"`
}

type Desc struct {
	// XMLName xml.Name `xml:"http://purl.org/dc/elements/1.1/ description"`
	Alt Alt `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# Alt"`
}

type Creator struct {
	// XMLName xml.Name `xml:"http://purl.org/dc/elements/1.1/ creator"`
	Seq Seq `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# Seq"`
}

type Description struct {
	// XMLName      xml.Name `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# Description"`
	Title        Title    `xml:"http://purl.org/dc/elements/1.1/ title"`
	Author       Creator  `xml:"http://purl.org/dc/elements/1.1/ creator"`
	Subject      Desc     `xml:"http://purl.org/dc/elements/1.1/ description"`
	Creator      string   `xml:"http://ns.adobe.com/xap/1.0/ CreatorTool"`
	CreationDate UserDate `xml:"http://ns.adobe.com/xap/1.0/ CreateDate"`
	ModDate      UserDate `xml:"http://ns.adobe.com/xap/1.0/ ModifyDate"`
	Producer     string   `xml:"http://ns.adobe.com/pdf/1.3/ Producer"`
	Trapped      bool     `xml:"http://ns.adobe.com/pdf/1.3/ Trapped"`
	Keywords     string   `xml:"http://ns.adobe.com/pdf/1.3/ Keywords"`
}

type RDF struct {
	XMLName     xml.Name `xml:"http://www.w3.org/1999/02/22-rdf-syntax-ns# RDF"`
	Description Description
}

type XMPMeta struct {
	XMLName xml.Name `xml:"adobe:ns:meta/ xmpmeta"`
	RDF     RDF
}

func removeTag(s, kw string) string {
	kwLen := len(kw)
	i := strings.Index(s, kw)
	if i < 0 {
		return ""
	}

	j := i + kwLen

	i = strings.LastIndex(s[:i], "<")
	if i < 0 {
		return ""
	}

	block1 := s[:i]

	s = s[j:]
	i = strings.Index(s, kw)
	if i < 0 {
		return ""
	}

	j = i + kwLen

	block2 := s[j:]

	s1 := block1 + block2

	return s1
}

func ModelRemoveKeywords(metadata *[]byte) error {
	// Opt for simple byte removal instead of xml de/encoding.

	s := string(*metadata)
	if len(s) == 0 {
		return nil
	}

	s = removeTag(s, "Keywords>")
	if len(s) == 0 {
		return nil
	}

	// Possible Acrobat bug.
	// Acrobat seems to use dc:subject for keywords but ***does not*** show the content in Subject.
	s = removeTag(s, "subject>")

	*metadata = []byte(s)

	return nil
}

type PageMode int

const (
	PageModeUseNone PageMode = iota
	PageModeUseOutlines
	PageModeUseThumbs
	PageModeFullScreen
	PageModeUseOC
	PageModeUseAttachments
)

func PageModeFor(s string) *PageMode {
	if s == "" {
		return nil
	}
	var pm PageMode
	switch strings.ToLower(s) {
	case "usenone":
		pm = PageModeUseNone
	case "useoutlines":
		pm = PageModeUseOutlines
	case "usethumbs":
		pm = PageModeUseThumbs
	case "fullscreen":
		pm = PageModeFullScreen
	case "useoc":
		pm = PageModeUseOC
	case "useattachments":
		pm = PageModeUseAttachments
	default:
		return nil
	}
	return &pm
}

func (pm *PageMode) String() string {
	if pm == nil {
		return ""
	}
	switch *pm {
	case PageModeUseNone:
		return "UseNone" // = default
	case PageModeUseOutlines:
		return "UseOutlines"
	case PageModeUseThumbs:
		return "UseThumbs"
	case PageModeFullScreen:
		return "FullScreen"
	case PageModeUseOC:
		return "UseOC"
	case PageModeUseAttachments:
		return "UseAttachments"
	default:
		return "?"
	}
}

type PageLayout int

const (
	PageLayoutSinglePage PageLayout = iota
	PageLayoutTwoColumnLeft
	PageLayoutTwoColumnRight
	PageLayoutTwoPageLeft
	PageLayoutTwoPageRight
)

func PageLayoutFor(s string) *PageLayout {
	if s == "" {
		return nil
	}
	var pl PageLayout
	switch strings.ToLower(s) {
	case "singlepage":
		pl = PageLayoutSinglePage
	case "twocolumnleft":
		pl = PageLayoutTwoColumnLeft
	case "twocolumnright":
		pl = PageLayoutTwoColumnRight
	case "twopageleft":
		pl = PageLayoutTwoPageLeft
	case "twopageright":
		pl = PageLayoutTwoPageRight
	default:
		return nil
	}
	return &pl
}

func (pl *PageLayout) String() string {
	if pl == nil {
		return ""
	}
	switch *pl {
	case PageLayoutSinglePage:
		return "SinglePage" // = default
	case PageLayoutTwoColumnLeft:
		return "TwoColumnLeft"
	case PageLayoutTwoColumnRight:
		return "TwoColumnRight"
	case PageLayoutTwoPageLeft:
		return "TwoPageLeft"
	case PageLayoutTwoPageRight:
		return "TwoPageRight"
	default:
		return "?"
	}
}

type NonFullScreenPageMode PageMode

const (
	NFSPageModeUseNone NonFullScreenPageMode = iota
	NFSPageModeUseOutlines
	NFSPageModeUseThumb
	NFSPageModeUseOC
)

type PageBoundary int

const (
	MediaBox PageBoundary = iota
	CropBox
	TrimBox
	BleedBox
	ArtBox
)

func PageBoundaryFor(s string) *PageBoundary {
	if s == "" {
		return nil
	}
	var pb PageBoundary
	switch strings.ToLower(s) {
	case "mediabox":
		pb = MediaBox
	case "cropbox":
		pb = CropBox
	case "trimbox":
		pb = TrimBox
	case "bleedbox":
		pb = BleedBox
	case "artbox":
		pb = ArtBox
	default:
		return nil
	}
	return &pb
}

func (pb *PageBoundary) String() string {
	if pb == nil {
		return ""
	}
	switch *pb {
	case MediaBox:
		return "MediaBox"
	case CropBox:
		return "CropBox"
	case TrimBox:
		return "TrimBox"
	case BleedBox:
		return "BleedBox"
	case ArtBox:
		return "ArtBox"
	default:
		return "?"
	}
}

type PrintScaling int

const (
	PrintScalingNone PrintScaling = iota
	PrintScalingAppDefault
)

func PrintScalingFor(s string) *PrintScaling {
	if s == "" {
		return nil
	}
	var ps PrintScaling
	switch strings.ToLower(s) {
	case "none":
		ps = PrintScalingNone
	case "appdefault":
		ps = PrintScalingAppDefault
	default:
		return nil
	}
	return &ps
}

func (ps *PrintScaling) String() string {
	if ps == nil {
		return ""
	}
	switch *ps {
	case PrintScalingNone:
		return "None"
	case PrintScalingAppDefault:
		return "AppDefault"
	default:
		return "?"
	}
}

type Direction int

const (
	L2R Direction = iota
	R2L
)

func DirectionFor(s string) *Direction {
	if s == "" {
		return nil
	}
	var d Direction
	switch strings.ToLower(s) {
	case "l2r":
		d = L2R
	case "r2l":
		d = R2L
	default:
		return nil
	}
	return &d
}

func (d *Direction) String() string {
	if d == nil {
		return ""
	}
	switch *d {
	case L2R:
		return "L2R"
	case R2L:
		return "R2L"
	default:
		return "?"
	}
}

type PaperHandling int

const (
	Simplex PaperHandling = iota
	DuplexFlipShortEdge
	DuplexFlipLongEdge
)

func PaperHandlingFor(s string) *PaperHandling {
	if s == "" {
		return nil
	}
	var ph PaperHandling
	switch strings.ToLower(s) {
	case "simplex":
		ph = Simplex
	case "duplexflipshortedge":
		ph = DuplexFlipShortEdge
	case "duplexfliplongedge":
		ph = DuplexFlipLongEdge
	default:
		return nil
	}
	return &ph
}

func (ph *PaperHandling) String() string {
	if ph == nil {
		return ""
	}
	switch *ph {
	case Simplex:
		return "Simplex"
	case DuplexFlipShortEdge:
		return "DuplexFlipShortEdge"
	case DuplexFlipLongEdge:
		return "DuplexFlipLongEdge"
	default:
		return "?"
	}
}

// ViewerPreferences see 12.2 Table 147
type ViewerPreferences struct {
	HideToolbar           *bool
	HideMenubar           *bool
	HideWindowUI          *bool
	FitWindow             *bool
	CenterWindow          *bool
	DisplayDocTitle       *bool // since 1.4
	NonFullScreenPageMode *NonFullScreenPageMode
	Direction             *Direction     // since 1.3
	ViewArea              *PageBoundary  // since 1.4 to 1.7
	ViewClip              *PageBoundary  // since 1.4 to 1.7
	PrintArea             *PageBoundary  // since 1.4 to 1.7
	PrintClip             *PageBoundary  // since 1.4 to 1.7
	PrintScaling          *PrintScaling  // since 1.6
	Duplex                *PaperHandling // since 1.7
	PickTrayByPDFSize     *bool          // since 1.7
	PrintPageRange        Array          // since 1.7
	NumCopies             *Integer       // since 1.7
	Enforce               Array          // since 2.0
}

func (vp *ViewerPreferences) validatePrinterPreferences(version Version) error {
	if vp.PrintScaling != nil && version < V16 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"PrintScaling\" - since PDF 1.6, got: %v\n", version)
	}
	if vp.Duplex != nil && version < V17 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"Duplex\" - since PDF 1.7, got: %v\n", version)
	}
	if vp.PickTrayByPDFSize != nil && version < V17 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"PickTrayByPDFSize\" - since PDF 1.7, got: %v\n", version)
	}
	if len(vp.PrintPageRange) > 0 && version < V17 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"PrintPageRange\" - since PDF 1.7, got: %v\n", version)
	}
	if vp.NumCopies != nil && version < V17 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"NumCopies\" - since PDF 1.7, got: %v\n", version)
	}
	if len(vp.Enforce) > 0 && version < V20 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"Enforce\" - since PDF 2.0, got: %v\n", version)
	}

	return nil
}

func (vp *ViewerPreferences) Validate(version Version) error {
	if vp.Direction != nil && version < V13 {
		return errors.Errorf("pdfcpu: invalid viewer preference \"Direction\" - since PDF 1.3, got: %v\n", version)
	}
	if vp.ViewArea != nil && (version < V14 || version > V17) {
		return errors.Errorf("pdfcpu: invalid viewer preference \"ViewArea\" - since PDF 1.4 until PDF 1.7, got: %v\n", version)
	}
	if vp.ViewClip != nil && (version < V14 || version > V17) {
		return errors.Errorf("pdfcpu: invalid viewer preference \"ViewClip\" - since PDF 1.4 until PDF 1.7, got: %v\n", version)
	}
	if vp.PrintArea != nil && (version < V14 || version > V17) {
		return errors.Errorf("pdfcpu: invalid viewer preference \"PrintArea\" - since PDF 1.4 until PDF 1.7, got: %v\n", version)
	}
	if vp.PrintClip != nil && (version < V14 || version > V17) {
		return errors.Errorf("pdfcpu: invalid viewer preference \"PrintClip\" - since PDF 1.4 until PDF 1.7, got: %v\n", version)
	}

	return vp.validatePrinterPreferences(version)
}

func (vp *ViewerPreferences) SetHideToolBar(val bool) {
	vp.HideToolbar = &val
}

func (vp *ViewerPreferences) SetHideMenuBar(val bool) {
	vp.HideMenubar = &val
}

func (vp *ViewerPreferences) SetHideWindowUI(val bool) {
	vp.HideWindowUI = &val
}

func (vp *ViewerPreferences) SetFitWindow(val bool) {
	vp.FitWindow = &val
}

func (vp *ViewerPreferences) SetCenterWindow(val bool) {
	vp.CenterWindow = &val
}

func (vp *ViewerPreferences) SetDisplayDocTitle(val bool) {
	vp.DisplayDocTitle = &val
}

func (vp *ViewerPreferences) SetPickTrayByPDFSize(val bool) {
	vp.PickTrayByPDFSize = &val
}

func (vp *ViewerPreferences) SetNumCopies(i int) {
	vp.NumCopies = (*Integer)(&i)
}

func (vp *ViewerPreferences) populatePrinterPreferences(vp1 *ViewerPreferences) {
	if vp1.PrintArea != nil {
		vp.PrintArea = vp1.PrintArea
	}
	if vp1.PrintClip != nil {
		vp.PrintClip = vp1.PrintClip
	}
	if vp1.PrintScaling != nil {
		vp.PrintScaling = vp1.PrintScaling
	}
	if vp1.Duplex != nil {
		vp.Duplex = vp1.Duplex
	}
	if vp1.PickTrayByPDFSize != nil {
		vp.PickTrayByPDFSize = vp1.PickTrayByPDFSize
	}
	if len(vp1.PrintPageRange) > 0 {
		vp.PrintPageRange = vp1.PrintPageRange
	}
	if vp1.NumCopies != nil {
		vp.NumCopies = vp1.NumCopies
	}
	if len(vp1.Enforce) > 0 {
		vp.Enforce = vp1.Enforce
	}
}

func (vp *ViewerPreferences) Populate(vp1 *ViewerPreferences) {
	if vp1.HideToolbar != nil {
		vp.HideToolbar = vp1.HideToolbar
	}
	if vp1.HideMenubar != nil {
		vp.HideMenubar = vp1.HideMenubar
	}
	if vp1.HideWindowUI != nil {
		vp.HideWindowUI = vp1.HideWindowUI
	}
	if vp1.FitWindow != nil {
		vp.FitWindow = vp1.FitWindow
	}
	if vp1.CenterWindow != nil {
		vp.CenterWindow = vp1.CenterWindow
	}
	if vp1.DisplayDocTitle != nil {
		vp.DisplayDocTitle = vp1.DisplayDocTitle
	}
	if vp1.NonFullScreenPageMode != nil {
		vp.NonFullScreenPageMode = vp1.NonFullScreenPageMode
	}
	if vp1.Direction != nil {
		vp.Direction = vp1.Direction
	}
	if vp1.ViewArea != nil {
		vp.ViewArea = vp1.ViewArea
	}
	if vp1.ViewClip != nil {
		vp.ViewClip = vp1.ViewClip
	}

	vp.populatePrinterPreferences(vp1)
}

func DefaultViewerPreferences(version Version) *ViewerPreferences {
	vp := ViewerPreferences{}
	vp.SetHideToolBar(false)
	vp.SetHideMenuBar(false)
	vp.SetHideWindowUI(false)
	vp.SetFitWindow(false)
	vp.SetCenterWindow(false)
	if version >= V14 {
		vp.SetDisplayDocTitle(false)
	}
	vp.NonFullScreenPageMode = (*NonFullScreenPageMode)(PageModeFor("UseNone"))
	if version >= V13 {
		vp.Direction = DirectionFor("L2R")
	}
	if version >= V14 && version < V20 {
		vp.ViewArea = PageBoundaryFor("CropBox")
		vp.ViewClip = PageBoundaryFor("CropBox")
		vp.PrintArea = PageBoundaryFor("CropBox")
		vp.PrintClip = PageBoundaryFor("CropBox")
	}
	if version >= V16 {
		vp.PrintScaling = PrintScalingFor("AppDefault")
	}
	if version >= V17 {
		vp.SetNumCopies(1)
	}

	return &vp
}

func ViewerPreferencesWithDefaults(vp *ViewerPreferences, version Version) (*ViewerPreferences, error) {
	vp1 := DefaultViewerPreferences(version)

	if vp == nil {
		return vp1, nil
	}

	vp1.Populate(vp)

	return vp1, nil
}

type ViewerPrefJSON struct {
	HideToolbar           *bool    `json:"hideToolbar,omitempty"`
	HideMenubar           *bool    `json:"hideMenubar,omitempty"`
	HideWindowUI          *bool    `json:"hideWindowUI,omitempty"`
	FitWindow             *bool    `json:"fitWindow,omitempty"`
	CenterWindow          *bool    `json:"centerWindow,omitempty"`
	DisplayDocTitle       *bool    `json:"displayDocTitle,omitempty"`
	NonFullScreenPageMode string   `json:"nonFullScreenPageMode,omitempty"`
	Direction             string   `json:"direction,omitempty"`
	ViewArea              string   `json:"viewArea,omitempty"`
	ViewClip              string   `json:"viewClip,omitempty"`
	PrintArea             string   `json:"printArea,omitempty"`
	PrintClip             string   `json:"printClip,omitempty"`
	PrintScaling          string   `json:"printScaling,omitempty"`
	Duplex                string   `json:"duplex,omitempty"`
	PickTrayByPDFSize     *bool    `json:"pickTrayByPDFSize,omitempty"`
	PrintPageRange        []int    `json:"printPageRange,omitempty"`
	NumCopies             *int     `json:"numCopies,omitempty"`
	Enforce               []string `json:"enforce,omitempty"`
}

func (vp *ViewerPreferences) MarshalJSON() ([]byte, error) {
	vpJSON := ViewerPrefJSON{
		HideToolbar:           vp.HideToolbar,
		HideMenubar:           vp.HideMenubar,
		HideWindowUI:          vp.HideWindowUI,
		FitWindow:             vp.FitWindow,
		CenterWindow:          vp.CenterWindow,
		DisplayDocTitle:       vp.DisplayDocTitle,
		NonFullScreenPageMode: (*PageMode)(vp.NonFullScreenPageMode).String(),
		Direction:             vp.Direction.String(),
		ViewArea:              vp.ViewArea.String(),
		ViewClip:              vp.ViewClip.String(),
		PrintArea:             vp.PrintArea.String(),
		PrintClip:             vp.PrintClip.String(),
		PrintScaling:          vp.PrintScaling.String(),
		Duplex:                vp.Duplex.String(),
		PickTrayByPDFSize:     vp.PickTrayByPDFSize,
		NumCopies:             (*int)(vp.NumCopies),
	}

	if len(vp.PrintPageRange) > 0 {
		var ii []int
		for _, v := range vp.PrintPageRange {
			ii = append(ii, v.(Integer).Value())
		}
		vpJSON.PrintPageRange = ii
	}

	if len(vp.Enforce) > 0 {
		var ss []string
		for _, v := range vp.Enforce {
			ss = append(ss, v.(NameType).Value())
		}
		vpJSON.Enforce = ss
	}

	return json.Marshal(&vpJSON)
}

func (vp *ViewerPreferences) unmarshalPrintPageRange(vpJSON ViewerPrefJSON) error {
	if len(vpJSON.PrintPageRange) > 0 {
		arr := vpJSON.PrintPageRange
		if len(arr)%2 > 0 {
			return errors.New("pdfcpu: invalid \"PrintPageRange\" - expecting pairs of ascending page numbers\n")
		}
		for i := 0; i < len(arr); i += 2 {
			if arr[i] >= arr[i+1] {
				// TODO validate ascending, non overlapping int intervals.
				return errors.New("pdfcpu: invalid \"PrintPageRange\" - expecting pairs of ascending page numbers\n")
			}
		}
		vp.PrintPageRange = NewIntegerArray(arr...)
	}

	return nil
}

func (vp *ViewerPreferences) unmarshalPrinterPreferences(vpJSON ViewerPrefJSON) error {
	vp.PrintArea = PageBoundaryFor(vpJSON.PrintArea)
	if vpJSON.PrintArea != "" && vp.PrintArea == nil {
		return errors.Errorf("pdfcpu: unknown \"PrintArea\", got: %s want one of: MediaBox, CropBox, TrimBox, BleedBox, ArtBox\n", vpJSON.PrintArea)
	}

	vp.PrintClip = PageBoundaryFor(vpJSON.PrintClip)
	if vpJSON.PrintClip != "" && vp.PrintClip == nil {
		return errors.Errorf("pdfcpu: unknown \"PrintClip\", got: %s want one of: MediaBox, CropBox, TrimBox, BleedBox, ArtBox\n", vpJSON.PrintClip)
	}

	vp.PrintScaling = PrintScalingFor(vpJSON.PrintScaling)
	if vpJSON.PrintScaling != "" && vp.PrintScaling == nil {
		return errors.Errorf("pdfcpu: unknown \"PrintScaling\", got: %s, want one of: None, AppDefault", vpJSON.PrintScaling)
	}

	vp.Duplex = PaperHandlingFor(vpJSON.Duplex)
	if vpJSON.Duplex != "" && vp.Duplex == nil {
		return errors.Errorf("pdfcpu: unknown \"Duplex\", got: %s, want one of: Simplex, DuplexFlipShortEdge, DuplexFlipLongEdge", vpJSON.Duplex)
	}

	if err := vp.unmarshalPrintPageRange(vpJSON); err != nil {
		return err
	}

	if len(vpJSON.Enforce) > 1 {
		return errors.New("pdfcpu: \"Enforce\" must be array with one element: \"PrintScaling\"\n")
	}

	if len(vpJSON.Enforce) > 0 {
		if vpJSON.Enforce[0] != "PrintScaling" {
			return errors.New("pdfcpu: \"Enforce\" must be array with one element: \"PrintScaling\"\n")
		}
		vp.Enforce = NewNameArray("PrintScaling")
	}

	return nil
}

func (vp *ViewerPreferences) UnmarshalJSON(data []byte) error {
	vpJSON := ViewerPrefJSON{}

	if err := json.Unmarshal(data, &vpJSON); err != nil {
		return err
	}

	*vp = ViewerPreferences{
		HideToolbar:       vpJSON.HideToolbar,
		HideMenubar:       vpJSON.HideMenubar,
		HideWindowUI:      vpJSON.HideWindowUI,
		FitWindow:         vpJSON.FitWindow,
		CenterWindow:      vpJSON.CenterWindow,
		DisplayDocTitle:   vpJSON.DisplayDocTitle,
		PickTrayByPDFSize: vpJSON.PickTrayByPDFSize,
		NumCopies:         (*Integer)(vpJSON.NumCopies),
	}

	if vp.NumCopies != nil && *vp.NumCopies < 1 {
		return errors.Errorf("pdfcpu: invalid \"NumCopies\", got: %d, want a numerical value > 0", *vp.NumCopies)
	}

	vp.NonFullScreenPageMode = (*NonFullScreenPageMode)(PageModeFor(vpJSON.NonFullScreenPageMode))
	if vpJSON.NonFullScreenPageMode != "" {
		if vp.NonFullScreenPageMode == nil {
			return errors.Errorf("pdfcpu: unknown \"NonFullScreenPageMode\", got: %s want one of: UseNone, UseOutlines, UseThumbs, UseOC\n", vpJSON.NonFullScreenPageMode)
		}
		pm := (PageMode)(*vp.NonFullScreenPageMode)
		if pm == PageModeFullScreen || pm == PageModeUseAttachments {
			return errors.Errorf("pdfcpu: unknown \"NonFullScreenPageMode\", got: %s want one of: UseNone, UseOutlines, UseThumbs, UseOC\n", vpJSON.NonFullScreenPageMode)
		}
	}

	vp.Direction = DirectionFor(vpJSON.Direction)
	if vpJSON.Direction != "" && vp.Direction == nil {
		return errors.Errorf("pdfcpu: unknown \"Direction\", got: %s want one of: L2R, R2L\n", vpJSON.Direction)
	}

	vp.ViewArea = PageBoundaryFor(vpJSON.ViewArea)
	if vpJSON.ViewArea != "" && vp.ViewArea == nil {
		return errors.Errorf("pdfcpu: unknown \"ViewArea\", got: %s want one of: MediaBox, CropBox, TrimBox, BleedBox, ArtBox\n", vpJSON.ViewArea)
	}

	vp.ViewClip = PageBoundaryFor(vpJSON.ViewClip)
	if vpJSON.ViewClip != "" && vp.ViewClip == nil {
		return errors.Errorf("pdfcpu: unknown \"ViewClip\", got: %s want one of: MediaBox, CropBox, TrimBox, BleedBox, ArtBox\n", vpJSON.ViewClip)
	}

	return vp.unmarshalPrinterPreferences(vpJSON)
}

func renderViewerFlags(vp ViewerPreferences, ss *[]string) {
	if vp.HideToolbar != nil {
		*ss = append(*ss, fmt.Sprintf("%22s%s = %t", "", "HideToolbar", *vp.HideToolbar))
	}

	if vp.HideMenubar != nil {
		*ss = append(*ss, fmt.Sprintf("%22s%s = %t", "", "HideMenubar", *vp.HideMenubar))
	}

	if vp.HideWindowUI != nil {
		*ss = append(*ss, fmt.Sprintf("%22s%s = %t", "", "HideWindowUI", *vp.HideWindowUI))
	}

	if vp.FitWindow != nil {
		*ss = append(*ss, fmt.Sprintf("%22s%s = %t", "", "FitWindow", *vp.FitWindow))
	}

	if vp.CenterWindow != nil {
		*ss = append(*ss, fmt.Sprintf("%22s%s = %t", "", "CenterWindow", *vp.CenterWindow))
	}

	if vp.DisplayDocTitle != nil {
		*ss = append(*ss, fmt.Sprintf("%22s%s = %t", "", "DisplayDocTitle", *vp.DisplayDocTitle))
	}

	if vp.NonFullScreenPageMode != nil {
		pm := PageMode(*vp.NonFullScreenPageMode)
		*ss = append(*ss, fmt.Sprintf("%22s%s = %s", "", "NonFullScreenPageMode", pm.String()))
	}
}

func listViewerFlags(vp ViewerPreferences, ss *[]string) {
	if vp.HideToolbar != nil {
		*ss = append(*ss, fmt.Sprintf("%s = %t", "HideToolbar", *vp.HideToolbar))
	}

	if vp.HideMenubar != nil {
		*ss = append(*ss, fmt.Sprintf("%s = %t", "HideMenubar", *vp.HideMenubar))
	}

	if vp.HideWindowUI != nil {
		*ss = append(*ss, fmt.Sprintf("%s = %t", "HideWindowUI", *vp.HideWindowUI))
	}

	if vp.FitWindow != nil {
		*ss = append(*ss, fmt.Sprintf("%s = %t", "FitWindow", *vp.FitWindow))
	}

	if vp.CenterWindow != nil {
		*ss = append(*ss, fmt.Sprintf("%s = %t", "CenterWindow", *vp.CenterWindow))
	}

	if vp.DisplayDocTitle != nil {
		*ss = append(*ss, fmt.Sprintf("%s = %t", "DisplayDocTitle", *vp.DisplayDocTitle))
	}

	if vp.NonFullScreenPageMode != nil {
		pm := PageMode(*vp.NonFullScreenPageMode)
		*ss = append(*ss, fmt.Sprintf("%s = %s", "NonFullScreenPageMode", pm.String()))
	}
}

func (vp ViewerPreferences) listPrinterPreferences() []string {
	var ss []string

	if vp.PrintArea != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "PrintArea", vp.PrintArea))
	}

	if vp.PrintClip != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "PrintClip", vp.PrintClip))
	}

	if vp.PrintScaling != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "PrintScaling", vp.PrintScaling))
	}

	if vp.Duplex != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "Duplex", vp.Duplex))
	}

	if vp.PickTrayByPDFSize != nil {
		ss = append(ss, fmt.Sprintf("%s = %t", "PickTrayByPDFSize", *vp.PickTrayByPDFSize))
	}

	if len(vp.PrintPageRange) > 0 {
		var ss1 []string
		for i := 0; i < len(vp.PrintPageRange); i += 2 {
			ss1 = append(ss1, fmt.Sprintf("%d-%d", vp.PrintPageRange[i].(Integer), vp.PrintPageRange[i+1].(Integer)))
		}
		ss = append(ss, fmt.Sprintf("%s = %s", "PrintPageRange", strings.Join(ss1, ",")))
	}

	if vp.NumCopies != nil {
		ss = append(ss, fmt.Sprintf("%s = %d", "NumCopies", *vp.NumCopies))
	}

	if len(vp.Enforce) > 0 {
		var ss1 []string
		for _, v := range vp.Enforce {
			ss1 = append(ss1, v.String())
		}
		ss = append(ss, fmt.Sprintf("%s = %s", "Enforce", strings.Join(ss1, ",")))
	}

	return ss
}

// List generates output for the viewer pref command.
func (vp ViewerPreferences) List() []string {
	var ss []string

	listViewerFlags(vp, &ss)

	if vp.Direction != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "Direction", vp.Direction))
	}

	if vp.ViewArea != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "ViewArea", vp.ViewArea))
	}

	if vp.ViewClip != nil {
		ss = append(ss, fmt.Sprintf("%s = %s", "ViewClip", vp.ViewClip))
	}

	ss = append(ss, vp.listPrinterPreferences()...)

	if len(ss) > 0 {
		ss1 := []string{"Viewer preferences:"}
		for _, s := range ss {
			ss1 = append(ss1, "   "+s)
		}
		ss = ss1
	} else {
		ss = append(ss, "No viewer preferences available.")
	}

	return ss
}

// String generates output for the info command.
func (vp ViewerPreferences) String() string {
	var ss []string

	renderViewerFlags(vp, &ss)

	if vp.Direction != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "Direction", vp.Direction))
	}

	if vp.ViewArea != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "ViewArea", vp.ViewArea))
	}

	if vp.ViewClip != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "ViewClip", vp.ViewClip))
	}

	if vp.PrintArea != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "PrintArea", vp.PrintArea))
	}

	if vp.PrintClip != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "PrintClip", vp.PrintClip))
	}

	if vp.PrintScaling != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "PrintScaling", vp.PrintScaling))
	}

	if vp.Duplex != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "Duplex", vp.Duplex))
	}

	if vp.PickTrayByPDFSize != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %t", "", "PickTrayByPDFSize", *vp.PickTrayByPDFSize))
	}

	if len(vp.PrintPageRange) > 0 {
		var ss1 []string
		for i := 0; i < len(vp.PrintPageRange); i += 2 {
			ss1 = append(ss1, fmt.Sprintf("%d-%d", vp.PrintPageRange[i].(Integer), vp.PrintPageRange[i+1].(Integer)))
		}
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "PrintPageRange", strings.Join(ss1, ",")))
	}

	if vp.NumCopies != nil {
		ss = append(ss, fmt.Sprintf("%22s%s = %d", "", "NumCopies", *vp.NumCopies))
	}

	if len(vp.Enforce) > 0 {
		var ss1 []string
		for _, v := range vp.Enforce {
			ss1 = append(ss1, v.String())
		}
		ss = append(ss, fmt.Sprintf("%22s%s = %s", "", "Enforce", strings.Join(ss1, ",")))
	}

	return strings.TrimSpace(strings.Join(ss, "\n"))
}

const (
	Unknown = iota
	False   // aka invalid, not ok
	True    // aka  valid, ok
)

// Preferred cert revocation checking mechanism values
const (
	CRL = iota
	OCSP
)

const (
	CertifiedSigPermNone = iota
	CertifiedSigPermNoChangesAllowed
	CertifiedSigPermFillingAndSigningOK
	CertifiedSigPermFillingAnnotatingAndSigningOK
)

const (
	SigTypeForm = iota
	SigTypePage
	SigTypeUR
	SigTypeDTS
)

const SignTSFormat = "2006-01-02 15:04:05 -0700"

type RevocationDetails struct {
	Status int
	Reason string
}

func (rd RevocationDetails) String() string {
	ss := []string{}
	ss = append(ss, fmt.Sprintf(" Status: %s", validString(rd.Status)))
	if len(rd.Reason) > 0 {
		ss = append(ss, fmt.Sprintf("                                         Reason: %s", rd.Reason))
	}
	return strings.Join(ss, "\n")
}

type TrustDetails struct {
	Status                                int
	Reason                                string
	SourceObtainedFrom                    string
	AllowSignDocuments                    bool
	AllowCertifyDocuments                 bool
	AllowExecuteDynamicContent            bool
	AllowExecuteJavaScript                bool
	AllowExecutePrivilegedSystemOperation bool
}

func (td TrustDetails) String() string {
	ss := []string{}
	ss = append(ss, fmt.Sprintf("      Status: %s", validString(td.Status)))
	if len(td.Reason) > 0 {
		ss = append(ss, fmt.Sprintf("                                         Reason: %s", td.Reason))
	}
	// if td.Status == True {
	// 	ss = append(ss, fmt.Sprintf("                                         SourceObtainedFrom:                    %s", td.SourceObtainedFrom))
	// 	ss = append(ss, fmt.Sprintf("                                         AllowSignDocuments:                    %t", td.AllowSignDocuments))
	// 	ss = append(ss, fmt.Sprintf("                                         AllowCertifyDocuments:                 %t", td.AllowCertifyDocuments))
	// 	ss = append(ss, fmt.Sprintf("                                         AllowExecuteDynamicContent:            %t", td.AllowExecuteDynamicContent))
	// 	ss = append(ss, fmt.Sprintf("                                         AllowExecuteJavaScript:                %t", td.AllowExecuteJavaScript))
	// 	ss = append(ss, fmt.Sprintf("                                         AllowExecutePrivilegedSystemOperation: %t", td.AllowExecutePrivilegedSystemOperation))
	// }
	return strings.Join(ss, "\n")
}

type CertificateDetails struct {
	Leaf              bool
	SelfSigned        bool
	Subject           string
	Issuer            string
	SerialNumber      string
	ValidFrom         time.Time
	ValidThru         time.Time
	Expired           bool
	Qualified         bool
	CA                bool
	Usage             string
	Version           int
	SignAlg           string
	KeySize           int
	Revocation        RevocationDetails
	Trust             TrustDetails
	IssuerCertificate *CertificateDetails
}

func (cd CertificateDetails) String() string {
	ss := []string{}
	ss = append(ss, fmt.Sprintf("                             Subject:    %s", cd.Subject))
	ss = append(ss, fmt.Sprintf("                             Issuer:     %s", cd.Issuer))
	ss = append(ss, fmt.Sprintf("                             SerialNr:   %s", cd.SerialNumber))
	ss = append(ss, fmt.Sprintf("                             Valid From: %s", cd.ValidFrom.Format(SignTSFormat)))
	ss = append(ss, fmt.Sprintf("                             Valid Thru: %s", cd.ValidThru.Format(SignTSFormat)))
	ss = append(ss, fmt.Sprintf("                             Expired:    %t", cd.Expired))
	ss = append(ss, fmt.Sprintf("                             Qualified:  %t", cd.Qualified))
	ss = append(ss, fmt.Sprintf("                             CA:         %t", cd.CA))
	ss = append(ss, fmt.Sprintf("                             Usage:      %s", cd.Usage))
	ss = append(ss, fmt.Sprintf("                             Version:    %d", cd.Version))
	ss = append(ss, fmt.Sprintf("                             SignAlg:    %s", cd.SignAlg))
	ss = append(ss, fmt.Sprintf("                             Key Size:   %d bits", cd.KeySize))
	ss = append(ss, fmt.Sprintf("                             SelfSigned: %t", cd.SelfSigned))
	ss = append(ss, fmt.Sprintf("                             Trust:%s", cd.Trust))
	if cd.Leaf && !cd.SelfSigned {
		ss = append(ss, fmt.Sprintf("                             Revocation:%s", cd.Revocation))
	}

	if cd.IssuerCertificate != nil {
		s := "             Intermediate"
		if cd.IssuerCertificate.IssuerCertificate == nil {
			s = "             Root"
		}
		if cd.IssuerCertificate.CA {
			s += "CA"
		}
		ss = append(ss, s+":")
		ss = append(ss, cd.IssuerCertificate.String())
	}
	return strings.Join(ss, "\n")
}

// Signature represents a digital signature.
type Signature struct {
	Type          int
	Certified     bool
	Authoritative bool
	Visible       bool
	Signed        bool
	ObjNr         int
	PageNr        int
}

func (sig Signature) String(status SignatureStatus) string {
	s := ""
	if sig.Type == SigTypeForm {
		s = "form signature ("
	} else if sig.Type == SigTypePage {
		s = "page signature ("
	} else if sig.Type == SigTypeUR {
		s = "usage rights signature ("
	} else {
		s = "document timestamp ("
	}

	if sig.Type != SigTypeDTS {
		if sig.Certified {
			s += "certified, "
		} else if sig.Authoritative {
			s += "authoritative, "
		}
	}

	if sig.Type == SigTypeDTS {
		s1 := "trusted, "
		if status != SignatureStatusValid {
			s1 = "not " + s1
		}
		s += s1
	}

	if sig.Visible {
		s += "visible, "
	} else {
		s += "invisible, "
	}

	if sig.Signed {
		s += "signed)"
	} else {
		s += "unsigned)"
	}

	if sig.Visible {
		s += fmt.Sprintf(" on page %d", sig.PageNr)
	}

	// s += fmt.Sprintf(" objNr%d", sig.ObjNr)

	return s
}

// SignatureStats represents signature stats for a file.
type SignatureStats struct {
	FormSigned          int
	FormSignedVisible   int
	FormUnsigned        int
	FormUnsignedVisible int
	PageSigned          int
	PageSignedVisible   int
	PageUnsigned        int
	PageUnsignedVisible int
	URSigned            int
	URSignedVisible     int
	URUnsigned          int
	URUnsignedVisible   int
	DTSSigned           int
	DTSSignedVisible    int
	DTSUnsigned         int
	DTSUnsignedVisible  int

	Total int
}

func (sigStats SignatureStats) Counter(svr *SignatureValidationResult) (*int, *int, *int, *int) {
	switch svr.Type {
	case SigTypeForm:
		return &sigStats.FormSigned, &sigStats.FormSignedVisible, &sigStats.FormUnsigned, &sigStats.FormUnsignedVisible
	case SigTypePage:
		return &sigStats.PageSigned, &sigStats.PageSignedVisible, &sigStats.PageUnsigned, &sigStats.PageUnsignedVisible
	case SigTypeUR:
		return &sigStats.URSigned, &sigStats.URSignedVisible, &sigStats.URUnsigned, &sigStats.URUnsignedVisible
	case SigTypeDTS:
		return &sigStats.DTSSigned, &sigStats.DTSSignedVisible, &sigStats.DTSUnsigned, &sigStats.DTSUnsignedVisible
	}
	return nil, nil, nil, nil
}

// SignatureStatus represents all possible signature statuses.
type SignatureStatus int

const (
	SignatureStatusUnknown SignatureStatus = 1 << iota
	SignatureStatusValid
	SignatureStatusInvalid
)

// SignatureStatusStrings manages string representations for signature statuses.
var SignatureStatusStrings = map[SignatureStatus]string{
	SignatureStatusUnknown: "validity of the signature is unknown",
	SignatureStatusValid:   "signature is valid",
	SignatureStatusInvalid: "signature is invalid",
}

func (st SignatureStatus) String() string {
	return SignatureStatusStrings[st]
}

type SignatureReason int

const (
	SignatureReasonUnknown SignatureReason = 1 << iota
	SignatureReasonDocNotModified
	SignatureReasonDocModified
	SignatureReasonSignatureForged
	SignatureReasonSigningTimeInvalid
	SignatureReasonTimestampTokenInvalid
	SignatureReasonCertInvalid
	SignatureReasonCertNotTrusted
	SignatureReasonCertExpired
	SignatureReasonCertRevoked
	SignatureReasonInternal
	SignatureReasonSelfSignedCertErr
)

// SignatureReasonStrings manages string representations for signature reasons.
var SignatureReasonStrings = map[SignatureReason]string{
	SignatureReasonUnknown:               "no reason",
	SignatureReasonDocNotModified:        "document has not been modified",
	SignatureReasonDocModified:           "document has been modified",
	SignatureReasonSignatureForged:       "signer's signature is not authentic",
	SignatureReasonTimestampTokenInvalid: "timestamp token is invalid",
	SignatureReasonCertInvalid:           "signer's certificate is invalid",
	SignatureReasonCertNotTrusted:        "signer's certificate chain is not in the trusted list of Root CAs",
	SignatureReasonCertExpired:           "signer's certificate or one of its parent certificates has expired",
	SignatureReasonCertRevoked:           "signer's certificate or one of its parent certificates has been revoked",
	SignatureReasonInternal:              "internal error",
	SignatureReasonSelfSignedCertErr:     "signer's self signed certificate is not trusted",
}

func (sr SignatureReason) String() string {
	return SignatureReasonStrings[sr]
}

type Signer struct {
	Certificate           *CertificateDetails
	CertificatePathStatus int
	HasTimestamp          bool
	Timestamp             time.Time // signature timestamp attribute (which contains a timestamp token)
	LTVEnabled            bool      // needs timestamp token & revocation info
	PAdES                 string    // baseline level: B-B, B-T, B-LT, B-LTA
	Certified             bool      // indicated by DocMDP entry
	Authoritative         bool      // true if certified or first (youngest) signature
	Permissions           int       // see table 257
	Problems              []string
}

func (signer *Signer) AddProblem(s string) {
	signer.Problems = append(signer.Problems, s)
}

func permString(i int) string {
	switch i {
	case CertifiedSigPermNoChangesAllowed:
		return "no changes allowed"
	case CertifiedSigPermFillingAndSigningOK:
		return "filling forms, signing"
	case CertifiedSigPermFillingAnnotatingAndSigningOK:
		return "filling forms, annotating, signing"
	}
	return ""
}

func (signer Signer) String(dts bool) string {
	ss := []string{}
	s := "false"
	if signer.HasTimestamp {
		if signer.Timestamp.IsZero() {
			s = "invalid"
		} else {
			s = signer.Timestamp.Format(SignTSFormat)
		}
	}

	ss = append(ss, fmt.Sprintf("             Timestamp:      %s", s))
	if !dts {
		ss = append(ss, fmt.Sprintf("             LTVEnabled:     %t", signer.LTVEnabled))
		if signer.PAdES != "" {
			ss = append(ss, fmt.Sprintf("             PAdES:          %s", signer.PAdES))
		}
		ss = append(ss, fmt.Sprintf("             Certified:      %t", signer.Certified))
		ss = append(ss, fmt.Sprintf("             Authoritative:  %t", signer.Authoritative))
		if signer.Certified && signer.Permissions > 0 {
			ss = append(ss, fmt.Sprintf("             Permissions:    %s", permString(signer.Permissions)))
		}
	}
	if signer.Certificate != nil {
		s := "             Certificate"
		if signer.Certificate.CA {
			s += "(CA)"
		}
		ss = append(ss, s+":")
		ss = append(ss, signer.Certificate.String())
	}

	for i, s := range signer.Problems {
		if i == 0 {
			ss = append(ss, fmt.Sprintf("             Problems:       %s", s))
			continue
		}
		ss = append(ss, fmt.Sprintf("                             %s", s))
	}

	return strings.Join(ss, "\n")
}

type SignatureDetails struct {
	SubFilter      string    // Signature Dict SubFilter
	SignerIdentity string    // extracted from signature
	SignerName     string    // Signature Dict Name
	ContactInfo    string    // Signature Dict ContactInfo
	Location       string    // Signature Dict Location
	Reason         string    // Signature Dict
	SigningTime    time.Time // Signature Dict M
	FieldName      string    // Signature Field T
	Signers        []*Signer
}

func (sd *SignatureDetails) AddSigner(s *Signer) {
	sd.Signers = append(sd.Signers, s)
}

func (sd *SignatureDetails) IsETSI_CAdES_detached() bool {
	return sd.SubFilter == "ETSI.CAdES.detached"
}

func (sd *SignatureDetails) IsETSI_RFC3161() bool {
	return sd.SubFilter == "ETSI.RFC3161"
}

func (sd *SignatureDetails) Permissions() int {
	for _, signer := range sd.Signers {
		if signer.Certified {
			return signer.Permissions
		}
	}
	return CertifiedSigPermNone
}

func (sd SignatureDetails) String() string {
	ss := []string{}
	ss = append(ss, fmt.Sprintf("             SubFilter:      %s", sd.SubFilter))
	ss = append(ss, fmt.Sprintf("             SignerIdentity: %s", sd.SignerIdentity))
	ss = append(ss, fmt.Sprintf("             SignerName:     %s", sd.SignerName))
	if !sd.IsETSI_RFC3161() {
		ss = append(ss, fmt.Sprintf("             ContactInfo:    %s", sd.ContactInfo))
		ss = append(ss, fmt.Sprintf("             Location:       %s", sd.Location))
		ss = append(ss, fmt.Sprintf("             Reason:         %s", sd.Reason))
	}
	ss = append(ss, fmt.Sprintf("             SigningTime:    %s", sd.SigningTime.Format(SignTSFormat)))
	ss = append(ss, fmt.Sprintf("             Field:          %s", sd.FieldName))

	if len(sd.Signers) == 1 {
		ss = append(ss, "     Signer:")
		ss = append(ss, sd.Signers[0].String(sd.IsETSI_RFC3161()))
	} else {
		for i, signer := range sd.Signers {
			ss = append(ss, fmt.Sprintf("   Signer %d:", i+1))
			ss = append(ss, signer.String(sd.IsETSI_RFC3161()))
		}
	}

	return strings.Join(ss, "\n")
}

type SignatureValidationResult struct {
	Signature
	Status      SignatureStatus
	Reason      SignatureReason
	Details     SignatureDetails
	DocModified int
	Problems    []string
}

func (svr *SignatureValidationResult) AddProblem(s string) {
	svr.Problems = append(svr.Problems, s)
}

func (svr *SignatureValidationResult) Certified() bool {
	return svr.Signature.Certified
}

func (svr *SignatureValidationResult) Permissions() int {
	return svr.Details.Permissions()
}

func (svr *SignatureValidationResult) SigningTime() string {
	if !svr.Details.SigningTime.IsZero() {
		return svr.Details.SigningTime.Format(SignTSFormat)
	}
	return "not available"
}

func (svr SignatureValidationResult) String() string {
	ss := []string{}

	ss = append(ss, fmt.Sprintf("       Type: %s", svr.Signature.String(svr.Status)))
	if !svr.Signed {
		return strings.Join(ss, "\n")
	}

	ss = append(ss, fmt.Sprintf("     Status: %s", svr.Status.String()))
	ss = append(ss, fmt.Sprintf("     Reason: %s", svr.Reason.String()))
	ss = append(ss, fmt.Sprintf("     Signed: %s", svr.SigningTime()))
	ss = append(ss, fmt.Sprintf("DocModified: %s", statusString(svr.DocModified)))
	ss = append(ss, fmt.Sprintf("    Details:\n%s", svr.Details))

	for i, s := range svr.Problems {
		if i == 0 {
			ss = append(ss, fmt.Sprintf("   Problems: %s", s))
			continue
		}
		ss = append(ss, fmt.Sprintf("             %s", s))
	}

	return strings.Join(ss, "\n")
}

func statusString(status int) string {
	switch status {
	case False:
		return "false"
	case True:
		return "true"
	}
	return "unknown"
}

func validString(status int) string {
	switch status {
	case False:
		return "not ok"
	case True:
		return "ok"
	}
	return "unknown"
}

// XRefTable represents a PDF cross reference table plus stats for a PDF file.
type XRefTable struct {
	Table               map[int]*XRefTableEntry
	Size                *int               // from trailer dict.
	MaxObjNr            int                // after reading in all objects from xRef table.
	PageCount           int                // Number of pages.
	Root                *IndirectRef       // Pointer to catalog (reference to root object).
	RootDict            Dict               // Catalog
	Names               map[string]*Node   // Cache for name trees as found in catalog.
	Dests               Dict               // Named destinations
	NameRefs            map[string]NameMap // Name refs for merging only
	Encrypt             *IndirectRef       // Encrypt dict.
	E                   *Enc
	EncKey              []byte // Encrypt key.
	AES4Strings         bool
	AES4Streams         bool
	AES4EmbeddedStreams bool

	// PDF Version
	HeaderVersion *Version // The PDF version the source is claiming to us as per its header.
	RootVersion   *Version // Optional PDF version taking precedence over the header version.

	// Document information section
	ID             Array        // from trailer
	Info           *IndirectRef // Infodict (reference to info dict object)
	Title          string
	Subject        string
	Author         string
	Creator        string
	Producer       string
	CreationDate   string
	ModDate        string
	Keywords       string
	KeywordList    StringSet
	Properties     map[string]string
	CatalogXMPMeta *XMPMeta

	PageLayout *PageLayout
	PageMode   *PageMode
	ViewerPref *ViewerPreferences

	// Linearization section (not yet supported)
	OffsetPrimaryHintTable  *int64
	OffsetOverflowHintTable *int64
	LinearizationObjs       IntSet

	// Page annotation cache
	PageAnnots map[int]PgAnnots

	// Thumbnail images
	PageThumbs map[int]IndirectRef

	Signatures        map[int]map[int]Signature // form signatures and signatures located via page annotations only keyed by increment #.
	URSignature       Dict                      // usage rights signature
	CertifiedSigObjNr int                       // authoritative signature
	DSS               Dict                      // document security store, currently unsupported
	DTS               time.Time                 // trusted digital timestamp

	// Offspec section
	AdditionalStreams *Array // array of IndirectRef - trailer :e.g., Oasis "Open Doc"

	Tagged           bool // File is using tags.
	CustomExtensions bool // File is using custom extensions for annotations and/or keywords.

	// Validation
	CurPage        int                       // current page during validation
	CurObj         int                       // current object during validation, the last dereferenced object
	Conf           *Configuration            // current command being executed
	ValidationMode int                       // see Configuration
	ValidateLinks  bool                      // check for broken links in LinkAnnotations/URIDicts.
	Valid          bool                      // true means successful validated against ISO 32000.
	URIs           map[int]map[string]string // URIs for link checking

	Optimized      bool
	Watermarked    bool
	Form           Dict
	Outlines       Dict
	SignatureExist bool
	AppendOnly     bool

	// Fonts
	UsedGIDs  map[string]map[uint16]bool
	FillFonts map[string]IndirectRef
}

// NewXRefTable creates a new XRefTable.
// TODO Export
func newXRefTable(conf *Configuration) (xRefTable *XRefTable) {
	return &XRefTable{
		Table:             map[int]*XRefTableEntry{},
		Names:             map[string]*Node{},
		NameRefs:          map[string]NameMap{},
		KeywordList:       StringSet{},
		Properties:        map[string]string{},
		LinearizationObjs: IntSet{},
		PageAnnots:        map[int]PgAnnots{},
		PageThumbs:        map[int]IndirectRef{},
		Signatures:        map[int]map[int]Signature{},
		ValidationMode:    conf.ValidationMode,
		ValidateLinks:     conf.ValidateLinks,
		URIs:              map[int]map[string]string{},
		UsedGIDs:          map[string]map[uint16]bool{},
		FillFonts:         map[string]IndirectRef{},
		Conf:              conf,
	}
}

// Version returns the PDF version of the PDF writer that created this file.
// Before V1.4 this is the header version.
// Since V1.4 the catalog may contain a Version entry which takes precedence over the header version.
func (xRefTable *XRefTable) Version() Version {
	if xRefTable.RootVersion != nil {
		return *xRefTable.RootVersion
	}

	return *xRefTable.HeaderVersion
}

// VersionString return a string representation for this PDF files PDF version.
func (xRefTable *XRefTable) VersionString() string {
	return xRefTable.Version().String()
}

// ParseRootVersion returns a string representation for an optional Version entry in the root object.
func (xRefTable *XRefTable) ParseRootVersion() (v *string, err error) {
	// Look in the catalog/root for a name entry "Version".
	// This entry overrides the header version.

	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return nil, err
	}

	return rootDict.NameEntry("Version"), nil
}

// ValidateVersion validates against the xRefTable's version.
func (xRefTable *XRefTable) ValidateVersion(element string, sinceVersion Version) error {
	if xRefTable.Version() < sinceVersion {
		return errors.Errorf("%s: unsupported in version %s\n", element, xRefTable.VersionString())
	}

	return nil
}

func (xRefTable *XRefTable) currentCommand() CommandMode {
	return xRefTable.Conf.Cmd
}

func (xRefTable *XRefTable) IsMerging() bool {
	cmd := xRefTable.currentCommand()
	return cmd == MERGECREATE || cmd == MERGEAPPEND
}

// EnsureVersionForWriting sets the version to the highest supported PDF Version 1.7.
// This is necessary to allow validation after adding features not supported
// by the original version of a document as during watermarking.
func (xRefTable *XRefTable) EnsureVersionForWriting() {
	v := V17
	xRefTable.RootVersion = &v
}

// IsLinearizationObject returns true if object #i is a a linearization object.
func (xRefTable *XRefTable) IsLinearizationObject(i int) bool {
	return xRefTable.LinearizationObjs[i]
}

// LinearizationObjsString returns a formatted string and the number of objs.
func (xRefTable *XRefTable) LinearizationObjsString() (int, string) {
	var objs []int
	for k := range xRefTable.LinearizationObjs {
		if xRefTable.LinearizationObjs[k] {
			objs = append(objs, k)
		}
	}
	sort.Ints(objs)

	var linObj []string
	for _, i := range objs {
		linObj = append(linObj, fmt.Sprintf("%d", i))
	}

	return len(linObj), strings.Join(linObj, ",")
}

// Exists returns true if xRefTable contains an entry for objNumber.
func (xRefTable *XRefTable) Exists(objNr int) bool {
	_, found := xRefTable.Table[objNr]
	return found
}

// Find returns the XRefTable entry for given object number.
func (xRefTable *XRefTable) Find(objNr int) (*XRefTableEntry, bool) {
	e, found := xRefTable.Table[objNr]
	if !found {
		return nil, false
	}
	return e, true
}

// FindObject returns the object of the XRefTableEntry for a specific object number.
func (xRefTable *XRefTable) FindObject(objNr int) (Object, error) {
	entry, ok := xRefTable.Find(objNr)
	if !ok {
		return nil, errors.Errorf("FindObject: obj#%d not registered in xRefTable", objNr)
	}
	return entry.Object, nil
}

// Free returns the cross ref table entry for given number of a free object.
func (xRefTable *XRefTable) Free(objNr int) (*XRefTableEntry, error) {
	entry, found := xRefTable.Find(objNr)
	if !found {
		return nil, nil
	}
	if !entry.Free {
		return nil, errors.Errorf("Free: object #%d found, but not free.", objNr)
	}
	return entry, nil
}

// NextForFree returns the number of the object the free object with objNumber links to.
// This is the successor of this free object in the free list.
func (xRefTable *XRefTable) NextForFree(objNr int) (int, error) {
	entry, err := xRefTable.Free(objNr)
	if err != nil {
		return 0, err
	}

	return int(*entry.Offset), nil
}

// FindTableEntryLight returns the XRefTable entry for given object number.
func (xRefTable *XRefTable) FindTableEntryLight(objNr int) (*XRefTableEntry, bool) {
	return xRefTable.Find(objNr)
}

// FindTableEntry returns the XRefTable entry for given object and generation numbers.
func (xRefTable *XRefTable) FindTableEntry(objNr int, genNr int) (*XRefTableEntry, bool) {
	// if log.TraceEnabled() {
	// 	log.Trace.Printf("FindTableEntry: obj#:%d gen:%d \n", objNr, genNr)
	// }
	return xRefTable.Find(objNr)
}

// FindTableEntryForIndRef returns the XRefTable entry for given indirect reference.
func (xRefTable *XRefTable) FindTableEntryForIndRef(indRef *IndirectRef) (*XRefTableEntry, bool) {
	if indRef == nil {
		return nil, false
	}
	return xRefTable.FindTableEntry(indRef.ObjectNumber.Value(), indRef.GenerationNumber.Value())
}

// IncrementRefCount increments the number of references for the object pointed to by indRef.
func (xRefTable *XRefTable) IncrementRefCount(indRef *IndirectRef) {
	if entry, ok := xRefTable.FindTableEntryForIndRef(indRef); ok {
		entry.RefCount++
	}
}

// InsertNew adds given xRefTableEntry at next new objNumber into the cross reference table.
// Only to be called once an xRefTable has been generated completely and all trailer dicts have been processed.
// xRefTable.Size is the size entry of the first trailer dict processed.
// Called on creation of new object streams.
// Called by InsertAndUseRecycled.
func (xRefTable *XRefTable) InsertNew(xRefTableEntry XRefTableEntry) (objNr int) {
	objNr = *xRefTable.Size
	xRefTable.Table[objNr] = &xRefTableEntry
	*xRefTable.Size++
	return
}

// InsertAndUseRecycled adds given xRefTableEntry into the cross reference table utilizing the freelist.
func (xRefTable *XRefTable) InsertAndUseRecycled(xRefTableEntry XRefTableEntry) (objNr int, err error) {
	// see 7.5.4 Cross-Reference Table

	// Hacky:
	// Although we increment the obj generation when recycling objects,
	// we always use generation 0 when reusing recycled objects.
	// This is because pdfcpu does not reuse objects
	// in an incremental fashion like laid out in the PDF spec.

	// if log.WriteEnabled() {
	// 	log.Write.Println("InsertAndUseRecycled: begin")
	// }

	// Get Next free object from freelist.
	freeListHeadEntry, err := xRefTable.Free(0)
	if err != nil {
		return 0, err
	}

	// If none available, add new object & return.
	if *freeListHeadEntry.Offset == 0 {
		xRefTableEntry.RefCount = 1
		objNr = xRefTable.InsertNew(xRefTableEntry)
		// if log.WriteEnabled() {
		// 	log.Write.Printf("InsertAndUseRecycled: end, new objNr=%d\n", objNr)
		// }
		return objNr, nil
	}

	// Recycle free object, update free list & return.
	objNr = int(*freeListHeadEntry.Offset)
	entry, found := xRefTable.FindTableEntryLight(objNr)
	if !found {
		return 0, errors.Errorf("InsertAndRecycle: no entry for obj #%d\n", objNr)
	}

	// The new free list head entry becomes the old head entry's successor.
	freeListHeadEntry.Offset = entry.Offset

	// The old head entry becomes garbage.
	entry.Free = false
	entry.Offset = nil

	// Create a new entry for the recycled object.
	// TODO use entrys generation.
	xRefTableEntry.RefCount = 1
	xRefTable.Table[objNr] = &xRefTableEntry

	// if log.WriteEnabled() {
	// 	log.Write.Printf("InsertAndUseRecycled: end, recycled objNr=%d\n", objNr)
	// }

	return objNr, nil
}

// InsertObject inserts an object into the xRefTable.
func (xRefTable *XRefTable) InsertObject(obj Object) (objNr int, err error) {
	xRefTableEntry := NewXRefTableEntryGen0(obj)
	xRefTableEntry.RefCount = 1
	return xRefTable.InsertNew(*xRefTableEntry), nil
}

// IndRefForNewObject inserts an object into the xRefTable and returns an indirect reference to it.
func (xRefTable *XRefTable) IndRefForNewObject(obj Object) (*IndirectRef, error) {
	xRefTableEntry := NewXRefTableEntryGen0(obj)
	objNr, err := xRefTable.InsertAndUseRecycled(*xRefTableEntry)
	if err != nil {
		return nil, err
	}

	return NewIndirectRef(objNr, *xRefTableEntry.Generation), nil
}

// NewStreamDictForBuf creates a streamDict for buf.
func (xRefTable *XRefTable) NewStreamDictForBuf(buf []byte) (*StreamDict, error) {
	sd := StreamDict{
		Dict:           NewDict(),
		Content:        buf,
		FilterPipeline: []PDFFilter{{Name: Flate, DecodeParms: nil}},
	}
	sd.InsertName("Filter", Flate)
	return &sd, nil
}

// NewEmbeddedStreamDict creates and returns an embeddedStreamDict containing the bytes represented by r.
func (xRefTable *XRefTable) NewEmbeddedStreamDict(r io.Reader, modDate time.Time) (*IndirectRef, error) {
	var buf bytes.Buffer
	if _, err := io.Copy(&buf, r); err != nil {
		return nil, err
	}

	bb := buf.Bytes()

	sd, err := xRefTable.NewStreamDictForBuf(bb)
	if err != nil {
		return nil, err
	}

	sd.InsertName("Type", "EmbeddedFile")
	d := NewDict()
	d.InsertInt("Size", len(bb))
	d.Insert("ModDate", StringLiteral(DateString(modDate)))
	sd.Insert("Params", d)
	if err = sd.Encode(); err != nil {
		return nil, err
	}

	return xRefTable.IndRefForNewObject(*sd)
}

func processDictRefCounts(xRefTable *XRefTable, d Dict) {
	for _, e := range d {
		switch o1 := e.(type) {
		case IndirectRef:
			xRefTable.IncrementRefCount(&o1)
		case Dict:
			ProcessRefCounts(xRefTable, o1)
		case Array:
			ProcessRefCounts(xRefTable, o1)
		}
	}
}

func processArrayRefCounts(xRefTable *XRefTable, a Array) {
	for _, e := range a {
		switch o1 := e.(type) {
		case IndirectRef:
			xRefTable.IncrementRefCount(&o1)
		case Dict:
			ProcessRefCounts(xRefTable, o1)
		case Array:
			ProcessRefCounts(xRefTable, o1)
		}
	}
}

func ProcessRefCounts(xRefTable *XRefTable, o Object) {
	switch o := o.(type) {
	case Dict:
		processDictRefCounts(xRefTable, o)
	case StreamDict:
		processDictRefCounts(xRefTable, o.Dict)
	case Array:
		processArrayRefCounts(xRefTable, o)
	}
}

// A ContextContext carries a deadline, a cancellation signal, and other values across
// API boundaries.
//
// ContextContext's methods may be called by multiple goroutines simultaneously.
type ContextContext interface {
	// Deadline returns the time when work done on behalf of this context
	// should be canceled. Deadline returns ok==false when no deadline is
	// set. Successive calls to Deadline return the same results.
	Deadline() (deadline time.Time, ok bool)

	// Done returns a channel that's closed when work done on behalf of this
	// context should be canceled. Done may return nil if this context can
	// never be canceled. Successive calls to Done return the same value.
	// The close of the Done channel may happen asynchronously,
	// after the cancel function returns.
	//
	// WithCancel arranges for Done to be closed when cancel is called;
	// WithDeadline arranges for Done to be closed when the deadline
	// expires; WithTimeout arranges for Done to be closed when the timeout
	// elapses.
	//
	// Done is provided for use in select statements:
	//
	//  // Stream generates values with DoSomething and sends them to out
	//  // until DoSomething returns an error or ctx.Done is closed.
	//  func Stream(ctx context.ContextContext, out chan<- Value) error {
	//  	for {
	//  		v, err := DoSomething(ctx)
	//  		if err != nil {
	//  			return err
	//  		}
	//  		select {
	//  		case <-ctx.Done():
	//  			return ctx.Err()
	//  		case out <- v:
	//  		}
	//  	}
	//  }
	//
	// See https://blog.golang.org/pipelines for more examples of how to use
	// a Done channel for cancellation.
	Done() <-chan struct{}

	// If Done is not yet closed, Err returns nil.
	// If Done is closed, Err returns a non-nil error explaining why:
	// DeadlineExceeded if the context's deadline passed,
	// or Canceled if the context was canceled for some other reason.
	// After Err returns a non-nil error, successive calls to Err return the same error.
	Err() error

	// Value returns the value associated with this context for key, or nil
	// if no value is associated with key. Successive calls to Value with
	// the same key returns the same result.
	//
	// Use context values only for request-scoped data that transits
	// processes and API boundaries, not for passing optional parameters to
	// functions.
	//
	// A key identifies a specific value in a ContextContext. Functions that wish
	// to store values in ContextContext typically allocate a key in a global
	// variable then use that key as the argument to context.WithValue and
	// ContextContext.Value. A key can be any type that supports equality;
	// packages should define keys as an unexported type to avoid
	// collisions.
	//
	// Packages that define a ContextContext key should provide type-safe accessors
	// for the values stored using that key:
	//
	// 	// Package user defines a User type that's stored in Contexts.
	// 	package user
	//
	// 	import "context"
	//
	// 	// User is the type of value stored in the Contexts.
	// 	type User struct {...}
	//
	// 	// key is an unexported type for keys defined in this package.
	// 	// This prevents collisions with keys defined in other packages.
	// 	type key int
	//
	// 	// userKey is the key for user.User values in Contexts. It is
	// 	// unexported; clients use user.NewContext and user.FromContext
	// 	// instead of using this key directly.
	// 	var userKey key
	//
	// 	// NewContext returns a new ContextContext that carries value u.
	// 	func NewContext(ctx context.ContextContext, u *User) context.ContextContext {
	// 		return context.WithValue(ctx, userKey, u)
	// 	}
	//
	// 	// FromContext returns the User value stored in ctx, if any.
	// 	func FromContext(ctx context.ContextContext) (*User, bool) {
	// 		u, ok := ctx.Value(userKey).(*User)
	// 		return u, ok
	// 	}
	Value(key any) any
}

// Canceled is the error returned by [ContextContext.Err] when the context is canceled
// for some reason other than its deadline passing.
var Canceled = errors.New("context canceled")

// DeadlineExceeded is the error returned by [ContextContext.Err] when the context is canceled
// due to its deadline passing.
var DeadlineExceeded error = deadlineExceededError{}

type deadlineExceededError struct{}

func (deadlineExceededError) Error() string   { return "context deadline exceeded" }
func (deadlineExceededError) Timeout() bool   { return true }
func (deadlineExceededError) Temporary() bool { return true }

// An emptyCtx is never canceled, has no values, and has no deadline.
// It is the common base of backgroundCtx and todoCtx.
type emptyCtx struct{}

func (emptyCtx) Deadline() (deadline time.Time, ok bool) {
	return
}

func (emptyCtx) Done() <-chan struct{} {
	return nil
}

func (emptyCtx) Err() error {
	return nil
}

func (emptyCtx) Value(key any) any {
	return nil
}

type backgroundCtx struct{ emptyCtx }

func (backgroundCtx) String() string {
	return "context.Background"
}

type todoCtx struct{ emptyCtx }

func (todoCtx) String() string {
	return "context.TODO"
}

// Background returns a non-nil, empty [ContextContext]. It is never canceled, has no
// values, and has no deadline. It is typically used by the main function,
// initialization, and tests, and as the top-level ContextContext for incoming
// requests.
func Background() ContextContext {
	return backgroundCtx{}
}

// TODO returns a non-nil, empty [ContextContext]. Code should use context.TODO when
// it's unclear which ContextContext to use or it is not yet available (because the
// surrounding function has not yet been extended to accept a ContextContext
// parameter).
func TODO() ContextContext {
	return todoCtx{}
}

// A CancelFunc tells an operation to abandon its work.
// A CancelFunc does not wait for the work to stop.
// A CancelFunc may be called by multiple goroutines simultaneously.
// After the first call, subsequent calls to a CancelFunc do nothing.
type CancelFunc func()

// WithCancel returns a derived context that points to the parent context
// but has a new Done channel. The returned context's Done channel is closed
// when the returned cancel function is called or when the parent context's
// Done channel is closed, whichever happens first.
//
// Canceling this context releases resources associated with it, so code should
// call cancel as soon as the operations running in this [ContextContext] complete.
func WithCancel(parent ContextContext) (ctx ContextContext, cancel CancelFunc) {
	c := withCancel(parent)
	return c, func() { c.cancel(true, Canceled, nil) }
}

// A CancelCauseFunc behaves like a [CancelFunc] but additionally sets the cancellation cause.
// This cause can be retrieved by calling [Cause] on the canceled ContextContext or on
// any of its derived Contexts.
//
// If the context has already been canceled, CancelCauseFunc does not set the cause.
// For example, if childContext is derived from parentContext:
//   - if parentContext is canceled with cause1 before childContext is canceled with cause2,
//     then Cause(parentContext) == Cause(childContext) == cause1
//   - if childContext is canceled with cause2 before parentContext is canceled with cause1,
//     then Cause(parentContext) == cause1 and Cause(childContext) == cause2
type CancelCauseFunc func(cause error)

// WithCancelCause behaves like [WithCancel] but returns a [CancelCauseFunc] instead of a [CancelFunc].
// Calling cancel with a non-nil error (the "cause") records that error in ctx;
// it can then be retrieved using Cause(ctx).
// Calling cancel with nil sets the cause to Canceled.
//
// Example use:
//
//	ctx, cancel := context.WithCancelCause(parent)
//	cancel(myError)
//	ctx.Err() // returns context.Canceled
//	context.Cause(ctx) // returns myError
func WithCancelCause(parent ContextContext) (ctx ContextContext, cancel CancelCauseFunc) {
	c := withCancel(parent)
	return c, func(cause error) { c.cancel(true, Canceled, cause) }
}

func withCancel(parent ContextContext) *cancelCtx {
	if parent == nil {
		panic("cannot create context from nil parent")
	}
	c := &cancelCtx{}
	c.propagateCancel(parent, c)
	return c
}

// Cause returns a non-nil error explaining why c was canceled.
// The first cancellation of c or one of its parents sets the cause.
// If that cancellation happened via a call to CancelCauseFunc(err),
// then [Cause] returns err.
// Otherwise Cause(c) returns the same value as c.Err().
// Cause returns nil if c has not been canceled yet.
func Cause(c ContextContext) error {
	if cc, ok := c.Value(&cancelCtxKey).(*cancelCtx); ok {
		cc.mu.Lock()
		defer cc.mu.Unlock()
		return cc.cause
	}
	// There is no cancelCtxKey value, so we know that c is
	// not a descendant of some ContextContext created by WithCancelCause.
	// Therefore, there is no specific cause to return.
	// If this is not one of the standard ContextContext types,
	// it might still have an error even though it won't have a cause.
	return c.Err()
}

// AfterFunc arranges to call f in its own goroutine after ctx is canceled.
// If ctx is already canceled, AfterFunc calls f immediately in its own goroutine.
//
// Multiple calls to AfterFunc on a context operate independently;
// one does not replace another.
//
// Calling the returned stop function stops the association of ctx with f.
// It returns true if the call stopped f from being run.
// If stop returns false,
// either the context is canceled and f has been started in its own goroutine;
// or f was already stopped.
// The stop function does not wait for f to complete before returning.
// If the caller needs to know whether f is completed,
// it must coordinate with f explicitly.
//
// If ctx has a "AfterFunc(func()) func() bool" method,
// AfterFunc will use it to schedule the call.
func AfterFunc(ctx ContextContext, f func()) (stop func() bool) {
	a := &afterFuncCtx{
		f: f,
	}
	a.cancelCtx.propagateCancel(ctx, a)
	return func() bool {
		stopped := false
		a.once.Do(func() {
			stopped = true
		})
		if stopped {
			a.cancel(true, Canceled, nil)
		}
		return stopped
	}
}

type afterFuncer interface {
	AfterFunc(func()) func() bool
}

type afterFuncCtx struct {
	cancelCtx
	once sync.Once // either starts running f or stops f from running
	f    func()
}

func (a *afterFuncCtx) cancel(removeFromParent bool, err, cause error) {
	a.cancelCtx.cancel(false, err, cause)
	if removeFromParent {
		removeChild(a.ContextContext, a)
	}
	a.once.Do(func() {
		go a.f()
	})
}

// A stopCtx is used as the parent context of a cancelCtx when
// an AfterFunc has been registered with the parent.
// It holds the stop function used to unregister the AfterFunc.
type stopCtx struct {
	ContextContext
	stop func() bool
}

// goroutines counts the number of goroutines ever created; for testing.
var goroutines atomic.Int32

// &cancelCtxKey is the key that a cancelCtx returns itself for.
var cancelCtxKey int

// parentCancelCtx returns the underlying *cancelCtx for parent.
// It does this by looking up parent.Value(&cancelCtxKey) to find
// the innermost enclosing *cancelCtx and then checking whether
// parent.Done() matches that *cancelCtx. (If not, the *cancelCtx
// has been wrapped in a custom implementation providing a
// different done channel, in which case we should not bypass it.)
func parentCancelCtx(parent ContextContext) (*cancelCtx, bool) {
	done := parent.Done()
	if done == closedchan || done == nil {
		return nil, false
	}
	p, ok := parent.Value(&cancelCtxKey).(*cancelCtx)
	if !ok {
		return nil, false
	}
	pdone, _ := p.done.Load().(chan struct{})
	if pdone != done {
		return nil, false
	}
	return p, true
}

// removeChild removes a context from its parent.
func removeChild(parent ContextContext, child canceler) {
	if s, ok := parent.(stopCtx); ok {
		s.stop()
		return
	}
	p, ok := parentCancelCtx(parent)
	if !ok {
		return
	}
	p.mu.Lock()
	if p.children != nil {
		delete(p.children, child)
	}
	p.mu.Unlock()
}

// A canceler is a context type that can be canceled directly. The
// implementations are *cancelCtx and *timerCtx.
type canceler interface {
	cancel(removeFromParent bool, err, cause error)
	Done() <-chan struct{}
}

// closedchan is a reusable closed channel.
var closedchan = make(chan struct{})

func init() {
	close(closedchan)
}

// A cancelCtx can be canceled. When canceled, it also cancels any children
// that implement canceler.
type cancelCtx struct {
	ContextContext

	mu       sync.Mutex            // protects following fields
	done     atomic.Value          // of chan struct{}, created lazily, closed by first cancel call
	children map[canceler]struct{} // set to nil by the first cancel call
	err      error                 // set to non-nil by the first cancel call
	cause    error                 // set to non-nil by the first cancel call
}

func (c *cancelCtx) Value(key any) any {
	if key == &cancelCtxKey {
		return c
	}
	return value(c.ContextContext, key)
}

func (c *cancelCtx) Done() <-chan struct{} {
	d := c.done.Load()
	if d != nil {
		return d.(chan struct{})
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	d = c.done.Load()
	if d == nil {
		d = make(chan struct{})
		c.done.Store(d)
	}
	return d.(chan struct{})
}

func (c *cancelCtx) Err() error {
	c.mu.Lock()
	err := c.err
	c.mu.Unlock()
	return err
}

// propagateCancel arranges for child to be canceled when parent is.
// It sets the parent context of cancelCtx.
func (c *cancelCtx) propagateCancel(parent ContextContext, child canceler) {
	c.ContextContext = parent

	done := parent.Done()
	if done == nil {
		return // parent is never canceled
	}

	select {
	case <-done:
		// parent is already canceled
		child.cancel(false, parent.Err(), Cause(parent))
		return
	default:
	}

	if p, ok := parentCancelCtx(parent); ok {
		// parent is a *cancelCtx, or derives from one.
		p.mu.Lock()
		if p.err != nil {
			// parent has already been canceled
			child.cancel(false, p.err, p.cause)
		} else {
			if p.children == nil {
				p.children = make(map[canceler]struct{})
			}
			p.children[child] = struct{}{}
		}
		p.mu.Unlock()
		return
	}

	if a, ok := parent.(afterFuncer); ok {
		// parent implements an AfterFunc method.
		c.mu.Lock()
		stop := a.AfterFunc(func() {
			child.cancel(false, parent.Err(), Cause(parent))
		})
		c.ContextContext = stopCtx{
			ContextContext: parent,
			stop:           stop,
		}
		c.mu.Unlock()
		return
	}

	goroutines.Add(1)
	go func() {
		select {
		case <-parent.Done():
			child.cancel(false, parent.Err(), Cause(parent))
		case <-child.Done():
		}
	}()
}

type stringer interface {
	String() string
}

func contextName(c ContextContext) string {
	if s, ok := c.(stringer); ok {
		return s.String()
	}
	return reflect.TypeOf(c).String()
}

func (c *cancelCtx) String() string {
	return contextName(c.ContextContext) + ".WithCancel"
}

// cancel closes c.done, cancels each of c's children, and, if
// removeFromParent is true, removes c from its parent's children.
// cancel sets c.cause to cause if this is the first time c is canceled.
func (c *cancelCtx) cancel(removeFromParent bool, err, cause error) {
	if err == nil {
		panic("context: internal error: missing cancel error")
	}
	if cause == nil {
		cause = err
	}
	c.mu.Lock()
	if c.err != nil {
		c.mu.Unlock()
		return // already canceled
	}
	c.err = err
	c.cause = cause
	d, _ := c.done.Load().(chan struct{})
	if d == nil {
		c.done.Store(closedchan)
	} else {
		close(d)
	}
	for child := range c.children {
		// NOTE: acquiring the child's lock while holding parent's lock.
		child.cancel(false, err, cause)
	}
	c.children = nil
	c.mu.Unlock()

	if removeFromParent {
		removeChild(c.ContextContext, c)
	}
}

// WithoutCancel returns a derived context that points to the parent context
// and is not canceled when parent is canceled.
// The returned context returns no Deadline or Err, and its Done channel is nil.
// Calling [Cause] on the returned context returns nil.
func WithoutCancel(parent ContextContext) ContextContext {
	if parent == nil {
		panic("cannot create context from nil parent")
	}
	return withoutCancelCtx{parent}
}

type withoutCancelCtx struct {
	c ContextContext
}

func (withoutCancelCtx) Deadline() (deadline time.Time, ok bool) {
	return
}

func (withoutCancelCtx) Done() <-chan struct{} {
	return nil
}

func (withoutCancelCtx) Err() error {
	return nil
}

func (c withoutCancelCtx) Value(key any) any {
	return value(c, key)
}

func (c withoutCancelCtx) String() string {
	return contextName(c.c) + ".WithoutCancel"
}

// WithDeadline returns a derived context that points to the parent context
// but has the deadline adjusted to be no later than d. If the parent's
// deadline is already earlier than d, WithDeadline(parent, d) is semantically
// equivalent to parent. The returned [ContextContext.Done] channel is closed when
// the deadline expires, when the returned cancel function is called,
// or when the parent context's Done channel is closed, whichever happens first.
//
// Canceling this context releases resources associated with it, so code should
// call cancel as soon as the operations running in this [ContextContext] complete.
func WithDeadline(parent ContextContext, d time.Time) (ContextContext, CancelFunc) {
	return WithDeadlineCause(parent, d, nil)
}

// WithDeadlineCause behaves like [WithDeadline] but also sets the cause of the
// returned ContextContext when the deadline is exceeded. The returned [CancelFunc] does
// not set the cause.
func WithDeadlineCause(parent ContextContext, d time.Time, cause error) (ContextContext, CancelFunc) {
	if parent == nil {
		panic("cannot create context from nil parent")
	}
	if cur, ok := parent.Deadline(); ok && cur.Before(d) {
		// The current deadline is already sooner than the new one.
		return WithCancel(parent)
	}
	c := &timerCtx{
		deadline: d,
	}
	c.cancelCtx.propagateCancel(parent, c)
	dur := time.Until(d)
	if dur <= 0 {
		c.cancel(true, DeadlineExceeded, cause) // deadline has already passed
		return c, func() { c.cancel(false, Canceled, nil) }
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.err == nil {
		c.timer = time.AfterFunc(dur, func() {
			c.cancel(true, DeadlineExceeded, cause)
		})
	}
	return c, func() { c.cancel(true, Canceled, nil) }
}

// A timerCtx carries a timer and a deadline. It embeds a cancelCtx to
// implement Done and Err. It implements cancel by stopping its timer then
// delegating to cancelCtx.cancel.
type timerCtx struct {
	cancelCtx
	timer *time.Timer // Under cancelCtx.mu.

	deadline time.Time
}

func (c *timerCtx) Deadline() (deadline time.Time, ok bool) {
	return c.deadline, true
}

func (c *timerCtx) String() string {
	return contextName(c.cancelCtx.ContextContext) + ".WithDeadline(" +
		c.deadline.String() + " [" +
		time.Until(c.deadline).String() + "])"
}

func (c *timerCtx) cancel(removeFromParent bool, err, cause error) {
	c.cancelCtx.cancel(false, err, cause)
	if removeFromParent {
		// Remove this timerCtx from its parent cancelCtx's children.
		removeChild(c.cancelCtx.ContextContext, c)
	}
	c.mu.Lock()
	if c.timer != nil {
		c.timer.Stop()
		c.timer = nil
	}
	c.mu.Unlock()
}

// WithTimeout returns WithDeadline(parent, time.Now().Add(timeout)).
//
// Canceling this context releases resources associated with it, so code should
// call cancel as soon as the operations running in this [ContextContext] complete:
//
//	func slowOperationWithTimeout(ctx context.ContextContext) (Result, error) {
//		ctx, cancel := context.WithTimeout(ctx, 100*time.Millisecond)
//		defer cancel()  // releases resources if slowOperation completes before timeout elapses
//		return slowOperation(ctx)
//	}
func WithTimeout(parent ContextContext, timeout time.Duration) (ContextContext, CancelFunc) {
	return WithDeadline(parent, time.Now().Add(timeout))
}

// WithTimeoutCause behaves like [WithTimeout] but also sets the cause of the
// returned ContextContext when the timeout expires. The returned [CancelFunc] does
// not set the cause.
func WithTimeoutCause(parent ContextContext, timeout time.Duration, cause error) (ContextContext, CancelFunc) {
	return WithDeadlineCause(parent, time.Now().Add(timeout), cause)
}

// WithValue returns a derived context that points to the parent ContextContext.
// In the derived context, the value associated with key is val.
//
// Use context Values only for request-scoped data that transits processes and
// APIs, not for passing optional parameters to functions.
//
// The provided key must be comparable and should not be of type
// string or any other built-in type to avoid collisions between
// packages using context. Users of WithValue should define their own
// types for keys. To avoid allocating when assigning to an
// interface{}, context keys often have concrete type
// struct{}. Alternatively, exported context key variables' static
// type should be a pointer or interface.
func WithValue(parent ContextContext, key, val any) ContextContext {
	if parent == nil {
		panic("cannot create context from nil parent")
	}
	if key == nil {
		panic("nil key")
	}
	if !reflect.TypeOf(key).Comparable() {
		panic("key is not comparable")
	}
	return &valueCtx{parent, key, val}
}

// A valueCtx carries a key-value pair. It implements Value for that key and
// delegates all other calls to the embedded ContextContext.
type valueCtx struct {
	ContextContext
	key, val any
}

// stringify tries a bit to stringify v, without using fmt, since we don't
// want context depending on the unicode tables. This is only used by
// *valueCtx.String().
func stringify(v any) string {
	switch s := v.(type) {
	case stringer:
		return s.String()
	case string:
		return s
	case nil:
		return "<nil>"
	}
	return reflect.TypeOf(v).String()
}

func (c *valueCtx) String() string {
	return contextName(c.ContextContext) + ".WithValue(" +
		stringify(c.key) + ", " +
		stringify(c.val) + ")"
}

func (c *valueCtx) Value(key any) any {
	if c.key == key {
		return c.val
	}
	return value(c.ContextContext, key)
}

func value(c ContextContext, key any) any {
	for {
		switch ctx := c.(type) {
		case *valueCtx:
			if key == ctx.key {
				return ctx.val
			}
			c = ctx.ContextContext
		case *cancelCtx:
			if key == &cancelCtxKey {
				return c
			}
			c = ctx.ContextContext
		case withoutCancelCtx:
			if key == &cancelCtxKey {
				// This implements Cause(ctx) == nil
				// when ctx is created using WithoutCancel.
				return nil
			}
			c = ctx.c
		case *timerCtx:
			if key == &cancelCtxKey {
				return &ctx.cancelCtx
			}
			c = ctx.ContextContext
		case backgroundCtx, todoCtx:
			return nil
		default:
			return c.Value(key)
		}
	}
}

func (xRefTable *XRefTable) indRefToObject(ir *IndirectRef, decodeLazy bool) (Object, int, error) {
	if ir == nil {
		return nil, 0, errors.New("pdfcpu: indRefToObject: input argument is nil")
	}

	// 7.3.10
	// An indirect reference to an undefined object shall not be considered an error by a conforming reader;
	// it shall be treated as a reference to the null object.
	entry, found := xRefTable.FindTableEntryForIndRef(ir)
	if !found || entry.Free {
		return nil, 0, nil
	}

	xRefTable.CurObj = int(ir.ObjectNumber)

	if l, ok := entry.Object.(LazyObjectStreamObject); ok && decodeLazy {
		ob, err := l.DecodedObject(TODO())
		if err != nil {
			return nil, 0, err
		}

		ProcessRefCounts(xRefTable, ob)
		entry.Object = ob
	}

	// return dereferenced object and increment nr.
	return entry.Object, entry.Incr, nil
}

// Dereference resolves an indirect object and returns the resulting PDF object.
func (xRefTable *XRefTable) Dereference(o Object) (Object, error) {
	ir, ok := o.(IndirectRef)
	if !ok {
		// Nothing do dereference.
		return o, nil
	}

	obj, _, err := xRefTable.indRefToObject(&ir, true)
	return obj, err
}

// Dereference resolves an indirect object and returns the resulting PDF object.
// It also returns the number of the written PDF Increment this object is part of.
// The higher the increment number the older the object.
func (xRefTable *XRefTable) DereferenceWithIncr(o Object) (Object, int, error) {
	ir, ok := o.(IndirectRef)
	if !ok {
		// Nothing do dereference.
		return o, 0, nil
	}

	return xRefTable.indRefToObject(&ir, true)
}

func (xRefTable *XRefTable) DereferenceForWrite(o Object) (Object, error) {
	ir, ok := o.(IndirectRef)
	if !ok {
		// Nothing do dereference.
		return o, nil
	}

	obj, _, err := xRefTable.indRefToObject(&ir, false)
	return obj, err
}

// DereferenceBoolean resolves and validates a boolean object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceBoolean(o Object, sinceVersion Version) (*Boolean, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return nil, err
	}

	b, ok := o.(Boolean)
	if !ok {
		return nil, errors.Errorf("pdfcpu: dereferenceBoolean: wrong type <%v>", o)
	}

	// Version check
	if err = xRefTable.ValidateVersion("DereferenceBoolean", sinceVersion); err != nil {
		return nil, err
	}

	return &b, nil
}

// DereferenceInteger resolves and validates an integer object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceInteger(o Object) (*Integer, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return nil, err
	}

	i, ok := o.(Integer)
	if !ok {
		return nil, errors.Errorf("pdfcpu: dereferenceInteger: wrong type <%v>", o)
	}

	return &i, nil
}

// DereferenceNumber resolves a number object, which may be an indirect reference and returns a float64.
func (xRefTable *XRefTable) DereferenceNumber(o Object) (float64, error) {
	var (
		f   float64
		err error
	)

	o, _ = xRefTable.Dereference(o)

	switch o := o.(type) {

	case Integer:
		f = float64(o.Value())

	case Float:
		f = o.Value()

	default:
		err = errors.Errorf("pdfcpu: dereferenceNumber: wrong type <%v>", o)

	}

	return f, err
}

// DereferenceName resolves and validates a name object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceName(o Object, sinceVersion Version, validate func(string) bool) (n NameType, err error) {
	o, err = xRefTable.Dereference(o)
	if err != nil || o == nil {
		return n, err
	}

	n, ok := o.(NameType)
	if !ok {
		return n, errors.Errorf("pdfcpu: dereferenceName: wrong type <%v>", o)
	}

	// Version check
	if err = xRefTable.ValidateVersion("DereferenceName", sinceVersion); err != nil {
		return n, err
	}

	// Validation
	if validate != nil && !validate(n.Value()) {
		return n, errors.Errorf("pdfcpu: dereferenceName: invalid <%s>", n.Value())
	}

	return n, nil
}

// DereferenceStringLiteral resolves and validates a string literal object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceStringLiteral(o Object, sinceVersion Version, validate func(string) bool) (s StringLiteral, err error) {
	o, err = xRefTable.Dereference(o)
	if err != nil || o == nil {
		return s, err
	}

	s, ok := o.(StringLiteral)
	if !ok {
		return s, errors.Errorf("pdfcpu: dereferenceStringLiteral: wrong type <%v>", o)
	}

	// Ensure UTF16 correctness.
	s1, err := StringLiteralToString(s)
	if err != nil {
		return s, err
	}

	// Version check
	if err = xRefTable.ValidateVersion("DereferenceStringLiteral", sinceVersion); err != nil {
		return s, err
	}

	// Validation
	if validate != nil && !validate(s1) {
		return s, errors.Errorf("pdfcpu: dereferenceStringLiteral: invalid <%s>", s1)
	}

	return s, nil
}

// DereferenceStringOrHexLiteral resolves and validates a string or hex literal object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceStringOrHexLiteral(obj Object, sinceVersion Version, validate func(string) bool) (s string, err error) {
	o, err := xRefTable.Dereference(obj)
	if err != nil || o == nil {
		return "", err
	}

	switch str := o.(type) {

	case StringLiteral:
		// Ensure UTF16 correctness.
		if s, err = StringLiteralToString(str); err != nil {
			return "", err
		}

	case HexLiteral:
		// Ensure UTF16 correctness.
		if s, err = HexLiteralToString(str); err != nil {
			return "", err
		}

	default:
		return "", errors.Errorf("pdfcpu: dereferenceStringOrHexLiteral: wrong type %T", obj)

	}

	// Version check
	if err = xRefTable.ValidateVersion("DereferenceStringOrHexLiteral", sinceVersion); err != nil {
		return "", err
	}

	// Validation
	if validate != nil && !validate(s) {
		return "", errors.Errorf("pdfcpu: dereferenceStringOrHexLiteral: invalid <%s>", s)
	}

	return s, nil
}

// Text returns a string based representation for String and Hexliterals.
func Text(o Object) (string, error) {
	switch obj := o.(type) {
	case StringLiteral:
		return StringLiteralToString(obj)
	case HexLiteral:
		return HexLiteralToString(obj)
	default:
		return "", errors.Errorf("pdfcpu: corrupt text: %v\n", obj)
	}
}

// DereferenceText resolves and validates a string or hex literal object to a string.
func (xRefTable *XRefTable) DereferenceText(o Object) (string, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil {
		return "", err
	}
	return Text(o)
}

func CSVSafeString(s string) string {
	return strings.Replace(s, ";", ",", -1)
}

// DereferenceCSVSafeText resolves and validates a string or hex literal object to a string.
func (xRefTable *XRefTable) DereferenceCSVSafeText(o Object) (string, error) {
	s, err := xRefTable.DereferenceText(o)
	if err != nil {
		return "", err
	}
	return CSVSafeString(s), nil
}

// DereferenceArray resolves and validates an array object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceArray(o Object) (Array, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return nil, err
	}

	a, ok := o.(Array)
	if !ok {
		return nil, errors.Errorf("pdfcpu: dereferenceArray: wrong type %T <%v>", o, o)
	}

	return a, nil
}

// DereferenceDict resolves and validates a dictionary object, which may be an indirect reference.
func (xRefTable *XRefTable) DereferenceDict(o Object) (Dict, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return nil, err
	}

	d, ok := o.(Dict)
	if !ok {
		return nil, errors.Errorf("pdfcpu: dereferenceDict: wrong type %T <%v>", o, o)
	}

	return d, nil
}

// DereferenceDictWithIncr resolves and validates a dictionary object, which may be an indirect reference.
// It also returns the number of the written PDF Increment this object is part of.
// The higher the increment number the older the object.
func (xRefTable *XRefTable) DereferenceDictWithIncr(o Object) (Dict, int, error) {
	o, incr, err := xRefTable.DereferenceWithIncr(o)
	if err != nil || o == nil {
		return nil, 0, err
	}

	d, ok := o.(Dict)
	if !ok {
		return nil, 0, errors.Errorf("pdfcpu: dereferenceDictWithIncr: wrong type %T <%v>", o, o)
	}

	return d, incr, nil
}

// DereferenceFontDict returns the font dict referenced by indRef.
func (xRefTable *XRefTable) DereferenceFontDict(indRef IndirectRef) (Dict, error) {
	d, err := xRefTable.DereferenceDict(indRef)
	if err != nil {
		return nil, err
	}
	if d == nil {
		return nil, nil
	}

	if d.Type() == nil {
		return nil, errors.Errorf("pdfcpu: DereferenceFontDict: missing dict type %s\n", indRef)
	}

	if *d.Type() != "Font" {
		return nil, errors.Errorf("pdfcpu: DereferenceFontDict: expected Type=Font, unexpected Type: %s", *d.Type())
	}

	return d, nil
}

// DereferencePageNodeDict returns the page node dict referenced by indRef.
func (xRefTable *XRefTable) DereferencePageNodeDict(indRef IndirectRef) (Dict, error) {
	d, err := xRefTable.DereferenceDict(indRef)
	if err != nil {
		return nil, err
	}
	if d == nil {
		return nil, nil
	}

	dictType := d.Type()
	if dictType == nil {
		return nil, errors.New("pdfcpu: DereferencePageNodeDict: Missing dict type")
	}

	if *dictType != "Pages" && *dictType != "Page" {
		return nil, errors.Errorf("pdfcpu: DereferencePageNodeDict: unexpected Type: %s", *dictType)
	}

	return d, nil
}

func (xRefTable *XRefTable) dereferenceDestArray(o Object) (Array, error) {
	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return nil, err
	}
	switch o := o.(type) {
	case Array:
		return o, nil
	case Dict:
		o1, err := xRefTable.DereferenceDictEntry(o, "D")
		if err != nil {
			return nil, err
		}
		arr, ok := o1.(Array)
		if !ok {
			errors.Errorf("pdfcpu: invalid dest array:\n%s\n", o)
		}
		return arr, nil
	}

	return nil, errors.Errorf("pdfcpu: invalid dest array:\n%s\n", o)
}

// DereferenceDestArray resolves the destination for key.
func (xRefTable *XRefTable) DereferenceDestArray(key string) (Array, error) {
	if dNames := xRefTable.Names["Dests"]; dNames != nil {
		if o, ok := dNames.Value(key); ok {
			return xRefTable.dereferenceDestArray(o)
		}
	}

	if o, ok := xRefTable.Dests[key]; ok {
		return xRefTable.dereferenceDestArray(o)
	}

	return nil, errors.Errorf("pdfcpu: invalid named destination for: %s", key)
}

// DereferenceDictEntry returns a dereferenced dict entry.
func (xRefTable *XRefTable) DereferenceDictEntry(d Dict, key string) (Object, error) {
	o, found := d.Find(key)
	if !found || o == nil {
		return nil, errors.Errorf("pdfcpu: dict=%s entry=%s missing.", d, key)
	}
	return xRefTable.Dereference(o)
}

// DereferenceStringEntryBytes returns the bytes of a string entry of d.
func (xRefTable *XRefTable) DereferenceStringEntryBytes(d Dict, key string) ([]byte, error) {
	o, found := d.Find(key)
	if !found || o == nil {
		return nil, nil
	}
	o, err := xRefTable.Dereference(o)
	if err != nil {
		return nil, nil
	}

	switch o := o.(type) {
	case StringLiteral:
		bb, err := Unescape(o.Value())
		if err != nil {
			return nil, err
		}
		return bb, nil

	case HexLiteral:
		return o.Bytes()

	}

	return nil, errors.Errorf("pdfcpu: DereferenceStringEntryBytes dict=%s entry=%s, wrong type %T <%v>", d, key, o, o)
}

func (xRefTable *XRefTable) DestName(obj Object) (string, error) {
	dest, err := xRefTable.Dereference(obj)
	if err != nil {
		return "", err
	}

	var s string

	switch d := dest.(type) {
	case NameType:
		s = d.Value()
	case StringLiteral:
		s, err = StringLiteralToString(d)
	case HexLiteral:
		s, err = HexLiteralToString(d)
	}

	return s, err
}

func (xRefTable *XRefTable) locateObjForIndRef(ir IndirectRef) (Object, error) {
	objNr := int(ir.ObjectNumber)

	entry, found := xRefTable.FindTableEntryLight(objNr)
	if !found {
		return nil, errors.Errorf("pdfcpu: locateObjForIndRef: no xref entry found for obj #%d\n", objNr)
	}

	// Check for multiple indRefs.
	if entry.RefCount > 1 {
		entry.RefCount--
		// By returning nil we signal this object is still in use and can't be deleted.
		return nil, nil
	}

	// Since this is the only indRef we can move on and delete the entire object graph.
	return xRefTable.Dereference(ir)
}

// FreeObject marks an objects xref table entry as free and inserts it into the free list right after the head.
func (xRefTable *XRefTable) FreeObject(objNr int) error {
	// see 7.5.4 Cross-Reference Table

	// if log.DebugEnabled() {
	// 	log.Debug.Printf("FreeObject: begin %d\n", objNr)
	// }

	freeListHeadEntry, err := xRefTable.Free(0)
	if err != nil {
		return err
	}

	entry, found := xRefTable.FindTableEntryLight(objNr)
	if !found {
		return errors.Errorf("FreeObject: no entry for obj #%d\n", objNr)
	}

	if entry.Free {
		// if log.DebugEnabled() {
		// 	log.Debug.Printf("FreeObject: end %d already free\n", objNr)
		// }
		return nil
	}

	*entry.Generation++
	entry.Free = true
	entry.Compressed = false
	entry.Offset = freeListHeadEntry.Offset
	entry.Object = nil
	entry.RefCount = 0

	next := int64(objNr)
	freeListHeadEntry.Offset = &next

	// if log.DebugEnabled() {
	// 	log.Debug.Printf("FreeObject: end %d\n", objNr)
	// }

	return nil
}

// DeleteObject makes a deep remove of o.
func (xRefTable *XRefTable) DeleteObject(o Object) error {
	var err error

	ir, ok := o.(IndirectRef)
	if ok {
		o, err = xRefTable.locateObjForIndRef(ir)
		if err != nil || o == nil {
			return err
		}
		if err = xRefTable.FreeObject(ir.ObjectNumber.Value()); err != nil {
			return err
		}
	}

	switch o := o.(type) {

	case Dict:
		for _, v := range o {
			err := xRefTable.DeleteObject(v)
			if err != nil {
				return err
			}
		}

	case StreamDict:
		for _, v := range o.Dict {
			err := xRefTable.DeleteObject(v)
			if err != nil {
				return err
			}
		}

	case Array:
		for _, v := range o {
			err := xRefTable.DeleteObject(v)
			if err != nil {
				return err
			}
		}

	}

	return nil
}

// DeleteObjectGraph deletes all objects reachable by indRef.
func (xRefTable *XRefTable) DeleteObjectGraph(o Object) error {
	// if log.DebugEnabled() {
	// 	log.Debug.Println("DeleteObjectGraph: begin")
	// }

	indRef, ok := o.(IndirectRef)
	if !ok {
		return nil
	}

	// Delete ObjectGraph for object indRef.ObjectNumber.Value() via recursion.
	if err := xRefTable.DeleteObject(indRef); err != nil {
		return err
	}

	// if log.DebugEnabled() {
	// 	log.Debug.Println("DeleteObjectGraph: end")
	// }

	return nil
}

// NewFileSpecDict creates and returns a new fileSpec dictionary.
func (xRefTable *XRefTable) NewFileSpecDict(f, uf, desc string, indRefStreamDict IndirectRef) (Dict, error) {
	d := NewDict()
	d.InsertName("Type", "Filespec")

	s, err := EscapedUTF16String(f)
	if err != nil {
		return nil, err
	}
	d.InsertString("F", *s)

	if s, err = EscapedUTF16String(uf); err != nil {
		return nil, err
	}
	d.InsertString("UF", *s)

	efDict := NewDict()
	efDict.Insert("F", indRefStreamDict)
	efDict.Insert("UF", indRefStreamDict)
	d.Insert("EF", efDict)

	if desc != "" {
		if s, err = EscapedUTF16String(desc); err != nil {
			return nil, err
		}
		d.InsertString("Desc", *s)
	}

	// CI, optional, collection item dict, since V1.7
	// a corresponding collection schema dict in a collection.
	ciDict := NewDict()
	// add contextual meta info here.
	d.Insert("CI", ciDict)

	return d, nil
}

func (xRefTable *XRefTable) freeObjects() IntSet {
	m := IntSet{}

	for k, v := range xRefTable.Table {
		if v != nil && v.Free && k > 0 {
			m[k] = true
		}
	}

	return m
}

func anyKey(m IntSet) int {
	for k := range m {
		return k
	}
	return -1
}

func (xRefTable *XRefTable) handleDanglingFree(m IntSet, head *XRefTableEntry) error {
	for i := range m {

		entry, found := xRefTable.FindTableEntryLight(i)
		if !found {
			return errors.Errorf("pdfcpu: ensureValidFreeList: no xref entry found for obj #%d\n", i)
		}

		if !entry.Free {
			return errors.Errorf("pdfcpu: ensureValidFreeList: xref entry is not free for obj #%d\n", i)
		}

		if *entry.Generation == FreeHeadGeneration {
			entry.Offset = &zero
			continue
		}

		entry.Offset = head.Offset
		next := int64(i)
		head.Offset = &next
	}
	return nil
}

func (xRefTable *XRefTable) validateFreeList(f int, m IntSet, e *XRefTableEntry) (*XRefTableEntry, int, error) {
	var lastValid *XRefTableEntry
	var nextFree int

	for f != 0 {
		// if log.TraceEnabled() {
		// 	log.Trace.Printf("EnsureValidFreeList: validating obj #%d %v\n", f, m)
		// }
		// verify if obj f is one of the free objects recorded.
		if !m[f] {
			if len(m) > 0 && lastValid == nil {
				lastValid = e
				f = anyKey(m)
				nextFree = f
				continue
			}
			// Repair last entry.
			*e.Offset = 0
			break
		}

		delete(m, f)

		var err error
		if e, err = xRefTable.Free(f); err != nil {
			return nil, 0, err
		}
		if e == nil {
			return nil, 0, errors.Errorf("pdfcpu: ensureValidFreeList: no xref entry found for obj #%d\n", f)
		}

		f = int(*e.Offset)
	}

	return lastValid, nextFree, nil
}

// EnsureValidFreeList ensures the integrity of the free list associated with the recorded free objects.
// See 7.5.4 Cross-Reference Table
func (xRefTable *XRefTable) EnsureValidFreeList() error {
	// if log.TraceEnabled() {
	// 	log.Trace.Println("EnsureValidFreeList: begin")
	// }

	m := xRefTable.freeObjects()

	// Verify free object 0 as free list head.
	head, _ := xRefTable.Find(0)
	if head == nil {
		g0 := FreeHeadGeneration
		head = &XRefTableEntry{Free: true, Offset: &zero, Generation: &g0}
		xRefTable.Table[0] = head
	}

	// verify generation of 56535
	if *head.Generation != FreeHeadGeneration {
		// Fix generation for obj 0.
		*head.Generation = FreeHeadGeneration
	}

	if len(m) == 0 {

		// no free object other than 0.

		// repair if necessary
		if *head.Offset != 0 {
			*head.Offset = 0
		}

		// if log.TraceEnabled() {
		// 	log.Trace.Println("EnsureValidFreeList: empty free list.")
		// }
		return nil
	}

	e := head
	f := int(*e.Offset)

	lastValid, nextFree, err := xRefTable.validateFreeList(f, m, e)
	if err != nil {
		return err
	}

	if lastValid != nil {
		*lastValid.Offset = int64(nextFree)
	}

	if len(m) == 0 {
		// if log.TraceEnabled() {
		// 	log.Trace.Println("EnsureValidFreeList: end, regular linked list")
		// }
		return nil
	}

	// insert remaining free objects into verified linked list
	// unless they are forever deleted with generation 65535.
	// In that case they have to point to obj 0.
	err = xRefTable.handleDanglingFree(m, head)

	// if log.TraceEnabled() {
	// 	log.Trace.Println("EnsureValidFreeList: end")
	// }

	return err
}

func (xRefTable *XRefTable) DeleteDictEntry(d Dict, key string) error {
	o, found := d.Find(key)
	if !found {
		return nil
	}
	if err := xRefTable.DeleteObject(o); err != nil {
		return err
	}
	d.Delete(key)
	return nil
}

// UndeleteObject ensures an object is not recorded in the free list.
// e.g. sometimes caused by indirect references to free objects in the original PDF file.
func (xRefTable *XRefTable) UndeleteObject(objectNumber int) error {
	// if log.DebugEnabled() {
	// 	log.Debug.Printf("UndeleteObject: begin %d\n", objectNumber)
	// }

	f, err := xRefTable.Free(0)
	if err != nil {
		return err
	}

	// until we have found the last free object which should point to obj 0.
	for *f.Offset != 0 {
		objNr := int(*f.Offset)

		entry, err := xRefTable.Free(objNr)
		if err != nil {
			return err
		}

		if objNr == objectNumber {
			// if log.DebugEnabled() {
			// 	log.Debug.Printf("UndeleteObject end: undeleting obj#%d\n", objectNumber)
			// }
			*f.Offset = *entry.Offset
			entry.Offset = nil
			if *entry.Generation > 0 {
				*entry.Generation--
			}
			entry.Free = false
			return nil
		}

		f = entry
	}

	// if log.DebugEnabled() {
	// 	log.Debug.Printf("UndeleteObject: end: obj#%d not in free list.\n", objectNumber)
	// }

	return nil
}

// IsObjValid returns true if the object with objNr and genNr is valid.
func (xRefTable *XRefTable) IsObjValid(objNr, genNr int) (bool, error) {
	entry, found := xRefTable.FindTableEntry(objNr, genNr)
	if !found {
		return false, errors.Errorf("pdfcpu: IsObjValid: no entry for obj#%d\n", objNr)
	}
	if entry.Free {
		return false, errors.Errorf("pdfcpu: IsObjValid: unexpected free entry for obj#%d\n", objNr)
	}
	return entry.Valid, nil
}

// IsValid returns true if the object referenced by ir is valid.
func (xRefTable *XRefTable) IsValid(ir IndirectRef) (bool, error) {
	return xRefTable.IsObjValid(ir.ObjectNumber.Value(), ir.GenerationNumber.Value())
}

// IsObjBeingValidated returns true if the object with objNr and genNr is being validated.
func (xRefTable *XRefTable) IsObjBeingValidated(objNr, genNr int) (bool, error) {
	entry, found := xRefTable.FindTableEntry(objNr, genNr)
	if !found {
		return false, errors.Errorf("pdfcpu: IsObjBeingValidated: no entry for obj#%d\n", objNr)
	}
	if entry.Free {
		return false, errors.Errorf("pdfcpu: IsObjBeingValidated: unexpected free entry for obj#%d\n", objNr)
	}
	return entry.BeingValidated, nil
}

// IsBeingValidated returns true if the object referenced by ir is being validated.
func (xRefTable *XRefTable) IsBeingValidated(ir IndirectRef) (bool, error) {
	return xRefTable.IsObjBeingValidated(ir.ObjectNumber.Value(), ir.GenerationNumber.Value())
}

// SetValid marks the xreftable entry of the object referenced by ir as valid.
func (xRefTable *XRefTable) SetValid(ir IndirectRef) error {
	entry, found := xRefTable.FindTableEntry(ir.ObjectNumber.Value(), ir.GenerationNumber.Value())
	if !found {
		return errors.Errorf("pdfcpu: SetValid: no entry for obj#%d\n", ir.ObjectNumber.Value())
	}
	if entry.Free {
		return errors.Errorf("pdfcpu: SetValid: unexpected free entry for obj#%d\n", ir.ObjectNumber.Value())
	}
	entry.Valid = true
	entry.BeingValidated = false

	return nil
}

// SetBeingValidated marks the xreftable entry of the object referenced by ir as being validated.
func (xRefTable *XRefTable) SetBeingValidated(ir IndirectRef) error {
	entry, found := xRefTable.FindTableEntry(ir.ObjectNumber.Value(), ir.GenerationNumber.Value())
	if !found {
		return errors.Errorf("pdfcpu: SetBeingValidated: no entry for obj#%d\n", ir.ObjectNumber.Value())
	}
	if entry.Free {
		return errors.Errorf("pdfcpu: SetBeingValidated: unexpected free entry for obj#%d\n", ir.ObjectNumber.Value())
	}
	entry.BeingValidated = true
	entry.Valid = false

	return nil
}

// DereferenceStreamDict resolves a stream dictionary object.
func (xRefTable *XRefTable) DereferenceStreamDict(o Object) (*StreamDict, bool, error) {
	// TODO Check if we still need the bool return value
	indRef, ok := o.(IndirectRef)
	if !ok {
		sd, ok := o.(StreamDict)
		if !ok {
			return nil, false, errors.Errorf("pdfcpu: DereferenceStreamDict: wrong type <%v> %T", o, o)
		}
		return &sd, false, nil
	}

	// 7.3.10
	// An indirect reference to an undefined object shall not be considered an error by a conforming reader;
	// it shall be treated as a reference to the null object.
	entry, found := xRefTable.FindTableEntry(indRef.ObjectNumber.Value(), indRef.GenerationNumber.Value())
	if !found || entry.Object == nil || entry.Free {
		return nil, false, nil
	}
	ev := entry.Valid
	if !entry.Valid {
		entry.Valid = true
	}
	sd, ok := entry.Object.(StreamDict)
	if !ok {
		return nil, false, errors.Errorf("pdfcpu: DereferenceStreamDict: wrong type <%v> %T", o, entry.Object)
	}

	return &sd, ev, nil
}

// DereferenceXObjectDict resolves an XObject.
func (xRefTable *XRefTable) DereferenceXObjectDict(indRef IndirectRef) (*StreamDict, error) {
	sd, _, err := xRefTable.DereferenceStreamDict(indRef)
	if err != nil {
		return nil, err
	}
	if sd == nil {
		return nil, nil
	}

	subType := sd.Dict.Subtype()
	if subType == nil {
		return nil, errors.Errorf("pdfcpu: DereferenceXObjectDict: missing stream dict Subtype %s\n", indRef)
	}

	if *subType != "Image" && *subType != "Form" {
		return nil, errors.Errorf("pdfcpu: DereferenceXObjectDict: unexpected stream dict Subtype %s\n", *subType)
	}

	return sd, nil
}

// Catalog returns a pointer to the root object / catalog.
func (xRefTable *XRefTable) Catalog() (Dict, error) {
	if xRefTable.RootDict != nil {
		return xRefTable.RootDict, nil
	}

	if xRefTable.Root == nil {
		return nil, errors.New("pdfcpu: Catalog: missing root dict")
	}

	o, _, err := xRefTable.indRefToObject(xRefTable.Root, true)
	if err != nil || o == nil {
		return nil, err
	}

	d, ok := o.(Dict)
	if !ok {
		return nil, errors.New("pdfcpu: catalog: corrupt root catalog")
	}

	xRefTable.RootDict = d

	return xRefTable.RootDict, nil
}

// EncryptDict returns a pointer to the root object / catalog.
func (xRefTable *XRefTable) EncryptDict() (Dict, error) {
	o, _, err := xRefTable.indRefToObject(xRefTable.Encrypt, true)
	if err != nil || o == nil {
		return nil, err
	}

	d, ok := o.(Dict)
	if !ok {
		return nil, errors.New("pdfcpu: encryptDict: corrupt encrypt dict")
	}

	return d, nil
}

// CatalogHasPieceInfo returns true if the root has an entry for \"PieceInfo\".
func (xRefTable *XRefTable) CatalogHasPieceInfo() (bool, error) {
	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return false, err
	}
	obj, hasPieceInfo := rootDict.Find("PieceInfo")
	return hasPieceInfo && obj != nil, nil
}

// Pages returns the Pages reference contained in the catalog.
func (xRefTable *XRefTable) Pages() (*IndirectRef, error) {
	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return nil, err
	}
	return rootDict.IndirectRefEntry("Pages"), nil
}

// MissingObjects returns the number of objects that were not written
// plus the corresponding comma separated string representation.
func (xRefTable *XRefTable) MissingObjects() (int, *string) {
	var missing []string

	for i := 0; i < *xRefTable.Size; i++ {
		if !xRefTable.Exists(i) {
			missing = append(missing, fmt.Sprintf("%d", i))
		}
	}

	var s *string

	if len(missing) > 0 {
		joined := strings.Join(missing, ",")
		s = &joined
	}

	return len(missing), s
}

func objStr(entry *XRefTableEntry, objNr int) string {
	typeStr := fmt.Sprintf("%T", entry.Object)

	d, ok := entry.Object.(Dict)
	if ok {
		if d.Type() != nil {
			typeStr += fmt.Sprintf(" type=%s", *d.Type())
		}
		if d.Subtype() != nil {
			typeStr += fmt.Sprintf(" subType=%s", *d.Subtype())
		}
	}

	if entry.ObjectStream != nil {
		// was compressed, offset is nil.
		return fmt.Sprintf("%5d: was compressed %d[%d] generation=%d %s \n%s\n", objNr, *entry.ObjectStream, *entry.ObjectStreamInd, *entry.Generation, typeStr, entry.Object)
	}

	// regular in use object with offset.
	if entry.Offset != nil {
		return fmt.Sprintf("%5d:   offset=%8d generation=%d %s \n%s\n", objNr, *entry.Offset, *entry.Generation, typeStr, entry.Object)
	}

	return fmt.Sprintf("%5d:   offset=nil generation=%d %s \n%s\n", objNr, *entry.Generation, typeStr, entry.Object)
}

// Lines is a split function for a Scanner that returns each line of
// text, stripped of any trailing end-of-line marker. The returned line may
// be empty. The end-of-line marker is one carriage return followed
// by one newline or one carriage return or one newline.
// The last non-empty line of input will be returned even if it has no newline.
func Lines(data []byte, atEOF bool) (advance int, token []byte, err error) {
	if atEOF && len(data) == 0 {
		return 0, nil, nil
	}

	indCR := bytes.IndexByte(data, '\r')
	indLF := bytes.IndexByte(data, '\n')

	switch {

	case indCR >= 0 && indLF >= 0:
		if indCR < indLF {
			if indCR+1 == indLF {
				// \r\n
				return indCR + 2, data[0:indCR], nil
			}
			// \r
			return indCR + 1, data[0:indCR], nil
		}
		// \n
		return indLF + 1, data[0:indLF], nil

	case indCR >= 0:
		// \r
		return indCR + 1, data[0:indCR], nil

	case indLF >= 0:
		// \n
		return indLF + 1, data[0:indLF], nil

	}

	// If we're at EOF, we have a final, non-terminated line. Return it.
	if atEOF {
		return len(data), data, nil
	}

	// Request more data.
	return 0, nil, nil
}

func (xRefTable *XRefTable) DumpObject(objNr, mode int) {
	// mode
	//  0 .. silent / obj only
	//  1 .. ascii
	//  2 .. hex
	entry := xRefTable.Table[objNr]
	if entry == nil || entry.Free || entry.Compressed || entry.Object == nil {
		fmt.Println(":(")
		return
	}

	str := objStr(entry, objNr)

	if mode > 0 {
		sd, ok := entry.Object.(StreamDict)
		if ok {

			err := sd.Decode()
			if err == ErrUnsupportedFilter {
				str += "stream filter unsupported!"
				fmt.Println(str)
				return
			}
			if err != nil {
				str += "decoding problem encountered!"
				fmt.Println(str)
				return
			}

			s := "decoded stream content (length = %d)\n%s\n"
			s1 := ""
			switch mode {
			case 1:
				sc := bufio.NewScanner(bytes.NewReader(sd.Content))
				sc.Split(Lines)
				for sc.Scan() {
					s1 += sc.Text() + "\n"
				}
				str += fmt.Sprintf(s, len(sd.Content), s1)
			case 2:
				str += fmt.Sprintf(s, len(sd.Content), hex.Dump(sd.Content))
			}
		}

		osd, ok := entry.Object.(ObjectStreamDictType)
		if ok {
			str += fmt.Sprintf("object stream count:%d size of objectarray:%d\n", osd.ObjCount, len(osd.ObjArray))
		}
	}

	fmt.Println(str)
}

func (xRefTable *XRefTable) bindNameTreeNode(name string, n *Node, root bool) error {
	var dict Dict

	if n.D == nil {
		dict = NewDict()
		n.D = dict
	} else {
		if root {
			namesDict, err := xRefTable.NamesDict()
			if err != nil {
				return err
			}
			if namesDict == nil {
				return errors.New("pdfcpu: root entry \"Names\" corrupt")
			}
			namesDict.Update(name, n.D)
		}
		// if log.DebugEnabled() {
		// 	log.Debug.Printf("bind dict = %v\n", n.D)
		// }
		dict = n.D
	}

	if !root {
		dict.Update("Limits", NewHexLiteralArray(n.Kmin, n.Kmax))
	} else {
		dict.Delete("Limits")
	}

	if n.leaf() {
		a := Array{}
		for _, e := range n.Names {
			a = append(a, NewHexLiteral([]byte(e.k)))
			a = append(a, e.v)
		}
		dict.Update("Names", a)
		// if log.DebugEnabled() {
		// 	log.Debug.Printf("bound nametree node(leaf): %s/n", dict)
		// }
		return nil
	}

	kids := Array{}
	for _, k := range n.Kids {
		if err := xRefTable.bindNameTreeNode(name, k, false); err != nil {
			return err
		}
		indRef, err := xRefTable.IndRefForNewObject(k.D)
		if err != nil {
			return err
		}
		kids = append(kids, *indRef)
	}

	dict.Update("Kids", kids)
	dict.Delete("Names")

	// if log.DebugEnabled() {
	// 	log.Debug.Printf("bound nametree node(intermediary): %s/n", dict)
	// }

	return nil
}

// BindNameTrees syncs up the internal name tree cache with the xreftable.
func (xRefTable *XRefTable) BindNameTrees() error {
	// if log.WriteEnabled() {
	// 	log.Write.Println("BindNameTrees..")
	// }

	// Iterate over internal name tree rep.
	for k, v := range xRefTable.Names {
		// if log.WriteEnabled() {
		// 	log.Write.Printf("bindNameTree: %s\n", k)
		// }
		if err := xRefTable.bindNameTreeNode(k, v, true); err != nil {
			return err
		}
	}

	return nil
}

// LocateNameTree locates/ensures a specific name tree.
func (xRefTable *XRefTable) LocateNameTree(nameTreeName string, ensure bool) error {
	if xRefTable.Names[nameTreeName] != nil {
		return nil
	}

	d, err := xRefTable.Catalog()
	if err != nil {
		return err
	}

	o, found := d.Find("Names")
	if !found {
		if !ensure {
			return nil
		}
		dict := NewDict()

		indRef, err := xRefTable.IndRefForNewObject(dict)
		if err != nil {
			return err
		}
		d.Insert("Names", *indRef)

		d = dict
	} else {
		d, err = xRefTable.DereferenceDict(o)
		if err != nil {
			return err
		}
	}

	o, found = d.Find(nameTreeName)
	if !found {
		if !ensure {
			return nil
		}
		dict := NewDict()
		dict.Insert("Names", Array{})

		indRef, err := xRefTable.IndRefForNewObject(dict)
		if err != nil {
			return err
		}

		d.Insert(nameTreeName, *indRef)

		xRefTable.Names[nameTreeName] = &Node{D: dict}

		return nil
	}

	d1, err := xRefTable.DereferenceDict(o)
	if err != nil {
		return err
	}

	xRefTable.Names[nameTreeName] = &Node{D: d1}

	return nil
}

// NamesDict returns the dict that contains all name trees.
func (xRefTable *XRefTable) NamesDict() (Dict, error) {
	d, err := xRefTable.Catalog()
	if err != nil {
		return nil, err
	}

	o, found := d.Find("Names")
	if !found {
		dict := NewDict()
		indRef, err := xRefTable.IndRefForNewObject(dict)
		if err != nil {
			return nil, err
		}
		d["Names"] = *indRef
		return dict, nil
	}

	return xRefTable.DereferenceDict(o)
}

// RemoveNameTree removes a specific name tree.
// Also removes a resulting empty names dict.
func (xRefTable *XRefTable) RemoveNameTree(nameTreeName string) error {
	namesDict, err := xRefTable.NamesDict()
	if err != nil {
		return err
	}

	if namesDict == nil {
		return errors.New("pdfcpu: removeNameTree: root entry \"Names\" corrupt")
	}

	// We have an existing name dict.

	// Delete the name tree.
	if err = xRefTable.DeleteDictEntry(namesDict, nameTreeName); err != nil {
		return err
	}
	if namesDict.Len() > 0 {
		return nil
	}

	// Remove empty names dict.
	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return err
	}
	if err = xRefTable.DeleteDictEntry(rootDict, "Names"); err != nil {
		return err
	}

	// if log.DebugEnabled() {
	// 	log.Debug.Printf("Deleted Names from root: %s\n", rootDict)
	// }

	return nil
}

// RemoveCollection removes an existing Collection entry from the catalog.
func (xRefTable *XRefTable) RemoveCollection() error {
	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return err
	}
	return xRefTable.DeleteDictEntry(rootDict, "Collection")
}

// EnsureCollection makes sure there is a Collection entry in the catalog.
// Needed for portfolio / portable collections eg. for file attachments.
func (xRefTable *XRefTable) EnsureCollection() error {
	rootDict, err := xRefTable.Catalog()
	if err != nil {
		return err
	}

	if _, found := rootDict.Find("Collection"); found {
		return nil
	}

	dict := NewDict()
	dict.Insert("Type", NameType("Collection"))
	dict.Insert("View", NameType("D"))

	schemaDict := NewDict()
	schemaDict.Insert("Type", NameType("CollectionSchema"))

	fileNameCFDict := NewDict()
	fileNameCFDict.Insert("Type", NameType("CollectionField"))
	fileNameCFDict.Insert("Subtype", NameType("F"))
	fileNameCFDict.Insert("N", StringLiteral("Filename"))
	fileNameCFDict.Insert("O", Integer(1))
	schemaDict.Insert("FileName", fileNameCFDict)

	descCFDict := NewDict()
	descCFDict.Insert("Type", NameType("CollectionField"))
	descCFDict.Insert("Subtype", NameType("Desc"))
	descCFDict.Insert("N", StringLiteral("Description"))
	descCFDict.Insert("O", Integer(2))
	schemaDict.Insert("Description", descCFDict)

	sizeCFDict := NewDict()
	sizeCFDict.Insert("Type", NameType("CollectionField"))
	sizeCFDict.Insert("Subtype", NameType("Size"))
	sizeCFDict.Insert("N", StringLiteral("Size"))
	sizeCFDict.Insert("O", Integer(3))
	schemaDict.Insert("Size", sizeCFDict)

	modDateCFDict := NewDict()
	modDateCFDict.Insert("Type", NameType("CollectionField"))
	modDateCFDict.Insert("Subtype", NameType("ModDate"))
	modDateCFDict.Insert("N", StringLiteral("Last Modification"))
	modDateCFDict.Insert("O", Integer(4))
	schemaDict.Insert("ModDate", modDateCFDict)

	// TODO use xRefTable.InsertAndUseRecycled(xRefTableEntry)

	indRef, err := xRefTable.IndRefForNewObject(schemaDict)
	if err != nil {
		return err
	}
	dict.Insert("Schema", *indRef)

	sortDict := NewDict()
	sortDict.Insert("S", NameType("ModDate"))
	sortDict.Insert("A", Boolean(false))
	dict.Insert("Sort", sortDict)

	indRef, err = xRefTable.IndRefForNewObject(dict)
	if err != nil {
		return err
	}
	rootDict.Insert("Collection", *indRef)

	return nil
}

// RemoveEmbeddedFilesNameTree removes both the embedded files name tree and the Collection dict.
func (xRefTable *XRefTable) RemoveEmbeddedFilesNameTree() error {
	delete(xRefTable.Names, "EmbeddedFiles")

	if err := xRefTable.RemoveNameTree("EmbeddedFiles"); err != nil {
		return err
	}

	return xRefTable.RemoveCollection()
}

// IDFirstElement returns the first element of ID.
func (xRefTable *XRefTable) IDFirstElement() (id []byte, err error) {
	hl, ok := xRefTable.ID[0].(HexLiteral)
	if ok {
		return hl.Bytes()
	}

	sl, ok := xRefTable.ID[0].(StringLiteral)
	if !ok {
		return nil, errors.New("pdfcpu: ID must contain hex literals or string literals")
	}

	bb, err := Unescape(sl.Value())
	if err != nil {
		return nil, err
	}

	return bb, nil
}

// InheritedPageAttrs represents all inherited page attributes.
type InheritedPageAttrs struct {
	Resources Dict
	MediaBox  *Rectangle
	CropBox   *Rectangle
	Rotate    int
}

func rect(xRefTable *XRefTable, a Array) (*Rectangle, error) {
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

func weaveResourceSubDict(d1, d2 Dict) {
	for k, v := range d1 {
		if v != nil {
			v = v.Clone()
		}
		d2[k] = v
	}
}

func (xRefTable *XRefTable) consolidateResources(obj Object, pAttrs *InheritedPageAttrs) error {
	d, err := xRefTable.DereferenceDict(obj)
	if err != nil {
		return err
	}
	if len(d) == 0 {
		return nil
	}

	if pAttrs.Resources == nil {
		// Create a resource dict that eventually will contain any inherited resources
		// walking down from page root to leaf node representing the page in question.
		pAttrs.Resources = d.Clone().(Dict)
		for k, v := range pAttrs.Resources {
			o, err := xRefTable.Dereference(v)
			if err != nil {
				return err
			}
			pAttrs.Resources[k] = o.Clone()
		}
		// if log.WriteEnabled() {
		// 	log.Write.Printf("pA:\n%s\n", pAttrs.Resources)
		// }
		return nil
	}

	// Accumulate any resources defined in this page node into the inherited resources.
	for k, v := range d {
		if k == "ProcSet" || v == nil {
			continue
		}
		d1, err := xRefTable.DereferenceDict(v)
		if err != nil {
			return err
		}
		if d1 == nil {
			continue
		}
		// We have identified a subdict that needs to go into the inherited res dict.
		if pAttrs.Resources[k] == nil {
			pAttrs.Resources[k] = d1.Clone()
			continue
		}
		d2, ok := pAttrs.Resources[k].(Dict)
		if !ok {
			return errors.Errorf("pdfcpu: checkInheritedPageAttrs: expected Dict d2: %T", pAttrs.Resources[k])
		}
		// Weave sub dict d1 into inherited sub dict d2.
		// Any existing resource names will be overridden.
		weaveResourceSubDict(d1, d2)
	}

	return nil
}

func (xRefTable *XRefTable) checkInheritedPageAttrs(pageDict Dict, pAttrs *InheritedPageAttrs, consolidateRes bool) error {
	// Return mediaBox, cropBox and rotate as inherited.
	// if consolidateRes is true
	// then consolidate all inherited resources as required by content stream
	// else return pageDict resources.
	var (
		obj   Object
		found bool
	)

	if obj, found = pageDict.Find("MediaBox"); found {
		a, err := xRefTable.DereferenceArray(obj)
		if err != nil {
			return err
		}
		if pAttrs.MediaBox, err = rect(xRefTable, a); err != nil {
			return err
		}
	}

	if obj, found = pageDict.Find("CropBox"); found {
		a, err := xRefTable.DereferenceArray(obj)
		if err != nil {
			return err
		}
		if pAttrs.CropBox, err = rect(xRefTable, a); err != nil {
			return err
		}
	}

	if obj, found = pageDict.Find("Rotate"); found {
		obj, err := xRefTable.Dereference(obj)
		if err != nil {
			return err
		}

		switch obj := obj.(type) {
		case Integer:
			pAttrs.Rotate = obj.Value()
		case Float:
			if xRefTable.ValidationMode == ValidationStrict {
				return errors.Errorf("pdfcpu: dereferenceNumber: wrong type <%v>", obj)
			}

			pAttrs.Rotate = int(math.Round(obj.Value()))
		default:
			return errors.Errorf("pdfcpu: dereferenceNumber: wrong type <%v>", obj)
		}
	}

	if obj, found = pageDict.Find("Resources"); !found {
		return nil
	}

	if !consolidateRes {
		// Return resourceDict as is.
		d, err := xRefTable.DereferenceDict(obj)
		if err != nil {
			return err
		}
		pAttrs.Resources = d
		return nil
	}

	// Accumulate inherited resources.
	return xRefTable.consolidateResources(obj, pAttrs)
}

// PageContent returns the content in PDF syntax for page dict d.
func (xRefTable *XRefTable) PageContent(d Dict, pageNr int) ([]byte, error) {
	o, _ := d.Find("Contents")
	if o == nil {
		return nil, ErrNoContent
	}

	o, err := xRefTable.Dereference(o)
	if err != nil || o == nil {
		return nil, err
	}

	bb := []byte{}

	switch o := o.(type) {

	case StreamDict:
		// no further processing.
		err := o.Decode()
		if err == ErrUnsupportedFilter {
			return nil, errors.New("pdfcpu: unsupported filter: unable to decode content")
		}
		if err != nil {
			return nil, errors.Errorf("page %d content decode: %v", pageNr, err)
		}

		bb = append(bb, o.Content...)

	case Array:
		// process array of content stream dicts.
		for _, o := range o {
			if o == nil {
				continue
			}
			o, _, err := xRefTable.DereferenceStreamDict(o)
			if err != nil {
				return nil, errors.Errorf("page %d content decode: %v", pageNr, err)
			}
			if o == nil {
				continue
			}
			err = o.Decode()
			if err == ErrUnsupportedFilter {
				return nil, errors.New("pdfcpu: unsupported filter: unable to decode content")
			}
			if err != nil {
				return nil, errors.Errorf("page %d content decode: %v", pageNr, err)
			}
			bb = append(bb, o.Content...)
		}

	default:
		return nil, errors.Errorf("pdfcpu: page content must be stream dict or array")
	}

	if len(bb) == 0 {
		return nil, ErrNoContent
	}

	return bb, nil
}

// FontObject represents a font used in a PDF file.
type FontObject struct {
	ResourceNames []string
	Prefix        string
	FontName      string
	FontDict      Dict
	Data          []byte
	Extension     string
	Embedded      bool
}

// AddResourceName adds a resourceName referring to this font.
func (fo *FontObject) AddResourceName(resourceName string) {
	for _, resName := range fo.ResourceNames {
		if resName == resourceName {
			return
		}
	}
	fo.ResourceNames = append(fo.ResourceNames, resourceName)
}

// ResourceNamesString returns a string representation of all the resource names of this font.
func (fo FontObject) ResourceNamesString() string {
	var resNames []string
	resNames = append(resNames, fo.ResourceNames...)
	return strings.Join(resNames, ",")
}

// Data returns the raw data belonging to this image object.
// func (fo FontObject) Data() []byte {
// 	return nil
// }

// SubType returns the SubType of this font.
func (fo FontObject) SubType() string {
	var subType string
	if fo.FontDict.Subtype() != nil {
		subType = *fo.FontDict.Subtype()
	}
	return subType
}

// Encoding returns the Encoding of this font.
func (fo FontObject) Encoding() string {
	encoding := "Built-in"
	pdfObject, found := fo.FontDict.Find("Encoding")
	if found {
		switch enc := pdfObject.(type) {
		case NameType:
			encoding = enc.Value()
		default:
			encoding = "Custom"
		}
	}
	return encoding
}

func (fo FontObject) String() string {
	return fmt.Sprintf("%-10s %-30s %-10s %-20s %-8v %s\n",
		fo.Prefix, fo.FontName,
		fo.SubType(), fo.Encoding(),
		fo.Embedded, fo.ResourceNamesString())
}

// ImageObject represents an image used in a PDF file.
type ImageObject struct {
	ResourceNames map[int]string
	ImageDict     *StreamDict
}

// DuplicateImageObject represents a redundant image.
type DuplicateImageObject struct {
	ImageDict *StreamDict
	NewObjNr  int
}

// AddResourceName adds a resourceName to this imageObject's ResourceNames map.
func (io *ImageObject) AddResourceName(pageNr int, resourceName string) {
	io.ResourceNames[pageNr] = resourceName
}

// ResourceNamesString returns a string representation of the ResourceNames for this image.
func (io ImageObject) ResourceNamesString() string {
	pageNrs := make([]int, 0, len(io.ResourceNames))
	for k := range io.ResourceNames {
		pageNrs = append(pageNrs, k)
	}
	sort.Ints(pageNrs)
	var sb strings.Builder
	for i, pageNr := range pageNrs {
		if i > 0 {
			sb.WriteString(", ")
		}
		sb.WriteString(fmt.Sprintf("%d:%s", pageNr, io.ResourceNames[pageNr]))
	}
	var resNames []string
	resNames = append(resNames, sb.String())
	return strings.Join(resNames, ",")
}

var resourceTypes = NewStringSet([]string{"ColorSpace", "ExtGState", "Font", "Pattern", "Properties", "Shading", "XObject"})

// PageResourceNames represents the required resource names for a specific page as extracted from its content streams.
type PageResourceNames map[string]StringSet

// NewPageResourceNames returns initialized pageResourceNames.
func NewPageResourceNames() PageResourceNames {
	m := make(map[string]StringSet, len(resourceTypes))
	for k := range resourceTypes {
		m[k] = StringSet{}
	}
	return m
}

// Resources returns a set of all required resource names for subdict s.
func (prn PageResourceNames) Resources(s string) StringSet {
	return prn[s]
}

// HasResources returns true for any resource names present in resource subDict s.
func (prn PageResourceNames) HasResources(s string) bool {
	return len(prn.Resources(s)) > 0
}

// HasContent returns true in any resource names present.
func (prn PageResourceNames) HasContent() bool {
	for k := range resourceTypes {
		if prn.HasResources(k) {
			return true
		}
	}
	return false
}

func (prn PageResourceNames) String() string {
	sep := ", "
	var ss []string
	s := []string{"PageResourceNames:\n"}
	for k := range resourceTypes {
		ss = nil
		for k := range prn.Resources(k) {
			ss = append(ss, k)
		}
		s = append(s, k+": "+strings.Join(ss, sep)+"\n")
	}
	return strings.Join(s, "")
}

func consolidateResourceSubDict(d Dict, key string, prn PageResourceNames, pageNr int) error {
	o := d[key]
	if o == nil {
		if prn.HasResources(key) {
			return errors.Errorf("pdfcpu: page %d: missing required resource subdict: %s\n%s", pageNr, key, prn)
		}
		return nil
	}
	if !prn.HasResources(key) {
		d.Delete(key)
		return nil
	}
	d1 := o.(Dict)
	set := StringSet{}
	res := prn.Resources(key)
	// Iterate over inherited resource sub dict and remove any entries not required.
	for k := range d1 {
		ki := NameType(k).Value()
		if !res[ki] {
			d1.Delete(k)
			continue
		}
		set[ki] = true
	}
	// Check for missing resource sub dict entries.
	for k := range res {
		if !set[k] {
			return errors.Errorf("pdfcpu: page %d: missing required %s: %s", pageNr, key, k)
		}
	}
	d[key] = d1
	return nil
}

func consolidateResourceDict(d Dict, prn PageResourceNames, pageNr int) error {
	for k := range resourceTypes {
		if err := consolidateResourceSubDict(d, k, prn, pageNr); err != nil {
			return err
		}
	}
	return nil
}

var (
	errPageContentCorrupt  = errors.New("pdfcpu: corrupt page content")
	errTJExpressionCorrupt = errors.New("pdfcpu: corrupt TJ expression")
	errBIExpressionCorrupt = errors.New("pdfcpu: corrupt BI expression")
)

func whitespaceOrEOL(c rune) bool {
	return unicode.IsSpace(c) || c == 0x0A || c == 0x0D || c == 0x00
}

var (
	errArrayCorrupt            = errors.New("pdfcpu: parse: corrupt array")
	errArrayNotTerminated      = errors.New("pdfcpu: parse: unterminated array")
	errDictionaryCorrupt       = errors.New("pdfcpu: parse: corrupt dictionary")
	errDictionaryNotTerminated = errors.New("pdfcpu: parse: unterminated dictionary")
	errHexLiteralCorrupt       = errors.New("pdfcpu: parse: corrupt hex literal")
	errHexLiteralNotTerminated = errors.New("pdfcpu: parse: hex literal not terminated")
	errNameObjectCorrupt       = errors.New("pdfcpu: parse: corrupt name object")
	errNoArray                 = errors.New("pdfcpu: parse: no array")
	errNoDictionary            = errors.New("pdfcpu: parse: no dictionary")
	errStringLiteralCorrupt    = errors.New("pdfcpu: parse: corrupt string literal, possibly unbalanced parenthesis")
	errBufNotAvailable         = errors.New("pdfcpu: parse: no buffer available")
	errXrefStreamMissingW      = errors.New("pdfcpu: parse: xref stream dict missing entry W")
	errXrefStreamCorruptW      = errors.New("pdfcpu: parse: xref stream dict corrupt entry W: expecting array of 3 int")
	errXrefStreamCorruptIndex  = errors.New("pdfcpu: parse: xref stream dict corrupt entry Index")
	errObjStreamMissingN       = errors.New("pdfcpu: parse: obj stream dict missing entry W")
	errObjStreamMissingFirst   = errors.New("pdfcpu: parse: obj stream dict missing entry First")
)

func positionToNextWhitespace(s string) (int, string) {
	for i, c := range s {
		if unicode.IsSpace(c) || c == 0x00 {
			return i, s[i:]
		}
	}
	return 0, s
}

// PositionToNextWhitespaceOrChar trims a string to next whitespace or one of given chars.
// Returns the index of the position or -1 if no match.
func positionToNextWhitespaceOrChar(s, chars string) (int, string) {
	if len(chars) == 0 {
		return positionToNextWhitespace(s)
	}

	for i, c := range s {
		for _, m := range chars {
			if c == m || unicode.IsSpace(c) || c == 0x00 {
				return i, s[i:]
			}
		}
	}

	return -1, s
}

func positionToNextEOL(s string) (string, int) {
	for i, c := range s {
		for _, m := range "\x0A\x0D" {
			if c == m {
				return s[i:], i
			}
		}
	}
	return "", 0
}

// trimLeftSpace trims leading whitespace and trailing comment.
func trimLeftSpace(s string, relaxed bool) (string, bool) {
	// if log.ParseEnabled() {
	// 	log.Parse.Printf("TrimLeftSpace: begin %s\n", s)
	// }

	whitespace := func(c rune) bool { return unicode.IsSpace(c) || c == 0x00 }

	whitespaceNoEol := func(r rune) bool {
		switch r {
		case '\t', '\v', '\f', ' ', 0x85, 0xA0, 0x00:
			return true
		}
		return false
	}

	var eol bool

	for {
		if relaxed {
			s = strings.TrimLeftFunc(s, whitespaceNoEol)
			if len(s) >= 1 && (s[0] == '\n' || s[0] == '\r') {
				eol = true
			}
		}
		s = strings.TrimLeftFunc(s, whitespace)
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("1 outstr: <%s>\n", s)
		// }
		if len(s) <= 1 || s[0] != '%' {
			break
		}
		// trim PDF comment (= '%' up to eol)
		s, _ = positionToNextEOL(s)
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("2 outstr: <%s>\n", s)
		// }
	}

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("TrimLeftSpace: end %s\n", s)
	// }

	return s, eol
}

// HexString validates and formats a hex string to be of even length.
func hexString(s string) (*string, bool) {
	if len(s) == 0 {
		s1 := ""
		return &s1, true
	}

	var sb strings.Builder
	i := 0

	for _, c := range strings.ToUpper(s) {
		if strings.ContainsRune(" \x09\x0A\x0C\x0D", c) {
			if i%2 > 0 {
				sb.WriteString("0")
				i = 0
			}
			continue
		}
		isHexChar := false
		for _, hexch := range "ABCDEF1234567890" {
			if c == hexch {
				isHexChar = true
				sb.WriteRune(c)
				i++
				break
			}
		}
		if !isHexChar {
			return nil, false
		}
	}

	// If the final digit of a hexadecimal string is missing -
	// that is, if there is an odd number of digits - the final digit shall be assumed to be 0.
	if i%2 > 0 {
		sb.WriteString("0")
	}

	ss := sb.String()
	return &ss, true
}

// balancedParenthesesPrefix returns the index of the end position of the balanced parentheses prefix of s
// or -1 if unbalanced. s has to start with '('
func balancedParenthesesPrefix(s string) int {
	var j int
	escaped := false

	for i := 0; i < len(s); i++ {

		c := s[i]

		if !escaped && c == '\\' {
			escaped = true
			continue
		}

		if escaped {
			escaped = false
			continue
		}

		if c == '(' {
			j++
		}

		if c == ')' {
			j--
		}

		if j == 0 {
			return i
		}

	}

	return -1
}

func forwardParseBuf(buf string, pos int) string {
	if pos < len(buf) {
		return buf[pos:]
	}
	return ""
}

func delimiter(b byte) bool {
	s := "<>[]()/"
	for i := 0; i < len(s); i++ {
		if b == s[i] {
			return true
		}
	}
	return false
}

// ParseObjectAttributes parses object number and generation of the next object for given string buffer.
func ParseObjectAttributes(line *string) (objectNumber *int, generationNumber *int, err error) {
	if line == nil || len(*line) == 0 {
		return nil, nil, errors.New("pdfcpu: ParseObjectAttributes: buf not available")
	}

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseObjectAttributes: buf=<%s>\n", *line)
	// }

	l := *line
	var remainder string

	i := strings.Index(l, "obj")
	if i < 0 {
		return nil, nil, errors.New("pdfcpu: ParseObjectAttributes: can't find \"obj\"")
	}

	remainder = l[i+len("obj"):]
	l = l[:i]

	// object number

	l, _ = trimLeftSpace(l, false)
	if len(l) == 0 {
		return nil, nil, errors.New("pdfcpu: ParseObjectAttributes: can't find object number")
	}

	i, _ = positionToNextWhitespaceOrChar(l, "%")
	if i <= 0 {
		return nil, nil, errors.New("pdfcpu: ParseObjectAttributes: can't find end of object number")
	}

	objNr, err := strconv.Atoi(l[:i])
	if err != nil {
		return nil, nil, err
	}

	// generation number

	l = l[i:]
	l, _ = trimLeftSpace(l, false)
	if len(l) == 0 {
		return nil, nil, errors.New("pdfcpu: ParseObjectAttributes: can't find generation number")
	}

	i, _ = positionToNextWhitespaceOrChar(l, "%")
	if i <= 0 {
		return nil, nil, errors.New("pdfcpu: ParseObjectAttributes: can't find end of generation number")
	}

	genNr, err := strconv.Atoi(l[:i])
	if err != nil {
		return nil, nil, err
	}

	objectNumber = &objNr
	generationNumber = &genNr

	*line = remainder

	return objectNumber, generationNumber, nil
}

func parseArray(c ContextContext, line *string) (*Array, error) {
	// if log.ParseEnabled() {
	// 	log.Parse.Println("ParseObject: value = Array")
	// }
	if line == nil || len(*line) == 0 {
		return nil, errNoArray
	}

	l := *line

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseArray: %s\n", l)
	// }

	if !strings.HasPrefix(l, "[") {
		return nil, errArrayCorrupt
	}

	if len(l) == 1 {
		return nil, errArrayNotTerminated
	}

	// position behind '['
	l = forwardParseBuf(l, 1)

	// position to first non whitespace char after '['
	l, _ = trimLeftSpace(l, false)

	if len(l) == 0 {
		// only whitespace after '['
		return nil, errArrayNotTerminated
	}

	a := Array{}

	for !strings.HasPrefix(l, "]") {

		obj, err := ParseObjectContext(c, &l)
		if err != nil {
			return nil, err
		}
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("ParseArray: new array obj=%v\n", obj)
		// }
		a = append(a, obj)

		// we are positioned on the char behind the last parsed array entry.
		if len(l) == 0 {
			return nil, errArrayNotTerminated
		}

		// position to next non whitespace char.
		l, _ = trimLeftSpace(l, false)
		if len(l) == 0 {
			return nil, errArrayNotTerminated
		}

		// position behind ']'
		l = forwardParseBuf(l, 1)

		*line = l

	}
	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseArray: returning array (len=%d): %v\n", len(a), a)
	// }

	return &a, nil
}

func parseStringLiteral(line *string) (Object, error) {
	// Balanced pairs of parenthesis are allowed.
	// Empty literals are allowed.
	// \ needs special treatment.
	// Allowed escape sequences:
	// \n	x0A
	// \r	x0D
	// \t	x09
	// \b	x08
	// \f	xFF
	// \(	x28
	// \)	x29
	// \\	x5C
	// \ddd octal code sequence, d=0..7

	// Ignore '\' for undefined escape sequences.

	// Unescaped 0x0A,0x0D or combination gets parsed as 0x0A.

	// Join split lines by '\' eol.

	if line == nil || len(*line) == 0 {
		return nil, errBufNotAvailable
	}

	l := *line

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("parseStringLiteral: begin <%s>\n", l)
	// }

	if len(l) < 2 || !strings.HasPrefix(l, "(") {
		return nil, errStringLiteralCorrupt
	}

	// Calculate prefix with balanced parentheses,
	// return index of enclosing ')'.
	i := balancedParenthesesPrefix(l)
	if i < 0 {
		// No balanced parentheses.
		return nil, errStringLiteralCorrupt
	}

	// remove enclosing '(', ')'
	balParStr := l[1:i]

	// Parse string literal, see 7.3.4.2
	// str := stringLiteral(balParStr)

	// position behind ')'
	*line = forwardParseBuf(l[i:], 1)

	stringLiteral := StringLiteral(balParStr)
	// if log.ParseEnabled() {
	// 	log.Parse.Printf("parseStringLiteral: end <%s>\n", stringLiteral)
	// }

	return stringLiteral, nil
}

func parseHexLiteral(line *string) (Object, error) {
	if line == nil || len(*line) == 0 {
		return nil, errBufNotAvailable
	}

	l := *line

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("parseHexLiteral: %s\n", l)
	//	}

	if len(l) < 2 || !strings.HasPrefix(l, "<") {
		return nil, errHexLiteralCorrupt
	}

	// position behind '<'
	l = forwardParseBuf(l, 1)

	eov := strings.Index(l, ">") // end of hex literal.
	if eov < 0 {
		return nil, errHexLiteralNotTerminated
	}

	hexStr, ok := hexString(strings.TrimSpace(l[:eov]))
	if !ok {
		return nil, errHexLiteralCorrupt
	}

	// position behind '>'
	*line = forwardParseBuf(l[eov:], 1)

	return HexLiteral(*hexStr), nil
}

func decodeNameHexSequence(s string) (string, error) {
	decoded, err := DecodeName(s)
	if err != nil {
		return "", errNameObjectCorrupt
	}

	return decoded, nil
}

func parseName(line *string) (*NameType, error) {
	// see 7.3.5
	// if log.ParseEnabled() {
	// 	log.Parse.Println("ParseObject: value = Name Object")
	// }
	if line == nil || len(*line) == 0 {
		return nil, errBufNotAvailable
	}

	l := *line

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("parseNameObject: %s\n", l)
	// }
	if len(l) < 2 || !strings.HasPrefix(l, "/") {
		return nil, errNameObjectCorrupt
	}

	// position behind '/'
	l = forwardParseBuf(l, 1)

	// cut off on whitespace or delimiter
	eok, _ := positionToNextWhitespaceOrChar(l, "/<>()[]%")
	if eok < 0 {
		// Name terminated by eol.
		*line = ""
	} else {
		*line = l[eok:]
		l = l[:eok]
	}

	// Decode optional #xx sequences
	l, err := decodeNameHexSequence(l)
	if err != nil {
		return nil, err
	}

	nameObj := NameType(l)
	return &nameObj, nil
}

func insertKey(d Dict, key string, val Object, relaxed bool) error {
	if _, found := d[key]; !found {
		d[key] = val
	} else {
		// was: for now we ignore duplicate keys - config flag ?

		// if !relaxed {
		// 	return errDictionaryDuplicateKey
		// }

		d[key] = val
	}

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseDict: dict[%s]=%v\n", key, val)
	// }

	return nil
}

func processDictKeys(c ContextContext, line *string, relaxed bool) (Dict, error) {
	l := *line
	var eol bool
	d := NewDict()

	for !strings.HasPrefix(l, ">>") {

		if err := c.Err(); err != nil {
			return nil, err
		}

		keyName, err := parseName(&l)
		if err != nil {
			return nil, err
		}

		// if log.ParseEnabled() {
		// 	log.Parse.Printf("ParseDict: key = %s\n", keyName)
		// }

		// Position to first non whitespace after key.
		l, eol = trimLeftSpace(l, relaxed)

		if len(l) == 0 {
			// if log.ParseEnabled() {
			// 	log.Parse.Println("ParseDict: only whitespace after key")
			// }
			// Only whitespace after key.
			return nil, errDictionaryNotTerminated
		}

		var val Object

		if eol {
			// #252: For dicts with kv pairs terminated by eol we accept a missing value as an empty string.
			val = StringLiteral("")
		} else {
			if val, err = ParseObject(&l); err != nil {
				return nil, err
			}
		}

		// Specifying the null object as the value of a dictionary entry (7.3.7, "Dictionary Objects")
		// shall be equivalent to omitting the entry entirely.
		if val != nil {
			if err := insertKey(d, string(*keyName), val, relaxed); err != nil {
				return nil, err
			}
		}

		// We are positioned on the char behind the last parsed dict value.
		if len(l) == 0 {
			return nil, errDictionaryNotTerminated
		}

		// Position to next non whitespace char.
		l, _ = trimLeftSpace(l, false)
		if len(l) == 0 {
			return nil, errDictionaryNotTerminated
		}

	}
	*line = l
	return d, nil
}

func parseDict(c ContextContext, line *string, relaxed bool) (Dict, error) {
	if line == nil || len(*line) == 0 {
		return nil, errNoDictionary
	}

	l := *line

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseDict: %s\n", l)
	// }

	if len(l) < 4 || !strings.HasPrefix(l, "<<") {
		return nil, errDictionaryCorrupt
	}

	// position behind '<<'
	l = forwardParseBuf(l, 2)

	// position to first non whitespace char after '<<'
	l, _ = trimLeftSpace(l, false)

	if len(l) == 0 {
		// only whitespace after '['
		return nil, errDictionaryNotTerminated
	}

	d, err := processDictKeys(c, &l, relaxed)
	if err != nil {
		return nil, err
	}

	// position behind '>>'
	l = forwardParseBuf(l, 2)

	*line = l

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseDict: returning dict at: %v\n", d)
	// }

	return d, nil
}

func noBuf(l *string) bool {
	return l == nil || len(*l) == 0
}

func startParseNumericOrIndRef(l string) (string, string, int) {
	i1, _ := positionToNextWhitespaceOrChar(l, "/<([]>%")
	var l1 string
	if i1 > 0 {
		l1 = l[i1:]
	} else {
		l1 = l[len(l):]
	}

	str := l
	if i1 > 0 {
		str = l[:i1]
	}

	/*
		Integers are sometimes prefixed with any form of 0.
		Following is a list of valid prefixes that can be safely ignored:
			0
			0.000000000
	*/
	if len(str) > 1 && str[0] == '0' {
		switch str[1] {
		case '+', '-':
			str = str[1:]
		case '.':
			var i int
			for i = 2; len(str) > i && str[i] == '0'; i++ {
			}
			if len(str) > i && (str[i] == '+' || str[i] == '-') {
				str = str[i:]
			}
		}
	}
	return str, l1, i1
}

func isRangeError(err error) bool {
	if err, ok := err.(*strconv.NumError); ok {
		if err.Err == strconv.ErrRange {
			return true
		}
	}
	return false
}

func parseIndRef(s, l, l1 string, line *string, i, i2 int) (Object, error) {
	g, err := strconv.Atoi(s)
	if err != nil {
		// 2nd int(generation number) not available.
		// Can't be an indirect reference.
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("parseIndRef: 3 objects, 2nd no int, value is no indirect ref but numeric int: %d\n", i)
		// }
		*line = l1
		return Integer(i), nil
	}

	l = l[i2:]
	l, _ = trimLeftSpace(l, false)

	if len(l) == 0 {
		// only whitespace
		*line = l1
		return Integer(i), nil
	}

	if l[0] == 'R' {
		*line = forwardParseBuf(l, 1)
		// We have all 3 components to create an indirect reference.
		return *NewIndirectRef(i, g), nil
	}

	// 'R' not available.
	// Can't be an indirect reference.
	// if log.ParseEnabled() {
	// 	log.Parse.Printf("parseNumericOrIndRef: value is no indirect ref(no 'R') but numeric int: %d\n", i)
	// }
	*line = l1

	return Integer(i), nil
}

func parseFloat(s string) (Object, error) {
	f, err := strconv.ParseFloat(s, 64)
	if err != nil {
		s = strings.Replace(s, ".-", ".", 1)
		f, err = strconv.ParseFloat(s, 64)
		if err != nil {
			return nil, err
		}
	}

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("parseFloat: value is: %f\n", f)
	// }

	return Float(f), nil
}

func parseNumericOrIndRef(line *string) (Object, error) {
	if noBuf(line) {
		return nil, errBufNotAvailable
	}

	l := *line

	// if this object is an integer we need to check for an indirect reference eg. 1 0 R
	// otherwise it has to be a float
	// we have to check first for integer
	s, l1, i1 := startParseNumericOrIndRef(l)

	// Try int
	i, err := strconv.Atoi(s)
	if err != nil {
		if isRangeError(err) {
			// #407
			i = 0
			*line = l1
			return Integer(i), nil
		}
		*line = l1
		return parseFloat(s)
	}

	// We have an Int!

	// if not followed by whitespace return sole integer value.
	if i1 <= 0 || delimiter(l[i1]) {
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("parseNumericOrIndRef: value is numeric int: %d\n", i)
		// }
		*line = l1
		return Integer(i), nil
	}

	// Must be indirect reference. (123 0 R)
	// Missing is the 2nd int and "R".

	l = l[i1:]
	l, _ = trimLeftSpace(l, false)
	if len(l) == 0 {
		// only whitespace
		*line = l1
		return Integer(i), nil
	}

	i2, _ := positionToNextWhitespaceOrChar(l, "/<([]>")

	// if only 2 token, can't be indirect reference.
	// if not followed by whitespace return sole integer value.
	if i2 <= 0 || delimiter(l[i2]) {
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("parseNumericOrIndRef: 2 objects => value is numeric int: %d\n", i)
		// }
		*line = l1
		return Integer(i), nil
	}

	s = l
	if i2 > 0 {
		s = l[:i2]
	}

	return parseIndRef(s, l, l1, line, i, i2)
}

func parseHexLiteralOrDict(c ContextContext, l *string) (val Object, err error) {
	if len(*l) < 2 {
		return nil, errBufNotAvailable
	}

	// if next char = '<' parseDict.
	if (*l)[1] == '<' {
		// if log.ParseEnabled() {
		// 	log.Parse.Println("parseHexLiteralOrDict: value = Dictionary")
		// }
		var (
			d   Dict
			err error
		)
		if d, err = parseDict(c, l, false); err != nil {
			if d, err = parseDict(c, l, true); err != nil {
				return nil, err
			}
		}
		val = d
	} else {
		// hex literals
		// if log.ParseEnabled() {
		// 	log.Parse.Println("parseHexLiteralOrDict: value = Hex Literal")
		// }
		if val, err = parseHexLiteral(l); err != nil {
			return nil, err
		}
	}

	return val, nil
}

func parseBooleanOrNull(l string) (val Object, s string, ok bool) {
	// null, absent object
	if strings.HasPrefix(l, "null") {
		// if log.ParseEnabled() {
		// 	log.Parse.Println("parseBoolean: value = null")
		// }
		return nil, "null", true
	}

	// boolean true
	if strings.HasPrefix(l, "true") {
		// if log.ParseEnabled() {
		// 	log.Parse.Println("parseBoolean: value = true")
		// }
		return Boolean(true), "true", true
	}

	// boolean false
	if strings.HasPrefix(l, "false") {
		// if log.ParseEnabled() {
		// 	log.Parse.Println("parseBoolean: value = false")
		// }
		return Boolean(false), "false", true
	}

	return nil, "", false
}

// ParseObject parses next Object from string buffer and returns the updated (left clipped) buffer.
func ParseObject(line *string) (Object, error) {
	return ParseObjectContext(Background(), line)
}

// ParseObjectContext parses next Object from string buffer and returns the updated (left clipped) buffer.
// If the passed context is cancelled, parsing will be interrupted.
func ParseObjectContext(c ContextContext, line *string) (Object, error) {
	if noBuf(line) {
		return nil, errBufNotAvailable
	}

	l := *line

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseObject: buf= <%s>\n", l)
	// }

	// position to first non whitespace char
	l, _ = trimLeftSpace(l, false)
	if len(l) == 0 {
		// only whitespace
		return nil, errBufNotAvailable
	}

	var value Object
	var err error

	switch l[0] {

	case '[': // array
		a, err := parseArray(c, &l)
		if err != nil {
			return nil, err
		}
		value = *a

	case '/': // name
		nameObj, err := parseName(&l)
		if err != nil {
			return nil, err
		}
		value = *nameObj

	case '<': // hex literal or dict
		value, err = parseHexLiteralOrDict(c, &l)
		if err != nil {
			return nil, err
		}

	case '(': // string literal
		if value, err = parseStringLiteral(&l); err != nil {
			return nil, err
		}

	default:
		var valStr string
		var ok bool
		value, valStr, ok = parseBooleanOrNull(l)
		if ok {
			l = forwardParseBuf(l, len(valStr))
			break
		}
		// Must be numeric or indirect reference:
		// int 0 r
		// int
		// float
		if value, err = parseNumericOrIndRef(&l); err != nil {
			return nil, err
		}

	}

	// if log.ParseEnabled() {
	// 	log.Parse.Printf("ParseObject returning %v\n", value)
	// }

	*line = l

	return value, nil
}

func createXRefStreamDict(sd *StreamDict, objs []int) (*XRefStreamDict, error) {
	// Read parameter W in order to decode the xref table.
	// array of integers representing the size of the fields in a single cross-reference entry.

	var wIntArr [3]int

	a := sd.W()
	if a == nil {
		return nil, errXrefStreamMissingW
	}

	// validate array with 3 positive integers
	if len(a) != 3 {
		return nil, errXrefStreamCorruptW
	}

	f := func(ok bool, i int) bool {
		return !ok || i < 0
	}

	i1, ok := a[0].(Integer)
	if f(ok, i1.Value()) {
		return nil, errXrefStreamCorruptW
	}
	wIntArr[0] = int(i1)

	i2, ok := a[1].(Integer)
	if f(ok, i2.Value()) {
		return nil, errXrefStreamCorruptW
	}
	wIntArr[1] = int(i2)

	i3, ok := a[2].(Integer)
	if f(ok, i3.Value()) {
		return nil, errXrefStreamCorruptW
	}
	wIntArr[2] = int(i3)

	return &XRefStreamDict{
		StreamDict:     *sd,
		Size:           *sd.Size(),
		Objects:        objs,
		W:              wIntArr,
		PreviousOffset: sd.Prev(),
	}, nil
}

// ParseXRefStreamDict creates a XRefStreamDict out of a StreamDict.
func ParseXRefStreamDict(sd *StreamDict) (*XRefStreamDict, error) {
	// if log.ParseEnabled() {
	// 	log.Parse.Println("ParseXRefStreamDict: begin")
	// }
	if sd.Size() == nil {
		return nil, errors.New("pdfcpu: ParseXRefStreamDict: \"Size\" not available")
	}

	objs := []int{}

	//	Read optional parameter Index
	indArr := sd.Index()
	if indArr != nil {
		// if log.ParseEnabled() {
		// 	log.Parse.Println("ParseXRefStreamDict: using index dict")
		// }

		if len(indArr)%2 != 0 {
			return nil, errXrefStreamCorruptIndex
		}

		for i := 0; i < len(indArr)/2; i++ {

			startObj, ok := indArr[i*2].(Integer)
			if !ok {
				return nil, errXrefStreamCorruptIndex
			}

			count, ok := indArr[i*2+1].(Integer)
			if !ok {
				return nil, errXrefStreamCorruptIndex
			}

			for j := 0; j < count.Value(); j++ {
				objs = append(objs, startObj.Value()+j)
			}
		}

	} else {
		// if log.ParseEnabled() {
		// 	log.Parse.Println("ParseXRefStreamDict: no index dict")
		// }
		for i := 0; i < *sd.Size(); i++ {
			objs = append(objs, i)
		}
	}

	xsd, err := createXRefStreamDict(sd, objs)
	if err != nil {
		return nil, err
	}

	// if log.ParseEnabled() {
	// 	log.Parse.Println("ParseXRefStreamDict: end")
	// }

	return xsd, nil
}

func isMarkerTerminated(r rune) bool {
	return r == 0x00 || unicode.IsSpace(r)
}

func detectMarker(line, marker string) int {
	i := strings.Index(line, marker)
	if i < 0 {
		return i
	}
	if i+len(marker) >= len(line) {
		return -1
	}
	off := i + len(marker)
	ind := i
	for !isMarkerTerminated(rune(line[off])) {
		line = line[off:]
		if marker == "endobj" {
			j := strings.Index(line, "xref")
			if j >= 0 {
				r := rune(line[j+4])
				if isMarkerTerminated(r) {
					return ind
				}
			}
		}
		i = strings.Index(line, marker)
		if i < 0 {
			return -1
		}
		if i+len(marker) >= len(line) {
			return -1
		}
		off = i + len(marker)
		ind += off
	}

	return ind
}

func detectMarkers(line string, endInd, streamInd *int) {
	// fmt.Printf("buflen=%d\n%s", len(line), hex.Dump([]byte(line)))
	if *endInd == 0 {
		*endInd = detectMarker(line, "endobj")
	}
	if *streamInd == 0 {
		*streamInd = detectMarker(line, "stream")
	}
}

func positionAfterStringLiteral(line string) (string, int, error) {
	i := balancedParenthesesPrefix(line)
	if i < 0 {
		return "", 0, errStringLiteralCorrupt
	}

	line = forwardParseBuf(line[i:], 1)

	return line, i + 1, nil
}

func posFloor(pos1, pos2 int) int {
	if pos1 < 0 {
		return pos2
	}
	if pos1 < pos2 {
		return pos1
	}
	if pos2 < 0 {
		return pos1
	}
	return pos2
}

func detectNonEscaped(line, s string) int {
	var ind int
	for {
		i := strings.Index(line, s)
		if i < 0 {
			// did not find s
			return -1
		}
		if i == 0 {
			// found s at pos 0
			return ind
		}
		if line[i-1] != 0x5c {
			// found s at pos i
			return ind + i
		}
		// found escaped s
		if i == len(line)-1 {
			// last is escaped s -> did not find s
			return -1
		}
		// moving on after escaped s
		line = line[i+1:]
		ind += i + 1
	}
}

func applyOffBoth(endInd, streamInd, off int) (int, int, error) {
	if endInd >= 0 {
		endInd += off
	}
	if streamInd >= 0 {
		streamInd += off
	}
	return endInd, streamInd, nil
}

func applyOffEndIndFirst(endInd, streamInd, off, floor int) (int, int, error) {
	endInd += off
	if streamInd > 0 {
		if streamInd > floor {
			// stream after any ( or % to skip
			streamInd = -1
		} else {
			streamInd += off
		}
	}
	return endInd, streamInd, nil
}

func applyOffStreamIndFirst(endInd, streamInd, off, floor int) (int, int, error) {
	streamInd += off
	if endInd > 0 {
		if endInd > floor {
			// endobj after any ( or % to skip
			endInd = -1
		} else {
			endInd += off
		}
	}
	return endInd, streamInd, nil
}

func isComment(commentPos, strLitPos int) bool {
	return commentPos > 0 && (strLitPos < 0 || commentPos < strLitPos)
}

func DetectKeywords(line string) (endInd int, streamInd int, err error) {
	return DetectKeywordsWithContext(Background(), line)
}

func skipComment(line string, commentPos int, off, endInd, streamInd *int) string {
	l, i := positionToNextEOL(line[commentPos:])
	if l == "" {
		return l
	}
	delta := commentPos + i
	*off += delta

	// Adjust found positions for changed line.
	if *endInd > delta {
		*endInd -= delta
	} else if *endInd != -1 {
		*endInd = 0
	}
	if *streamInd > delta {
		*streamInd -= delta
	} else if *streamInd != -1 {
		*streamInd = 0
	}
	return l
}

func skipStringLit(line string, strLitPos int, off, endInd, streamInd *int) (string, error) {
	l, i, err := positionAfterStringLiteral(line[strLitPos:])
	if err != nil {
		return "", err
	}
	delta := strLitPos + i
	*off += delta
	// Adjust found positions for changed line.
	if *endInd > delta {
		*endInd -= delta
	} else if *endInd != -1 {
		*endInd = 0
	}
	if *streamInd > delta {
		*streamInd -= delta
	} else if *streamInd != -1 {
		*streamInd = 0
	}
	return l, nil
}

func skipCommentOrStringLiteral(line string, commentPos, slPos int, off, endInd, streamInd *int) (string, error) {
	if isComment(commentPos, slPos) {
		// skip comment if % before any (
		line = skipComment(line, commentPos, off, endInd, streamInd)
		if line == "" {
			return "", nil
		}
		return line, nil
	}
	return skipStringLit(line, slPos, off, endInd, streamInd)
}

func DetectKeywordsWithContext(c ContextContext, line string) (endInd int, streamInd int, err error) {
	// return endInd or streamInd which ever first encountered.
	off := 0
	strLitPos, commentPos := 0, 0
	for {
		if err := c.Err(); err != nil {
			return -1, -1, err
		}

		detectMarkers(line, &endInd, &streamInd)

		if off == 0 && endInd < 0 && streamInd < 0 {
			return -1, -1, nil
		}

		// Don't re-search in partial line if known to be not present.
		if strLitPos != -1 {
			strLitPos = detectNonEscaped(line, "(")
		}
		if commentPos != -1 {
			commentPos = detectNonEscaped(line, "%")
		}

		if strLitPos < 0 && commentPos < 0 {
			// neither ( nor % to skip
			return applyOffBoth(endInd, streamInd, off)
		}

		floor := posFloor(strLitPos, commentPos)

		if endInd > 0 {
			if endInd < floor {
				// endobj before any ( or % to skip
				return applyOffEndIndFirst(endInd, streamInd, off, floor)
			}
		}

		if streamInd > 0 {
			if streamInd < floor {
				// stream before any ( or % to skip
				return applyOffStreamIndFirst(endInd, streamInd, off, floor)
			}
		}

		line, err = skipCommentOrStringLiteral(line, commentPos, strLitPos, &off, &endInd, &streamInd)
		if err != nil {
			return -1, -1, err
		}
	}
}

func skipDict(l *string) error {
	s := *l
	if !strings.HasPrefix(s, "<<") {
		return errDictionaryCorrupt
	}
	s = s[2:]
	j := 0
	for {
		i := strings.IndexAny(s, "<>")
		if i < 0 {
			return errDictionaryCorrupt
		}
		if s[i] == '<' {
			j++
			s = s[i+1:]
			continue
		}
		if s[i] == '>' {
			if j > 0 {
				j--
				s = s[i+1:]
				continue
			}
			// >> ?
			s = s[i:]
			if !strings.HasPrefix(s, ">>") {
				return errDictionaryCorrupt
			}
			*l = s[2:]
			break
		}
	}
	return nil
}

func skipStringLiteral(l *string) error {
	s := *l
	i := 0
	for {
		i = strings.IndexByte(s, byte(')'))
		if i <= 0 || i > 0 && s[i-1] != '\\' {
			break
		}
		k := 0
		for j := i - 1; j >= 0 && s[j] == '\\'; j-- {
			k++
		}
		if k%2 == 0 {
			break
		}
		// Skip \)
		s = s[i+1:]
	}
	if i < 0 {
		return errStringLiteralCorrupt
	}
	s = s[i+1:]
	*l = s
	return nil
}

func skipHexStringLiteral(l *string) error {
	s := *l
	i := strings.Index(s, ">")
	if i < 0 {
		return errHexLiteralCorrupt
	}
	s = s[i+1:]
	*l = s
	return nil
}

func skipTJ(l *string) error {
	// Each element shall be either a string or a number.
	s := *l
	for {
		s = strings.TrimLeftFunc(s, whitespaceOrEOL)
		if s[0] == ']' {
			s = s[1:]
			break
		}
		if s[0] == '(' {
			if err := skipStringLiteral(&s); err != nil {
				return err
			}
		}
		if s[0] == '<' {
			if err := skipHexStringLiteral(&s); err != nil {
				return err
			}
		}
		i, _ := positionToNextWhitespaceOrChar(s, "<(]")
		if i < 0 {
			return errTJExpressionCorrupt
		}
		s = s[i:]
	}
	*l = s
	return nil
}

// MemberOf returns true if list contains s.
func MemberOf(s string, list []string) bool {
	for _, v := range list {
		if s == v {
			return true
		}
	}
	return false
}

// IntMemberOf returns true if list contains i.
func IntMemberOf(i int, list []int) bool {
	for _, v := range list {
		if i == v {
			return true
		}
	}
	return false
}

// IntMemberOf returns true if list contains i.
func IndRefMemberOf(i IndirectRef, arr Array) bool {
	for _, v := range arr {
		if i == v {
			return true
		}
	}
	return false
}

func EqualSlices(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i, v := range a {
		if v != b[i] {
			return false
		}
	}
	return true
}

func skipBI(l *string, prn PageResourceNames) error {
	s := *l
	// fmt.Printf("skipBI <%s>\n", s)
	for {
		s = strings.TrimLeftFunc(s, whitespaceOrEOL)
		if strings.HasPrefix(s, "ID") && whitespaceOrEOL(rune(s[2])) {
			s = s[2:]
			i := strings.Index(s, "EI")
			if i < 0 {
				return errBIExpressionCorrupt
			}
			if i == len(s)-2 {
				break
			}
			i += 2
			if whitespaceOrEOL(rune(s[i])) {
				s = s[i+1:]
				break
			} else {
				return errBIExpressionCorrupt
			}
		}
		if len(s) == 0 {
			return errBIExpressionCorrupt
		}
		if s[0] == '/' {
			s = s[1:]
			i, _ := positionToNextWhitespaceOrChar(s, "/")
			if i < 0 {
				return errBIExpressionCorrupt
			}
			token := s[:i]
			if token == "CS" || token == "ColorSpace" {
				s = s[i:]
				s, _ = trimLeftSpace(s, false)
				s = s[1:]
				i, _ = positionToNextWhitespaceOrChar(s, "/")
				if i < 0 {
					return errBIExpressionCorrupt
				}
				name := s[:i]
				if !MemberOf(name, []string{"DeviceGray", "DeviceRGB", "DeviceCMYK", "Indexed", "G", "RGB", "CMYK", "I"}) {
					prn["ColorSpace"][name] = true
				}
			}
			s = s[i:]
			continue
		}
		i, _ := positionToNextWhitespaceOrChar(s, "/")
		if i < 0 {
			return errBIExpressionCorrupt
		}
		s = s[i:]
	}
	*l = s
	return nil
}

func positionToNextContentToken(line *string, prn PageResourceNames) (bool, error) {
	l := *line
	for {
		l = strings.TrimLeftFunc(l, whitespaceOrEOL)
		if len(l) == 0 {
			// whitespace or eol only
			return true, nil
		}
		if l[0] == '%' {
			// Skip comment.
			l, _ = positionToNextEOL(l)
			continue
		}

		if l[0] == '[' {
			// Skip TJ expression:
			// [()...()] TJ
			// [<>...<>] TJ
			if err := skipTJ(&l); err != nil {
				return true, err
			}
			continue
		}
		if l[0] == '(' {
			// Skip text strings as in TJ, Tj, ', " expressions
			if err := skipStringLiteral(&l); err != nil {
				return true, err
			}
			continue
		}
		if l[0] == '<' {
			// Skip hex strings as in TJ, Tj, ', " expressions
			if err := skipHexStringLiteral(&l); err != nil {
				return true, err
			}
			continue
		}
		if strings.HasPrefix(l, "BI") && (l[2] == '/' || whitespaceOrEOL(rune(l[2]))) {
			// Handle inline image
			l = l[2:]
			if err := skipBI(&l, prn); err != nil {
				return true, err
			}
			continue
		}
		*line = l
		return false, nil
	}
}

func nextContentToken(pre string, line *string, prn PageResourceNames) (string, error) {
	// A token is either a name or some chunk terminated by white space or one of /, (, [
	if noBuf(line) {
		return "", nil
	}
	l := pre + *line
	t := ""

	// log.Parse.Printf("nextContentToken: start buf= <%s>\n", *line)

	// Skip Tj, TJ and inline images.
	done, err := positionToNextContentToken(&l, prn)
	if err != nil {
		return t, err
	}
	if done {
		return "", nil
	}

	if l[0] == '/' {
		// Cut off at / [ ( < or white space.
		l1 := l[1:]
		i, _ := positionToNextWhitespaceOrChar(l1, "/[(<")
		if i <= 0 {
			*line = ""
			return t, errPageContentCorrupt
		}
		t = l1[:i]
		l1 = l1[i:]
		l1 = strings.TrimLeftFunc(l1, whitespaceOrEOL)
		if !strings.HasPrefix(l1, "<<") {
			t = "/" + t
			*line = l1
			return t, nil
		}
		if err := skipDict(&l1); err != nil {
			return t, err
		}
		*line = l1
		return t, nil
	}

	i, _ := positionToNextWhitespaceOrChar(l, "/[(<")
	if i <= 0 {
		*line = ""
		return l, nil
	}
	t = l[:i]
	l = l[i:]
	if strings.HasPrefix(l, "<<") {
		if err := skipDict(&l); err != nil {
			return t, err
		}
	}
	*line = l
	return t, nil
}

func colorSpace(s, name string, prn PageResourceNames) bool {
	if strings.HasPrefix(s, "cs") || strings.HasPrefix(s, "CS") {
		if !MemberOf(name, []string{"DeviceGray", "DeviceRGB", "DeviceCMYK", "Pattern"}) {
			prn["ColorSpace"][name] = true
			// if log.ParseEnabled() {
			// 	log.Parse.Printf("ColorSpace[%s]\n", name)
			// }
		}
		return true
	}
	return false
}

func resourceNameAtPos1(s, name string, prn PageResourceNames) (string, bool) {
	if colorSpace(s, name, prn) {
		return s[2:], true
	}

	if strings.HasPrefix(s, "gs") {
		prn["ExtGState"][name] = true
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("ExtGState[%s]\n", name)
		// }
		return s[2:], true
	}

	if strings.HasPrefix(s, "Do") {
		prn["XObject"][name] = true
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("XObject[%s]\n", name)
		// }
		return s[2:], true
	}

	if strings.HasPrefix(s, "sh") {
		prn["Shading"][name] = true
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("Shading[%s]\n", name)
		// }
		return s[2:], true
	}

	if strings.HasPrefix(s, "scn") || strings.HasPrefix(s, "SCN") {
		prn["Pattern"][name] = true
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("Pattern[%s]\n", name)
		// }
		return s[3:], true
	}

	if strings.HasPrefix(s, "ri") || strings.HasPrefix(s, "MP") {
		return s[2:], true
	}

	if strings.HasPrefix(s, "BMC") {
		return s[3:], true
	}

	return "", false
}

func resourceNameAtPos2(s, name string, prn PageResourceNames) (string, bool) {
	switch s {
	case "Tf":
		prn["Font"][name] = true
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("Font[%s]\n", name)
		// }
		return "", true
	case "BDC", "DP":
		prn["Properties"][name] = true
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("Properties[%s]\n", name)
		// }
		return "", true
	}
	return "", false
}

func parseContent(s string) (PageResourceNames, error) {
	var (
		pre  string
		name string
		n    bool
		ok   bool
	)
	prn := NewPageResourceNames()

	// fmt.Printf("parseContent:\n%s\n", hex.Dump([]byte(s)))

	for pos := 0; ; {
		t, err := nextContentToken(pre, &s, prn)
		pre = ""
		// if log.ParseEnabled() {
		// 	log.Parse.Printf("t = <%s>\n", t)
		// }
		if err != nil {
			return nil, err
		}
		if t == "" {
			return prn, nil
		}

		if t[0] == '/' {
			name = t[1:]
			if n {
				pos++
			} else {
				n = true
				pos = 0
			}
			// if log.ParseEnabled() {
			// 	log.Parse.Printf("name=%s\n", name)
			// }
			continue
		}

		if !n {
			// if log.ParseEnabled() {
			// 	log.Parse.Printf("skip:%s\n", t)
			// }
			continue
		}

		pos++
		if pos == 1 {
			if pre, ok = resourceNameAtPos1(t, name, prn); ok {
				n = false
			}
			continue
		}
		if pos == 2 {
			if pre, ok = resourceNameAtPos2(t, name, prn); ok {
				n = false
			}
			continue
		}
		return nil, errPageContentCorrupt
	}
}

func (xRefTable *XRefTable) consolidateResourcesWithContent(pageDict, resDict Dict, pageNr int, consolidateRes bool) error {
	if !consolidateRes {
		return nil
	}

	bb, err := xRefTable.PageContent(pageDict, pageNr)
	if err != nil {
		if err == ErrNoContent {
			return nil
		}
		return err
	}

	// Calculate resources required by the content stream of this page.
	prn, err := parseContent(string(bb))
	if err != nil {
		return err
	}

	// Compare required resources (prn) with available resources (pAttrs.resources).
	// Remove any resource that's not required.
	// Return an error for any required resource missing.
	// TODO Calculate and accumulate resources required by content streams of any present form or type 3 fonts.
	return consolidateResourceDict(resDict, prn, pageNr)
}

func (xRefTable *XRefTable) pageObjType(indRef IndirectRef) (string, error) {
	pageNodeDict, err := xRefTable.DereferenceDict(indRef)
	if err != nil {
		return "", err
	}

	if t := pageNodeDict.Type(); t != nil {
		return *t, nil
	}

	objType := ""

	if xRefTable.ValidationMode == ValidationRelaxed {
		if _, hasCount := pageNodeDict.Find("Count"); hasCount {
			if _, hasKids := pageNodeDict.Find("Kids"); hasKids {
				objType = "Pages"
			}
		}
	}

	return objType, nil
}

func errForUnexpectedPageObjectType(validationMode int, objType string, indRef IndirectRef) error {
	if validationMode == ValidationRelaxed {
		return nil
	}

	if objType == "Template" {
		return errors.Errorf("Template page tree nodes not supported: %s", indRef)
	}

	if objType == "" {
		return errors.Errorf("page tree node without type: %s", indRef)
	}

	return errors.Errorf("unsupported page tree node: %s", indRef)
}

func (xRefTable *XRefTable) processPageTreeForPageDict(root *IndirectRef, pAttrs *InheritedPageAttrs, p *int, page int, consolidateRes bool) (Dict, *IndirectRef, error) {
	// Walk this page tree all the way down to the leaf node representing page.

	// fmt.Printf("entering processPageTreeForPageDict: p=%d obj#%d\n", *p, root.ObjectNumber.Value())

	d, err := xRefTable.DereferenceDict(*root)
	if err != nil {
		return nil, nil, err
	}

	pageCount := d.IntEntry("Count")
	if pageCount != nil {
		if *p+*pageCount < page {
			// Skip sub pagetree.
			*p += *pageCount
			return nil, nil, nil
		}
	}

	// Return the current state of all page attributes that may be inherited.
	if err = xRefTable.checkInheritedPageAttrs(d, pAttrs, consolidateRes); err != nil {
		return nil, nil, err
	}

	kids := d.ArrayEntry("Kids")
	if kids == nil {
		return d, root, xRefTable.consolidateResourcesWithContent(d, pAttrs.Resources, page, consolidateRes)
	}

	for _, o := range kids {

		if o == nil {
			continue
		}

		// Process next page node dict.

		indRef, ok := o.(IndirectRef)
		if !ok {
			return nil, nil, errors.Errorf("pdfcpu: processPageTreeForPageDict: corrupt page node dict")
		}

		objType, err := xRefTable.pageObjType(indRef)
		if err != nil {
			return nil, nil, err
		}

		switch objType {

		case "Pages":
			// Recurse over sub pagetree.
			pageDict, pageDictIndRef, err := xRefTable.processPageTreeForPageDict(&indRef, pAttrs, p, page, consolidateRes)
			if err != nil {
				return nil, nil, err
			}
			if pageDict != nil {
				return pageDict, pageDictIndRef, nil
			}

		case "Page":
			*p++
			if *p == page {
				return xRefTable.processPageTreeForPageDict(&indRef, pAttrs, p, page, consolidateRes)
			}

		default:
			return nil, nil, errForUnexpectedPageObjectType(xRefTable.ValidationMode, objType, indRef)

		}

	}

	return nil, nil, nil
}

// PageDict returns a specific page dict along with the resources, mediaBox and CropBox in effect.
// consolidateRes ensures optimized resources in InheritedPageAttrs.
func (xRefTable *XRefTable) PageDict(pageNr int, consolidateRes bool) (Dict, *IndirectRef, *InheritedPageAttrs, error) {
	var (
		inhPAttrs InheritedPageAttrs
		pageCount int
	)

	if pageNr <= 0 || pageNr > xRefTable.PageCount {
		return nil, nil, nil, errors.New("pdfcpu: page not found")
	}

	// Get an indirect reference to the page tree root dict.
	pageRootDictIndRef, err := xRefTable.Pages()
	if err != nil {
		return nil, nil, nil, err
	}

	if consolidateRes {
		consolidateRes = xRefTable.Conf.OptimizeResourceDicts
	}

	// Calculate and return only resources that are really needed by
	// any content stream of this page and any possible forms or type 3 fonts referenced.
	pageDict, pageDictindRef, err := xRefTable.processPageTreeForPageDict(pageRootDictIndRef, &inhPAttrs, &pageCount, pageNr, consolidateRes)
	if err != nil {
		return nil, nil, nil, err
	}

	return pageDict, pageDictindRef, &inhPAttrs, nil
}

// PageDictIndRef returns the pageDict IndRef for a logical page number.
func (xRefTable *XRefTable) PageDictIndRef(page int) (*IndirectRef, error) {
	var (
		inhPAttrs InheritedPageAttrs
		pageCount int
	)

	// Get an indirect reference to the page tree root dict.
	pageRootDictIndRef, err := xRefTable.Pages()
	if err != nil {
		return nil, err
	}

	// Calculate and return only resources that are really needed by
	// any content stream of this page and any possible forms or type 3 fonts referenced.
	consolidateRes := false
	_, ir, err := xRefTable.processPageTreeForPageDict(pageRootDictIndRef, &inhPAttrs, &pageCount, page, consolidateRes)

	return ir, err
}

// Calculate logical page number for page dict object number.
func (xRefTable *XRefTable) processPageTreeForPageNumber(root *IndirectRef, pageCount *int, pageObjNr int) (int, error) {
	// fmt.Printf("entering processPageTreeForPageNumber: p=%d obj#%d\n", *p, root.ObjectNumber.Value())

	d, err := xRefTable.DereferenceDict(*root)
	if err != nil {
		return 0, err
	}

	// Iterate over page tree.
	for _, o := range d.ArrayEntry("Kids") {

		if o == nil {
			continue
		}

		// Dereference next page node dict.
		indRef, ok := o.(IndirectRef)
		if !ok {
			return 0, errors.Errorf("pdfcpu: processPageTreeForPageNumber: corrupt page node dict")
		}

		objNr := indRef.ObjectNumber.Value()

		pageNodeDict, err := xRefTable.DereferenceDict(indRef)
		if err != nil {
			return 0, err
		}

		switch *pageNodeDict.Type() {

		case "Pages":
			// Recurse over sub pagetree.
			pageNr, err := xRefTable.processPageTreeForPageNumber(&indRef, pageCount, pageObjNr)
			if err != nil {
				return 0, err
			}
			if pageNr > 0 {
				return pageNr, nil
			}

		case "Page":
			*pageCount++
			if objNr == pageObjNr {
				return *pageCount, nil
			}
		}

	}

	return 0, nil
}

// PageNumber returns the logical page number for a page dict object number.
func (xRefTable *XRefTable) PageNumber(pageObjNr int) (int, error) {
	// Get an indirect reference to the page tree root dict.
	pageRootDict, _ := xRefTable.Pages()
	pageCount := 0
	return xRefTable.processPageTreeForPageNumber(pageRootDict, &pageCount, pageObjNr)
}

// EnsurePageCount evaluates the page count for xRefTable if necessary.
func (xRefTable *XRefTable) EnsurePageCount() error {
	if xRefTable.PageCount > 0 {
		return nil
	}

	pageRoot, err := xRefTable.Pages()
	if err != nil {
		return err
	}

	d, err := xRefTable.DereferenceDict(*pageRoot)
	if err != nil {
		return err
	}

	pageCount := d.IntEntry("Count")
	if pageCount == nil {
		return errors.New("pdfcpu: pageDict: missing \"Count\"")
	}

	xRefTable.PageCount = *pageCount

	return nil
}

func (xRefTable *XRefTable) resolvePageBoundary(d Dict, boxName string) (*Rectangle, error) {
	obj, found := d.Find(boxName)
	if !found {
		return nil, nil
	}
	a, err := xRefTable.DereferenceArray(obj)
	if err != nil {
		return nil, err
	}
	return rect(xRefTable, a)
}

type Box struct {
	Rect      *Rectangle `json:"rect"` // Rectangle in user space.
	Inherited bool       `json:"-"`    // Media box and Crop box may be inherited.
	RefBox    string     `json:"-"`    // Use position of another box,
	// Margins to parent box in points.
	// Relative to parent box if 0 < x < 0.5
	MLeft, MRight float64 `json:"-"`
	MTop, MBot    float64 `json:"-"`
	// Relative position within parent box
	Dim    *Dim   `json:"-"` // dimensions
	Pos    Anchor `json:"-"` // position anchor within parent box, one of tl,tc,tr,l,c,r,bl,bc,br.
	Dx, Dy int    `json:"-"` // anchor offset
}

// PageBoundaries represent the defined PDF page boundaries.
type PageBoundaries struct {
	Media       *Box   `json:"mediaBox,omitempty"`
	Crop        *Box   `json:"cropBox,omitempty"`
	Trim        *Box   `json:"trimBox,omitempty"`
	Bleed       *Box   `json:"bleedBox,omitempty"`
	Art         *Box   `json:"artBox,omitempty"`
	Rot         int    `json:"rot"` // The effective page rotation.
	Orientation string `json:"orient"`
}

// SelectAll selects all page boundaries.
func (pb *PageBoundaries) SelectAll() {
	b := &Box{}
	pb.Media, pb.Crop, pb.Trim, pb.Bleed, pb.Art = b, b, b, b, b
}

func (pb PageBoundaries) String() string {
	ss := []string{}
	if pb.Media != nil {
		ss = append(ss, "mediaBox")
	}
	if pb.Crop != nil {
		ss = append(ss, "cropBox")
	}
	if pb.Trim != nil {
		ss = append(ss, "trimBox")
	}
	if pb.Bleed != nil {
		ss = append(ss, "bleedBox")
	}
	if pb.Art != nil {
		ss = append(ss, "artBox")
	}
	return strings.Join(ss, ", ")
}

// MediaBox returns the effective mediabox for pb.
func (pb PageBoundaries) MediaBox() *Rectangle {
	if pb.Media == nil {
		return nil
	}
	return pb.Media.Rect
}

// CropBox returns the effective cropbox for pb.
func (pb PageBoundaries) CropBox() *Rectangle {
	if pb.Crop == nil || pb.Crop.Rect == nil {
		return pb.MediaBox()
	}
	return pb.Crop.Rect
}

// TrimBox returns the effective trimbox for pb.
func (pb PageBoundaries) TrimBox() *Rectangle {
	if pb.Trim == nil || pb.Trim.Rect == nil {
		return pb.CropBox()
	}
	return pb.Trim.Rect
}

// BleedBox returns the effective bleedbox for pb.
func (pb PageBoundaries) BleedBox() *Rectangle {
	if pb.Bleed == nil || pb.Bleed.Rect == nil {
		return pb.CropBox()
	}
	return pb.Bleed.Rect
}

// ArtBox returns the effective artbox for pb.
func (pb PageBoundaries) ArtBox() *Rectangle {
	if pb.Art == nil || pb.Art.Rect == nil {
		return pb.CropBox()
	}
	return pb.Art.Rect
}

// ResolveBox resolves s and tries to assign an empty page boundary.
func (pb *PageBoundaries) ResolveBox(s string) error {
	for _, k := range []string{"media", "crop", "trim", "bleed", "art"} {
		b := &Box{}
		if strings.HasPrefix(k, s) {
			switch k {
			case "media":
				pb.Media = b
			case "crop":
				pb.Crop = b
			case "trim":
				pb.Trim = b
			case "bleed":
				pb.Bleed = b
			case "art":
				pb.Art = b
			}
			return nil
		}
	}
	return errors.Errorf("pdfcpu: invalid box prefix: %s", s)
}

// ParseBoxList parses a list of box
func ParseBoxList(s string) (*PageBoundaries, error) {
	// A comma separated, unsorted list of values:
	//
	// m(edia), c(rop), t(rim), b(leed), a(rt)

	s = strings.TrimSpace(s)
	if len(s) == 0 {
		return nil, nil
	}
	pb := &PageBoundaries{}
	for _, s := range strings.Split(s, ",") {
		if err := pb.ResolveBox(strings.TrimSpace(s)); err != nil {
			return nil, err
		}
	}
	return pb, nil
}

func resolveBoxType(s string) (string, error) {
	for _, k := range []string{"media", "crop", "trim", "bleed", "art"} {
		if strings.HasPrefix(k, s) {
			return k, nil
		}
	}
	return "", errors.Errorf("pdfcpu: invalid box type: %s", s)
}

func processBox(b **Box, boxID, paramValueStr string, unit DisplayUnit) error {
	var err error
	if *b != nil {
		return errors.Errorf("pdfcpu: duplicate box definition: %s", boxID)
	}
	// process box assignment
	boxVal, err := resolveBoxType(paramValueStr)
	if err == nil {
		if boxVal == boxID {
			return errors.Errorf("pdfcpu: invalid box self assignment: %s", boxID)
		}
		*b = &Box{RefBox: boxVal}
		return nil
	}
	// process box definition
	*b, err = ParseBox(paramValueStr, unit)
	return err
}

// ParsePageBoundaries parses a list of box definitions and assignments.
func ParsePageBoundaries(s string, unit DisplayUnit) (*PageBoundaries, error) {
	// A sequence of box definitions/assignments:
	//
	// 	  m(edia): {box}
	//     c(rop): {box}
	//      a(rt): {box} | b(leed) | c(rop)  | m(edia) | t(rim)
	//    b(leed): {box} | a(rt)   | c(rop)  | m(edia) | t(rim)
	//     t(rim): {box} | a(rt)   | b(leed) | c(rop)  | m(edia)

	s = strings.TrimSpace(s)
	if len(s) == 0 {
		return nil, errors.New("pdfcpu: missing page boundaries in the form of box definitions/assignments")
	}
	pb := &PageBoundaries{}
	for _, s := range strings.Split(s, ",") {

		s1 := strings.Split(s, ":")
		if len(s1) != 2 {
			return nil, errors.New("pdfcpu: invalid box assignment")
		}

		paramPrefix := strings.TrimSpace(s1[0])
		paramValueStr := strings.TrimSpace(s1[1])

		boxKey, err := resolveBoxType(paramPrefix)
		if err != nil {
			return nil, errors.New("pdfcpu: invalid box type")
		}

		// process box definition
		switch boxKey {
		case "media":
			if pb.Media != nil {
				return nil, errors.New("pdfcpu: duplicate box definition: media")
			}
			// process media box definition
			pb.Media, err = ParseBox(paramValueStr, unit)

		case "crop":
			if pb.Crop != nil {
				return nil, errors.New("pdfcpu: duplicate box definition: crop")
			}
			// process crop box definition
			pb.Crop, err = ParseBox(paramValueStr, unit)

		case "trim":
			err = processBox(&pb.Trim, "trim", paramValueStr, unit)

		case "bleed":
			err = processBox(&pb.Bleed, "bleed", paramValueStr, unit)

		case "art":
			err = processBox(&pb.Art, "art", paramValueStr, unit)

		}

		if err != nil {
			return nil, err
		}
	}
	return pb, nil
}

func parseBoxByRectangle(s string, u DisplayUnit) (*Box, error) {
	ss := strings.Fields(s)
	if len(ss) != 4 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	f, err := strconv.ParseFloat(ss[0], 64)
	if err != nil {
		return nil, err
	}
	xmin := ToUserSpace(f, u)

	f, err = strconv.ParseFloat(ss[1], 64)
	if err != nil {
		return nil, err
	}
	ymin := ToUserSpace(f, u)

	f, err = strconv.ParseFloat(ss[2], 64)
	if err != nil {
		return nil, err
	}
	xmax := ToUserSpace(f, u)

	f, err = strconv.ParseFloat(ss[3], 64)
	if err != nil {
		return nil, err
	}
	ymax := ToUserSpace(f, u)

	if xmax < xmin {
		xmin, xmax = xmax, xmin
	}

	if ymax < ymin {
		ymin, ymax = ymax, ymin
	}

	return &Box{Rect: NewRectangle(xmin, ymin, xmax, ymax)}, nil
}

func parseBoxPercentage(s string) (float64, error) {
	pct, err := strconv.ParseFloat(s, 64)
	if err != nil {
		return 0, err
	}
	if pct <= -50 || pct >= 50 {
		return 0, errors.Errorf("pdfcpu: invalid margin percentage: %s must be < 50%%", s)
	}
	return pct / 100, nil
}

func parseBoxBySingleMarginVal(s, s1 string, abs bool, u DisplayUnit) (*Box, error) {
	if s1[len(s1)-1] == '%' {
		// margin percentage
		// 10.5%
		// % has higher precedence than abs/rel.
		s1 = s1[:len(s1)-1]
		if len(s1) == 0 {
			return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
		}
		m, err := parseBoxPercentage(s1)
		if err != nil {
			return nil, err
		}
		return &Box{MLeft: m, MRight: m, MTop: m, MBot: m}, nil
	}
	m, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}
	if !abs {
		// 0.25 rel (=25%)
		if m <= 0 || m >= .5 {
			return nil, errors.Errorf("pdfcpu: invalid relative box margin: %f must be positive < 0.5", m)
		}
		return &Box{MLeft: m, MRight: m, MTop: m, MBot: m}, nil
	}
	// 10
	// 10 abs
	// .5
	// .5 abs
	m = ToUserSpace(m, u)
	return &Box{MLeft: m, MRight: m, MTop: m, MBot: m}, nil
}

func parseBoxBy2Percentages(s, s1, s2 string) (*Box, error) {
	// 10% 40%
	// Parse vert margin.
	s1 = s1[:len(s1)-1]
	if len(s1) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	vm, err := parseBoxPercentage(s1)
	if err != nil {
		return nil, err
	}

	if s2[len(s2)-1] != '%' {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	// Parse hor margin.
	s2 = s2[:len(s2)-1]
	if len(s2) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	hm, err := parseBoxPercentage(s2)
	if err != nil {
		return nil, err
	}
	return &Box{MLeft: hm, MRight: hm, MTop: vm, MBot: vm}, nil
}

func parseBoxBy2MarginVals(s, s1, s2 string, abs bool, u DisplayUnit) (*Box, error) {
	if s1[len(s1)-1] == '%' {
		return parseBoxBy2Percentages(s, s1, s2)
	}

	// 10 5
	// 10 5 abs
	// .1 .5
	// .1 .5 abs
	// .1 .4 rel
	vm, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}
	if !abs {
		// eg 0.25 rel (=25%)
		if vm <= 0 || vm >= .5 {
			return nil, errors.Errorf("pdfcpu: invalid relative vertical box margin: %f must be positive < 0.5", vm)
		}
	}
	hm, err := strconv.ParseFloat(s2, 64)
	if err != nil {
		return nil, err
	}
	if !abs {
		// eg 0.25 rel (=25%)
		if hm <= 0 || hm >= .5 {
			return nil, errors.Errorf("pdfcpu: invalid relative horizontal box margin: %f must be positive < 0.5", hm)
		}
	}
	if abs {
		vm = ToUserSpace(vm, u)
		hm = ToUserSpace(hm, u)
	}
	return &Box{MLeft: hm, MRight: hm, MTop: vm, MBot: vm}, nil
}

func parseBoxBy3Percentages(s, s1, s2, s3 string) (*Box, error) {
	// 10% 15.5% 10%
	// Parse top margin.
	s1 = s1[:len(s1)-1]
	if len(s1) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}
	tm := pct / 100

	if s2[len(s2)-1] != '%' {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	// Parse hor margin.
	s2 = s2[:len(s2)-1]
	if len(s2) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	hm, err := parseBoxPercentage(s2)
	if err != nil {
		return nil, err
	}

	if s3[len(s3)-1] != '%' {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	// Parse bottom margin.
	s3 = s3[:len(s3)-1]
	if len(s3) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err = strconv.ParseFloat(s3, 64)
	if err != nil {
		return nil, err
	}
	bm := pct / 100
	if tm+bm >= 1 {
		return nil, errors.Errorf("pdfcpu: vertical margin overflow: %s", s)
	}

	return &Box{MLeft: hm, MRight: hm, MTop: tm, MBot: bm}, nil
}

func parseBoxBy3MarginVals(s, s1, s2, s3 string, abs bool, u DisplayUnit) (*Box, error) {
	if s1[len(s1)-1] == '%' {
		return parseBoxBy3Percentages(s, s1, s2, s3)
	}

	// 10 5 15 				... absolute, top:10 left,right:5 bottom:15
	// 10 5 15 abs			... absolute, top:10 left,right:5 bottom:15
	// .1 .155 .1			... absolute, top:.1 left,right:.155 bottom:.1
	// .1 .155 .1 abs		... absolute, top:.1 left,right:.155 bottom:.1
	// .1 .155 .1 rel 		... relative, top:.1 left,right:.155 bottom:.1
	tm, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}

	hm, err := strconv.ParseFloat(s2, 64)
	if err != nil {
		return nil, err
	}
	if !abs {
		// eg 0.25 rel (=25%)
		if hm <= 0 || hm >= .5 {
			return nil, errors.Errorf("pdfcpu: invalid relative horizontal box margin: %f must be positive < 0.5", hm)
		}
	}

	bm, err := strconv.ParseFloat(s3, 64)
	if err != nil {
		return nil, err
	}
	if !abs && (tm+bm >= 1) {
		return nil, errors.Errorf("pdfcpu: vertical margin overflow: %s", s)
	}

	if abs {
		tm = ToUserSpace(tm, u)
		hm = ToUserSpace(hm, u)
		bm = ToUserSpace(bm, u)
	}
	return &Box{MLeft: hm, MRight: hm, MTop: tm, MBot: bm}, nil
}

func parseBoxBy4Percentages(s, s1, s2, s3, s4 string) (*Box, error) {
	// 10% 15% 15% 10%
	// Parse top margin.
	s1 = s1[:len(s1)-1]
	if len(s1) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}
	tm := pct / 100

	// Parse right margin.
	if s2[len(s2)-1] != '%' {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	s2 = s2[:len(s2)-1]
	if len(s2) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err = strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}
	rm := pct / 100

	// Parse bottom margin.
	if s3[len(s3)-1] != '%' {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	s3 = s3[:len(s3)-1]
	if len(s3) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err = strconv.ParseFloat(s3, 64)
	if err != nil {
		return nil, err
	}
	bm := pct / 100

	// Parse left margin.
	if s4[len(s4)-1] != '%' {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	s4 = s4[:len(s4)-1]
	if len(s4) == 0 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err = strconv.ParseFloat(s3, 64)
	if err != nil {
		return nil, err
	}
	lm := pct / 100

	if tm+bm >= 1 {
		return nil, errors.Errorf("pdfcpu: vertical margin overflow: %s", s)
	}
	if rm+lm >= 1 {
		return nil, errors.Errorf("pdfcpu: horizontal margin overflow: %s", s)
	}

	return &Box{MLeft: lm, MRight: rm, MTop: tm, MBot: bm}, nil
}

func parseBoxBy4MarginVals(s, s1, s2, s3, s4 string, abs bool, u DisplayUnit) (*Box, error) {
	if s1[len(s1)-1] == '%' {
		return parseBoxBy4Percentages(s, s1, s2, s3, s4)
	}

	// 0.4 0.4 20 20		... absolute, top:.4 right:.4 bottom:20 left:20
	// 0.4 0.4 .1 .1		... absolute, top:.4 right:.4 bottom:.1 left:.1
	// 0.4 0.4 .1 .1 abs	... absolute, top:.4 right:.4 bottom:.1 left:.1
	// 0.4 0.4 .1 .1 rel  	... relative, top:.4 right:.4 bottom:.1 left:.1

	// Parse top margin.
	tm, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return nil, err
	}

	// Parse right margin.
	rm, err := strconv.ParseFloat(s2, 64)
	if err != nil {
		return nil, err
	}

	// Parse bottom margin.
	bm, err := strconv.ParseFloat(s3, 64)
	if err != nil {
		return nil, err
	}

	// Parse left margin.
	lm, err := strconv.ParseFloat(s4, 64)
	if err != nil {
		return nil, err
	}
	if !abs {
		if tm+bm >= 1 {
			return nil, errors.Errorf("pdfcpu: vertical margin overflow: %s", s)
		}
		if lm+rm >= 1 {
			return nil, errors.Errorf("pdfcpu: horizontal margin overflow: %s", s)
		}
	}

	if abs {
		tm = ToUserSpace(tm, u)
		rm = ToUserSpace(rm, u)
		bm = ToUserSpace(bm, u)
		lm = ToUserSpace(lm, u)
	}
	return &Box{MLeft: lm, MRight: rm, MTop: tm, MBot: bm}, nil
}

func parseBoxOffset(s string, b *Box, u DisplayUnit) error {
	d := strings.Split(s, " ")
	if len(d) != 2 {
		return errors.Errorf("pdfcpu: illegal position offset string: need 2 numeric values, %s\n", s)
	}

	f, err := strconv.ParseFloat(d[0], 64)
	if err != nil {
		return err
	}
	b.Dx = int(ToUserSpace(f, u))

	f, err = strconv.ParseFloat(d[1], 64)
	if err != nil {
		return err
	}
	b.Dy = int(ToUserSpace(f, u))

	return nil
}

func parseBoxDimByPercentage(s, s1, s2 string, b *Box) error {
	// 10% 40%
	// Parse width.
	s1 = s1[:len(s1)-1]
	if len(s1) == 0 {
		return errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err := strconv.ParseFloat(s1, 64)
	if err != nil {
		return err
	}
	if pct <= 0 || pct > 100 {
		return errors.Errorf("pdfcpu: invalid percentage: %s", s)
	}
	w := pct / 100

	if s2[len(s2)-1] != '%' {
		return errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	// Parse height.
	s2 = s2[:len(s2)-1]
	if len(s2) == 0 {
		return errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	pct, err = strconv.ParseFloat(s2, 64)
	if err != nil {
		return err
	}
	if pct <= 0 || pct > 100 {
		return errors.Errorf("pdfcpu: invalid percentage: %s", s)
	}
	h := pct / 100
	b.Dim = &Dim{Width: w, Height: h}
	return nil
}

func parseBoxDimWidthAndHeight(s1, s2 string, abs bool) (float64, float64, error) {
	var (
		w, h float64
		err  error
	)

	w, err = strconv.ParseFloat(s1, 64)
	if err != nil {
		return w, h, err
	}
	if !abs {
		// eg 0.25 rel (=25%)
		if w <= 0 || w > 1 {
			return w, h, errors.Errorf("pdfcpu: invalid relative box width: %f must be positive <= 1", w)
		}
	}

	h, err = strconv.ParseFloat(s2, 64)
	if err != nil {
		return w, h, err
	}
	if !abs {
		// eg 0.25 rel (=25%)
		if h <= 0 || h > 1 {
			return w, h, errors.Errorf("pdfcpu: invalid relative box height: %f must be positive <= 1", h)
		}
	}

	return w, h, nil
}

func parseBoxDim(s string, b *Box, u DisplayUnit) error {
	ss := strings.Fields(s)
	if len(ss) != 2 && len(ss) != 3 {
		return errors.Errorf("pdfcpu: illegal dimension string: need 2 positive numeric values, %s\n", s)
	}
	abs := true
	if len(ss) == 3 {
		s1 := ss[2]
		if s1 != "rel" && s1 != "abs" {
			return errors.New("pdfcpu: illegal dimension string")
		}
		abs = s1 == "abs"
	}

	s1, s2 := ss[0], ss[1]
	if s1[len(s1)-1] == '%' {
		return parseBoxDimByPercentage(s, s1, s2, b)
	}

	w, h, err := parseBoxDimWidthAndHeight(s1, s2, abs)
	if err != nil {
		return err
	}

	if abs {
		w = ToUserSpace(w, u)
		h = ToUserSpace(h, u)
	}
	b.Dim = &Dim{Width: w, Height: h}
	return nil
}

func parseBoxByPosWithinParent(ss []string, u DisplayUnit) (*Box, error) {
	b := &Box{Pos: Center}
	for _, s := range ss {

		ss1 := strings.Split(s, ":")
		if len(ss1) != 2 {
			return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
		}

		paramPrefix := strings.TrimSpace(ss1[0])
		paramValueStr := strings.TrimSpace(ss1[1])

		switch paramPrefix {
		case "dim":
			if err := parseBoxDim(paramValueStr, b, u); err != nil {
				return nil, err
			}

		case "pos":
			a, err := ParsePositionAnchor(paramValueStr)
			if err != nil {
				return nil, err
			}
			b.Pos = a

		case "off":
			if err := parseBoxOffset(paramValueStr, b, u); err != nil {
				return nil, err
			}

		default:
			return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
		}
	}
	if b.Dim == nil {
		return nil, errors.New("pdfcpu: missing box definition attr dim")
	}
	return b, nil
}

func parseBoxByMarginVals(ss []string, s string, abs bool, u DisplayUnit) (*Box, error) {
	switch len(ss) {
	case 1:
		return parseBoxBySingleMarginVal(s, ss[0], abs, u)
	case 2:
		return parseBoxBy2MarginVals(s, ss[0], ss[1], abs, u)
	case 3:
		return parseBoxBy3MarginVals(s, ss[0], ss[1], ss[2], abs, u)
	case 4:
		return parseBoxBy4MarginVals(s, ss[0], ss[1], ss[2], ss[3], abs, u)
	case 5:
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	return nil, nil
}

// ParseBox parses a box definition.
func ParseBox(s string, u DisplayUnit) (*Box, error) {
	// A rectangular region in userspace expressed in terms of
	// a rectangle or margins relative to its parent box.
	// Media box serves as parent/default for crop box.
	// Crop box serves as parent/default for trim, bleed and art box:

	// [0 10 200 150]		... rectangle

	// 0.5 0.5 20 20		... absolute, top:.5 right:.5 bottom:20 left:20
	// 0.5 0.5 .1 .1 abs	... absolute, top:.5 right:.5 bottom:.1 left:.1
	// 0.5 0.5 .1 .1 rel  	... relative, top:.5 right:.5 bottom:20 left:20
	// 10                 	... absolute, top,right,bottom,left:10
	// 10 5               	... absolute, top,bottom:10  left,right:5
	// 10 5 15            	... absolute, top:10 left,right:5 bottom:15
	// 5%         <50%      ... relative, top,right,bottom,left:5% of parent box width/height
	// .1 .5              	... absolute, top,bottom:.1  left,right:.5
	// .1 .3 rel         	... relative, top,bottom:.1=10%  left,right:.3=30%
	// -10                	... absolute, top,right,bottom,left enlarging the parent box as well

	// dim:30 30			... 30 x 30 display units, anchored at center of parent box
	// dim:30 30 abs		... 30 x 30 display units, anchored at center of parent box
	// dim:.3 .3 rel  		... 0.3 x 0.3 relative width/height of parent box, anchored at center of parent box
	// dim:30% 30%			... 0.3 x 0.3 relative width/height of parent box, anchored at center of parent box
	// pos:tl, dim:30 30	... 0.3 x 0.3 relative width/height of parent box, anchored at top left corner of parent box
	// pos:bl, off: 5 5, dim:30 30			...30 x 30 display units with offset 5/5, anchored at bottom left corner of parent box
	// pos:bl, off: -5 -5, dim:.3 .3 rel 	...0.3 x 0.3 relative width/height and anchored at bottom left corner of parent box

	s = strings.TrimSpace(s)
	if len(s) == 0 {
		return nil, nil
	}

	if s[0] == '[' && s[len(s)-1] == ']' {
		// Rectangle in PDF Array notation.
		return parseBoxByRectangle(s[1:len(s)-1], u)
	}

	// Via relative position within parent box.
	ss := strings.Split(s, ",")
	if len(ss) > 3 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	if len(ss) > 1 || strings.HasPrefix(ss[0], "dim") {
		return parseBoxByPosWithinParent(ss, u)
	}

	// Via margins relative to parent box.
	ss = strings.Fields(s)
	if len(ss) > 5 {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}
	if len(ss) == 1 && (ss[0] == "abs" || ss[0] == "rel") {
		return nil, errors.Errorf("pdfcpu: invalid box definition: %s", s)
	}

	abs := true
	l := len(ss) - 1
	s1 := ss[l]
	if s1 == "rel" || s1 == "abs" {
		abs = s1 == "abs"
		ss = ss[:l]
	}

	return parseBoxByMarginVals(ss, s, abs, u)
}

func (ctx *Context) addPageBoundaryString(i int, pb PageBoundaries, wantPB *PageBoundaries) []string {
	unit := ctx.UnitString()
	ss := []string{}
	d := pb.CropBox().Dimensions()
	if pb.Rot%180 != 0 {
		d.Width, d.Height = d.Height, d.Width
	}
	or := "portrait"
	if d.Landscape() {
		or = "landscape"
	}

	s := fmt.Sprintf("rot=%+d orientation:%s", pb.Rot, or)
	ss = append(ss, fmt.Sprintf("Page %d: %s", i+1, s))
	if wantPB.Media != nil {
		s := ""
		if pb.Media.Inherited {
			s = "(inherited)"
		}
		ss = append(ss, fmt.Sprintf("  MediaBox (%s) %v %s", unit, pb.MediaBox().Format(ctx.Unit), s))
	}
	if wantPB.Crop != nil {
		s := ""
		if pb.Crop == nil {
			s = "(default)"
		} else if pb.Crop.Inherited {
			s = "(inherited)"
		}
		ss = append(ss, fmt.Sprintf("   CropBox (%s) %v %s", unit, pb.CropBox().Format(ctx.Unit), s))
	}
	if wantPB.Trim != nil {
		s := ""
		if pb.Trim == nil {
			s = "(default)"
		}
		ss = append(ss, fmt.Sprintf("   TrimBox (%s) %v %s", unit, pb.TrimBox().Format(ctx.Unit), s))
	}
	if wantPB.Bleed != nil {
		s := ""
		if pb.Bleed == nil {
			s = "(default)"
		}
		ss = append(ss, fmt.Sprintf("  BleedBox (%s) %v %s", unit, pb.BleedBox().Format(ctx.Unit), s))
	}
	if wantPB.Art != nil {
		s := ""
		if pb.Art == nil {
			s = "(default)"
		}
		ss = append(ss, fmt.Sprintf("    ArtBox (%s) %v %s", unit, pb.ArtBox().Format(ctx.Unit), s))
	}
	return append(ss, "")
}

// ListPageBoundaries lists page boundaries specified in wantPB for selected pages.
func (ctx *Context) ListPageBoundaries(selectedPages IntSet, wantPB *PageBoundaries) ([]string, error) {
	pbs, err := ctx.PageBoundaries(selectedPages)
	if err != nil {
		return nil, err
	}
	ss := []string{}
	for i, pb := range pbs {
		if _, found := selectedPages[i+1]; !found {
			continue
		}
		ss = append(ss, ctx.addPageBoundaryString(i, pb, wantPB)...)
	}

	return ss, nil
}

// RemovePageBoundaries removes page boundaries specified by pb for selected pages.
// The media box is mandatory (inherited or not) and can't be removed.
// A removed crop box defaults to the media box.
// Removed trim/bleed/art boxes default to the crop box.
func (ctx *Context) RemovePageBoundaries(selectedPages IntSet, pb *PageBoundaries) error {
	for k, v := range selectedPages {
		if !v {
			continue
		}
		d, _, inhPAttrs, err := ctx.PageDict(k, false)
		if err != nil {
			return err
		}
		if pb.Crop != nil {
			if oldVal := d.Delete("CropBox"); oldVal == nil {
				d.Insert("CropBox", inhPAttrs.MediaBox.Array())
			}
		}
		if pb.Trim != nil {
			d.Delete("TrimBox")
		}
		if pb.Bleed != nil {
			d.Delete("BleedBox")
		}
		if pb.Art != nil {
			d.Delete("ArtBox")
		}
	}
	return nil
}

func boxLowerLeftCorner(r *Rectangle, w, h float64, a Anchor) Point {
	var p Point

	switch a {

	case TopLeft:
		p.X = r.LL.X
		p.Y = r.UR.Y - h

	case TopCenter:
		p.X = r.UR.X - r.Width()/2 - w/2
		p.Y = r.UR.Y - h

	case TopRight:
		p.X = r.UR.X - w
		p.Y = r.UR.Y - h

	case Left:
		p.X = r.LL.X
		p.Y = r.UR.Y - r.Height()/2 - h/2

	case Center:
		p.X = r.UR.X - r.Width()/2 - w/2
		p.Y = r.UR.Y - r.Height()/2 - h/2

	case Right:
		p.X = r.UR.X - w
		p.Y = r.UR.Y - r.Height()/2 - h/2

	case BottomLeft:
		p.X = r.LL.X
		p.Y = r.LL.Y

	case BottomCenter:
		p.X = r.UR.X - r.Width()/2 - w/2
		p.Y = r.LL.Y

	case BottomRight:
		p.X = r.UR.X - w
		p.Y = r.LL.Y
	}

	return p
}

func boxByDim(boxName string, b *Box, d Dict, parent *Rectangle) *Rectangle {
	w := b.Dim.Width
	if w <= 1 {
		w *= parent.Width()
	}
	h := b.Dim.Height
	if h <= 1 {
		h *= parent.Height()
	}
	ll := boxLowerLeftCorner(parent, w, h, b.Pos)
	r := RectForWidthAndHeight(ll.X+float64(b.Dx), ll.Y+float64(b.Dy), w, h)
	if d != nil {
		d.Update(boxName, r.Array())
	}
	return r
}

func ensureCropBoxWithinMediaBox(xmin, xmax, ymin, ymax float64, d Dict, parent *Rectangle) {
	if xmin < parent.LL.X || ymin < parent.LL.Y || xmax > parent.UR.X || ymax > parent.UR.Y {
		// Expand media box.
		if xmin < parent.LL.X {
			parent.LL.X = xmin
		}
		if xmax > parent.UR.X {
			parent.UR.X = xmax
		}
		if ymin < parent.LL.Y {
			parent.LL.Y = ymin
		}
		if ymax > parent.UR.Y {
			parent.UR.Y = ymax
		}
		if d != nil {
			d.Update("MediaBox", parent.Array())
		}
	}
}
