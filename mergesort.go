package mergesort

import (
	"fmt"
	"sort"
	"encoding/csv"
	encoding "encoding/csv"
	"strings"
	"bufio"
	"io"
	"io/ioutil"
	"os"
	// "log"
	"strconv"
	// "runtime"
	"errors"
	"regexp"
)

//Some utilities that are useful when processing CSV headers and data.
type Index map[string]int

// Return a map that maps each string in the input slice to its index in the slice.
func NewIndex(a []string) Index {
	index := make(map[string]int)
	for i, v := range a {
		index[v] = i
	}
	return index
}

// Answer true if the index contains the specified string.
func (i Index) Contains(k string) bool {
	_, ok := i[k]
	return ok
}

// Calculate the intersection between two string slices. The first returned slice
// is the intersection between the two slices. The second returned slice is
// a slice of elements in the first slice but not the second. The third returned
// slice is a slice of elements in the second slice but not the first.
func Intersect(a []string, b []string) ([]string, []string, []string) {
	index := NewIndex(a)
	result := make([]string, 0, len(b))
	aNotB := make([]string, len(a), len(a))
	copy(aNotB, a)
	bNotA := make([]string, 0, len(b))
	for _, v := range b {
		if i, ok := index[v]; ok {
			result = append(result, v)
			aNotB[i] = ""
		} else {
			bNotA = append(bNotA, v)
		}
	}
	i := 0
	for j := range a {
		present := (aNotB[j] == a[j])
		aNotB[i] = a[j]
		if present {
			i++
		}
	}
	aNotB = aNotB[0:i]
	return result, aNotB, bNotA
}

// A RecordComparator is a function that returns true if the left Record is 'less' than the right Record
// according to some total order.
type RecordComparator func(l, r Record) bool

// Constructs a single RecordComparator from a slice of RecordComparators
func AsRecordComparator(comparators []RecordComparator) RecordComparator {
	return func(l, r Record) bool {
		for _, c := range comparators {
			if c(l, r) {
				return true
			} else if c(r, l) {
				return false
			}
		}
		return false
	}

}

// A StringComparator is a function that returns true if the left string is 'less' then the right string
// according to some total order.
type StringComparator func(l, r string) bool

// A StringSliceComparator is a function that returns true if the left slice is 'less' than the right slice
// according to some total order.
type StringSliceComparator func(l, r []string) bool

func AsStringSliceComparator(comparators []StringComparator) StringSliceComparator {
	return func(l, r []string) bool {
		for i, c := range comparators {
			if c(l[i], r[i]) {
				return true
			} else if c(r[i], l[i]) {
				return false
			}
		}
		return false
	}
}

// A Sort comparator compares two records, identified by i and j, and returns true if the ith record is
// less than the jth record according to some total order.
type SortComparator func(i, j int) bool

//Record provides keyed access to the fields of data records where each field
//of a data record is keyed by the value of the corresponding field in the header record.
type Record interface {
	// Return the header of the record.
	Header() []string
	// Gets the value of the field specified by the key. Returns the empty string
	// if the field does not exist in the record.
	Get(key string) string
	// Puts the value into the field specified by the key.
	Put(key string, value string)
	// Return the contents of the record as a map. Mutation of the map is not supported.
	AsMap() map[string]string
	// Return the contents of the record as a slice. Mutation of the slice is not supported.
	AsSlice() []string
	// Puts all the matching values from the specified record into the receiving record
	// PutAll(r Record)
	// Return true if the receiver and the specified record have the same header.
	// SameHeader(r Record) bool
	// Puts all the matching values from the specified record into the receiving record
	PutAll(r Record)
	// Return true if the receiver and the specified record have the same header.
	SameHeader(r Record) bool
}

// A StringProjection is a function which produces a slice of strings from a Record.
type StringProjection func(r Record) []string

type record struct {
	header []string
	index  map[string]int
	fields []string
	cache  map[string]string
}

type RecordBuilder func(fields []string) Record

// NewRecordBuilder returns a function that can be used to create new Records
// for a CSV stream with the specified header.
//
// This can be used with raw encoding/csv streams in cases where a CSV stream contains
// more than one record type.
func NewRecordBuilder(header []string) RecordBuilder {
	index := NewIndex(header)
	return func(fields []string) Record {
		if len(header) < len(fields) {
			fmt.Fprintf(os.Stderr, "invariant violated: [%d]fields=%v, [%d]header=%v\n", len(fields), fields, len(header), header)
		}
		tmp := make([]string, len(header), len(header))
		copy(tmp, fields)
		return &record{
			header: header,
			index:  index,
			fields: tmp,
		}
	}
}

// Return a map containing a copy of the contents of the record.
func (r *record) AsMap() map[string]string {
	if r.cache != nil {
		return r.cache
	}

	result := make(map[string]string)
	for i, h := range r.header {
		if i < len(r.fields) {
			result[h] = r.fields[i]
		} else {
			result[h] = ""
		}
	}
	r.cache = result
	return result
}

// Return the record values as a slice.
func (r *record) AsSlice() []string {
	return r.fields
}

// Puts all the specified value into the record.
func (r *record) PutAll(o Record) {
	if r.SameHeader(o) {
		copy(r.fields, o.AsSlice())
		r.cache = nil
	} else {
		for i, k := range r.header {
			v := o.Get(k)
			r.fields[i] = v
			if r.cache != nil {
				r.cache[k] = v
			}
		}
	}
}

// Efficiently check that the receiver and specified records have the same header
func (r *record) SameHeader(o Record) bool {
	h := o.Header()
	if len(r.header) != len(h) {
		return false
	} else if len(h) == 0 || &h[0] == &r.header[0] {
		// two slices with the same address and length have the same contents
		return true
	} else {
		for i, k := range r.header {
			if h[i] != k {
				return false
			}
		}
		return true
	}
}

func (r *record) Header() []string {
	return r.header
}

// Answer the value of the field indexed by the column containing the specified header value.
func (r *record) Get(key string) string {
	x, ok := r.index[key]
	if ok && x < len(r.fields) {
		return r.fields[x]
	}
	return ""
}

// Puts the specified value into the record at the index determined by the key value.
func (r *record) Put(key string, value string) {
	x, ok := r.index[key]
	if ok && x < cap(r.fields) {
		if x > len(r.fields) {
			r.fields = r.fields[0:x]
		}
		if r.cache != nil {
			r.cache[key] = value
		}
		r.fields[x] = value
	}
}

// An adapter that converts a slice of CSV records into an instance of sort.Interface using the
// specified comparators, in order, to compare records.
type Sortable struct {
	Keys        []string
	Data        []Record
	Comparators []SortComparator
}

// An implementation of sort.Interface.Len()
func (b *Sortable) Len() int {
	return len(b.Data)
}

// An implementation of sort.Interface.Swap()
func (b *Sortable) Swap(i, j int) {
	b.Data[i], b.Data[j] = b.Data[j], b.Data[i]
}

// An implementation of sort.Interface.Less()
func (b *Sortable) Less(i, j int) bool {
	for _, c := range b.Comparators {
		if c(i, j) {
			return true
		} else if c(j, i) {
			return false
		}
	}
	return false
}

// Derives a SortProcess from the receiver. Note that it isn't safe
// to run multiple processes derived from the same Sortable at the same
// time.
func (b *Sortable) AsSortProcess() *SortProcess {
	return &SortProcess{
		Keys: b.Keys,
		AsSort: func(data []Record) sort.Interface {
			b.Data = data
			return b
		},
	}
}

// Answer a comparator for the field named k, using the string comparator specified by less.
func (b *Sortable) Comparator(k string, less StringComparator) SortComparator {
	return func(i, j int) bool {
		return less(b.Data[i].Get(k), b.Data[j].Get(k))
	}
}

// Answers true if l is less than r, according to a lexical comparison
func LessStrings(l, r string) bool {
	return l < r
}

// Answers true if the numeric value of l is less than r according to a numerical
// comparison (if l and r are both parseable as floats) or according to a lexical
// comparison otherwise.
func LessNumericStrings(l, r string) bool {
	var lf, rf float64
	if _, err := fmt.Sscanf(l, "%f", &lf); err != nil {
		return LessStrings(l, r)
	} else if _, err := fmt.Sscanf(r, "%f", &rf); err != nil {
		return LessStrings(l, r)
	} else {
		return lf < rf
	}
}


// Reader provides a reader of CSV streams whose first record is a header describing each field.
type Reader interface {
	// Answers the header.
	Header() []string
	// Answers a channel that iterates over a sequence of Records in the stream. The channel
	// remains open until an error is encountered or until the stream is exhausted.
	C() <-chan Record
	// Answers the error that caused the stream to close, if any.
	Error() error
	// Close the reader and release any resources associated with it.
	Close()
}

type reader struct {
	init   chan interface{}
	quit   chan interface{}
	header []string
	err    error
	io     <-chan Record
}

// ReadAll reads all the records from the specified reader and only returns a non-nil error
// if an error, other than EOF, occurs during the reading process.
func ReadAll(reader Reader) ([]Record, error) {
	all := make([]Record, 0, 1)
	for record := range reader.C() {
		all = append(all, record)
	}
	return all, reader.Error()
}

// WithIoReader creates a csv Reader from the specified io Reader.
func WithIoReader(io io.ReadCloser) Reader {
	csvReader := csv.NewReader(io)
	csvReader.FieldsPerRecord = -1
	return WithCsvReader(csvReader, io)
}

// WithCsvReader creates a csv reader from the specified encoding/csv Reader.
func WithCsvReader(r *csv.Reader, c io.Closer) Reader {
	ch := make(chan Record)
	result := &reader{
		init: make(chan interface{}),
		quit: make(chan interface{}),
		io:   ch,
	}
	go func() {
		defer close(ch)
		defer func() {
			if c != nil {
				e := c.Close()
				if result.err == nil {
					result.err = e
				}
			}
		}()
		if h, e := r.Read(); e != nil {
			result.header = []string{}
			result.err = e
			close(result.init)
			return
		} else {
			result.header = h
			close(result.init)
		}
		builder := NewRecordBuilder(result.header)
		for {
			if a, e := r.Read(); e != nil {
				if e != io.EOF {
					result.err = e
				}
				break
			} else {
				select {
				case <-result.quit:
					break
				default:
				}
				ch <- builder(a)
			}
		}
	}()
	return result
}

func (reader *reader) Header() []string {
	<-reader.init
	return reader.header
}

func (reader *reader) Error() error {
	<-reader.init
	return reader.err
}

func (reader *reader) C() <-chan Record {
	return reader.io
}

func (reader *reader) Close() {
	close(reader.quit)
}

type Writer interface {
	Header() []string      // Answer the header of the stream.
	Blank() Record         // Provide a blank record compatible with the stream.
	Write(r Record) error  // Write a single record into the underying stream.
	Error() error          // Return the final error.
	Close(err error) error // Close the writer with the specified error.
}

// A constructor for a writer using the specified header.
// By convention, passing a nil to the Builder returns a Writer
// which will release any underlying resources held by the builder
// when Close(error) is called.
type WriterBuilder func(header []string) Writer

type writer struct {
	header  []string
	builder RecordBuilder
	encoder *encoding.Writer
	closer  io.Closer
	err     error
}

// Answer a Writer for the CSV stream constrained by specified header, using the specified encoding writer
func WithCsvWriter(w *encoding.Writer, c io.Closer) WriterBuilder {
	return func(header []string) Writer {
		result := &writer{
			header:  header,
			builder: NewRecordBuilder(header),
			encoder: w,
			closer:  c,
		}
		result.err = result.encoder.Write(header)
		return result
	}
}

// Answer a Writer for the CSV stream constrained by the specified header, using the specified io writer.
func WithIoWriter(w io.WriteCloser) WriterBuilder {
	return WithCsvWriter(encoding.NewWriter(w), w)
}

// Answer the header that constrains the output stream
func (w *writer) Header() []string {
	return w.header
}

// Answer a blank record for the output stream
func (w *writer) Blank() Record {
	return w.builder(make([]string, len(w.header), len(w.header)))
}

// Write a record into the underlying stream.
func (w *writer) Write(r Record) error {
	if w.err != nil {
		return w.err
	}
	h := r.Header()
	var d []string
	if len(h) > 0 && len(w.header) == len(h) && &h[0] == &w.header[0] {
		// optimisation to avoid copying or iterating over slice in default case
		d = r.AsSlice()
	} else {
		// fallback in case where the stream and the record have a different header
		d := make([]string, len(w.header), len(w.header))
		for i, k := range w.header {
			d[i] = r.Get(k)
		}
	}
	return w.encoder.Write(d)
}

func (w *writer) Error() error {
	return w.err
}

// Close the stream and propagate an error
func (w *writer) Close(err error) error {
	w.encoder.Flush()
	if err == nil {
		err = w.encoder.Error()
	}
	w.err = err
	if w.closer != nil {
		return w.closer.Close()
	} else {
		return nil
	}
}

// Specifies the keys to be used by a CSV sort.
type SortKeys struct {
	Keys     []string // list of columns to use for sorting
	Numeric  []string // list of columns for which a numerical string comparison is used
	Reversed []string // list of columns for which the comparison is reversed
}

// Answer a Sort for the specified slice of CSV records, using the comparators derived from the
// keys specified by the receiver.
func (p *SortKeys) AsSort(data []Record) sort.Interface {
	return p.AsSortable(data)
}

// Answer a Sortable whose comparators have been initialized with string or numerical string
// comparators according the specification of the receiver.
func (p *SortKeys) AsSortable(data []Record) *Sortable {
	bk := &Sortable{
		Keys:        p.Keys,
		Data:        data,
		Comparators: make([]SortComparator, len(p.Keys), len(p.Keys)),
	}
	for x, c := range p.AsRecordComparators() {
		c := c
		bk.Comparators[x] = func(i, j int) bool {
			return c(bk.Data[i], bk.Data[j])
		}
	}
	return bk
}

// Derive a SortProcess from the receiver.
func (p *SortKeys) AsSortProcess() *SortProcess {
	return &SortProcess{
		AsSort: p.AsSort,
		Keys:   p.Keys,
	}
}

// Derive a StringProjection from the sort keys.
func (p *SortKeys) AsStringProjection() StringProjection {
	return func(r Record) []string {
		result := make([]string, len(p.Keys))
		for i, k := range p.Keys {
			result[i] = r.Get(k)
		}
		return result
	}
}

// Answers a comparator that can compare two slices.
func (p *SortKeys) AsStringSliceComparator() StringSliceComparator {
	numeric := NewIndex(p.Numeric)
	reverseIndex := NewIndex(p.Reversed)
	comparators := make([]StringComparator, len(p.Keys))
	for i, k := range p.Keys {
		if numeric.Contains(k) {
			comparators[i] = LessNumericStrings
		} else {
			comparators[i] = LessStrings
		}
		if reverseIndex.Contains(k) {
			f := comparators[i]
			comparators[i] = func(l, r string) bool {
				return !f(l, r)
			}
		}
	}
	return AsStringSliceComparator(comparators)
}

// Answers a slice of comparators that can compare two records.
func (p *SortKeys) AsRecordComparators() []RecordComparator {
	numeric := NewIndex(p.Numeric)
	reverseIndex := NewIndex(p.Reversed)
	comparators := make([]RecordComparator, len(p.Keys))
	for i, k := range p.Keys {
		k := k
		if numeric.Contains(k) {
			comparators[i] = func(l, r Record) bool {
				return LessNumericStrings(l.Get(k), r.Get(k))
			}
		} else {
			comparators[i] = func(l, r Record) bool {
				return LessStrings(l.Get(k), r.Get(k))
			}
		}
		if reverseIndex.Contains(k) {
			f := comparators[i]
			comparators[i] = func(l, r Record) bool {
				return !f(l, r)
			}
		}
	}
	return comparators
}

// Answers a comparator that can compare two records.
func (p *SortKeys) AsRecordComparator() RecordComparator {
	return AsRecordComparator(p.AsRecordComparators())
}

// A process, which given a CSV reader, sorts a stream of Records using the sort
// specified by the result of the AsSort function. The stream is checked to verify
// that it has the specified keys.
type SortProcess struct {
	AsSort func(data []Record) sort.Interface
	Keys   []string
}

// Run the sort process specified by the receiver against the specified CSV reader,
// writing the results to a Writer constructed from the specified builder.
// Termination of the sort process is signalled by writing nil or at most one error
// into the specified error channel.
// It is an error to apply the receiving process to a reader whose Header is not
// a strict superset of the receiver's Keys.
func (p *SortProcess) Run(reader Reader, builder WriterBuilder, errCh chan<- error) {

	errCh <- func() (err error) {
		defer reader.Close()

		keys := p.Keys

		// get the data header
		dataHeader := reader.Header()
		writer := builder(dataHeader)
		defer writer.Close(err)

		_, x, _ := Intersect(keys, dataHeader)
		if len(x) != 0 {
			return fmt.Errorf("invalid keys: %v", x)
		}

		if all, err := ReadAll(reader); err != nil {
			return err
		} else {

			sort.Sort(p.AsSort(all))

			for _, e := range all {
				if err := writer.Write(e); err != nil {
					return err
				}
			}
		}
		return nil
	}()
}


//Parse a string representing one or more encoded CSV record and returns the first such record.
func Parse(record string) ([]string, error) {
	reader := csv.NewReader(strings.NewReader(record))
	result, err := reader.Read()
	if err != nil {
		return nil, err
	}
	return result, nil
}

func sortconfigure(keys, numeric, reversed []string) (*SortProcess, error) {
	return (&SortKeys{Keys: keys, Numeric: numeric, Reversed: reversed}).AsSortProcess(), nil
}

/*
func halt(msg string) {
	pc, _, _, ok := runtime.Caller(1)
	details      := runtime.FuncForPC(pc)
	if ok && details != nil {
		log.Fatalln(fmt.Sprintf("\a%s: %s", details.Name(), msg))
	}
	log.Fatalln("\aoctree: FATAL ERROR!")
}
*/

// Add header with specified field name to the file
func addHeaderToFile(textFile, csvFile, recordSep string) error {
	file, err := os.Open(textFile)
	if err != nil {
		return err
	}
	defer file.Close()
	
	f, err := os.Create(csvFile)
	if err != nil {
		return err
	}
	defer f.Close()
	
	scanner := bufio.NewScanner(file)
	scanner.Scan()
	fields := strings.Split(scanner.Text(), recordSep)
	header := ""
	for i := 0; i < len(fields)-1; i++ {
		header = header + strconv.Itoa(i+1) + recordSep
	}
	f.WriteString(header)
	f.WriteString("\r\n")
	f.WriteString(scanner.Text())
	f.WriteString("\r\n")
	for scanner.Scan() {
		f.WriteString(scanner.Text())
		f.WriteString("\r\n")
	}
	return nil
}

// Remove specified header from file
func removeHeaderFromFile(csvFile, textFile string) (error, int) {
	file, err := os.Open(csvFile)
	if err != nil {
		return err, 0
	}
	defer file.Close()
	
	f, err := os.Create(textFile)
	if err != nil {
		return err, 0
	}
	defer f.Close()
	
	scanner := bufio.NewScanner(file)
	// skip header
	scanner.Scan()
	var recordCnt int
	recordCnt = 0
	for scanner.Scan() {
		f.WriteString(scanner.Text())
		f.WriteString("\r\n")
		recordCnt++
	}
	return nil, recordCnt
}

func parseSortKeys(sortKeys, sep string, verbose bool) ([]string, []string, []string, string, error) {
	// list of columns to use for sorting
	var keys []string		// key must specify one or more columns
	// list of columns for which a numerical string comparison is used
	var numeric []string	// numeric must specify the list of numeric keys and must be a strict subset of --key
	// list of columns for which the comparison is reversed
	var reversed []string	// reverse must specify the list of keys to be sorted in reverse order and must be a strict subset of --key
	var dupSpec string      // keeps one record of each key field value

	sp1 := strings.Split(sortKeys, sep)
	if verbose {
		fmt.Println("parseSortKeys: sp1", sp1, "len", len(sp1))
	}
	if len(sp1) >= 4 {
		keys = strings.Split(sp1[0], ",")
		numericTmp := strings.Split(sp1[1], ",")
		for i, element := range numericTmp {
			if element == "n" {
				numeric = append(numeric, keys[i])
			}
		}
		reversedTmp := strings.Split(sp1[2], ",")
		for i, element := range reversedTmp {
			if element == "d" {
				reversed = append(reversed, keys[i])
			}
		}
		if len(sp1) == 5 {
			// key field value for dupo process
			dupSpec = sp1[3]
		}
	} else {
		return keys, numeric, reversed, dupSpec, errors.New("keySpec: wrong format")
	}
	return keys, numeric, reversed, dupSpec, nil
}

func CsvSort(inFile, outFile, keySpec, dupType, recordSep, wDir string, verbose bool) (int, int) {
	/* Purpose   : sorts a CSV stream according to the specified columns.
	 * Arguments : inFile  = path of the file with the data to be sorted.
	 *             outFile = path of the file for the sorted data.
	 *             keySpec = "key...|numeric...|reversed..."
	 *						Ex. "1,2,3,4,5,6|c,c,c,c,c,c|a,a,a,a,a,a|1,2,3|"
	 *						key      : list of columns to use for sorting
	 *						numeric  : list of sort type associating with sorting columns (c for character string and n for numeric)
	 *						reversed : list of sort order associating with sorting columns (a for ascending and d for descending)
	 *						dupSpec  : list of columns to use for duplicating selection
	 *			   dupType = "dupo" or "dupe" or "dupi"
	 *						dupo : keeps one record of each key field value
	 *						dupe : removes all records with non-unique key fields from the output file
	 *						dupi : includes all records with non-unique key fields on the output file
	 *			   recordSep = the field separator
	 *             verbose = boolean flag for verbose mode. If true, the main execution stages will be echoed to Stdout.
	 *
	 * Run the sort process specified by the receiver against the specified CSV reader,
	 * writing the results to a Writer constructed from the specified builder.
	 * Termination of the sort process is signalled by writing nil or at most one error
	 * into the specified error channel.
	 * It is an error to apply the receiving process to a reader whose header is not
	 * a strict superset of the receiver's Keys
	 */

	 var (
		// tempDir     = filepath.ToSlash(os.TempDir())    //temporary directory for the temp files (import "path/filepath")
		tempDir = wDir
		tempCsvFile = fmt.Sprintf("%s/temp_csv.dat", tempDir) //glob pattern for the temporary csv file
		tempOutFile = fmt.Sprintf("%s/temp_csv.out", tempDir) //glob pattern for the temporary out file
	)

	if verbose {
		fmt.Println("inFile",  inFile,  "tempCsvFile", tempCsvFile)
		fmt.Println("outFile", outFile, "tempOutFile", tempOutFile)
	}

	// As a rule, CSV files has to include a header record that describes the contents of each field.

	if inFile == "" {
		// halt("the input text file was not specified")
		return 213, 0
	}
	if tempCsvFile == "" {
		// halt("the output csv file was not specified")
		return 211, 0
	}
	if recordSep == "" {
		// halt("the dlimited were not specified")
		return 201, 0
	}
	fi, err := os.Stat(inFile)
	if err != nil || fi.Size() == 0 {
		// halt("the input text file cannot be located or is empty")
		return 213, 0
	}

	err = addHeaderToFile(inFile, tempCsvFile, recordSep)
	if err != nil {
		// err is printable
		// elements passed are separated by space automatically
		// halt("addHeaderToFile function failed")
		return 215, 0
	}

	var keys []string		// key must specify one or more columns
	var numeric []string	// numeric must specify the list of numeric keys and must be a strict subset of --key
	var reversed []string	// reverse must specify the list of keys to be sorted in reverse order and must be a strict subset of --key
	var dupSpec string      // list of columns to use for duplicating selection

	keys, numeric, reversed, dupSpec, err = parseSortKeys(keySpec, "|", verbose)
	if err != nil {
		// halt("parseSortKeys function failed")
		return 102, 0
	}

	if verbose {
		fmt.Println("keys", keys, "numeric", numeric, "reversed", reversed, "dupSpec", dupSpec)
	}

	var p *SortProcess
	var errCh = make(chan error, 1)

	csvTmpFile, err := os.Open(tempCsvFile)
	defer csvTmpFile.Close()

	if err != nil {
		// elements passed are separated by space automatically
		// log.Fatal("Unable to open tempCsvFile")
		return 214, 0
	}
	// automatically call Close() at the end of current method
	reader := csv.NewReader(csvTmpFile)
	reader.Comma = rune(recordSep[0])
	var rc io.Closer
	
	// write results to a new csv
	outTmpFile, err := os.Create(tempOutFile)
	if err != nil {
		// log.Fatal("Unable to open output")
		return 210, 0
	}
	defer outTmpFile.Close()
	writer := csv.NewWriter(outTmpFile)
	writer.Comma = rune(recordSep[0])
	writer.UseCRLF = true
	var wc io.Closer
	
	if p, err = sortconfigure(keys, numeric, reversed); err == nil {
		p.Run(WithCsvReader(reader, rc), WithCsvWriter(writer, wc), errCh)
		err = <-errCh
	}
	
	if err != nil {
		// fmt.Printf("fatal: %v\n", err)
		return 999, 0
		// os.Exit(1)
	}

	var recordCnt int

	if tempOutFile == "" {
		// halt("the input csv file was not specified")
		return 213, 0
	}
	if outFile == "" {
		// halt("the output csv file was not specified")
		return 211, 0
	}
	fi, err = os.Stat(tempOutFile)
	if err != nil || fi.Size() == 0 {
		// halt("the input csv file cannot be located or is empty")
		return 213, 0
	}

	err, recordCnt = removeHeaderFromFile(tempOutFile, outFile)
	if err != nil {
		// err is printable
		// elements passed are separated by space automatically
		// halt("removeHeaderFromFile function failed")
		// fmt.Println("Error (removeHeaderFromFile):", err)
		return 221, 0
	}

	csvTmpFile.Close()
	// delete csv temp file
	err = os.Remove(tempCsvFile)
	if err != nil {
		// log.Fatal(err)
		return 312, 0
	}

	outTmpFile.Close()
	// delete output temp file
	err = os.Remove(tempOutFile)
	if err != nil {
		// log.Fatal(err)
		return 312, 0
	}

	// check if need to remove duplicate lines
	if len(dupSpec) > 0 {
		if verbose {
			fmt.Println("calling remove duplicate line function")
		}
		err := ProcessDuplicateLine(outFile, dupSpec, dupType, recordSep, wDir, verbose)
		if err != nil {
			// fmt.Println("error in ProcessDuplicateLine", err)
			return 666, 0
		}
	} else {
		if verbose {
			fmt.Println("No need to process duplicate")
		}
	}
	return 0, recordCnt
}

func ProcessDuplicateLine(inFile, dupSpec, dupType, recordSep, wDir string, verbose bool) error {
	/* Purpose   : Remove duplicate line/row from the text file (text is already sorted).
	 * Arguments : inFile  = path of the file with the data to be inspected and save and overwrite the text file.
	 *             dupSpec = list of columns to use for processing the duplicate line
	 *			   dupType = "dupo" or "dupe" or "dupi"
	 *						dupo : keeps one record of each key field value
	 *						dupe : removes all records with non-unique key fields from the output file
	 *						dupi : includes all records with non-unique key fields on the output file
	 *			   recordSep = the field separator
	 *             verbose = boolean flag for verbose mode. If true, the main execution stages will be echoed to Stdout.
	 */
	
	if strings.ToLower(dupType) != "dupo" &&
		strings.ToLower(dupType) != "dupi" &&
		strings.ToLower(dupType) != "dupe" {
		return errors.New("dupType should be \"dupo\", \"dupi\", or \"dupe\"")
	}
		 
	var (
		// tempDir     = filepath.ToSlash(os.TempDir())    //temporary directory for the temp files (import "path/filepath")
		tempDir = wDir
		tempOutFile = fmt.Sprintf("%s/temp_csv.out", tempDir) //glob pattern for the temporary out file
	)
	
	csvFile, err := os.Open(inFile)
	if err != nil {
		 return err
	}
	
	reader := csv.NewReader(csvFile)
	// change comma ',' to pipe '|' delimiter in csv file
	reader.Comma = rune(recordSep[0])
	
	records, err := reader.ReadAll()
	if err != nil {
		 return err
	}
	
	file, err := os.Create(tempOutFile)
	if err != nil {
		return err
	}
		
	write := csv.NewWriter(file)
	// change comma ',' to pipe '|' delimiter in csv file
	write.Comma = rune(recordSep[0])
	write.UseCRLF = true
	 
	nameExistMap := make(map[string]bool)
	dupExistMap  := make(map[string]bool)
	dupCol := strings.Split(dupSpec, ",")
	if verbose {
		fmt.Println("dupSpec", dupSpec, "len", len(dupSpec), "dupCol", dupCol, "len", len(dupCol))
	}
	
	for _, row := range records {
		var dupKey string
		for _, val := range dupCol {
			index, _ := strconv.Atoi(val)
			dupKey = dupKey + row[index-1]
		}
		if verbose {
			fmt.Println("dupKey", dupKey)
		}
		if _, exist := nameExistMap[dupKey]; exist {
			if _, exist := dupExistMap[dupKey]; !exist {
				dupExistMap[dupKey] = true
			}
			continue
		} else {
			nameExistMap[dupKey] = true
			// Do Output Here
			if strings.ToLower(dupType) == "dupo" {
				if verbose {
					fmt.Println("processing duplicate unique output : ", dupType)
				}
				err := write.Write(row)
				if err != nil {
					 return err
				}
			}
		}
	}
	
	// process DUPE (duplicate exclude) or DUPI (duplicate include) if necessary
	if strings.ToLower(dupType) == "dupi" || strings.ToLower(dupType) == "dupe" {
		csvFile.Seek(0, 0)	// rewind file pointer
		reader = csv.NewReader(csvFile)
			
		reader.Comma = rune(recordSep[0])	// change comma ',' to pipe '|' delimiter in csv file
		
		records, err = reader.ReadAll()
		if err != nil {
			 return err
		}
		
		for _, row := range records {
			var dupKey string
			for _, val := range dupCol {
				index, _ := strconv.Atoi(val)
				dupKey = dupKey + row[index-1]
			}
			if verbose {
				fmt.Println("dupKey", dupKey)
			}
			if _, exist := dupExistMap[dupKey]; exist {
				// Do Output Here for DUPI
				if strings.ToLower(dupType) == "dupi" {
					if verbose {
						fmt.Println("processing duplicate included : ", dupType)
					}
					err := write.Write(row)
					if err != nil {
						 return err
					}
				}
			} else {
				// Do Output Here for DUPE
				if strings.ToLower(dupType) == "dupe" {
					if verbose {
						fmt.Println("processing duplicate excluded : ", dupType)
					}
					err := write.Write(row)
					if err != nil {
						 return err
					}
				}
			}
		}	// end of for
	}
	
	// close original text file
	csvFile.Close()
		
	// remove original text file
	err = os.Remove(inFile)
	if err != nil {
		// log.Fatal(err)
		return err
	}
	
	// Write any buffered data to the underlying writer (standard output).
	write.Flush()
	file.Close()
	err =  os.Rename(tempOutFile, inFile)
	// err =  os.Rename(tempOutFile, "pipefile1.out")
	
	if err != nil {
		fmt.Println(err)
		return err
	}
	
	return nil
}

// A Join can be used to construct a process that will join two streams of CSV records by matching
// records from each stream on the specified key columns.
type Join struct {
	LeftKeys   []string // the names of the keys from the left stream
	RightKeys  []string // the names of the keys from the right stream
	Numeric    []string // the names of the keys in the left stream that are numeric keys
	LeftOuter  bool     // perform a left outer join - left rows are copied even if there is no matching right row
	RightOuter bool     // perform a right outer join - right rows are copied even if there is no matching left row
}

func joinconfigure(joinKey, numericKey string, joinType bool, twoFiles, sep string, verbose bool) (*Join, []string, error) {
	
	leftKeys := strings.Split(joinKey, sep)
	rightKeys := strings.Split(joinKey, sep)
	numeric := strings.Split(numericKey, sep)
	fn := strings.Split(twoFiles, sep)
	if len(fn) < 2 {
		return nil, nil, fmt.Errorf("expected at least 2 file arguments, found %d", len(fn))
	}
	
	if verbose {
		fmt.Println("leftKeys", leftKeys)
		fmt.Println("rightKeys", rightKeys)
		fmt.Println("numeric", numeric)
		fmt.Println("fn", fn)
	}
	var leftOuter, rightOuter bool
	leftOuter = joinType
	rightOuter = joinType
	
	return &Join{
		LeftKeys:   leftKeys,
		RightKeys:  rightKeys,
		Numeric:    numeric,
		LeftOuter:  leftOuter,
		RightOuter: rightOuter,
	}, fn, nil
}
	
func openReader(n string) (Reader, error) {
	if n == "-" {
		return WithIoReader(os.Stdin), nil
	} else {
		if f, err := os.Open(n); err != nil {
			return nil, err
		} else {
			return WithIoReader(f), nil
		}
	}
}

// A Process is a function that can be run asynchronously that consumes a stream of CSV
// records provided by reader and writes them into a writer of CSV records as
// constructed by the specified builder. It signals its successful completion by
// writing a nil into the specified error channel. An unsuccessful completion
// is signaled by writing at most one error into the specified error channel.
type Process interface {
	Run(reader Reader, builder WriterBuilder, errCh chan<- error)
}

// A decorator for a reader that returns groups of consecutive records from the underlying reader
// that have the same key.
type groupReader struct {
	next   Record
	group  []Record
	reader Reader
	key    []string
	tokey  func(r Record) []string
	less   func(l, r []string) bool
}

// Fill up the group slice with the set of records in the underlying stream that have the same key
func (g *groupReader) fill() bool {
	if g.next == nil {
		g.next = <-g.reader.C()
	}
	if g.next == nil {
		return false
	} else {
		g.key = g.tokey(g.next)
	}
	g.group = []Record{g.next}
	for {
		g.next = <-g.reader.C()
		var k []string
		if g.next != nil {
			k = g.tokey(g.next)
		}
		if g.next == nil || g.less(k, g.key) || g.less(g.key, k) {
			return true
		} else {
			g.group = append(g.group, g.next)
		}
	}
}

// Answers true if get() will yield a new group
func (g *groupReader) hasNext() bool {
	if g.group != nil && len(g.group) > 0 {
		return true
	}
	return g.fill()
}

// Answers the next group of records from the stream.
func (g *groupReader) get() []Record {
	if !g.hasNext() {
		panic("illegal state: get() called when hasNext() is false")
	}
	r := g.group
	g.group = nil
	return r
}

// Construct a key comparison function for key values
func (p *Join) less() StringSliceComparator {
	return (&SortKeys{
		Keys:    p.LeftKeys,
		Numeric: p.Numeric,
	}).AsStringSliceComparator()
}

// split the headers into the set of all headers, the set of key headers, the set of left headers
// and the set of right headers
func (p *Join) headers(leftHeader []string, rightHeader []string) ([]string, []string, []string, []string) {
	i, a, _ := Intersect(leftHeader, p.LeftKeys)
	_, b, _ := Intersect(rightHeader, p.RightKeys)
	f := make([]string, len(i)+len(a)+len(b))

	copy(f, i)
	copy(f[len(i):], a)
	copy(f[len(i)+len(a):], b)

	return f, i, a, b
}

func (p *Join) run(left Reader, right Reader, builder WriterBuilder, errCh chan<- error) {
	errCh <- func() (err error) {
		defer left.Close()
		defer right.Close()

		less := p.less()

		leftBlank := NewRecordBuilder(left.Header())([]string{})
		rightBlank := NewRecordBuilder(right.Header())([]string{})

		outputHeader, keyHeader, leftHeader, rightHeader := p.headers(left.Header(), right.Header())
		writer := builder(outputHeader)
		defer writer.Close(err)

		leftG := &groupReader{reader: left, less: less, tokey: (&SortKeys{Keys: p.LeftKeys}).AsStringProjection()}
		rightG := &groupReader{reader: right, less: less, tokey: (&SortKeys{Keys: p.RightKeys}).AsStringProjection()}

		w := func(k []string, l, r Record) error {
			o := writer.Blank()
			for i, h := range keyHeader {
				o.Put(h, k[i])
			}
			for _, h := range leftHeader {
				o.Put(h, l.Get(h))
			}
			for _, h := range rightHeader {
				o.Put(h, r.Get(h))
			}
			return writer.Write(o)
		}

		for leftG.hasNext() && rightG.hasNext() {
			if less(leftG.key, rightG.key) {
				//
				// copy left to output
				//
				for _, r := range leftG.get() {
					if p.LeftOuter {
						if err := w(leftG.key, r, rightBlank); err != nil {
							return err
						}
					}
				}
			} else if less(rightG.key, leftG.key) {
				//
				// copy right to output
				//
				for _, r := range rightG.get() {
					if p.RightOuter {
						if err := w(rightG.key, leftBlank, r); err != nil {
							return err
						}
					}
				}
			} else {
				// copy join product to output
				rg := rightG.get()
				for _, l := range leftG.get() {
					for _, r := range rg {
						if err := w(leftG.key, l, r); err != nil {
							return err
						}
					}
				}
			}
		}
		for leftG.hasNext() {
			//
			// copy left to output
			//
			for _, r := range leftG.get() {
				if p.LeftOuter {
					if err := w(leftG.key, r, rightBlank); err != nil {
						return err
					}
				}
			}
		}
		for rightG.hasNext() {
			//
			// copy right to output
			//
			for _, r := range rightG.get() {
				if p.RightOuter {
					if err := w(rightG.key, leftBlank, r); err != nil {
						return err
					}
				}
			}
		}

		lerr := left.Error()
		if lerr != nil {
			return lerr
		} else {
			return right.Error()
		}
	}()

}

type joinProcess struct {
	join  *Join
	right Reader
}

// Binds the specified reader as the right-hand side of a join and returns
// a Process whose reader will be considered as the left-hand side of the join.
func (p *Join) WithRight(r Reader) Process {
	return &joinProcess{
		join:  p,
		right: r,
	}
}

func (j *joinProcess) Run(r Reader, builder WriterBuilder, errCh chan<- error) {
	j.join.run(r, j.right, builder, errCh)
}

// A process that copies the reader to the writer.
type CatProcess struct {
}

func (p *CatProcess) Run(r Reader, b WriterBuilder, errCh chan<- error) {
	errCh <- func() (err error) {
		w := b(r.Header())
		defer w.Close(err)
		for rec := range r.C() {
			if e := w.Write(rec); e != nil {
				return e
			}
		}
		return r.Error()
	}()
}

type pipe struct {
	header []string
	ch     chan Record
	init   chan interface{}
	err    error
}

// A pipeline of processes.
type pipeline struct {
	stages []Process
}

// Implements a unidirectional channel that can connect a reader process to a writer process.
type Pipe interface {
	Builder() WriterBuilder // Builds a Writer for the write end of the pipe
	Reader() Reader         // Returns the Reader for the read end of the pipe
}

type pipeWriter struct {
	pipe    *pipe
	builder RecordBuilder
}

// Answer a new Pipe whose Builder and Reader can be used to connect two chained
// processes.
func NewPipe() Pipe {
	return &pipe{
		ch:   make(chan Record),
		err:  nil,
		init: make(chan interface{}),
	}
}

func (p *pipe) Reader() Reader {
	return p
}

func (p *pipe) C() <-chan Record {
	<-p.init
	return p.ch
}

func (p *pipe) Close() {
}

func (p *pipe) Header() []string {
	<-p.init
	return p.header
}

func (p *pipe) Error() error {
	<-p.init
	return p.err
}

func (p *pipe) Builder() WriterBuilder {
	return func(header []string) Writer {
		p.header = header
		close(p.init)
		return &pipeWriter{pipe: p, builder: NewRecordBuilder(header)}
	}
}

func (p *pipeWriter) Blank() Record {
	return p.builder(make([]string, len(p.pipe.header)))
}

func (p *pipeWriter) Close(err error) error {
	p.pipe.err = err
	close(p.pipe.ch)
	return nil
}

func (p *pipeWriter) Error() error {
	return p.pipe.err
}

func (p *pipeWriter) Header() []string {
	return p.pipe.header
}

func (p *pipeWriter) Write(r Record) error {
	p.pipe.ch <- r
	return nil
}

// Join a sequence of processes by connecting them with pipes, returning a new process that
// represents the entire pipeline.
func NewPipeLine(p []Process) Process {
	if p == nil || len(p) == 0 {
		p = []Process{&CatProcess{}}
	}
	return &pipeline{
		stages: p,
	}
}

// Run the pipeline by connecting each stage with pipes and then running each stage
// as a goroutine.
func (p *pipeline) Run(r Reader, b WriterBuilder, errCh chan<- error) {
	errCh <- func() (err error) {

		errors := make(chan error, len(p.stages))
		for _, c := range p.stages[:len(p.stages)-1] {
			p := NewPipe()
			go c.Run(r, p.Builder(), errors)
			r = p.Reader()
		}
		go p.stages[len(p.stages)-1].Run(r, b, errors)

		running := len(p.stages)

		for running > 0 {
			e := <-errors
			running--
			if err == nil {
				err = e
			}
		}

		return err
	}()
}

// Given a reader and a process, answer a new reader which is the result of
// applying the specified process to the specified reader.
func WithProcess(r Reader, p Process) Reader {
	pipe := NewPipe()
	go p.Run(r, pipe.Builder(), make(chan error, 1))
	return pipe.Reader()
}

func CsvJoin (twoFiles, outFile, joinKey, numericKey string, joinType bool, inSep, outSep, keySep string, verbose bool) error {
	var j *Join
	var err error
	var fn []string

	err = func() error {
		if j, fn, err = joinconfigure(joinKey, numericKey, joinType, twoFiles, keySep, verbose); err == nil {

			// construct a sort process for the left most file

			leftSortProcess := (&SortKeys{
				Numeric: j.Numeric,
				Keys:    j.LeftKeys,
			}).AsSortProcess()

			// map the numeric key to the keyspace of the rightmost files

			l2r := map[string]string{}
			for i, k := range j.LeftKeys {
				l2r[k] = j.RightKeys[i]
			}
			if verbose {
				fmt.Println("l2r", l2r)
			}

			rightNumeric := make([]string, len(j.Numeric))
			for i, k := range j.Numeric {
				rightNumeric[i] = l2r[k]
			}
			if verbose {
				fmt.Println("rightNumeric", rightNumeric)
			}

			// create a sort process for the right most files.

			rightSortProcess := (&SortKeys{
				Numeric: rightNumeric,
				Keys:    j.RightKeys,
			}).AsSortProcess()

			// open one reader for each file
			readers := make([]Reader, len(fn))
			for i, n := range fn {
				if readers[i], err = openReader(n); err != nil {
					return err
				}
			}

			// write results to a new csv
			outTmpFile, err := os.Create(outFile)
			if err != nil {
				// log.Fatal("Unable to open output")
				return err
			}
			defer outTmpFile.Close()
			writer := csv.NewWriter(outTmpFile)
			writer.Comma = rune(outSep[0])
			writer.UseCRLF = true
			var wc io.Closer

			// create one join process for each of the last n-1 readers
			procs := make([]Process, len(readers)-1)
			for i, _ := range procs {
				procs[i] = j.WithRight(WithProcess(readers[i+1], rightSortProcess))
			}

			// create a pipeline from the n-1 join processes
			pipeline := NewPipeLine(procs)

			// run the join pipeline with the first reader
			var errCh = make(chan error, 1)
			// pipeline.Run(WithProcess(readers[0], leftSortProcess), WithIoWriter(os.Stdout), errCh)
			pipeline.Run(WithProcess(readers[0], leftSortProcess), WithCsvWriter(writer, wc), errCh)
			return <-errCh
		} else {
			return err
		}
	}()

	if err != nil {
		// fmt.Printf("fatal: %v\n", err)
		// os.Exit(1)
		return err
	}
	return nil
}


// Given a header-prefixed input stream of CSV records select the fields that match the specified key (Key).
// If PermuteOnly is is specified, all the fields of the input stream are preserved, but the output stream
// is permuted so that the key fields occupy the left-most fields of the output stream. The remaining fields
// are preserved in their original order.
type SelectProcess struct {
	Keys        []string
	PermuteOnly bool
}

func selectconfigure(key, sep string, permuteOnly, verbose bool) (*SelectProcess, error) {

	// Use  a CSV parser to extract the partial keys from the parameter
	keys := strings.Split(key, sep)

	return &SelectProcess{
		Keys:        keys,
		PermuteOnly: permuteOnly,
	}, nil

}

func (p *SelectProcess) Run(reader Reader, builder WriterBuilder, errCh chan<- error) {
	errCh <- func() (err error) {
		defer reader.Close()

		keys := p.Keys
		permuteOnly := p.PermuteOnly

		// get the data header
		dataHeader := reader.Header()

		_, _, b := Intersect(keys, dataHeader)
		if len(b) > 0 && permuteOnly {
			extend := make([]string, len(keys)+len(b))
			copy(extend, keys)
			copy(extend[len(keys):], b)
			keys = extend
		}

		// create a new output stream
		writer := builder(keys)
		defer writer.Close(err)

		for data := range reader.C() {
			outputData := writer.Blank()
			outputData.PutAll(data)
			if err = writer.Write(outputData); err != nil {
				return err
			}
		}

		return reader.Error()
	}()
}

func CsvSelect(inFile, outFile, key, inSep, outSep, keySep string, permuteOnly, verbose bool) error {
	var p *SelectProcess
	var err error
	var errCh = make(chan error, 1)

	inTmpFile, err := os.Open(inFile)
	defer inTmpFile.Close()

	if err != nil {
		// elements passed are separated by space automatically
		// log.Fatal("Unable to open inFile")
		return err
	}
	// automatically call Close() at the end of current method
	reader := csv.NewReader(inTmpFile)
	reader.Comma = rune(inSep[0])
	var rc io.Closer
	
	// write results to a new csv
	outTmpFile, err := os.Create(outFile)
	if err != nil {
		// log.Fatal("Unable to open outFile")
		return err
	}
	defer outTmpFile.Close()
	writer := csv.NewWriter(outTmpFile)
	writer.Comma = rune(outSep[0])
	writer.UseCRLF = true
	var wc io.Closer

	if p, err = selectconfigure(key, keySep, permuteOnly, verbose); err == nil {
		p.Run(WithCsvReader(reader, rc), WithCsvWriter(writer, wc), errCh)
		err = <-errCh
	}

	if err != nil {
		// fmt.Printf("fatal: %v\n", err)
		// os.Exit(1)
		return err
	}
	return nil
}

func ConvertTextFileToCsvFile(inFile, inSep, outSep string) {
	read, err := ioutil.ReadFile(inFile)
	newContents := strings.Replace(string(read), inSep, outSep, -1)
	err = ioutil.WriteFile(inFile, []byte(newContents), 0)
		
	if err != nil {
		panic(err)
		os.Exit(1)
	}
//	return nil
}

func ConvertTBtableToCsvFile(inFile, inSep, outFile, outSep string) error {
	tableTmpFile, err := os.Open(inFile)
	defer tableTmpFile.Close()

	if err != nil {
		// elements passed are separated by space automatically
		// log.Fatal("Unable to open tempCsvFile")
		// panic(err)
		// os.Exit(1)
		return err
	}
	r := csv.NewReader(tableTmpFile)
	in := inSep
	r.Comma = rune(in[0])

	file, err := os.Create(outFile)
	if err != nil {
		// panic(err)
		// os.Exit(1)
		return err
	}

	write := csv.NewWriter(file)
	// change comma ',' to pipe '|' delimiter in csv file
	out := outSep
	write.Comma = rune(out[0])
	write.UseCRLF = true

	// Skip index header
	_, err = r.Read()

	// Handle table header
	header, err := r.Read()
	var s []string
	for value := range header {
		if value %5 == 0 {
			s = append(s, header[value])
		}
	}

	err = write.Write(s)
	if err != nil {
		// panic(err)
		// os.Exit(1)
		return err
	}

	for {
		record, err := r.Read()
        // Stop at EOF.
		if err == io.EOF {
			break
		}
		err = write.Write(record)
		if err != nil {
			// panic(err)
			// os.Exit(1)
			return err
		}
	}
	
	// Write any buffered data to the underlying writer (standard output).
	write.Flush()
	file.Close()

	return nil
}

func Ds_sort(inFile, outFile, ctlparms string, numRecs, retCode *int) {
	var verbose = false
	keySpec, dupType, wDir, delimiter := parseForSort(ctlparms)
	
	errNo, recordCnt := CsvSort(inFile, outFile, keySpec, dupType, delimiter, wDir, verbose) 
	*retCode = errNo
	*numRecs = recordCnt
}

// from  "s(#1,c,a, #2,c,d, #3,c,a, #4,c,a, #5,c,a) del(124)"
// to    "1,2,3,4,5|c,c,c,c,c|a,d,a,a,a|"
func parseForSort(ctlparms string) (string, string, string, string) {
	var duptype string
	if strings.Contains(ctlparms, "dupo") {
		duptype = "dupo"
	} else if strings.Contains(ctlparms, "dupi") {
		duptype = "dupi"
	} else if strings.Contains(ctlparms, "dupe") {
		duptype = "dupe"
	} else {
		duptype = ""
	}

	r, _ := regexp.Compile("s\\(.+[a-z]\\)")
	s := r.FindString(ctlparms)
	s = strings.Trim(s, ")")

	ctlStr := strings.Split(s, "#")
	ctlStrNew := ""
	typeStr := ""
	orderStr := ""
	if len(ctlStr) > 1 {
		for i := 1; i < len(ctlStr); i++ {
			strTmp := strings.Split(ctlStr[i], ",")
			if i == len(ctlStr)-1 {
				ctlStrNew = ctlStrNew + strTmp[0]
				typeStr = typeStr + strTmp[1]
				orderStr = orderStr + strTmp[2]
			} else {
				ctlStrNew = ctlStrNew + strTmp[0] + ","
				typeStr = typeStr + strTmp[1] + ","
				orderStr = orderStr + strTmp[2] + ","
			}
		}
	}
	ctlStrNew = ctlStrNew + "|" + typeStr + "|" + orderStr + "|"
//		fmt.Printf("ctlStrNew = %s typeStr = %s orderStr = %s len = %d\n", ctlStrNew, typeStr, orderStr, len(ctlStr))
		
	r, _ = regexp.Compile("dup.\\(.+[0-9]\\)")
	s = r.FindString(ctlparms)
	s = strings.Trim(s, ")")
	strTmp := strings.Split(s, "#")
	dupStr := ""
	if len(strTmp) > 1 {
		for i := 1; i < len(strTmp); i++ {
			s := strings.Split(strTmp[i], ",")
			if i == len(strTmp)-1 {
				dupStr = dupStr + s[0]
			} else {
				dupStr = dupStr + s[0] + ","
			}
		}
		ctlStrNew = ctlStrNew + dupStr + "|"
	}

	// find the delimiter del(124); 124 to ascii "|"
	r, _ = regexp.Compile("del\\([0-9]*\\)")
	s = r.FindString(ctlparms)
	s = strings.Trim(s, "del(")
	s = strings.Trim(s, ")")
	i, _ := strconv.Atoi(s)
	delimiter := string(i)

	// find the working tmp directory
	ss := strings.Split(ctlparms, "W(")
	wDir := ss[1]
	wDir = strings.Trim(wDir, ")")
	wDir = strings.Replace(wDir, "\\", `/`, -1)

	// ctlStrNew contains field #|data type|order|field #(if any for dupo)
	return ctlStrNew, duptype, wDir, delimiter
}

