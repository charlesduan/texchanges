#!/usr/bin/env ruby

require 'zip'
require 'nokogiri'
require 'set'
require 'forwardable'
require 'diff/lcs'
require 'colorize'

class Range
  def +(num)
    if num.is_a?(Integer)
      return Range.new(self.begin + num, self.end + num, self.exclude_end?)
    else
      super(num)
    end
  end

  def -(num)
    return self + (-num)
  end
end

########################################################################
#
# A string with metadata or insertions indexed as part of the string. An
# IndexedString is made up of a string and a list of positioned marks, stored as
# a two-dimensional array where the elements of the top-level array are
# two-element arrays containing the mark object and the position.
#
class IndexedString
  extend Forwardable

  # @str is the string; @indexes is a hash mapping Range objects to lists of
  # marks.
  def initialize
    @str = ""
    @indexes = {}
  end

  def_delegators :@str, :[], :end_with?, :length

  attr_accessor :indexes, :end_marks

  def each
    current = 0
    each_mark do |range, marks|
      yield(@str[current...range.first], marks, @str[range])
      current = range.first
    end
    if current < @str.length - 1
      yield(@str[current..-1], [], "")
    end
  end

  def each_mark
    @indexes.keys.sort { |x, y|
      res = x.first <=> y.first
      0 == res ? (x.last <=> y.last) : res
    }.each do |range|
      marks = @indexes[range]
      yield(range, marks)
    end
  end

  def <<(str)
    if str.is_a?(IndexedString)
      cur_pos = @str.length
      str.indexes.each do |range, objs|
        new_range = range + cur_pos
        if @indexes[new_range]
          @indexes[new_range].concat(objs)
        else
          @indexes[new_range] = objs.dup
        end
      end
    end
    @str << str.to_s
    return self
  end

  def space
    @str << ' ' unless @str.end_with?(' ')
    return self
  end

  def mark(obj)
    pos = @str.length
    (@indexes[pos...pos] ||= []).push(obj)
    return self
  end

  def mark_at(pos, obj)
    raise "Invalid position" if pos < 0 or pos > @str.length
    (@indexes[pos...pos] ||= []).push(obj)
  end

  def mark_range(obj)
    start_pos = @str.length
    yield
    stop_pos = @str.length
    (@indexes[start_pos...stop_pos] ||= []).push(obj)
  end

  def to_s
    @str
  end

end


########################################################################
#
# A Token is a positioned word in a string. The object records the text of the
# word and the numeric position of the word in the string.
#
# Tokens are stored in an array of an NgramTokenizer, but they also form a
# doubly linked list to simplify iterating forwards and backwards.
#
class Token
  def initialize(word, pos)
    @word = word
    @pos = pos
    raise "Invalid token pos #{pos}" unless pos.is_a?(Integer)
  end

  def inspect
    "#<#@word@#@pos>"
  end
  def to_s
    "#<#@word@#@pos>"
  end

  attr_accessor :next, :prev, :word, :pos

  def link_next(next_token)
    self.next = next_token
    next_token.prev = self
    return self
  end

  def link_prev(prev_token)
    prev_token.link_next(self)
    return self
  end

  def ngram(n)
    res = []
    cur = self
    n.times do
      res.push(cur)
      cur = cur.next
      break if cur.nil?
    end
    return res
  end

  def end_pos
    @pos + @word.length - 1
  end

  def ==(other)
    other.is_a?(Token) and other.word == self.word
  end

  alias eql? ==

  def hash
    word.hash
  end

  def array(to)
    cur = self
    res = []
    loop do
      res.push(cur)
      return res if cur.equal?(to)
      cur = cur.next
      raise "Token #{to} not found as successor to #{self}" unless cur
    end
  end

  def covers?(a_pos)
    a_pos >= @pos && (@next.nil? || a_pos < @next.pos)
  end

  def bsearch_covers?(a_pos)
    @next.nil? || a_pos < @next.pos
  end


end



########################################################################
#
# Separates a string into an array of space-delimited tokens, for purposes of
# assembling ngrams.
#
class NgramTokenizer

  def initialize(str)
    @str = str
    @tokens = []
    tokenize
  end

  attr_accessor :str, :tokens

  def tokenize
    current = 0
    str = @str
    len = str.length
    while current < len && m = /\s+/.match(str, current)
      add_token(str[current...m.offset(0).first], current)
      current = m.offset(0).last
    end
    add_token(current...len, current) if len < current
  end

  def add_token(word, pos)
    t = Token.new(word, pos)
    if @tokens.last
      t.prev = @tokens.last
      @tokens.last.next = t
    end
    @tokens.push(t)
  end

  def pad_tokens(n)
    (n - 1).times do
      @tokens.unshift(Token.new(nil, -1).link_next(@tokens.first))
      @tokens.push(Token.new(nil, @str.length + 1).link_prev(@tokens.last))
    end
  end

  def token_at(pos)
    raise "Invalid position #{pos}" unless pos.is_a?(Integer)
    return @tokens.bsearch { |t| t.bsearch_covers?(pos) }
  end

  def make_ngrams(n)
    @tokens.each_cons(n) do |cons|
      yield(cons)
    end
  end

end


########################################################################
#
# Parses and manages the parts of a Word document.
#
class WordFile
  def parse_file(name)
    return Nokogiri::XML(
      @zip.entries.find { |x| x.name == "word/#{name}.xml" }.get_input_stream
    )
  end

  attr_accessor :document_string, :tokenizer, :document, :footnotes, :endnotes,
    :comments

  def initialize(filename)
    @filename = filename
    @zip = Zip::File.open(filename)
    @document = parse_file('document')
    @footnotes = parse_file('footnotes')
    @endnotes = parse_file('endnotes')
    @comments = parse_file('comments')

    @document_string = EditFinder.new(self).parse
  end

  def tokenize_document(ngram_size)
    @tokenizer = NgramTokenizer.new(@document_string.to_s)
    @tokenizer.pad_tokens(ngram_size)
  end

  def each_edit
    @document_string.each_mark do |range, marks|
      yield(WordEdit.new(self, range, marks))
    end
  end

end

########################################################################
#
# Represents an edit to the Word document, providing the contextual information
# necessary to enable matching and reporting on this edit.
#
class WordEdit
  def initialize(word_file, range, marks)
    @word_file, @range, @marks = word_file, range, marks
    @token = @word_file.tokenizer.token_at(range.begin)
    @etoken = @word_file.tokenizer.token_at(range.end)
    @pre_edit, @post_edit = EditInterpreter.new(word_file).parse_multiple(marks)
  end

  def edit_id
    @marks[0]['w:id']
  end

  attr_reader :word_file, :range, :marks, :token, :etoken, :pre_edit, :post_edit

  def context_string(t = nil, et = nil)
    unless (t && et)
      t, et = @token, @etoken
      10.times do
        t = t.prev if t.prev && !t.prev.word.nil?
        et = et.next if et.next && !et.next.word.nil?
      end
    end
    text = @word_file.document_string[t.pos .. et.end_pos]
    offset_range = @range - t.pos
    if @pre_edit.nil?
      text[offset_range] = "-<<#{text[offset_range]}>>-"
    else
      text[offset_range] = "+<<#@pre_edit#{text[offset_range]}#@post_edit>>+"
    end
    return text
  end
end




########################################################################
#
# An abstract class for parsing the XML of a Word document.
#
class DocxParser

  def initialize(word_file)
    @word_file = word_file
  end

  IGNORE_TAGS = Set[
    'annotationRef',
    'commentRangeStart',
    'commentRangeEnd',
    'moveFromRangeStart',
    'moveFromRangeEnd',
    'moveToRangeStart',
    'moveToRangeEnd',
    'footnoteRef',
    'rPr',
    'pPr',
    'sectPr',
    'proofErr',
    'fldChar',
    'instrText',
    'delInstrText',
    'bookmarkStart',
    'bookmarkEnd',
    'lastRenderedPageBreak',
  ]

  PASS_TAGS = Set[
    'hyperlink',
    'footnotes',
    'body',
  ]

  def process(node)
    if respond_to?("proc_#{node.name}")
      return send("proc_#{node.name}", node)
    elsif PASS_TAGS.include?(node.name)
      process_children(node)
    elsif IGNORE_TAGS.include?(node.name)
    else
      warn("#{node.name}: no method for processing this node")
    end
    return nil
  end

  def process_children(node)
    node.children.each do |n|
      process(n)
    end
  end

end

########################################################################
#
# Parses a Word document to look for edits.
#
class EditFinder < DocxParser

  def parse
    @footnote_list = {}
    process(@word_file.footnotes.at_xpath('//w:footnotes'))
    @current_string = IndexedString.new
    process(@word_file.document.at_xpath('//w:body'))
    return @current_string
  end

  def mark_edit(edit)
    @current_string.mark(edit)
  end

  def proc_footnote(node)
    if node['w:type'].nil? or node['w:type'] == 'normal'
      num = node['w:id']
      @current_string = IndexedString.new
      process_children(node)
      @footnote_list[num] = @current_string
    end
  end

  def proc_p(node)

    ins = node.at_xpath('./w:pPr/w:rPr/w:ins|./w:pPr/w:rPr/w:moveTo')
    del = node.at_xpath('./w:pPr/w:rPr/w:del|./w:pPr/w:rPr/w:moveFrom')
    chg = node.at_xpath('./w:pPr/w:pPrChange')
    # Ignoring rPrChange in a paragraph mark (./w:pPr/w:rPr/w:rPrChange) because
    # TeX doesn't care about formatting of paragraph marks

    if chg
      @current_string.mark_range(chg) do
        process_children(node)
      end
    else
      process_children(node)
    end

    if ins
      mark_edit(ins)
      @current_string.space
    elsif del
      @current_string.mark_range(del) do
        @current_string.space
        @current_string << '\\par '
      end
    else
      @current_string.space
      @current_string << '\\par '
    end
  end

  def proc_r(node)
    chg = node.at_xpath('./w:rPr/w:rPrChange')
    if chg
      @current_string.mark_range(chg) do
        process_children(node)
      end
    else
      process_children(node)
    end
  end

  def proc_br(node)
    @current_string.space << " \\break "
  end

  def proc_t(node)
    @current_string << node.content
  end

  def proc_tab(node)
    @current_string.space
  end

  def proc_del(node)
    @current_string.mark_range(node) do
      process_children(node)
    end
  end

  def proc_delText(node)
    @current_string << node.content
  end

  def proc_moveFrom(node)
    @current_string.mark_range(node) do
      process_children(node)
    end
  end

  def proc_ins(node)
    mark_edit(node)
  end

  def proc_moveTo(node)
    mark_edit(node)
  end

  def proc_commentReference(node)
    mark_edit(node)
  end

  def proc_footnoteReference(node)
    note_text = @footnote_list[node['w:id']]
    if note_text
      @current_string.space << note_text
    else
      warn("footnoteReference: no corresponding note text found")
    end
  end

end

########################################################################
#
# Parses an edit node in a Word document to determine what the edit does.
#
class EditInterpreter < DocxParser

  def parse_multiple(edits)
    all_pre, all_post = "", ""
    edits.each do |edit|
      pre, post = parse(edit)
      return nil, nil if pre.nil?
      all_pre += pre
      all_post = post + all_post
    end
    return all_pre, all_post
  end

  def parse(edit)
    @current_string = ""

    case edit.name
    when 'ins', 'moveTo'
      if edit.at_xpath('./parent::w:rPr/parent::w:pPr')
        return " \\par ", ''
      else
        process(edit)
        return @current_string, ''
      end

    when 'del', 'moveFrom'
      return nil, nil

    when 'commentReference'
      process(edit)
      return @current_string, ''
    when 'rPrChange'
      rPr = edit.at_xpath('./parent::w:rPr')
      raise "Misplaced rPrChange #{edit.parent}" unless rPr
      return read_properties(rPr)
    when 'pPrChange'
      pPr = edit.at_xpath('./parent::w:pPr')
      raise "Misplaced rPrChange #{edit}" unless pPr
      return read_properties(pPr)
    end
  end

  IGNORE_PROPERTIES = Set[
    # pPr elements
    'keepNext', 'keepLines', 'pageBreakBefore', 'widowControl', 'pBdr', 'shd',
    'tabs', 'suppressAutoHyphens', 'kinsoku', 'wordWrap', 'overflowPunct',
    'topLinePunct', 'autoSpaceDE', 'autoSpaceDN', 'bidi', 'adjustRightInd',
    'snapToGrid', 'spacing', 'ind', 'contextualSpacing', 'mirrorIndents',
    'suppressOverlap', 'jc', 'textDirection', 'textAlignment',
    'textboxTightWrap', 'divId', 'cnfStyle', 'pPrChange', 'rPr',
    # rPr elements
    'rFonts', 'bCs', 'iCs', 'outline', 'shadow', 'emboss', 'imprint', 'noProof',
    'snapToGrid', 'color', 'spacing', 'w', 'kern', 'szCs', 'highlight',
    'effect', 'bdr', 'shd', 'fitText', 'rtl', 'cs', 'lang', 'eastAsianLayout',
    'specVanish', 'oMath', 'rPrChange', 'sz',
  ]
  PROPERTIES = {
    'b' => %w(\textbf{ }),
    'i' => %w(\emph{ }),
    'caps' => %w(\MakeUppercase{ }),
    'smallCaps' => %w(\textsc{ }),
    'u' => %w(\emph{ }),
  }

  IGNORE_STYLES = %w(
    Footnote
    FootnoteReference
    FootnoteText
    CommentText
    CommentReference
    Hyperlink
  )

  STYLES = {
    'textit' => %w(\emph{ }),
    'Emphasis' => %w(\emph{ }),
    'textbf' => %w(\textbf{ }),
    'textsc' => %w(\textsc{ }),
  }

  def read_properties(node)
    notes, adds = [], []
    node.children.reject { |x|
      IGNORE_PROPERTIES.include?(x.name)
    }.each do |x|
      if PROPERTIES[x.name]
        adds.push(PROPERTIES[x.name])
      elsif %w(rStyle pStyle).include?(x.name) && STYLES.include?(x['w:val'])
        adds.push(STYLES[x['w:val']]) unless adds.include?(STYLES[x['w:val']])
      elsif %w(rStyle pStyle).include?(x.name) &&
        IGNORE_STYLES.include?(x['w:val'])
      else
        notes.push(x.to_s)
      end
    end
    res, trail = "", ""
    res, trail = adds.transpose.map { |x| x.join } unless adds.empty?
    unless notes.empty?
      res = "%\n% Unprocessed edits:\n" + notes.map { |x|
        "%  #{x}\n"
      }.join + res
      trail += "% end of edits\n"
    end
    return [ res, trail ]
  end

  TEX_CONVERTS = {
    "“" => "``",
    "”" => "''",
    "‘" => "`",
    "’" => "'",
    "–" => "--",
    "—" => "---",
    "~" => "\\textasciitilde ",
    "\\" => "\\textbackslash ",
    "%" => "\\%",
    "{" => "\\{",
    "}" => "\\}",
    "#" => "\\#",
    "$" => "\\$",
    "&" => "\\&",
    "_" => "\\_",
    "^" => "\\^{}",
  }
  def tex_escape(text)
    TEX_CONVERTS.each do |from, to|
      text = text.gsub(from, to)
    end
    return text
  end

  def remove_trailing_par
    @current_string.sub!(/\s*\\par\s*\z/, '')
  end

  def proc_ins(node)
    process_children(node)
  end

  def proc_del(node)
  end

  def proc_moveFrom(node)
    proc_del(node)
  end

  def proc_moveTo(node)
    proc_ins(node)
  end

  def proc_commentReference(node)
    comment_id = node['w:id']
    @current_string << "\\comment{"
    process_children(@word_file.comments.at_xpath(
      '//w:comment[@w:id=$id]', nil, :id => comment_id
    ))
    remove_trailing_par
    @current_string << "}"
  end

  def proc_footnoteReference(node)
    note_id = node['w:id']
    str = @current_string
    @current_string = ""
    process_children(@word_file.footnotes.at_xpath(
      '//w:footnote[@w:id=$id]', nil, :id => note_id
    ))
    @current_string.strip!
    remove_trailing_par
    str << "\\footnote{#{@current_string}}"
    @current_string = str
  end

  def proc_p(node)
    pPr = node.at_xpath('./w:pPr')
    if pPr
      properties, trail = read_properties(pPr)
      @current_string << properties
      process_children(node)
      @current_string << trail
    else
      process_children(node)
    end
    remove_trailing_par
    @current_string << '\\par '
  end


  def proc_r(node)
    rPr = node.at_xpath('./w:rPr')
    if rPr
      properties, trail = read_properties(rPr)
      @current_string << properties
      process_children(node)
      @current_string << trail
    else
      process_children(node)
    end
  end

  def proc_br(node)
    @current_string.space << " \\break "
  end

  def proc_t(node)
    @current_string << tex_escape(node.content)
  end

  def proc_tab(node)
    @current_string.space
  end

end

########################################################################
#
# Represents a TeX file that contains text mirroring the Word document.
#
class TeXFile
  def initialize(file)
    @file = file
    @parsed_text = IndexedString.new
    @edited = false
    parse
  end

  attr_accessor :file, :parsed_text, :tokenizer
  attr_accessor :edited

  BRACE_RE = /(?<brace>\{(?:[^{}]|\g<brace>)*\})/
  TEX_BOUNDARY = /(?:\{|\}|\\[A-Za-z]+\b\s*|(?<!\\)%.*\n)+/

  def parse
    text = File.open(@file) { |io| io.read }.gsub(/^\s*$/, '\\par')

    while m = TEX_BOUNDARY.match(text)
      @parsed_text << m.pre_match
      if m.to_s =~ /\\(?:footnote|note|cn)\b/
        @parsed_text.mark("START DELETE")
        @parsed_text << ' '
        @parsed_text.mark("END DELETE")
      end
      @parsed_text.mark(m.to_s)
      text = m.post_match
    end
    @parsed_text << text
  end

  def tokenize
    @tokenizer = NgramTokenizer.new(@parsed_text.to_s)
  end

  def write(new_filename)
    text = ""
    delete_count = 0
    @parsed_text.each do |str, marks, text_range|
      raise "Not expecting text range in TeX file" unless text_range.empty?
      text << (str) if delete_count <= 0
      marks.each do |mark|
        case mark
        when "START DELETE" then delete_count += 1
        when "END DELETE"   then delete_count -= 1
        when /\AINSERT /    then text << $'
        else                     text << mark if delete_count <= 0
        end
      end
    end
    text.gsub!(/\s*(?:\\par\s+)+/, "\n\n")
    File.open(new_filename, 'w') do |io|
      io.write(text)
    end
  end

end

########################################################################
#
# A data structure for representing a match between an input file (the Word
# document) and an output file (the TeX file), where the text of the Word
# document between the start and end input tokens is similar to the text between
# the start and end output tokens.
#
class TokenMatch
  attr_accessor :word_start_token, :word_end_token, :tex_start_token,
    :tex_end_token, :tex_file

  def set_start(input, output, file)
    raise "set_end: expected Token" unless input.is_a?(Token)
    raise "set_end: expected Token" unless output.is_a?(Token)
    @word_start_token, @tex_start_token, @tex_file = input, output,
      file
    return true
  end
  def set_end(input, output, file)
    raise "set_end: expected Token" unless input.is_a?(Token)
    raise "set_end: expected Token" unless output.is_a?(Token)
    return false unless file == @tex_file
    return false unless input.pos >= @word_start_token.pos
    return false unless output.pos >= @tex_start_token.pos
    @word_end_token, @tex_end_token = input, output
    return true
  end

  def word_range
    return (word_start_token.pos) .. (word_end_token.end_pos)
  end

  def word_array
    return @word_start_token.array(word_end_token)
  end

  def modify_input(text, range)
    context = text[@word_start_token.pos .. @word_end_token.end_pos]
    offset_range = range - @word_start_token.pos
    context[offset_range] = yield(context[offset_range])
    return context
  end

  def tex_range
    return (tex_start_token.pos) .. (tex_end_token.end_pos)
  end

  def tex_array
    return tex_start_token.array(tex_end_token)
  end

  def match_pos(diff, pos)
    i = diff.find_index { |x|
      x.old_element && x.old_element.covers?(pos)
    }
    if diff[i].action == '='
      return diff[i].new_element.pos + pos - diff[i].old_element.pos
    else
      i -= 1 until i <= 0 || diff[i].action == '='
      return diff[i].new_element.next
    end
  end


  def match_range(start_pos, stop_pos)
    diff = Diff::LCS.sdiff(word_array, tex_array)
    start = match_pos(diff, start_pos)
    return start if start.is_a?(Token)

    if stop_pos.nil? or stop_pos == start_pos
      return start ... start
    else
      stop = match_pos(diff, stop_pos)
      return stop if stop.is_a?(Token)
      return start ... stop
    end
  end
end


########################################################################
#
# Collects ngrams from TeX files and then matches a Word document against them.
class TextMatcher
  def initialize(size)
    @ngrams = {}
    @ngram_size = 5
  end

  def input(tex_file)
    tokenizer = tex_file.tokenizer
    tokenizer.pad_tokens(@ngram_size)
    tokenizer.make_ngrams(@ngram_size) do |ngram|
      (@ngrams[ngram] ||= []).push([ tex_file, ngram ])
    end
  end

  def match_search(token, iterator)
    token = token.send(iterator)
    50.times do
      ngram = token.ngram(@ngram_size)
      if @ngrams.include?(ngram) && @ngrams[ngram].size == 1
        file, new_ngram = @ngrams[ngram].first
        return true if yield(ngram, new_ngram, file)
      end
      token = token.send(iterator)
      break unless token
    end
    return false
  end

  def match(word_edit)
    tm = TokenMatch.new
    return nil unless match_search(word_edit.token, :prev) do |n1, n2, file|
      tm.set_start(n1.first, n2.first, file)
    end

    return nil unless match_search(word_edit.etoken, :next) do |n1, n2, file|
      tm.set_end(n1.last, n2.last, file)
    end

    range = tm.match_range(word_edit.range.begin, word_edit.range.end)
    return TeXEdit.new(word_edit, tm, range)
  end

end

class TeXEdit
  def initialize(word_edit, token_match, range)
    @word_edit, @token_match, @range = word_edit, token_match, range
    @file = @token_match.tex_file
  end

  def show_range_edit(pre, post)
    context_range = @token_match.tex_range
    text = @token_match.tex_file.parsed_text[context_range]
    offset_range = @range - context_range.begin
    if pre.nil?
      text[offset_range] = "-<#{text[offset_range]}>-"
    else
      text[offset_range] = "+<#{pre}#{text[offset_range]}#{post}>+"
    end
    text
  end

  def show_token_edit
    context_range = @token_match.tex_range
    text = @token_match.tex_file.parsed_text[context_range]
    offset = @range.pos - context_range.begin
    text[offset...offset] = "<<EDIT>>"
    return text
  end


  def explain_edit
    text = "WEDIT#{@word_edit.edit_id}: #{@token_match.tex_file.file}\n"
    case @range
    when Token
      return text + "Edit approximately here:\n\n" + show_token_edit +
        "\n\nOriginal word edit was:\n\n" +
        @word_edit.context_string(@token_match.word_start_token,
                                 @token_match.word_end_token)
    when Range
      return text + "Edit as follows:\n\n" +
        show_range_edit(@word_edit.pre_edit, @word_edit.post_edit) +
        "\n\nOriginal word edit was:\n\n" +
        @word_edit.context_string(@token_match.word_start_token,
                                 @token_match.word_end_token)
    else
      raise "Unexpected TeXEdit range #{tm}"
    end
  end

  def do_edit
    @token_match.tex_file.edited = true
    case @range
    when Token then do_approx_edit
    when Range then do_exact_edit
    else raise "Unexpected TeXEdit range #{tm}"
    end
  end

  def do_exact_edit
    tex_text = @token_match.tex_file.parsed_text
    comment_pos = @range.begin
    comment_pos -= 1 until 0 == comment_pos or tex_text[comment_pos - 1] == "\n"
    tex_text.mark_at(comment_pos, "% WEDIT#{@word_edit.edit_id}\n")

    if @word_edit.pre_edit.nil?
      tex_text.mark_at(@range.begin, "START DELETE")
      tex_text.mark_at(@range.end, "END DELETE")
    else
      tex_text.mark_at(
        @range.begin, "INSERT " + @word_edit.pre_edit
      )
      tex_text.mark_at(
        @range.end, "INSERT " + @word_edit.post_edit
      )
    end
  end

  def do_approx_edit
    token = @range
    indexed_string = @token_match.tex_file.parsed_text
    tex_text = @token_match.tex_file.parsed_text
    comment_pos = token.pos
    comment_pos -= 1 until 0 == comment_pos or tex_text[comment_pos - 1] == "\n"
    word_context = @word_edit.context_string(
      @token_match.word_start_token, @token_match.word_end_token
    )
    word_context.gsub(/\s*\\par\s*\z/, "\n\n")

    tex_text.mark_at(
      comment_pos,
      "%\n% WEDIT#{@word_edit.edit_id}\n" +
      "% Approximately here, edit as follows:\n" +
      wrap_lines(word_context, 72, "%   ") + "%\n"
    )

  end

end





########################################################################
#
# MAIN PROGRAM
#

def wrap_lines(text, width = 80, prefix = "")
  text.gsub(
    /(.{1,#{width}})( +|$\n?)|(\S{#{width},})( +|$\n?)/,
    "#{prefix}\\1\\3\n"
  )
end

word_file, *tex_files = *ARGV

word_file = WordFile.new(word_file)
word_file.tokenize_document(5)

text_matcher = TextMatcher.new(5)
tex_files = tex_files.map do |file|
  f = TeXFile.new(file)
  f.tokenize
  text_matcher.input(f)
  f
end

ei = EditInterpreter.new(word_file)

word_file.each_edit do |word_edit|
  next if word_edit.pre_edit == '' && word_edit.post_edit == ''
  tex_edit = text_matcher.match(word_edit)

  if tex_edit
    tex_edit.do_edit
    puts wrap_lines(tex_edit.explain_edit)
  else
    puts wrap_lines("Could not match edit:\n\n#{word_edit.context_string}")
  end

    puts "----------"
    puts

end


tex_files.each do |file|
  name = file.file
  next unless file.edited
  file.write(File.join(File.dirname(name), "new-" + File.basename(name)))
end


