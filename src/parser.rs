use std::ascii::AsciiExt;
use std::char;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::error::Error;
use std::fmt;
use std::str;

use Array as TomlArray;
use Table as TomlTable;
use Value::{self, Array, Table, Float, Integer, Boolean, Datetime};

macro_rules! try {
    ($e:expr) => (match $e { Some(s) => s, None => return None })
}

pub trait ShowType {
    fn type_str(&self) -> &'static str;
}

// T is the table type
// A is the array type
// V is the variant type for possible values
// W is for the whitespace
pub trait Builder
    where Self::Key: fmt::Display,
          Self::Value: ShowType {
    type Table;
    type Array;
    type Key;
    type Value;

    fn table(lead_ws: &str) -> Self::Table;
    fn array(vals: Vec<Self::Value>, lead_ws: &str) -> Self::Array;
    fn key(val: String, lead_ws: &str) -> Self::Key;
    fn value_string(parsed: String, raw: &str, lead_ws: &str) -> Self::Value;
    fn value_integer(parsed: i64, raw: &str, lead_ws: &str) -> Self::Value;
    fn value_float(parsed: f64, raw: &str, lead_ws: &str) -> Self::Value;
    fn value_boolean(parsed: bool, raw: &str, lead_ws: &str) -> Self::Value;
    fn value_datetime(parsed: String, raw: &str, lead_ws: &str) -> Self::Value;
    fn value_array(parsed: Self::Array, raw: &str, lead_ws: &str) -> Self::Value;
    fn value_table(parsed: Self::Table, raw: &str, lead_ws: &str) -> Self::Value;
    // If table doesn't contain key, adds value and returns true.
    // If table contains key returns false.
    fn insert(t: &mut Self::Table, key: Self::Key, value: Self::Value) -> bool;
    fn insert_container<'b>(t: &'b mut Self::Table, keys: &[String],
                            key_lo: usize, key_hi: usize)
        -> Result<&'b mut Self::Table, ParserError>;
    fn get_table<'b>(&'b mut Self::Table, &'b str) -> Option<&'b mut Self::Table>;
    fn get_array<'b>(&'b mut Self::Table, &'b str) -> Option<&'b mut Self::Array>;
    fn contains_table(&Self::Table) -> bool;
    // Moves all (key, value) pairs from `from` into `into` table.
    // Returns Err(String) if the key already exists in the `into` table.
    fn merge(into: &mut Self::Table, from: Self::Table) -> Result<(), String>;
    // Returns Err(&str) if the if the array is of a different type.
    // &str returned by the error conditions is the type_str() of the array
    fn push<'b>(&'b mut Self::Array, Self::Value) -> Result<(), &'b str>;
}

struct SimpleBuilder;
impl ShowType for Value {
    fn type_str(&self) -> &'static str { self.type_str() }
}

impl Builder for SimpleBuilder {
    type Table = TomlTable;
    type Array = TomlArray;
    type Key = String;
    type Value = Value;

    fn table(lead_ws: &str)-> TomlTable { BTreeMap::new() }
    fn array(vals: Vec<Value>, lead_ws: &str) -> TomlArray { vals }
    fn key(val: String, lead_ws: &str) -> String { val.to_string() }
    fn value_string(parsed: String, raw: &str, lead_ws: &str) -> Value { Value::String(parsed) }
    fn value_integer(parsed: i64, raw: &str, lead_ws: &str) -> Value { Integer(parsed) }
    fn value_float(parsed: f64, raw: &str, lead_ws: &str) -> Value { Float(parsed) }
    fn value_boolean(parsed: bool, raw: &str, lead_ws: &str) -> Value { Boolean(parsed) }
    fn value_datetime(parsed: String, raw: &str, lead_ws: &str) -> Value { Datetime(parsed) }
    fn value_array(parsed: TomlArray, raw: &str, lead_ws: &str) -> Value { Array(parsed) }
    fn value_table(parsed: TomlTable, raw: &str, lead_ws: &str) -> Value { Table(parsed) }
    fn insert(table: &mut TomlTable, key: String, v: Value) -> bool {
        match table.entry(key) {
            Entry::Vacant(entry) => { entry.insert(v); true }
            Entry::Occupied(_) => false
        }
    }
    fn insert_container<'b>(mut cur: &'b mut TomlTable, keys: &[String],
                            key_lo: usize, key_hi: usize)
        -> Result<&'b mut TomlTable, ParserError> {
        for part in keys {
            let tmp = cur;

            if tmp.contains_key(part) {
                match *tmp.get_mut(part).unwrap() {
                    Table(ref mut table) => {
                        cur = table;
                        continue
                    }
                    Array(ref mut array) => {
                        match array.last_mut() {
                            Some(&mut Table(ref mut table)) => cur = table,
                            _ => {
                                return Err(ParserError { // TODO: create real errors
                                    lo: key_lo,
                                    hi: key_hi,
                                    desc: format!("array `{}` does not contain \
                                                   tables", part)
                                });
                            }
                        }
                        continue
                    }
                    _ => {
                        return Err(ParserError { // TODO: create real errors
                            lo: key_lo,
                            hi: key_hi,
                            desc: format!("key `{}` was not previously a table",
                                          part)
                        });
                    }
                }
            }

            // Initialize an empty table as part of this sub-key
            tmp.insert(part.clone(), Table(BTreeMap::new()));
            match *tmp.get_mut(part).unwrap() {
                Table(ref mut inner) => cur = inner,
                _ => unreachable!(),
            }
        }
        Ok(cur)
    }
    fn get_table<'b>(t: &'b mut TomlTable, key: &'b str) -> Option<&'b mut TomlTable> { 
        t.get_mut(key).and_then(|x| match x { &mut Value::Table(ref mut s) => Some(s), _ => None })
    }
    fn get_array<'b>(t: &'b mut TomlTable, key: &'b str) -> Option<&'b mut TomlArray>{ 
        t.get_mut(key).and_then(|x| match x { &mut Value::Array(ref mut s) => Some(s), _ => None })
    }
    fn contains_table(t: &TomlTable) -> bool {
        t.values().any(|v| v.as_table().is_some())
    }
    fn merge(table: &mut TomlTable, value: TomlTable) -> Result<(), String> {
        for (k, v) in value.into_iter() {
            if table.insert(k.clone(), v).is_some() {
                return Err(k);
            }
        }
        Ok(())
    }
    fn push<'b>(vec: &'b mut TomlArray, value: Value) -> Result<(), &'b str> {
        match vec.first() {
            Some(ref v) if !v.same_type(&value) => return Err(v.type_str()),
            _ => {}
        }
        vec.push(value);
        Ok(())
    }
}

/// Parser for converting a string to a TOML `Value` instance.
///
/// This parser contains the string slice that is being parsed, and exports the
/// list of errors which have occurred during parsing.
pub struct Parser<'a> {
    input: &'a str,
    /// A list of all errors which have occurred during parsing.
    ///
    /// Not all parse errors are fatal, so this list is added to as much as
    /// possible without aborting parsing. If `None` is returned by `parse`, it
    /// is guaranteed that this list is not empty.
    pub errors: Vec<ParserError>,
}

pub struct ParseSession<'a, B:Builder> {
    input: &'a str,
    cur: str::CharIndices<'a>,
    pub errors: Vec<ParserError>,
    builder: B
}

/// A structure representing a parse error.
///
/// The data in this structure can be used to trace back to the original cause
/// of the error in order to provide diagnostics about parse errors.
#[derive(Debug)]
pub struct ParserError {
    /// The low byte at which this error is pointing at.
    pub lo: usize,
    /// One byte beyond the last character at which this error is pointing at.
    pub hi: usize,
    /// A human-readable description explaining what the error is.
    pub desc: String,
}

impl<'a> Parser<'a> {
    /// Creates a new parser for a string.
    ///
    /// The parser can be executed by invoking the `parse` method.
    ///
    /// # Example
    ///
    /// ```
    /// let toml = r#"
    ///     [test]
    ///     foo = "bar"
    /// "#;
    ///
    /// let mut parser = toml::Parser::new(toml);
    /// match parser.parse() {
    ///     Some(value) => println!("found toml: {:?}", value),
    ///     None => {
    ///         println!("parse errors: {:?}", parser.errors);
    ///     }
    /// }
    /// ```
    pub fn new(s: &'a str) -> Parser<'a> {
        Parser {
            input:s,
            errors: Vec::new()
        }
    }
    
    /// Converts a byte offset from an error message to a (line, column) pair
    ///
    /// All indexes are 0-based.
    pub fn to_linecol(&self, offset: usize) -> (usize, usize) {
        let mut cur = 0;
        for (i, line) in self.input.lines().enumerate() {
            if cur + line.len() > offset {
                return (i, offset - cur)
            }
            cur += line.len() + 1;
        }
        return (self.input.lines().count(), 0)
    }

    pub fn parse(&mut self) -> Option<TomlTable> {
        let mut builder = ParseSession::<SimpleBuilder>::new(self.input, SimpleBuilder);
        let ret = builder.parse();
        self.errors = builder.errors;
        return ret;
    }
}

impl<'a, B:Builder> ParseSession<'a, B> {
    pub fn new(s: &'a str, b: B) -> ParseSession<'a, B> {
        ParseSession {
            input: s,
            cur: s.char_indices(),
            errors: Vec::new(),
            builder: b
        }
    }

    fn next_pos(&self) -> usize {
        self.cur.clone().next().map(|p| p.0).unwrap_or(self.input.len())
    }

    // Returns true and consumes the next character if it matches `ch`,
    // otherwise do nothing and return false
    fn eat(&mut self, ch: char) -> bool {
        match self.peek(0) {
            Some((_, c)) if c == ch => { self.cur.next(); true }
            Some(_) | None => false,
        }
    }

    // Peeks ahead `n` characters
    fn peek(&self, n: usize) -> Option<(usize, char)> {
        self.cur.clone().skip(n).next()
    }

    fn expect(&mut self, ch: char) -> bool {
        if self.eat(ch) { return true }
        let mut it = self.cur.clone();
        let lo = it.next().map(|p| p.0).unwrap_or(self.input.len());
        let hi = it.next().map(|p| p.0).unwrap_or(self.input.len());
        self.errors.push(ParserError {
            lo: lo,
            hi: hi,
            desc: match self.cur.clone().next() {
                Some((_, c)) => format!("expected `{}`, but found `{}`", ch, c),
                None => format!("expected `{}`, but found eof", ch)
            }
        });
        false
    }

    // Consumes whitespace ('\t' and ' ') until another character (or EOF) is
    // reached. Returns if any whitespace was consumed
    fn ws(&mut self) -> bool {
        let mut ret = false;
        loop {
            match self.peek(0) {
                Some((_, '\t')) |
                Some((_, ' ')) => { self.cur.next(); ret = true; }
                _ => break,
            }
        }
        ret
    }

    // Consumes the rest of the line after a comment character
    fn comment(&mut self) -> bool {
        if !self.eat('#') { return false }
        for (_, ch) in self.cur.by_ref() {
            if ch == '\n' { break }
        }
        true
    }

    // Consumes a newline if one is next
    fn newline(&mut self) -> bool {
        match self.peek(0) {
            Some((_, '\n')) => { self.cur.next(); true }
            Some((_, '\r')) if self.peek(1).map(|c| c.1) == Some('\n') => {
                self.cur.next(); self.cur.next(); true
            }
            _ => false
        }
    }

    pub fn parse(&mut self) -> Option<B::Table> {
        let mut ret = None;
        while self.peek(0).is_some() {
            let pre_ws_start = self.next_pos();
            self.ws();
            if self.newline() { continue }
            if self.comment() { continue }
            let pre_ws_end = self.next_pos();
            if self.eat('[') {
                if ret.is_none() { ret = Some(B::table(&self.input[0..pre_ws_end])) }
                let array = self.eat('[');

                // Parse the name of the section
                let mut keys = Vec::new();
                let mut keys_end;
                loop {
                    self.ws();
                    match self.key_name() {
                        Some(s) => keys.push(s),
                        None => {}
                    }
                    self.ws();
                    if self.eat(']') {
                        if array && !self.expect(']') { return None }
                        keys_end = self.next_pos();
                        break
                    }
                    if !self.expect('.') { return None }
                }
                if keys.len() == 0 { return None }

                // Build the section table
                let mut table = B::table(&self.input[pre_ws_start..pre_ws_end]);
                if !self.values(&mut table) { return None }
                if array {
                    self.insert_array(ret.as_mut().unwrap(), keys,
                                      B::value_table(table, "", ""), pre_ws_end, keys_end)
                } else {
                    self.insert_table(ret.as_mut().unwrap(), keys, table, pre_ws_end, keys_end)
                }
            } else {
                if ret.is_none() { ret = Some(B::table(&self.input[0..pre_ws_end])) }
                if !self.values(ret.as_mut().unwrap()) { return None }
            }
        }
        if self.errors.len() > 0 {
            None
        } else {
            if ret.is_none() { ret = Some(B::table(self.input)) }
            ret
        }
    }

    // Parse a single key name starting at `start`
    fn key_name(&mut self) -> Option<String> {
        let start = self.next_pos();
        let key = if self.eat('"') {
            self.finish_string(start, false)
        } else {
            let mut ret = String::new();
            loop {
                match self.cur.clone().next() {
                    Some((_, ch)) => {
                        match ch {
                            'a' ... 'z' |
                            'A' ... 'Z' |
                            '0' ... '9' |
                            '_' | '-' => { self.cur.next(); ret.push(ch) }
                            _ => break,
                        }
                    }
                    None => break
                }
            }
            Some(ret)
        };
        match key {
            Some(ref name) if name.len() == 0 => {
                self.errors.push(ParserError {
                    lo: start,
                    hi: start,
                    desc: format!("expected a key but found an empty string"),
                });
                None
            }
            Some(name) => Some(name),
            None => None,
        }
    }

    // Parses the values into the given TomlTable. Returns true in case of success
    // and false in case of error.
    fn values(&mut self, into: &mut B::Table) -> bool {
        loop {
            let key_ws_start = self.next_pos();
            self.ws();
            if self.newline() { continue }
            if self.comment() { continue }
            let key_ws_end = self.next_pos();
            match self.peek(0) {
                Some((_, '[')) => break,
                Some(..) => {}
                None => break,
            }
            let key_lo = self.next_pos();
            let key = match self.key_name() {
                Some(s) => s,
                None => return false
            };
            let key_hi = self.next_pos();
            if !self.keyval_sep() { return false }
            let value = match self.value(key_hi) {
                Some(value) => value,
                None => return false,
            };
            self.insert(into, B::key(key, &self.input[key_ws_start..key_ws_end]),
                        value, key_lo, key_hi);
        }
        return true
    }

    fn keyval_sep(&mut self) -> bool {
        self.ws();
        if !self.expect('=') { return false }
        self.ws();
        true
    }

    // Parses a value
    fn value(&mut self, lead: usize) -> Option<B::Value> {
        self.ws();
        match self.cur.clone().next() {
            Some((pos, '"')) => self.string(pos).map(|s| {B::value_string(s, "", "")}),
            Some((pos, '\'')) => self.literal_string(pos).map(|s| {B::value_string(s, "", "")}),
            Some((pos, 't')) |
            Some((pos, 'f')) => self.boolean(pos).map(|s| {B::value_boolean(s, "", "")}),
            Some((pos, '[')) => self.array(pos).map(|s| {B::value_array(s, "", "")}),
            Some((pos, '{')) => self.inline_table(pos).map(|s| {B::value_table(s, "", "")}),
            Some((pos, '-')) |
            Some((pos, '+')) => self.number_or_datetime(pos),
            Some((pos, ch)) if is_digit(ch) => self.number_or_datetime(pos),
            _ => {
                let mut it = self.cur.clone();
                let lo = it.next().map(|p| p.0).unwrap_or(self.input.len());
                let hi = it.next().map(|p| p.0).unwrap_or(self.input.len());
                self.errors.push(ParserError {
                    lo: lo,
                    hi: hi,
                    desc: format!("expected a value"),
                });
                return None
            }
        }
    }

    // Parses a single or multi-line string
    fn string(&mut self, start: usize) -> Option<String> {
        if !self.expect('"') { return None }
        let mut multiline = false;

        // detect multiline literals, but be careful about empty ""
        // strings
        if self.eat('"') {
            if self.eat('"') {
                multiline = true;
                self.newline();
            } else {
                // empty
                return Some(String::new())
            }
        }

        self.finish_string(start, multiline)
    }

    // Finish parsing a basic string after the opening quote has been seen
    fn finish_string(&mut self,
                     start: usize,
                     multiline: bool) -> Option<String> {
        let mut ret = String::new();
        loop {
            while multiline && self.newline() { ret.push('\n') }
            match self.cur.next() {
                Some((_, '"')) => {
                    if multiline {
                        if !self.eat('"') { ret.push_str("\""); continue }
                        if !self.eat('"') { ret.push_str("\"\""); continue }
                    }
                    return Some(ret)
                }
                Some((pos, '\\')) => {
                    match escape(self, pos, multiline) {
                        Some(c) => ret.push(c),
                        None => {}
                    }
                }
                Some((pos, ch)) if ch < '\u{1f}' => {
                    self.errors.push(ParserError {
                        lo: pos,
                        hi: pos + 1,
                        desc: format!("control character `{}` must be escaped",
                                      ch.escape_default().collect::<String>())
                    });
                }
                Some((_, ch)) => ret.push(ch),
                None => {
                    self.errors.push(ParserError {
                        lo: start,
                        hi: self.input.len(),
                        desc: format!("unterminated string literal"),
                    });
                    return None
                }
            }
        }

        fn escape<B:Builder>(me: &mut ParseSession<B>, pos: usize, multiline: bool) -> Option<char> {
            if multiline && me.newline() {
                while me.ws() || me.newline() { /* ... */ }
                return None
            }
            match me.cur.next() {
                Some((_, 'b')) => Some('\u{8}'),
                Some((_, 't')) => Some('\u{9}'),
                Some((_, 'n')) => Some('\u{a}'),
                Some((_, 'f')) => Some('\u{c}'),
                Some((_, 'r')) => Some('\u{d}'),
                Some((_, '"')) => Some('\u{22}'),
                Some((_, '\\')) => Some('\u{5c}'),
                Some((pos, c @ 'u')) |
                Some((pos, c @ 'U')) => {
                    let len = if c == 'u' {4} else {8};
                    let num = &me.input[pos+1..];
                    let num = if num.len() >= len && num.is_ascii() {
                        &num[..len]
                    } else {
                        "invalid"
                    };
                    match u32::from_str_radix(num, 16).ok() {
                        Some(n) => {
                            match char::from_u32(n) {
                                Some(c) => {
                                    me.cur.by_ref().skip(len - 1).next();
                                    return Some(c)
                                }
                                None => {
                                    me.errors.push(ParserError {
                                        lo: pos + 1,
                                        hi: pos + 5,
                                        desc: format!("codepoint `{:x}` is \
                                                       not a valid unicode \
                                                       codepoint", n),
                                    })
                                }
                            }
                        }
                        None => {
                            me.errors.push(ParserError {
                                lo: pos,
                                hi: pos + 1,
                                desc: format!("expected {} hex digits \
                                               after a `{}` escape", len, c),
                            })
                        }
                    }
                    None
                }
                Some((pos, ch)) => {
                    let next_pos = me.next_pos();
                    me.errors.push(ParserError {
                        lo: pos,
                        hi: next_pos,
                        desc: format!("unknown string escape: `{}`",
                                      ch.escape_default().collect::<String>()),
                    });
                    None
                }
                None => {
                    me.errors.push(ParserError {
                        lo: pos,
                        hi: pos + 1,
                        desc: format!("unterminated escape sequence"),
                    });
                    None
                }
            }
        }
    }

    fn literal_string(&mut self, start: usize) -> Option<String> {
        if !self.expect('\'') { return None }
        let mut multiline = false;
        let mut ret = String::new();

        // detect multiline literals
        if self.eat('\'') {
            if self.eat('\'') {
                multiline = true;
                self.newline();
            } else {
                return Some(ret) // empty
            }
        }

        loop {
            if !multiline && self.newline() {
                let next = self.next_pos();
                self.errors.push(ParserError {
                    lo: start,
                    hi: next,
                    desc: format!("literal strings cannot contain newlines"),
                });
                return None
            }
            match self.cur.next() {
                Some((_, '\'')) => {
                    if multiline {
                        if !self.eat('\'') { ret.push_str("'"); continue }
                        if !self.eat('\'') { ret.push_str("''"); continue }
                    }
                    break
                }
                Some((_, ch)) => ret.push(ch),
                None => {
                    self.errors.push(ParserError {
                        lo: start,
                        hi: self.input.len(),
                        desc: format!("unterminated string literal"),
                    });
                    return None
                }
            }
        }

        return Some(ret);
    }

    fn number_or_datetime(&mut self, start: usize) -> Option<B::Value> {
        let mut is_float = false;
        let prefix = try!(self.integer(start, false, true));
        let decimal = if self.eat('.') {
            is_float = true;
            Some(try!(self.integer(start, true, false)))
        } else {
            None
        };
        let exponent = if self.eat('e') || self.eat('E') {
            is_float = true;
            Some(try!(self.integer(start, false, true)))
        } else {
            None
        };
        let end = self.next_pos();
        let input = &self.input[start..end];
        let ret = if !is_float && !input.starts_with("+") &&
                     !input.starts_with("-") && self.eat('-') {
            self.datetime(start, end + 1)
        } else {
            let input = match (decimal, exponent) {
                (None, None) => prefix,
                (Some(ref d), None) => prefix + "." + d,
                (None, Some(ref e)) => prefix + "E" + e,
                (Some(ref d), Some(ref e)) => prefix + "." + d + "E" + e,
            };
            let input = input.trim_left_matches('+');
            if is_float {
                input.parse().ok().map(|s| B::value_float(s, "", ""))
            } else {
                input.parse().ok().map(|s| B::value_integer(s, "", ""))
            }
        };
        if ret.is_none() {
            self.errors.push(ParserError {
                lo: start,
                hi: end,
                desc: format!("invalid numeric literal"),
            });
        }
        return ret;
    }

    fn integer(&mut self, start: usize, allow_leading_zeros: bool,
               allow_sign: bool) -> Option<String> {
        let mut s = String::new();
        if allow_sign {
            if self.eat('-') { s.push('-'); }
            else if self.eat('+') { s.push('+'); }
        }
        match self.cur.next() {
            Some((_, '0')) if !allow_leading_zeros => {
                s.push('0');
                match self.peek(0) {
                    Some((pos, c)) if '0' <= c && c <= '9' => {
                        self.errors.push(ParserError {
                            lo: start,
                            hi: pos,
                            desc: format!("leading zeroes are not allowed"),
                        });
                        return None
                    }
                    _ => {}
                }
            }
            Some((_, ch)) if '0' <= ch && ch <= '9' => {
                s.push(ch);
            }
            _ => {
                let pos = self.next_pos();
                self.errors.push(ParserError {
                    lo: pos,
                    hi: pos,
                    desc: format!("expected start of a numeric literal"),
                });
                return None;
            }
        }
        let mut underscore = false;
        loop {
            match self.cur.clone().next() {
                Some((_, ch)) if '0' <= ch && ch <= '9' => {
                    s.push(ch);
                    self.cur.next();
                    underscore = false;
                }
                Some((_, '_')) if !underscore => {
                    self.cur.next();
                    underscore = true;
                }
                Some(_) | None => break,
            }
        }
        if underscore {
            let pos = self.next_pos();
            self.errors.push(ParserError {
                lo: pos,
                hi: pos,
                desc: format!("numeral cannot end with an underscore"),
            });
            return None
        } else {
            Some(s)
        }
    }

    fn boolean(&mut self, start: usize) -> Option<bool> {
        let rest = &self.input[start..];
        if rest.starts_with("true") {
            for _ in 0..4 {
                self.cur.next();
            }
            Some(true)
        } else if rest.starts_with("false") {
            for _ in 0..5 {
                self.cur.next();
            }
            Some(false)
        } else {
            let next = self.next_pos();
            self.errors.push(ParserError {
                lo: start,
                hi: next,
                desc: format!("unexpected character: `{}`",
                              rest.chars().next().unwrap()),
            });
            None
        }
    }

    fn datetime(&mut self, start: usize, end_so_far: usize) -> Option<B::Value> {
        let mut date = format!("{}", &self.input[start..end_so_far]);
        for _ in 0..15 {
            match self.cur.next() {
                Some((_, ch)) => date.push(ch),
                None => {
                    self.errors.push(ParserError {
                        lo: start,
                        hi: end_so_far,
                        desc: format!("malformed date literal"),
                    });
                    return None
                }
            }
        }
        let mut it = date.chars();
        let mut valid = true;
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(|c| c == '-').unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(|c| c == '-').unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(|c| c == 'T').unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(|c| c == ':').unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(|c| c == ':').unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(is_digit).unwrap_or(false);
        valid = valid && it.next().map(|c| c == 'Z').unwrap_or(false);
        if valid {
            Some(B::value_datetime(date.clone(), "", ""))
        } else {
            self.errors.push(ParserError {
                lo: start,
                hi: start + date.len(),
                desc: format!("malformed date literal"),
            });
            None
        }
    }

    fn array(&mut self, _start: usize) -> Option<B::Array> {
        if !self.expect('[') { return None }
        let mut ret = Vec::new();
        fn consume<B:Builder>(me: &mut ParseSession<B>) {
            loop {
                me.ws();
                if !me.newline() && !me.comment() { break }
            }
        }
        let mut type_str = None;
        loop {
            // Break out early if we see the closing bracket
            consume(self);
            if self.eat(']') { return Some(B::array(ret, "")) }

            // Attempt to parse a value, triggering an error if it's the wrong
            // type.
            let start = self.next_pos();
            let value = try!(self.value(0));
            let end = self.next_pos();
            let expected = type_str.unwrap_or(value.type_str());
            if value.type_str() != expected {
                self.errors.push(ParserError {
                    lo: start,
                    hi: end,
                    desc: format!("expected type `{}`, found type `{}`",
                                  expected, value.type_str()),
                });
            } else {
                type_str = Some(expected);
                ret.push(value);
            }

            // Look for a comma. If we don't find one we're done
            consume(self);
            if !self.eat(',') { break }
        }
        consume(self);
        if !self.expect(']') { return None }
        return Some(B::array(ret, ""))
    }

    fn inline_table(&mut self, _start: usize) -> Option<B::Table> {
        if !self.expect('{') { return None }
        self.ws();
        let mut ret = B::table("");
        if self.eat('}') { return Some(ret) }
        loop {
            let lo = self.next_pos();
            let key = try!(self.key_name());
            if !self.keyval_sep() { return None }
            let value = try!(self.value(0));
            self.insert(&mut ret, B::key(key, ""), value, lo, lo);

            self.ws();
            if self.eat('}') { break }
            if !self.expect(',') { return None }
            self.ws();
        }
        return Some(ret)
    }

    fn insert(&mut self, into: &mut B::Table, key: B::Key, value: B::Value,
              key_lo: usize, key_hi: usize) {
        if !B::insert(into, key, value) {
            self.errors.push(ParserError {
                lo: key_lo,
                hi: key_hi,
                desc: format!("duplicate key: `{}`",
                              self.input[key_lo..key_hi].to_string()),
            })
        }
    }

    fn insert_table(&mut self, into: &mut B::Table, mut keys: Vec<String>,
                    value: B::Table, key_lo: usize, key_hi: usize) {
        let into = match B::insert_container(into, &keys[..keys.len()-1], key_lo, key_hi) {
            Ok(into) => into,
            Err(err) => { self.errors.push(err); return }
        };
        let last_key = keys.pop().unwrap();
        let key_text = format!("{}", last_key);
        let mut added = B::insert(into, B::key(last_key, ""), B::value_table(B::table(""), "", ""));
        match B::get_table(into, &key_text[..]) {
            Some(table) => {
                let any_tables = B::contains_table(&table);
                if !any_tables && !added {
                    self.errors.push(ParserError {
                        lo: key_lo,
                        hi: key_hi,
                        desc: format!("redefinition of table `{}`", key_text),
                    });
                }
                match B::merge(table, value) {
                    Ok(_) => {},
                    Err(k) => {
                        self.errors.push(ParserError {
                            lo: key_lo,
                            hi: key_hi,
                            desc: format!("duplicate key `{}` in table", k),
                        });
                    }
                }
            }
            None => {
                self.errors.push(ParserError {
                    lo: key_lo,
                    hi: key_hi,
                    desc: format!("duplicate key `{}` in table", key_text),
                });
            }
        }
    }

    fn insert_array(&mut self, into: &mut B::Table, mut keys: Vec<String>,
                    value: B::Value, key_lo: usize, key_hi: usize) {
        let into = match B::insert_container(into, &keys[..keys.len()-1], key_lo, key_hi) {
            Ok(into) => into,
            Err(err) => { self.errors.push(err); return }
        };
        let last_key = keys.pop().unwrap();
        let key_text = format!("{}", last_key);
        let mut added = B::insert(into, B::key(last_key, ""), B::value_array(B::array(vec!(), ""), "", ""));
        match B::get_array(into, &key_text[..]) {
            Some(arr) => {
                let value_type = value.type_str();
                match B::push(arr, value) {
                    Ok(_) => {},
                    Err(array_type)=> {
                        self.errors.push(ParserError {
                            lo: key_lo,
                            hi: key_hi,
                            desc: format!("expected type `{}`, found type `{}`",
                                          array_type, value_type),
                        })
                    }
                }
            }
            _ => {
                self.errors.push(ParserError {
                    lo: key_lo,
                    hi: key_hi,
                    desc: format!("key `{}` was previously not an array", key_text),
                });
            }
        }
    }
}

impl Error for ParserError {
    fn description(&self) -> &str { "TOML parse error" }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.desc.fmt(f)
    }
}

fn is_digit(c: char) -> bool {
    match c { '0' ... '9' => true, _ => false }
}

#[cfg(test)]
mod tests {
    use Value::Table;
    use Parser;

    macro_rules! bad {
        ($s:expr, $lo: expr, $hi: expr, $msg:expr) => ({
            let mut p = Parser::new($s);
            assert!(p.parse().is_none());
            assert!(p.errors.iter().any(
                    |e| { e.desc.contains($msg) && e.lo == $lo && e.hi == $hi }
                ),
                "errors: {:?}",
                p.errors);
        })
    }

    #[test]
    fn crlf() {
        let mut p = Parser::new("\
[project]\r\n\
\r\n\
name = \"splay\"\r\n\
version = \"0.1.0\"\r\n\
authors = [\"alex@crichton.co\"]\r\n\
\r\n\
[[lib]]\r\n\
\r\n\
path = \"lib.rs\"\r\n\
name = \"splay\"\r\n\
description = \"\"\"\
A Rust implementation of a TAR file reader and writer. This library does not\r\n\
currently handle compression, but it is abstract over all I/O readers and\r\n\
writers. Additionally, great lengths are taken to ensure that the entire\r\n\
contents are never required to be entirely resident in memory all at once.\r\n\
\"\"\"\
");
        assert!(p.parse().is_some());
    }

    #[test]
    fn linecol() {
        let p = Parser::new("ab\ncde\nf");
        assert_eq!(p.to_linecol(0), (0, 0));
        assert_eq!(p.to_linecol(1), (0, 1));
        assert_eq!(p.to_linecol(3), (1, 0));
        assert_eq!(p.to_linecol(4), (1, 1));
        assert_eq!(p.to_linecol(7), (2, 0));
    }

    #[test]
    fn fun_with_strings() {
        let mut p = Parser::new(r#"
bar = "\U00000000"
key1 = "One\nTwo"
key2 = """One\nTwo"""
key3 = """
One
Two"""

key4 = "The quick brown fox jumps over the lazy dog."
key5 = """
The quick brown \


  fox jumps over \
    the lazy dog."""
key6 = """\
       The quick brown \
       fox jumps over \
       the lazy dog.\
       """
# What you see is what you get.
winpath  = 'C:\Users\nodejs\templates'
winpath2 = '\\ServerX\admin$\system32\'
quoted   = 'Tom "Dubs" Preston-Werner'
regex    = '<\i\c*\s*>'

regex2 = '''I [dw]on't need \d{2} apples'''
lines  = '''
The first newline is
trimmed in raw strings.
   All other whitespace
   is preserved.
'''
"#);
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("bar").and_then(|k| k.as_str()), Some("\0"));
        assert_eq!(table.lookup("key1").and_then(|k| k.as_str()),
                   Some("One\nTwo"));
        assert_eq!(table.lookup("key2").and_then(|k| k.as_str()),
                   Some("One\nTwo"));
        assert_eq!(table.lookup("key3").and_then(|k| k.as_str()),
                   Some("One\nTwo"));

        let msg = "The quick brown fox jumps over the lazy dog.";
        assert_eq!(table.lookup("key4").and_then(|k| k.as_str()), Some(msg));
        assert_eq!(table.lookup("key5").and_then(|k| k.as_str()), Some(msg));
        assert_eq!(table.lookup("key6").and_then(|k| k.as_str()), Some(msg));

        assert_eq!(table.lookup("winpath").and_then(|k| k.as_str()),
                   Some(r"C:\Users\nodejs\templates"));
        assert_eq!(table.lookup("winpath2").and_then(|k| k.as_str()),
                   Some(r"\\ServerX\admin$\system32\"));
        assert_eq!(table.lookup("quoted").and_then(|k| k.as_str()),
                   Some(r#"Tom "Dubs" Preston-Werner"#));
        assert_eq!(table.lookup("regex").and_then(|k| k.as_str()),
                   Some(r"<\i\c*\s*>"));
        assert_eq!(table.lookup("regex2").and_then(|k| k.as_str()),
                   Some(r"I [dw]on't need \d{2} apples"));
        assert_eq!(table.lookup("lines").and_then(|k| k.as_str()),
                   Some("The first newline is\n\
                         trimmed in raw strings.\n   \
                            All other whitespace\n   \
                            is preserved.\n"));
    }

    #[test]
    fn tables_in_arrays() {
        let mut p = Parser::new(r#"
[[foo]]
  #…
  [foo.bar]
    #…

[[foo]]
  #…
  [foo.bar]
    #...
"#);
        let table = Table(p.parse().unwrap());
        table.lookup("foo.0.bar").unwrap().as_table().unwrap();
        table.lookup("foo.1.bar").unwrap().as_table().unwrap();
    }

    #[test]
    fn fruit() {
        let mut p = Parser::new(r#"
[[fruit]]
  name = "apple"

  [fruit.physical]
    color = "red"
    shape = "round"

  [[fruit.variety]]
    name = "red delicious"

  [[fruit.variety]]
    name = "granny smith"

[[fruit]]
  name = "banana"

  [[fruit.variety]]
    name = "plantain"
"#);
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("fruit.0.name").and_then(|k| k.as_str()),
                   Some("apple"));
        assert_eq!(table.lookup("fruit.0.physical.color").and_then(|k| k.as_str()),
                   Some("red"));
        assert_eq!(table.lookup("fruit.0.physical.shape").and_then(|k| k.as_str()),
                   Some("round"));
        assert_eq!(table.lookup("fruit.0.variety.0.name").and_then(|k| k.as_str()),
                   Some("red delicious"));
        assert_eq!(table.lookup("fruit.0.variety.1.name").and_then(|k| k.as_str()),
                   Some("granny smith"));
        assert_eq!(table.lookup("fruit.1.name").and_then(|k| k.as_str()),
                   Some("banana"));
        assert_eq!(table.lookup("fruit.1.variety.0.name").and_then(|k| k.as_str()),
                   Some("plantain"));
    }

    #[test]
    fn stray_cr() {
        assert!(Parser::new("\r").parse().is_none());
        assert!(Parser::new("a = [ \r ]").parse().is_none());
        assert!(Parser::new("a = \"\"\"\r\"\"\"").parse().is_none());
        assert!(Parser::new("a = \"\"\"\\  \r  \"\"\"").parse().is_none());

        let mut p = Parser::new("foo = '''\r'''");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").and_then(|k| k.as_str()), Some("\r"));

        let mut p = Parser::new("foo = '\r'");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").and_then(|k| k.as_str()), Some("\r"));
    }

    #[test]
    fn blank_literal_string() {
        let mut p = Parser::new("foo = ''");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").and_then(|k| k.as_str()), Some(""));
    }

    #[test]
    fn many_blank() {
        let mut p = Parser::new("foo = \"\"\"\n\n\n\"\"\"");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").and_then(|k| k.as_str()), Some("\n\n"));
    }

    #[test]
    fn literal_eats_crlf() {
        let mut p = Parser::new("
            foo = \"\"\"\\\r\n\"\"\"
            bar = \"\"\"\\\r\n   \r\n   \r\n   a\"\"\"
        ");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").and_then(|k| k.as_str()), Some(""));
        assert_eq!(table.lookup("bar").and_then(|k| k.as_str()), Some("a"));
    }

    #[test]
    fn string_no_newline() {
        assert!(Parser::new("a = \"\n\"").parse().is_none());
        assert!(Parser::new("a = '\n'").parse().is_none());
    }

    #[test]
    fn bad_leading_zeros() {
        assert!(Parser::new("a = 00").parse().is_none());
        assert!(Parser::new("a = -00").parse().is_none());
        assert!(Parser::new("a = +00").parse().is_none());
        assert!(Parser::new("a = 00.0").parse().is_none());
        assert!(Parser::new("a = -00.0").parse().is_none());
        assert!(Parser::new("a = +00.0").parse().is_none());
        assert!(Parser::new("a = 9223372036854775808").parse().is_none());
        assert!(Parser::new("a = -9223372036854775809").parse().is_none());
    }

    #[test]
    fn bad_floats() {
        assert!(Parser::new("a = 0.").parse().is_none());
        assert!(Parser::new("a = 0.e").parse().is_none());
        assert!(Parser::new("a = 0.E").parse().is_none());
        assert!(Parser::new("a = 0.0E").parse().is_none());
        assert!(Parser::new("a = 0.0e").parse().is_none());
        assert!(Parser::new("a = 0.0e-").parse().is_none());
        assert!(Parser::new("a = 0.0e+").parse().is_none());
        assert!(Parser::new("a = 0.0e+00").parse().is_none());
    }

    #[test]
    fn floats() {
        macro_rules! t {
            ($actual:expr, $expected:expr) => ({
                let f = format!("foo = {}", $actual);
                let mut p = Parser::new(&f);
                let table = Table(p.parse().unwrap());
                assert_eq!(table.lookup("foo").and_then(|k| k.as_float()),
                           Some($expected));
            })
        }

        t!("1.0", 1.0);
        t!("1.0e0", 1.0);
        t!("1.0e+0", 1.0);
        t!("1.0e-0", 1.0);
        t!("1.001e-0", 1.001);
        t!("2e10", 2e10);
        t!("2e+10", 2e10);
        t!("2e-10", 2e-10);
        t!("2_0.0", 20.0);
        t!("2_0.0_0e0_0", 20.0);
        t!("2_0.1_0e1_0", 20.1e10);
    }

    #[test]
    fn bare_key_names() {
        let mut p = Parser::new("
            foo = 3
            foo_3 = 3
            foo_-2--3--r23f--4-f2-4 = 3
            _ = 3
            - = 3
            8 = 8
            \"a\" = 3
            \"!\" = 3
            \"a^b\" = 3
            \"\\\"\" = 3
            \"character encoding\" = \"value\"
            \"ʎǝʞ\" = \"value\"
        ");
        let table = Table(p.parse().unwrap());
        assert!(table.lookup("foo").is_some());
        assert!(table.lookup("-").is_some());
        assert!(table.lookup("_").is_some());
        assert!(table.lookup("8").is_some());
        assert!(table.lookup("foo_3").is_some());
        assert!(table.lookup("foo_-2--3--r23f--4-f2-4").is_some());
        assert!(table.lookup("a").is_some());
        assert!(table.lookup("!").is_some());
        assert!(table.lookup("\"").is_some());
        assert!(table.lookup("character encoding").is_some());
        assert!(table.lookup("ʎǝʞ").is_some());
    }

    #[test]
    fn bad_keys() {
        assert!(Parser::new("key\n=3").parse().is_none());
        assert!(Parser::new("key=\n3").parse().is_none());
        assert!(Parser::new("key|=3").parse().is_none());
        assert!(Parser::new("\"\"=3").parse().is_none());
        assert!(Parser::new("=3").parse().is_none());
        assert!(Parser::new("\"\"|=3").parse().is_none());
        assert!(Parser::new("\"\n\"|=3").parse().is_none());
        assert!(Parser::new("\"\r\"|=3").parse().is_none());
    }

    #[test]
    fn bad_table_names() {
        assert!(Parser::new("[]").parse().is_none());
        assert!(Parser::new("[.]").parse().is_none());
        assert!(Parser::new("[\"\".\"\"]").parse().is_none());
        assert!(Parser::new("[a.]").parse().is_none());
        assert!(Parser::new("[\"\"]").parse().is_none());
        assert!(Parser::new("[!]").parse().is_none());
        assert!(Parser::new("[\"\n\"]").parse().is_none());
        assert!(Parser::new("[a.b]\n[a.\"b\"]").parse().is_none());
    }

    #[test]
    fn table_names() {
        let mut p = Parser::new("
            [a.\"b\"]
            [\"f f\"]
            [\"f.f\"]
            [\"\\\"\"]
        ");
        let table = Table(p.parse().unwrap());
        assert!(table.lookup("a.b").is_some());
        assert!(table.lookup("f f").is_some());
        assert!(table.lookup("\"").is_some());
    }

    #[test]
    fn invalid_bare_numeral() {
        assert!(Parser::new("4").parse().is_none());
    }

    #[test]
    fn inline_tables() {
        assert!(Parser::new("a = {}").parse().is_some());
        assert!(Parser::new("a = {b=1}").parse().is_some());
        assert!(Parser::new("a = {   b   =   1    }").parse().is_some());
        assert!(Parser::new("a = {a=1,b=2}").parse().is_some());
        assert!(Parser::new("a = {a=1,b=2,c={}}").parse().is_some());
        assert!(Parser::new("a = {a=1,}").parse().is_none());
        assert!(Parser::new("a = {,}").parse().is_none());
        assert!(Parser::new("a = {a=1,a=1}").parse().is_none());
        assert!(Parser::new("a = {\n}").parse().is_none());
        assert!(Parser::new("a = {").parse().is_none());
        assert!(Parser::new("a = {a=[\n]}").parse().is_some());
        assert!(Parser::new("a = {\"a\"=[\n]}").parse().is_some());
        assert!(Parser::new("a = [\n{},\n{},\n]").parse().is_some());
    }

    #[test]
    fn number_underscores() {
        macro_rules! t {
            ($actual:expr, $expected:expr) => ({
                let f = format!("foo = {}", $actual);
                let mut p = Parser::new(&f);
                let table = Table(p.parse().unwrap());
                assert_eq!(table.lookup("foo").and_then(|k| k.as_integer()),
                           Some($expected));
            })
        }

        t!("1_0", 10);
        t!("1_0_0", 100);
        t!("1_000", 1000);
        t!("+1_000", 1000);
        t!("-1_000", -1000);
    }

    #[test]
    fn bad_underscores() {
        assert!(Parser::new("foo = 0_").parse().is_none());
        assert!(Parser::new("foo = 0__0").parse().is_none());
        assert!(Parser::new("foo = __0").parse().is_none());
        assert!(Parser::new("foo = 1_0_").parse().is_none());
    }

    #[test]
    fn bad_unicode_codepoint() {
        bad!("foo = \"\\uD800\"", 9, 13, "not a valid unicode codepoint");
    }

    #[test]
    fn bad_strings() {
        bad!("foo = \"\\uxx\"", 8, 9, "expected 4 hex digits");
        bad!("foo = \"\\u\"", 8, 9, "expected 4 hex digits");
        bad!("foo = \"\\", 7, 8, "unterminated");
        bad!("foo = '", 6, 7, "unterminated");
    }

    #[test]
    fn empty_string() {
        let mut p = Parser::new("foo = \"\"");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").unwrap().as_str(), Some(""));
    }

    #[test]
    fn booleans() {
        let mut p = Parser::new("foo = true");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").unwrap().as_bool(), Some(true));

        let mut p = Parser::new("foo = false");
        let table = Table(p.parse().unwrap());
        assert_eq!(table.lookup("foo").unwrap().as_bool(), Some(false));

        assert!(Parser::new("foo = true2").parse().is_none());
        assert!(Parser::new("foo = false2").parse().is_none());
        assert!(Parser::new("foo = t1").parse().is_none());
        assert!(Parser::new("foo = f2").parse().is_none());
    }

    #[test]
    fn bad_nesting() {
        bad!("
            a = [2]
            [[a]]
            b = 5
        ",
        33, 38,
        "expected type `integer`, found type `table`");
        bad!("
            a = 1
            [a.b]
        ",
        31, 36,
        "key `a` was not previously a table");
        bad!("
            a = []
            [a.b]
        ",
        32, 37,
        "array `a` does not contain tables");
        bad!("
            a = []
            [[a.b]]
        ",
        32, 39,
        "array `a` does not contain tables");
        bad!("
            [a]
            b = { c = 2, d = {} }
            [a.b]
            c = 2
        ",
        63, 68,
        "duplicate key `c` in table");
    }
}
