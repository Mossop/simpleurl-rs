#![warn(missing_docs)]
#![deny(unused_variables)]

use super::{Authentication, Host, Path, Scheme, UrlBuilder, UrlError, UrlResult};
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};
use std::str::Chars;

/// These are the allowable code points in most parts of a uri string.
const URL_CODE_POINTS: &str =
    "0-9A-Za-z!$&'()*+,-\\./:;=?@_~\u{00A0}-\u{D7FF}\u{E000}-\u{10FFFD}--\
     [\u{FDD0}-\u{FDEF}\u{FFFE}\u{FFFF}\u{1FFFE}\u{1FFFF}\u{2FFFE}\u{2FFFF}\
     \u{3FFFE}\u{3FFFF}\u{4FFFE}\u{4FFFF}\u{5FFFE}\u{5FFFF}\u{6FFFE}\u{6FFFF}\
     \u{7FFFE}\u{7FFFF}\u{8FFFE}\u{8FFFF}\u{9FFFE}\u{9FFFF}\u{AFFFE}\u{AFFFF}\
     \u{BFFFE}\u{BFFFF}\u{CFFFE}\u{CFFFF}\u{DFFFE}\u{DFFFF}\u{EFFFE}\u{EFFFF}\
     \u{FFFFE}\u{FFFFF}\u{10FFFE}\u{10FFFF}]\
     ";

/// Responsible for percent decoding a string.
///
/// The result contains all the characters from the original with percent
/// encoded bytes converted back to their original representation.
pub fn percent_decode(data: &str) -> String {
    String::from(data)
}

/// Responsible for percent encoding a string.
///
/// The result contains all the characters from the original with illegal
/// characters percent encoded.
pub fn percent_encode(data: &str) -> String {
    String::from(data)
}

/// Represents an inclusive range of `char`s,
#[derive(Clone)]
struct CodepointRange {
    start: Option<char>,
    end: Option<char>,
}

impl CodepointRange {
    /// Creates a range that only matches the give `char`.
    fn from_codepoint(c: char) -> CodepointRange {
        CodepointRange::from_range(c, c)
    }

    /// Creates a range that matches the given codepoint range inclusively.
    fn from_range(start: char, end: char) -> CodepointRange {
        CodepointRange {
            start: Some(start),
            end: Some(end),
        }
    }

    /// Tests if this range includes the given `char`.
    fn includes(&self, c: char) -> bool {
        if let Some(s) = self.start {
            if c < s {
                return false;
            }
        }

        if let Some(e) = self.end {
            if c > e {
                return false;
            }
        }

        true
    }

    /// Converts this to a `CodepointSet` that includes this range.
    fn as_included_set(&self) -> CodepointSet {
        CodepointSet {
            included: vec![self.clone()],
            excluded: Default::default(),
        }
    }
}

impl Add for CodepointRange {
    type Output = CodepointSet;

    fn add(self, other: CodepointRange) -> CodepointSet {
        CodepointSet {
            included: vec![self, other],
            excluded: Default::default(),
        }
    }
}

impl Sub for CodepointRange {
    type Output = CodepointSet;

    fn sub(self, other: CodepointRange) -> CodepointSet {
        CodepointSet {
            included: vec![self],
            excluded: vec![other],
        }
    }
}

/// An [`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) over
/// a set of `CodepointRanges`.
struct CodepointRangeIterator<'a> {
    // The underlying char iterator.
    char_iter: Chars<'a>,

    // A pending codepoint to be returned or converted into a range.
    previous: Option<char>,
}

impl<'a> CodepointRangeIterator<'a> {
    /// Creates a new `CodepointRangeIterator over a codepoint set.
    ///
    /// the set is essentially that of regular expressions. It contains a set of
    /// codepoints and ranges of codepoints separated by the `-` character.
    fn new(set: &'a str) -> CodepointRangeIterator {
        let mut iter = set.chars();
        let first = iter.next();
        CodepointRangeIterator {
            char_iter: iter,
            previous: first,
        }
    }
}

impl<'a> Iterator for CodepointRangeIterator<'a> {
    type Item = CodepointRange;

    fn next(&mut self) -> Option<CodepointRange> {
        if let Some(prev) = self.previous {
            let next = self.char_iter.next();
            self.previous = next;

            if prev == '\\' {
                if let Some(ch) = next {
                    // Load previous up with the next codepoint.
                    self.previous = self.char_iter.next();
                    // Just create a range for the escaped codepoint as-is.
                    Some(CodepointRange::from_codepoint(ch))
                } else {
                    // Nothing to escape? Just output the `\` codepoint.
                    // `previous` is already none at this point and so the next
                    // call will end iteration.
                    Some(CodepointRange::from_codepoint('\\'))
                }
            } else {
                match next {
                    Some('-') => {
                        // This is a range. `prev` holds the codepoint at the
                        // start of the range. The next codepoint will be the
                        // end.
                        let last = self.char_iter.next();
                        match last {
                            Some(ch) => {
                                // Load previous up with the next codepoint.
                                self.previous = self.char_iter.next();
                                // Create a new range.
                                Some(CodepointRange::from_range(prev, ch))
                            }
                            // No end of the range? I guess just include the
                            // first codepoint?
                            None => Some(CodepointRange::from_codepoint(prev)),
                        }
                    }
                    // Not a range, just output `prev`. `previous` already has
                    // the next codepoint pending.
                    _ => Some(CodepointRange::from_codepoint(prev)),
                }
            }
        } else {
            None
        }
    }
}

#[derive(Default, Clone)]
struct CodepointSet {
    included: Vec<CodepointRange>,
    excluded: Vec<CodepointRange>,
}

impl CodepointSet {
    fn from_included_set(set: &str) -> CodepointSet {
        let mut pointset: CodepointSet = Default::default();
        pointset.include_set(set);
        pointset
    }

    fn from_excluded_set(set: &str) -> CodepointSet {
        let mut pointset: CodepointSet = Default::default();
        pointset.exclude_set(set);
        pointset
    }

    fn include_set(&mut self, set: &str) {
        self.included.extend(CodepointRangeIterator::new(set));
    }

    fn exclude_set(&mut self, set: &str) {
        self.excluded.extend(CodepointRangeIterator::new(set));
    }

    fn includes(&self, c: char) -> bool {
        for range in &self.excluded {
            if range.includes(c) {
                return false;
            }
        }

        if self.included.is_empty() {
            return true;
        }

        for range in &self.included {
            if range.includes(c) {
                return true;
            }
        }

        false
    }
}

impl Add<CodepointRange> for CodepointSet {
    type Output = CodepointSet;

    fn add(self, range: CodepointRange) -> CodepointSet {
        let mut result = self.clone();
        result.included.push(range);
        result
    }
}

impl AddAssign<CodepointRange> for CodepointSet {
    fn add_assign(&mut self, range: CodepointRange) {
        self.included.push(range);
    }
}

impl Sub<CodepointRange> for CodepointSet {
    type Output = CodepointSet;

    fn sub(self, range: CodepointRange) -> CodepointSet {
        let mut result = self.clone();
        result.excluded.push(range);
        result
    }
}

impl SubAssign<CodepointRange> for CodepointSet {
    fn sub_assign(&mut self, range: CodepointRange) {
        self.excluded.push(range);
    }
}

impl Neg for CodepointSet {
    type Output = CodepointSet;

    fn neg(self) -> CodepointSet {
        CodepointSet {
            included: self.excluded,
            excluded: self.included,
        }
    }
}

pub(crate) struct ParseResult {
    pub builder: UrlBuilder,
    pub is_valid: bool,
}

/// Responsible for parsing URLs.
pub(crate) struct UrlParser<'a> {
    spec: &'a str,
    result: ParseResult,

    chars: Vec<char>,
}

impl<'a> UrlParser<'a> {
    // Generates a UrlError including the spec being parsed.
    fn error(&self, message: &str) -> UrlError {
        UrlError::new(message, self.spec)
    }

    // Drops the first `count` codepoints.
    fn move_start(&mut self, count: usize) -> UrlResult<()> {
        self.extract_start(count).map(|_| ())
    }

    fn extract_start(&mut self, count: usize) -> UrlResult<String> {
        if count > self.chars.len() {
            Err(self.error("Parser ran past the end of the spec."))
        } else {
            Ok(self.chars.drain(0..count).collect())
        }
    }

    // Drops the last `count` codepoints.
    fn move_end(&mut self, count: usize) -> UrlResult<()> {
        self.extract_end(count).map(|_| ())
    }

    fn extract_end(&mut self, count: usize) -> UrlResult<String> {
        if count > self.chars.len() {
            Err(self.error("Parser ran past the start of the spec."))
        } else {
            Ok(self
                .chars
                .drain(self.chars.len() - count..self.chars.len())
                .collect())
        }
    }

    // Walks from the start of the codepoints to find the first that is included
    // by the `CodepointSet`.
    //
    // The returned option is `None` if no codepoint was found or the offset of
    // the codepoint from the start.
    fn find_forwards(&self, until: &CodepointSet) -> usize {
        for (i, ch) in self.chars.iter().enumerate() {
            if until.includes(*ch) {
                return i;
            }
        }

        self.chars.len()
    }

    // Walks from the end of the codepoints to find the first that is included
    // by the `CodepointSet`.
    //
    // The returned option is `None` if no codepoint was found or the offset of
    // the codepoint from the start.
    fn find_backwards(&self, until: &CodepointSet) -> usize {
        for (i, ch) in self.chars.iter().rev().enumerate() {
            if until.includes(*ch) {
                return i;
            }
        }

        self.chars.len()
    }

    fn starts_with_drive_letter(&self) -> bool {
        let win_drive_letter = CodepointSet::from_included_set("a-zA-Z");
        let win_drive_separator = CodepointSet::from_included_set(":|");
        let end_points = CodepointSet::from_included_set("\\\\/?#");

        self.chars.len() >= 2
            && win_drive_letter.includes(self.chars[0])
            && win_drive_separator.includes(self.chars[1])
            && self.chars.len() > 2
            && end_points.includes(self.chars[2])
    }
}

impl<'a> UrlParser<'a> {
    pub(crate) fn parse(spec: &str) -> UrlResult<ParseResult> {
        let result = ParseResult {
            builder: Default::default(),
            is_valid: true,
        };

        if spec.is_empty() {
            return Ok(result);
        }

        let mut parser = UrlParser {
            spec,
            result,
            chars: spec.chars().collect(),
        };

        // First strip any invalid codepoints.
        parser.strip_invalid()?;
        if parser.chars.is_empty() {
            return Ok(parser.result);
        }

        parser.parse_scheme()?;
        if parser.chars.is_empty() {
            return Ok(parser.result);
        }

        if parser.result.builder.scheme == Some(Scheme::File) {
            parser.parse_file_host()?;
        } else {
            parser.parse_host()?;
        }

        parser.parse_path()?;
        if parser.chars.is_empty() {
            return Ok(parser.result);
        }

        if parser.chars[0] == '?' {
            parser.move_start(1)?;
            parser.parse_query()?;
            if parser.chars.is_empty() {
                return Ok(parser.result);
            }
        }

        if parser.chars[0] == '#' {
            parser.move_start(1)?;
            parser.parse_fragment()?;
            assert!(parser.chars.is_empty());
        }

        Ok(parser.result)
    }

    fn strip_invalid(&mut self) -> UrlResult<()> {
        // At this point the chars is guaranteed to be non-empty and contains
        // the entire spec.

        // These code points are not allowed at the beginning or end of a URL.
        let c0_and_space = CodepointSet::from_excluded_set("\u{0000}-\u{001F} ");

        // Find the first codepoint that is not invalid.
        let chars = self.find_forwards(&c0_and_space);
        if chars > 0 {
            self.move_start(chars)?;
            self.result.is_valid = false;
        }

        // Find the last codepoint that is not invalid.
        let chars = self.find_backwards(&c0_and_space);
        if chars > 0 {
            self.move_end(chars)?;
            self.result.is_valid = false;
        }

        // Strip the invalid whitespace codepoints.
        let non_whitespace = CodepointSet::from_excluded_set("\n\t");
        let mut i = 0;
        while i < self.chars.len() {
            if non_whitespace.includes(self.chars[i]) {
                i += 1;
            } else {
                self.chars.remove(i);
                self.result.is_valid = false;
            }
        }

        Ok(())
    }

    fn parse_scheme(&mut self) -> UrlResult<()> {
        // At this point the chars is guaranteed to be non-empty and contains
        // the entire spec.

        // scheme start state

        if !self.chars[0].is_ascii_alphabetic() {
            // This is an invalid codepoint for the start of the scheme so
            // assume there is no scheme.
            return Ok(());
        }

        // scheme state

        let scheme_points = CodepointSet::from_included_set("a-zA-Z0-9+\\-.");

        // Find the first character that isn't a valid scheme codepoint.
        let pos = self.find_forwards(&-scheme_points);
        if pos < self.chars.len() && self.chars[pos] == ':' {
            self.result.builder.scheme = Scheme::from(&self.extract_start(pos)?);
            self.move_start(1)?;
        }

        Ok(())
    }

    fn parse_hostname(&mut self, count: usize) -> UrlResult<String> {
        Ok(self.extract_start(count)?)
    }

    fn parse_host(&mut self) -> UrlResult<()> {
        // Here we are just after after the `:` of the scheme, chars is non-empty.

        let count = self.find_forwards(&CodepointSet::from_excluded_set("\\\\/"));

        // special schemes are allowed fewer that two slashes.
        let is_special = if let Some(ref s) = self.result.builder.scheme {
            if let Scheme::Special(_) = s {
                true
            } else {
                false
            }
        } else {
            false
        };

        if count < 2 && !is_special {
            // No host at all.
            return Ok(());
        }

        if self.find_forwards(&CodepointRange::from_codepoint('\\').as_included_set()) <= count
            && count < self.chars.len()
        {
            self.result.is_valid = false;
        }

        if count > 2 {
            self.result.is_valid = false;
        }

        self.move_start(count)?;
        let mut host: Host = Default::default();

        // authority state

        let mut end_pos = self.find_forwards(&CodepointSet::from_included_set("\\\\/?#"));
        if end_pos == 0 {
            return Err(self.error("Expected a non-empty host"));
        }

        let at_pos = self.find_forwards(&CodepointRange::from_codepoint('@').as_included_set());

        if at_pos == (end_pos - 1) {
            return Err(self.error("Expected a non-empty host"));
        } else if at_pos < end_pos {
            let mut auth: Authentication = Default::default();

            let pass_pos =
                self.find_forwards(&CodepointRange::from_codepoint(':').as_included_set());

            let (user_count, pass_count) = if pass_pos < at_pos {
                (pass_pos, at_pos - (pass_pos + 1))
            } else {
                (at_pos, 0)
            };

            auth.username = self.extract_start(user_count)?;
            if pass_pos < at_pos {
                self.move_start(1)?;
            }
            auth.password = self.extract_start(pass_count)?;
            self.move_start(1)?;

            host.authentication = Some(auth);

            end_pos -= at_pos + 1;
        }

        assert!(end_pos <= self.chars.len());

        // host state

        let mut in_ipv6 = false;
        let mut pos = 0;
        loop {
            if self.chars[pos] == '[' {
                in_ipv6 = true;
            } else if self.chars[pos] == ']' {
                in_ipv6 = false;
            } else if self.chars[pos] == ':' && !in_ipv6 {
                if pos == 0 {
                    self.result.is_valid = false;
                } else {
                    host.hostname = self.parse_hostname(pos)?;
                }
                self.move_start(1)?;
                end_pos -= pos + 1;

                // port state

                let bad_pos = self.find_forwards(&CodepointSet::from_excluded_set("0-9"));
                if bad_pos < end_pos {
                    return Err(self.error("Port component can only contain ascii digits."));
                }

                let port_str = self.extract_start(end_pos)?;
                match u32::from_str_radix(&port_str, 10) {
                    Ok(p) => host.port = Some(p),
                    Err(_) => return Err(self.error("Unable to parse port number.")),
                }

                break;
            }
            pos += 1;

            if pos == end_pos {
                host.hostname = self.parse_hostname(pos)?;
                break;
            }
        }

        self.result.builder.host = Some(host);

        Ok(())
    }

    fn parse_file_host(&mut self) -> UrlResult<()> {
        // Here we are just after the `:` of the scheme, chars is non-empty.

        // file state

        self.result.builder.host = Some(Default::default());

        if self.chars[0] == '/' {
            self.move_start(1)?;
        } else if self.chars[0] == '\\' {
            self.result.is_valid = false;
            self.move_start(1)?;
        } else if self.chars[0] == '?' || self.chars[0] == '#' {
            self.result.builder.host = Some(Default::default());
            return Ok(());
        } else {
            if self.starts_with_drive_letter() {
                self.result.is_valid = false;
            }

            return Ok(());
        }

        // file slash state

        if self.chars.is_empty() {
            self.result.is_valid = false;
            return Ok(());
        }

        if self.chars[0] == '/' {
            self.move_start(1)?;
        } else if self.chars[0] == '\\' {
            self.result.is_valid = false;
            self.move_start(1)?;
        } else {
            return Ok(());
        }

        if self.starts_with_drive_letter() {
            return Ok(());
        }

        // file host state

        let mut host: Host = Default::default();

        let end_points = CodepointSet::from_included_set("\\\\/?#");
        let count = self.find_forwards(&end_points);

        if count > 0 {
            host.hostname = self.parse_hostname(count)?;
            if host.hostname == "localhost" {
                host.hostname = String::new();
            }
        }

        self.result.builder.host = Some(host);

        Ok(())
    }

    fn parse_path(&mut self) -> UrlResult<()> {
        // Here we are at the start of the path, chars may be empty.

        // path start state

        let endings = CodepointSet::from_included_set("?#");

        if self.chars.is_empty() || endings.includes(self.chars[0]) {
            // If we have a host then we always have an absolute path.
            if self.result.builder.host.is_some() {
                self.result.builder.path = Path::from("/");
            }
            return Ok(());
        }

        let separators = CodepointSet::from_included_set("\\\\/");

        let mut is_absolute = separators.includes(self.chars[0]);
        if is_absolute {
            if self.chars[0] == '\\' {
                self.result.is_valid = false;
            }
            self.move_start(1)?;
        }

        let mut pos = 0;
        loop {
            if pos == self.chars.len()
                || endings.includes(self.chars[pos])
                || separators.includes(self.chars[pos])
            {
                // Parse out path part.

                if pos == 2
                    && self.result.builder.path.components.is_empty()
                    && self.result.builder.scheme == Some(Scheme::File)
                    && self.chars[0].is_alphabetic()
                    && (self.chars[1] == '|' || self.chars[1] == ':')
                {
                    self.chars[1] = ':';
                    is_absolute = true;
                }

                let part = self.extract_start(pos)?;
                pos = 0;
                self.result.builder.path.components.push(part);

                if self.chars.is_empty() || endings.includes(self.chars[pos]) {
                    break;
                }

                if self.chars[pos] == '\\' {
                    self.result.is_valid = false;
                }

                self.move_start(1)?;
                pos = 0;
            } else if self.chars[pos] == '%'
                && (self.chars.len() - pos < 3
                    || !self.chars[1].is_ascii_hexdigit()
                    || !self.chars[2].is_ascii_hexdigit())
            {
                self.result.is_valid = false;
                self.chars.insert(pos + 1, '2');
                self.chars.insert(pos + 2, '5');
                pos += 3;
            } else {
                // TODO Check if invalid.
                pos += 1;
            }
        }

        if is_absolute {
            self.result.builder.path.components.insert(0, String::new());
        }

        self.result.builder.normalize();

        Ok(())
    }

    fn parse_query(&mut self) -> UrlResult<()> {
        // At this point chars may be empty and will not contain the `?` prefix.

        // query state

        let count = self.find_forwards(&CodepointRange::from_codepoint('#').as_included_set());
        // TODO check for invalid codepoints.

        self.result.builder.query = Some(self.extract_start(count)?);

        Ok(())
    }

    fn parse_fragment(&mut self) -> UrlResult<()> {
        // At this point chars may be empty and will not contain the `#` prefix.

        // fragment state

        // TODO check for invalid codepoints.

        self.result.builder.fragment = Some(self.extract_start(self.chars.len())?);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::cyclomatic_complexity)]
    use super::*;

    fn verify_codepoint_range(range: &CodepointRange, includes: Vec<char>, excludes: Vec<char>) {
        for ch in includes {
            if !range.includes(ch) {
                panic!(format!("Range failed to include '{}'.", ch))
            }
        }

        for ch in excludes {
            if range.includes(ch) {
                panic!(format!("Range failed to exclude '{}'.", ch))
            }
        }
    }

    #[test]
    fn test_codepoint_range() {
        let range = CodepointRange::from_codepoint('b');
        verify_codepoint_range(&range, vec!['b'], vec!['a', 'c']);

        let range = CodepointRange::from_range('b', 'd');
        verify_codepoint_range(&range, vec!['b', 'c', 'd'], vec!['a', 'e']);
    }

    fn verify_codepoint_set(set: &CodepointSet, includes: Vec<char>, excludes: Vec<char>) {
        for ch in includes {
            if !set.includes(ch) {
                panic!(format!("Set failed to include '{}'.", ch))
            }
        }

        for ch in excludes {
            if set.includes(ch) {
                panic!(format!("Set failed to exclude '{}'.", ch))
            }
        }
    }

    #[test]
    fn test_codepoint_set() {
        let set = CodepointRange::from_codepoint('b').as_included_set();
        verify_codepoint_set(&set, vec!['b'], vec!['a', 'c']);

        let set = CodepointRange::from_range('b', 'd').as_included_set();
        verify_codepoint_set(&set, vec!['b', 'c', 'd'], vec!['a', 'e']);

        let set = CodepointSet::from_included_set("A-Gb-cz");
        verify_codepoint_set(
            &set,
            vec!['A', 'B', 'F', 'G', 'b', 'c', 'z'],
            vec!['a', 'd', 'y'],
        );

        let mut set = CodepointSet::from_included_set("b-dg4-8");
        verify_codepoint_set(
            &set,
            vec!['b', 'c', 'd', 'g', '4', '5', '7', '8'],
            vec!['a', 'e', '3', '9'],
        );

        set -= CodepointRange::from_codepoint('5');
        verify_codepoint_set(&set, vec!['6', '7', '8'], vec!['5', '3', '9']);

        let set = CodepointSet::from_included_set("4-5\\-7");
        verify_codepoint_set(&set, vec!['4', '5', '-', '7'], vec!['3', '6', '8', '\\']);
    }

    /// Test that invalid codepoints are stripped.
    #[test]
    fn test_parser_invalid() {
        let result = UrlParser::parse("  https://www.google.com/ ").unwrap();
        assert!(!result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("https"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www.google.com"),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("\tht\ntps://w\tww.g\n\toogle.com/\n\n").unwrap();
        assert!(!result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("https"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www.google.com"),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn test_parser_scheme() {
        let result = UrlParser::parse("goodscheme:").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::NotSpecial(String::from("goodscheme"))),
                host: None,
                path: Default::default(),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("UppErscheme:").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::NotSpecial(String::from("upperscheme"))),
                host: None,
                path: Default::default(),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("noscheme").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from("noscheme"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("1badscheme:").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from("1badscheme:"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("bad>scheme:").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from("bad>scheme:"),
                query: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn test_parser_host() {
        let result = UrlParser::parse("scheme://host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::NotSpecial(String::from("scheme"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        assert!(UrlParser::parse("scheme://").is_err());

        let result = UrlParser::parse("scheme:////host").unwrap();
        assert!(!result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::NotSpecial(String::from("scheme"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("scheme:\\\\host").unwrap();
        assert!(!result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::NotSpecial(String::from("scheme"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("//host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("//foo:bar@host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("foo"),
                        password: String::from("bar"),
                    }),
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("//foo@host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("foo"),
                        password: String::new(),
                    }),
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("//:bar@host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::new(),
                        password: String::from("bar"),
                    }),
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("//:bar@");
        assert!(result.is_err());

        let result = UrlParser::parse("//host:ng");
        assert!(result.is_err());

        let result = UrlParser::parse("//host:59").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: Some(59),
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("http:host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("http:/host").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("file:///").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("file://").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("file://localhost/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("file://c:/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/c:/"),
                query: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn test_parser_path() {
        let result = UrlParser::parse("file://c:/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/c:/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("file:///c|/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/c:/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("file:///foo/c|/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from("/foo/c|/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("http://host/foo/bar").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from("/foo/bar"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("http://host/foo/bar/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from("/foo/bar/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("http://host/foo/../bar/./..").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("http://host/./foo/../bar/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from("/bar/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("/foo/bar").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from("/foo/bar"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("/foo/bar/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from("/foo/bar/"),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse("/foo/../bar/").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from("/bar/"),
                query: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn test_parser_query() {
        let result = UrlParser::parse("?foobarhello").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Default::default(),
                query: Some(String::from("foobarhello")),
                fragment: None,
            }
        );

        let result = UrlParser::parse("http://www?foobarhello").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www"),
                    port: None,
                }),
                path: Path::from("/"),
                query: Some(String::from("foobarhello")),
                fragment: None,
            }
        );
    }

    #[test]
    fn test_parser_fragment() {
        let result = UrlParser::parse("#foobarhello").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Default::default(),
                query: None,
                fragment: Some(String::from("foobarhello")),
            }
        );

        let result = UrlParser::parse("http://www#foobarhello").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www"),
                    port: None,
                }),
                path: Path::from("/"),
                query: None,
                fragment: Some(String::from("foobarhello")),
            }
        );

        let result = UrlParser::parse("?#foobarhello").unwrap();
        assert!(result.is_valid);
        assert_eq!(
            result.builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Default::default(),
                query: Some(String::new()),
                fragment: Some(String::from("foobarhello")),
            }
        );
    }
}
