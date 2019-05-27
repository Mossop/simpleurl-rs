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

pub struct CodepointSetIterator<'a> {
    set: CodepointSet,
    base: Chars<'a>,
    is_done: bool,
}

impl<'a> CodepointSetIterator<'a> {
    fn new(set: CodepointSet, base: &str) -> CodepointSetIterator {
        CodepointSetIterator {
            set,
            base: base.chars(),
            is_done: false,
        }
    }
}

impl<'a> Iterator for CodepointSetIterator<'a> {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        if self.is_done {
            return None;
        }

        let mut buffer = String::new();

        while let Some(c) = self.base.next() {
            if self.set.includes(c) {
                return Some(buffer);
            } else {
                buffer.push(c);
            }
        }

        self.is_done = true;
        Some(buffer)
    }
}

#[derive(Default, Clone)]
pub(crate) struct CodepointSet {
    included: Vec<CodepointRange>,
    excluded: Vec<CodepointRange>,
}

impl CodepointSet {
    pub fn from_included_set(set: &str) -> CodepointSet {
        let mut pointset: CodepointSet = Default::default();
        pointset.include_set(set);
        pointset
    }

    pub fn from_excluded_set(set: &str) -> CodepointSet {
        let mut pointset: CodepointSet = Default::default();
        pointset.exclude_set(set);
        pointset
    }

    pub fn include_set(&mut self, set: &str) {
        self.included.extend(CodepointRangeIterator::new(set));
    }

    pub fn exclude_set(&mut self, set: &str) {
        self.excluded.extend(CodepointRangeIterator::new(set));
    }

    pub fn includes(&self, c: char) -> bool {
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

    pub fn split(self, string: &str) -> CodepointSetIterator {
        CodepointSetIterator::new(self, string)
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

/// Responsible for parsing URLs.
pub(crate) struct UrlParser<'a> {
    spec: &'a str,
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
}

impl<'a> UrlParser<'a> {
    pub(crate) fn parse_spec(spec: &str) -> UrlResult<UrlBuilder> {
        if spec.is_empty() {
            return Ok(Default::default());
        }

        let mut parser = UrlParser {
            spec,
            chars: spec.chars().collect(),
        };

        parser.parse()
    }

    fn parse(&mut self) -> UrlResult<UrlBuilder> {
        // First strip any invalid codepoints.
        self.strip_invalid()?;
        if self.chars.is_empty() {
            return Ok(Default::default());
        }

        let mut builder: UrlBuilder = Default::default();

        builder.scheme = self.parse_scheme()?;
        if self.chars.is_empty() {
            return Ok(builder);
        }

        if builder.scheme == Some(Scheme::File) {
            builder.host = self.parse_file_host()?;
        } else {
            builder.host = self.parse_host()?;
        }

        builder.path =
            self.parse_path(builder.host.is_some(), builder.scheme == Some(Scheme::File))?;
        if self.chars.is_empty() {
            return Ok(builder);
        }

        if self.chars[0] == '?' {
            self.move_start(1)?;
            builder.query = Some(self.parse_query()?);
            if self.chars.is_empty() {
                return Ok(builder);
            }
        }

        if self.chars[0] == '#' {
            self.move_start(1)?;
            builder.fragment = Some(self.parse_fragment()?);
        }

        assert!(self.chars.is_empty());
        Ok(builder)
    }

    fn strip_invalid(&mut self) -> UrlResult<()> {
        // At this point the chars is guaranteed to be non-empty and contains
        // the entire spec.

        // These code points are not allowed at the beginning or end of a URL.
        let c0_and_space = CodepointSet::from_excluded_set("\u{0000}-\u{0020} ");

        // Find the first codepoint that is not invalid.
        let chars = self.find_forwards(&c0_and_space);
        if chars > 0 {
            self.move_start(chars)?;
        }

        // Find the last codepoint that is not invalid.
        let chars = self.find_backwards(&c0_and_space);
        if chars > 0 {
            self.move_end(chars)?;
        }

        // Strip the invalid whitespace codepoints.
        let non_whitespace = CodepointSet::from_excluded_set("\n\t");
        let mut i = 0;
        while i < self.chars.len() {
            if non_whitespace.includes(self.chars[i]) {
                i += 1;
            } else {
                self.chars.remove(i);
            }
        }

        Ok(())
    }

    fn parse_scheme(&mut self) -> UrlResult<Option<Scheme>> {
        // At this point chars is guaranteed to be non-empty and contains
        // the entire spec.

        // scheme start state

        if !self.chars[0].is_ascii_alphabetic() {
            // This is an invalid codepoint for the start of the scheme so
            // assume there is no scheme.
            return Ok(None);
        }

        // scheme state

        let scheme_points = CodepointSet::from_included_set("a-zA-Z0-9+\\-.");

        // Find the first character that isn't a valid scheme codepoint.
        let pos = self.find_forwards(&-scheme_points);
        if pos == self.chars.len() || self.chars[pos] != ':' {
            Ok(None)
        } else {
            let scheme_str = self.extract_start(pos)?;
            // Skip the `:`
            self.move_start(1)?;
            Ok(Scheme::from(&scheme_str))
        }
    }

    fn parse_hostname(&mut self, length: usize) -> UrlResult<String> {
        Ok(self.extract_start(length)?)
    }

    fn parse_host(&mut self) -> UrlResult<Option<Host>> {
        // Here we are just after after the `:` of the scheme, chars is not empty.

        let count = self.find_forwards(&CodepointSet::from_excluded_set("\\\\/"));
        if count < 2 {
            // No host separator means no host.
            return Ok(None);
        }

        // We have some kind of host for sure now.
        let mut host: Host = Default::default();

        // Strip all slashes?
        self.move_start(2)?;

        // authority state

        // The length of the auth/hostname/port portion.
        let mut host_len = if count > 2 {
            0
        } else {
            self.find_forwards(&CodepointSet::from_included_set("\\\\/?#"))
        };

        if host_len == 0 {
            return Ok(Some(host));
        }

        // The length of the authority portion.
        let auth_len = self.find_forwards(&CodepointRange::from_codepoint('@').as_included_set());

        // There is only auth info if it occurs before the end of the host part.
        if auth_len < host_len {
            host_len -= auth_len + 1;

            let mut auth: Authentication = Default::default();

            let pass_pos =
                self.find_forwards(&CodepointRange::from_codepoint(':').as_included_set());
            assert!(pass_pos != auth_len);

            if pass_pos < auth_len {
                // Handle the case where there is a password given.
                auth.username = self.extract_start(pass_pos)?;
                // Skip over the `:`.
                self.move_start(1)?;
                auth.password = self.extract_start(auth_len - (pass_pos + 1))?;
            } else {
                // Otherwise the entire auth is the username.
                auth.username = self.extract_start(auth_len)?;
            }

            // Skip over the `@`.
            self.move_start(1)?;

            host.authentication = Some(auth);
        }

        assert!(host_len <= self.chars.len());

        // host state

        let mut in_ipv6 = false;
        let mut pos = 0;
        loop {
            if pos == host_len {
                host.hostname = self.parse_hostname(pos)?;
                break;
            }

            if self.chars[pos] == '[' {
                in_ipv6 = true;
            } else if self.chars[pos] == ']' {
                in_ipv6 = false;
            } else if self.chars[pos] == ':' && !in_ipv6 {
                if pos == 0 {
                    return Err(self.error("Cannot include a port without a hostname."));
                }

                host.hostname = self.parse_hostname(pos)?;
                self.move_start(1)?;

                // port state

                let port_str = self.extract_start(host_len - (pos + 1))?;
                match u32::from_str_radix(&port_str, 10) {
                    Ok(p) => host.port = Some(p),
                    Err(_) => return Err(self.error("Unable to parse port number.")),
                }

                break;
            }
            pos += 1;
        }

        Ok(Some(host))
    }

    fn parse_file_host(&mut self) -> UrlResult<Option<Host>> {
        // Here we are just after the `:` of the scheme, chars is not empty.

        // file state

        Ok(self.parse_host()?.map(|mut h| {
            if h.hostname == "localhost" {
                h.hostname = String::new();
            }
            h
        }))
    }

    fn parse_path(&mut self, has_host: bool, is_file_path: bool) -> UrlResult<Path> {
        // Here we are at the start of the path, chars may be empty.

        // path start state

        // If there is a host then the path is always absolute.
        let endings = CodepointSet::from_included_set("?#");
        let length = if self.chars.is_empty() {
            0
        } else {
            self.find_forwards(&endings)
        };

        if length == 0 {
            // If we have a host then we always have an absolute path.
            if has_host {
                return Ok(Path::root_path());
            }
            return Ok(Default::default());
        }

        let mut path: Path = self.extract_start(length)?.parse()?;

        if is_file_path && path.components.len() > 1 && path.is_absolute() {
            if let Some(component) = path.components.get(1) {
                if component.len() == 2 && component.ends_with('|') {
                    if let Some(drive) = component.chars().next() {
                        if drive.is_ascii_alphabetic() {
                            path.components.remove(1);
                            path.components.insert(1, drive.to_string() + ":");
                        }
                    }
                }
            }
        }

        Ok(path)
    }

    fn parse_query(&mut self) -> UrlResult<String> {
        // At this point chars may be empty and will not contain the `?` prefix.

        // query state

        let count = self.find_forwards(&CodepointRange::from_codepoint('#').as_included_set());

        Ok(self.extract_start(count)?)
    }

    fn parse_fragment(&mut self) -> UrlResult<String> {
        // At this point chars may be empty and will not contain the `#` prefix.

        // fragment state

        Ok(self.extract_start(self.chars.len())?)
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::cognitive_complexity)]
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

        let set = CodepointSet::from_included_set("4-5\\\\97");
        verify_codepoint_set(&set, vec!['4', '5', '\\', '7', '9'], vec!['3', '6', '8']);
    }

    fn check_split(set: CodepointSet, string: &str, expected: Vec<&str>) {
        assert_eq!(
            set.split(string).collect::<Vec<String>>(),
            expected
                .iter()
                .cloned()
                .map(|s| s.to_owned())
                .collect::<Vec<String>>()
        );
    }

    #[test]
    fn test_split_codepointset() {
        check_split(
            CodepointSet::from_included_set("s"),
            "foosbar",
            vec!["foo", "bar"],
        );

        check_split(
            CodepointSet::from_included_set("g-h"),
            "foogbarhzed",
            vec!["foo", "bar", "zed"],
        );
    }

    /// Test that invalid codepoints are stripped.
    #[test]
    fn test_parser_invalid() -> UrlResult<()> {
        let builder = UrlParser::parse_spec("  https://www.google.com/ ")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("https"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www.google.com"),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("\tht\ntps://w\tww.g\n\toogle.com/\n\n")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("https"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www.google.com"),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        Ok(())
    }

    #[test]
    fn test_parser_scheme() -> UrlResult<()> {
        let builder = UrlParser::parse_spec("goodscheme:")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("goodscheme"))),
                host: None,
                path: Default::default(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("UppErscheme:")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("upperscheme"))),
                host: None,
                path: Default::default(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("noscheme")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["noscheme"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("1badscheme:")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["1badscheme:"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("bad>scheme:")?;
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["bad>scheme:"]),
                query: None,
                fragment: None,
            }
        );

        Ok(())
    }

    #[test]
    fn test_parser_host() -> UrlResult<()> {
        let builder = UrlParser::parse_spec("scheme://host")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("scheme://")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: Some(Default::default()),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("scheme:/")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: None,
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("scheme:/foo")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: None,
                path: Path::from_components(vec!["", "foo"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("scheme:foo")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: None,
                path: Path::from_components(vec!["foo"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http:///")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Default::default()),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Default::default()),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("scheme:////host")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: Some(Default::default()),
                path: Path::from_components(vec!["", "", "host"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("scheme:\\\\host")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("scheme"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("//host")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("//foo:bar@host")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
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
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("//foo@host")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
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
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("//:bar@host")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
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
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("//:bar@")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::new(),
                        password: String::from("bar"),
                    }),
                    hostname: String::new(),
                    port: None
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse_spec("//host:ng");
        assert!(result.is_err());

        let builder = UrlParser::parse_spec("//host:59")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: Some(59),
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http:host")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: None,
                path: Path::from_components(vec!["host"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http:/host")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: None,
                path: Path::from_components(vec!["", "host"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file:////")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from_components(vec!["", "", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file:///")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file://")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file:/")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: None,
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file://localhost/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let result = UrlParser::parse_spec("file://c:/");
        assert!(result.is_err());

        Ok(())
    }

    #[test]
    fn test_parser_path() -> UrlResult<()> {
        let builder = UrlParser::parse_spec("file:///c:/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from_components(vec!["", "c:", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file:///c|/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from_components(vec!["", "c:", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("file:///foo/c|/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "c|", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://host/foo/bar")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://host/foo/bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://host/foo/../bar/./..")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "..", "bar", ".", ".."]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://host/./foo/../bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", ".", "foo", "..", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("/foo/bar")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["", "foo", "bar"]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("/foo/bar/")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["", "foo", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("/foo/../bar/")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["", "foo", "..", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://user:pass@host/foo/bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("user"),
                        password: String::from("pass"),
                    }),
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://user:@host/foo/bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("user"),
                        password: String::new(),
                    }),
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://user@host/foo/bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("user"),
                        password: String::new(),
                    }),
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://:pass@host/foo/bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::new(),
                        password: String::from("pass"),
                    }),
                    hostname: String::from("host"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        Ok(())
    }

    #[test]
    fn test_parser_query() -> UrlResult<()> {
        let builder = UrlParser::parse_spec("?foobarhello")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Default::default(),
                query: Some(String::from("foobarhello")),
                fragment: None,
            }
        );

        let builder = UrlParser::parse_spec("http://www?foobarhello")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www"),
                    port: None,
                }),
                path: Path::root_path(),
                query: Some(String::from("foobarhello")),
                fragment: None,
            }
        );

        Ok(())
    }

    #[test]
    fn test_parser_fragment() -> UrlResult<()> {
        let builder = UrlParser::parse_spec("#foobarhello")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Default::default(),
                query: None,
                fragment: Some(String::from("foobarhello")),
            }
        );

        let builder = UrlParser::parse_spec("http://www#foobarhello")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www"),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: Some(String::from("foobarhello")),
            }
        );

        let builder = UrlParser::parse_spec("?#foobarhello")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Default::default(),
                query: Some(String::new()),
                fragment: Some(String::from("foobarhello")),
            }
        );

        let builder = UrlParser::parse_spec("hello?#foobarhello")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["hello"]),
                query: Some(String::new()),
                fragment: Some(String::from("foobarhello")),
            }
        );

        let builder = UrlParser::parse_spec("hello#foobarhello?")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["hello"]),
                query: None,
                fragment: Some(String::from("foobarhello?")),
            }
        );

        Ok(())
    }

    fn parse_succeeds<'a, O>(spec: &str, base: O, expected: &str) -> UrlResult<()>
    where
        O: Into<Option<&'a str>>,
    {
        let builder = UrlParser::parse_spec(spec)?;

        let mut builder = match base.into() {
            Some(s) => UrlParser::parse_spec(s)?.join(&builder)?,
            None => builder,
        };

        builder.normalize();
        assert_eq!(builder.spec(), expected);

        Ok(())
    }

    fn parse_fails(spec: &str) {
        // Here a parse failure essentially means "not an absolute URL".
        let failed = match UrlParser::parse_spec(spec) {
            Ok(builder) => !builder.is_absolute_url(),
            Err(_) => true,
        };

        assert!(failed);
    }

    #[test]
    fn test_parser_spec_examples() -> UrlResult<()> {
        parse_succeeds(
            "https://example.com/././foo",
            None,
            "https://example.com/foo",
        )?;

        parse_succeeds(
            "example",
            "https://example.com/demo",
            "https://example.com/example",
        )?;

        // Test seems wrong? Expected is meant to be `file:///C:/`. Firefox
        // disagrees.
        parse_succeeds("..", "file:///C:/demo", "file:///")?;

        // Needs percent decoding to work.
        // parse_succeeds("file://loc%61lhost/", None, "file:///");

        // Needs host parsing.
        // parse_succeeds("https://EXAMPLE.com/../x", None, "https://example.com/x");

        parse_succeeds(
            "https://////example.com///",
            None,
            "https://////example.com///",
        )?;

        parse_succeeds(
            "\\example\\..\\demo/.\\",
            "https://example.com/",
            "https://example.com/demo/",
        )?;
        parse_succeeds("file:///C|/demo", None, "file:///C:/demo")?;
        parse_succeeds(
            "https://user:password@example.org/",
            None,
            "https://user:password@example.org/",
        )?;

        // Needs percent encoding.
        /*parse_succeeds(
            "https://example.org/foo bar",
            None,
            "https://example.org/foo%20bar",
        );*/

        // Needs percent encoding.
        // parse_fails("https://ex ample.org/");

        parse_fails("example");
        parse_fails("https:example.org");
        parse_fails("https://example.com:demo");
        parse_fails("hello:world");
        parse_fails("https:example.org");

        // Needs host parsing.
        // parse_fails("http://[www.example.com]/");

        Ok(())
    }
}
