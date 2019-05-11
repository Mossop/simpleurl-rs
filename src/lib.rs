//! A crate for creating, parsing and manipulating URLs including relative URLs.
//!
//! There are a multitude of crates dedicated to URL parsing and serialising so
//! I strongly recommend you look them over and evaluate the options available.
//! I created this one partly because I am new to Rust and wanted to develop a
//! library and partly because when looking at the other crates I could not find
//! one that supported relative URLs very well including automatically
//! generating relative urls from two absolute urls.
//!
//! The lowest level of URL manipulation provided is the [`UrlBuilder`] which
//! allows you to build a URL from the precise components you want starting from
//! nothing. This can mean that you end up with an invalid URL though so the
//! higher level structs may be useful.
//!
//! At the higher level this crate provides the [`Url`] and [`RelativeUrl`]
//! structs. Both use the [`UrlBuilder`] under the hood bug [`Url`] ensures that
//! you always have a valid absolute URL and [`RelativeUrl`] ensures that you
//! always have a valid relative URL.
//!
//! Both [`Url`] and [`RelativeUrl`] follow the web specification for
//! [URL objects](https://developer.mozilla.org/en-US/docs/Web/API/URL) with a
//! few minor differences where it makes sense.
//!
//! The term `spec` is used frequently throughout the docs to mean a string of
//! characters that is intended to represent. [`UrlBuilder`], [`Url`] and
//! [`RelativeUrl`] all provide a `spec()` method to serialize their current
//! URL into a spec.
//!
//! # Examples
//!
//! ```
//! # use urlbuilder::UrlError;
//! use urlbuilder::{Url, RelativeUrl};
//!
//! # fn main() -> Result<(), UrlError> {
//! let mut url: Url = "https://www.google.com/foo/bar".parse()?;
//! assert_eq!(url.spec(), "https://www.google.com/foo/bar");
//! assert_eq!(url.protocol(), "https:");
//! url.set_host("www.example.com")?;
//! assert_eq!(url.spec(), "https://www.example.com/foo/bar");
//!
//! let mut relative: RelativeUrl = "/bar/foo".parse()?;
//! assert_eq!(relative.spec(), "/bar/foo");
//!
//! let joined = url.join(&relative)?;
//! assert_eq!(joined.spec(), "https://www.example.com/bar/foo");
//!
//! relative.set_host("www.google.com");
//! assert_eq!(relative.spec(), "//www.google.com/bar/foo");
//!
//! let joined = url.join(&relative)?;
//! assert_eq!(joined.spec(), "https://www.google.com/bar/foo");
//! # Ok(())
//! # }
//! ```
//!
//! [`Url`]: struct.Url.html
//! [`RelativeUrl`]: struct.RelativeUrl.html
//! [`UrlBuilder`]: struct.UrlBuilder.html

#![warn(missing_docs)]
#![deny(unused_variables)]

use regex::Regex;
use std::convert::{TryFrom, TryInto};
use std::error;
use std::fmt;
use std::str::FromStr;
use std::string::ToString;

/// These code points are not allowed anywhere in a uri string.
const C0_CONTROL: &str = "\u{0000}-\u{001F}";
/// These are the allowable code points in most parts of a uri string.
const URL_CODE_POINTS: &str =
    "0-9A-Za-z!$&'()*+,-\\./:;=?@_~\u{00A0}-\u{D7FF}\u{E000}-\u{10FFFD}--\
     [\u{FDD0}-\u{FDEF}\u{FFFE}\u{FFFF}\u{1FFFE}\u{1FFFF}\u{2FFFE}\u{2FFFF}\
     \u{3FFFE}\u{3FFFF}\u{4FFFE}\u{4FFFF}\u{5FFFE}\u{5FFFF}\u{6FFFE}\u{6FFFF}\
     \u{7FFFE}\u{7FFFF}\u{8FFFE}\u{8FFFF}\u{9FFFE}\u{9FFFF}\u{AFFFE}\u{AFFFF}\
     \u{BFFFE}\u{BFFFF}\u{CFFFE}\u{CFFFF}\u{DFFFE}\u{DFFFF}\u{EFFFE}\u{EFFFF}\
     \u{FFFFE}\u{FFFFF}\u{10FFFE}\u{10FFFF}]\
     ";
/// Matches a percent encoded code point.
const PERCENT_ENCODED_BYTE: &str = "%[0-9a-fA-F]{2}";

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

/// Represents an error that occurred while parsing or manipulating a URI.
///
/// Currently doesn't provide much that a program can use to figure out what
/// went wrong.
#[derive(Debug)]
pub struct UrlError {
    spec: String,
    message: String,
}

impl UrlError {
    /// Creates a new `UrlError` from a message and the
    /// spec currently being parsed.
    fn new(message: &str, spec: &str) -> Self {
        Self {
            spec: spec.to_owned(),
            message: message.to_owned(),
        }
    }
}

impl fmt::Display for UrlError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_fmt(format_args!("Url error: {}", self.message))
    }
}

impl error::Error for UrlError {}

/// A specialized result where the error is always a [`UrlError`](struct.UrlError.html).
pub type UrlResult<T> = Result<T, UrlError>;

/// A simple wrapper around generating a regular expression.
fn regex(r: &str) -> UrlResult<Regex> {
    match Regex::new(r) {
        Ok(result) => Ok(result),
        Err(err) => Err(match err {
            regex::Error::Syntax(_) => UrlError::new(
                "Syntax error in regular expression. Please report a bug.",
                r,
            ),
            regex::Error::CompiledTooBig(_) => {
                UrlError::new("Regular expressions was too large. Please report a bug.", r)
            }
            _ => UrlError::new(
                "Unexpected regular expression error. Please report a bug.",
                r,
            ),
        }),
    }
}

/// The default ports for the non-file special schemes.
const SPECIAL_SCHEMES: [(&str, u32); 6] = [
    ("ftp", 21),
    ("gopher", 70),
    ("http", 80),
    ("https", 443),
    ("ws", 80),
    ("wss", 443),
];

/// Lists the different scheme types.
#[derive(Debug, Clone, PartialEq)]
enum Scheme {
    Special(String),
    NotSpecial(String),
    File,
}

impl Scheme {
    /// Converts a string to a `Scheme`. The string should
    /// not contain a trailing `:`.
    fn from(scheme: &str) -> Option<Self> {
        if scheme.is_empty() {
            return None;
        }

        let lower = scheme.to_lowercase();

        if lower == "file" {
            Some(Scheme::File)
        } else {
            for info in &SPECIAL_SCHEMES {
                if lower == info.0 {
                    return Some(Scheme::Special(lower));
                }
            }
            Some(Scheme::NotSpecial(percent_decode(&lower)))
        }
    }

    /// Gets the default port for this scheme. Only Special schemes have a
    /// default port.
    fn default_port(&self) -> Option<u32> {
        match self {
            Scheme::Special(s) => {
                for info in &SPECIAL_SCHEMES {
                    if s == info.0 {
                        return Some(info.1);
                    }
                }

                panic!("Unreachable");
            }
            _ => None,
        }
    }
}

impl FromStr for Scheme {
    type Err = UrlError;

    fn from_str(scheme: &str) -> Result<Self, Self::Err> {
        match Scheme::from(scheme) {
            Some(s) => Ok(s),
            None => Err(UrlError::new("Failed to parse scheme.", scheme)),
        }
    }
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Scheme::Special(s) => f.write_str(&s),
            Scheme::NotSpecial(s) => f.write_str(&percent_encode(&s)),
            Scheme::File => f.write_str("file"),
        }
    }
}

/// Holds the username, password, hostname and port of the URL.
///
/// There is always a hostname, the other fields are optional.
#[derive(Debug, Clone, PartialEq, Default)]
struct Host {
    username: Option<String>,
    password: Option<String>,
    hostname: String,
    port: Option<u32>,
}

impl Host {
    /// Gets the host and port parts of the host.
    fn hostport(&self) -> String {
        match self.port {
            Some(p) => format!("{}:{}", percent_encode(&self.hostname), p),
            None => self.hostname.clone(),
        }
    }
}

impl fmt::Display for Host {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.username.is_some() || self.password.is_some() {
            if let Some(ref u) = self.username {
                f.write_str(&percent_encode(&u))?;
            }

            if let Some(ref p) = self.password {
                f.write_fmt(format_args!(":{}", &percent_encode(&p)))?;
            }

            f.write_str("@")?;
        }

        f.write_str(&self.hostport())
    }
}

/// Normalizes set of path segments by removing any `.` segments and making `..`
/// elements remove the preceeding segment. When the path is absolute any `..`
/// segments at the start of the path are stripped.
fn normalize(components: &[String]) -> Vec<String> {
    let mut result: Vec<String> = Default::default();

    if components.is_empty() {
        result.extend_from_slice(components);
        return result;
    }

    // We know there is at least one element here.
    let is_absolute = components[0] == "";

    let mut pos: usize = 0;
    let mut result_len: usize = 0;
    let mut needs_dir = false;

    while pos < components.len() {
        if components[pos] == "." {
            // Just ignore this component.
            needs_dir = true;
        } else if components[pos] == ".." {
            if is_absolute && result_len == 1 {
                // Ignore preceeding double dot segments from absolute paths.
                needs_dir = false;
            } else if result_len > 0 && result[result_len - 1] != ".." {
                // Strip off the last path entry.
                result.truncate(result_len - 1);
                result_len -= 1;
                needs_dir = true;
            } else {
                // This is the first part or the previous part could not be stripped.
                result.push(components[pos].clone());
                result_len += 1;
                needs_dir = false; // ???
            }
        } else {
            // Just pass through everything else.
            result.push(components[pos].clone());
            result_len += 1;
            needs_dir = false;
        }

        pos += 1;
    }

    if needs_dir {
        result.push(String::new());
    }

    result
}

/// Holds a relative or absolute path. Held as a set of path segments such that
/// joining the segments with a `/` will result in the full path. A preceeding
/// `""` marks the path as absolute, a trailing `""` marks it as referencing
/// to something treated like a directory.
#[derive(Debug, Clone, PartialEq, Default)]
struct Path {
    components: Vec<String>,
}

impl Path {
    /// Converts a full path to a `Path`.
    pub fn from(path: &str) -> Self {
        if path.is_empty() {
            Default::default()
        } else {
            Path {
                components: path.split('/').map(|p| percent_decode(p)).collect(),
            }
        }
    }

    /// Normalizes the path components.
    fn normalize(&mut self) {
        self.components = normalize(&self.components);
    }

    /// Joins one path to another. At a high level this is similar to being in
    /// this path in a filesystem and running `cd <relative>`.
    pub fn join(&self, relative: &Path) -> UrlResult<Path> {
        if relative.is_empty() {
            return Ok(self.clone());
        }

        if relative.is_absolute() {
            return Ok(relative.clone());
        }

        let mut new_path = self.clone();
        if !new_path.is_empty() {
            new_path.components.truncate(new_path.components.len() - 1);
        }

        new_path.components.extend_from_slice(&relative.components);
        new_path.normalize();

        Ok(new_path)
    }

    /// Generates a relative path then when joined with the `base_path` will
    /// result in this path.
    pub fn relative_to(&self, base_path: &Path) -> UrlResult<Path> {
        if self.is_absolute() != base_path.is_absolute() {
            return Err(UrlError::new(
                "Paths are differing forms.",
                &base_path.to_string(),
            ));
        }

        // Shortcut the easy case.
        if self == base_path {
            return Ok(Default::default());
        }

        let normalized_new = normalize(&self.components);
        let normalized_base = normalize(&base_path.components);

        let mut new_components = normalized_new.into_iter();
        let mut base_components = normalized_base.into_iter();

        let mut result: Vec<String> = Default::default();

        let mut new = new_components.next();
        let mut base = base_components.next();
        while new == base {
            if new == None {
                // This means all the components match, which chould have been
                // caught above.
                panic!("Matching components should have been matched previously.")
            }

            new = new_components.next();
            base = base_components.next();
        }

        // Either the path parts differ, or one of the paths ends with a
        // directory marker.

        // Add a ".." part for every remaining part of base
        if base != None && base != Some(String::new()) {
            let count = base_components.count();

            for _ in 0..count {
                result.push(String::from(".."));
            }
        }

        // Now add the rest of self's components including this one.
        while let Some(s) = new {
            result.push(s.clone());
            new = new_components.next();
        }

        let result = Path { components: result };
        Ok(result)
    }

    /// Returns true if the current path has no segments.
    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    /// Returns true if this is an absolute path (starts with `/`).
    pub fn is_absolute(&self) -> bool {
        match self.components.first() {
            Some(p) => p.is_empty(),
            None => false,
        }
    }

    /// Returns true if this is a relative path (does not start with `/`).
    pub fn is_relative(&self) -> bool {
        match self.components.first() {
            Some(p) => !p.is_empty(),
            None => true,
        }
    }

    /// Returns true if this references a directory (ends with `/`).
    pub fn is_directory(&self) -> bool {
        match self.components.last() {
            Some(p) => p.is_empty(),
            None => false,
        }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_str(
            &self
                .components
                .iter()
                .map(|p| percent_encode(p))
                .collect::<Vec<String>>()
                .join("/"),
        )
    }
}

/// Currently unused.
#[derive(Debug, Clone, PartialEq)]
pub struct UrlSearchParams {}

impl fmt::Display for UrlSearchParams {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        Ok(())
    }
}

/// Parses a scheme out of the current spec.
fn parse_scheme(
    spec: &str,
    start_pos: &mut usize,
    end_pos: &mut usize,
) -> UrlResult<Option<Scheme>> {
    if end_pos < start_pos {
        return Err(UrlError::new("Parse failure (end < start).", spec));
    }

    let search = &spec[*start_pos..*end_pos];
    let re = regex("[a-zA-Z][a-zA-Z0-9+-\\.]*:")?;

    let scheme_match = match re.find(search) {
        Some(m) => m,
        None => return Ok(None),
    };

    if scheme_match.start() >= scheme_match.end() {
        return Err(UrlError::new("Invalid scheme.", spec));
    }

    let scheme = &search[scheme_match.start()..scheme_match.end() - 1];
    *start_pos += scheme_match.end();
    Ok(Some(Scheme::from_str(scheme)?))
}

/// Helper to convert a `Option<Match>` to a `Option<String>`.
fn map_match_to_string(option: Option<regex::Match>, _spec: &str) -> Option<String> {
    option.map(|m| m.as_str().to_owned())
}

/// Helper to convert a `Option<Match>` to a `Option<u32>` or an error if the
/// text could not be converted to a `u32`.
fn map_match_to_u32(option: Option<regex::Match>, spec: &str) -> UrlResult<Option<u32>> {
    match option {
        Some(m) => match m.as_str().parse::<u32>() {
            Ok(p) => Ok(Some(p)),
            _ => Err(UrlError::new("Unable to parse port number", spec)),
        },
        None => Ok(None),
    }
}

/// Parses a host out of the current spec.
fn parse_host(spec: &str, start_pos: &mut usize, end_pos: &mut usize) -> UrlResult<Option<Host>> {
    if end_pos < start_pos {
        return Err(UrlError::new("Parse failure (end < start).", spec));
    }

    if (*end_pos - *start_pos) < 3 || &spec[*start_pos..*start_pos + 2] != "//" {
        return Ok(None);
    }

    *start_pos += 2;

    let search = &spec[*start_pos..*end_pos];
    let re = regex(&format!(
        "^(?:([{0}--[@:/]]*)(?::([{0}--[@:/]]*))?@)?([{}--[/:]]+)(?::(\\d+))?",
        URL_CODE_POINTS
    ))?;

    match re.captures(search) {
        Some(captures) => {
            *start_pos += captures[0].len();
            Ok(Some(Host {
                username: map_match_to_string(captures.get(1), spec),
                password: map_match_to_string(captures.get(2), spec),
                hostname: captures[3].to_owned(),
                port: map_match_to_u32(captures.get(4), spec)?,
            }))
        }
        None => Ok(Some(Default::default())),
    }
}

/// Parses a path out of the current spec.
fn parse_path(spec: &str, start_pos: &mut usize, end_pos: &mut usize) -> UrlResult<Path> {
    if end_pos < start_pos {
        return Err(UrlError::new("Parse failure (end < start).", spec));
    }

    let search = &spec[*start_pos..*end_pos];
    *start_pos = *end_pos;

    Ok(Path::from(search))
}

/// Parses a query string out of the current spec.
fn parse_query(
    spec: &str,
    start_pos: &mut usize,
    end_pos: &mut usize,
) -> UrlResult<Option<String>> {
    if end_pos < start_pos {
        return Err(UrlError::new("Parse failure (end < start).", spec));
    }

    let search = &spec[*start_pos..*end_pos];
    let re = regex(&format!(
        "\\?(?:[{}]|[{}])*$",
        URL_CODE_POINTS, PERCENT_ENCODED_BYTE
    ))?;

    let frag_match = match re.find(search) {
        Some(m) => m,
        None => return Ok(None),
    };

    *end_pos = frag_match.start();
    Ok(Some(frag_match.as_str()[1..].to_owned()))
}

/// Parses a fragment out of the current spec.
fn parse_fragment(
    spec: &str,
    start_pos: &mut usize,
    end_pos: &mut usize,
) -> UrlResult<Option<String>> {
    if end_pos < start_pos {
        return Err(UrlError::new("Parse failure (end < start).", spec));
    }

    let search = &spec[*start_pos..*end_pos];
    let re = regex(&format!(
        "#(?:[{}]|[{}])*$",
        URL_CODE_POINTS, PERCENT_ENCODED_BYTE
    ))?;

    let frag_match = match re.find(search) {
        Some(m) => m,
        None => return Ok(None),
    };

    *end_pos = frag_match.start();
    Ok(Some(percent_decode(&frag_match.as_str()[1..])))
}

/// Low-level support for building and manipulating URLs.
///
/// The `UrlBuilder`is used by both [`Url`] and [`RelativeUrl`] to handle
/// parsing, manipulating, serializing, splitting and joining URLs. In many
/// cases you may not need to use this struct directly but it can be useful to
/// get very low level access to the URL components.
///
/// As a low-level component however it has a more verbose API and you can shoot
/// yourself in the foot. It is possible to build invalid URLs with this. Look
/// to the [`is_absolute_url()`](#method.is_absolute_url) and
/// [`is_relative()_url`](#method.is_relative_url) methods to see if the current
/// state can be used as appropriate.
///
/// You can convert a [`UrlBuilder`] using the [`TryInto<Url>`](#impl-TryInto%3CUrl%3E)
/// or [`TryInto<RelativeUrl>`](#impl-TryInto%3CRelativeUrl%3E) trait
/// implementations.
///
/// # Examples
///
/// ```
/// # use urlbuilder::UrlResult;
/// use std::convert::TryInto;
/// use urlbuilder::{Url, UrlBuilder};
///
/// # fn main() -> UrlResult<()> {
/// let mut builder: UrlBuilder = Default::default();
/// assert_eq!(builder.spec(), "");
/// assert!(!builder.is_absolute_url());
/// assert!(builder.is_relative_url());
///
/// builder.set_scheme(Some("http"))?;
/// assert_eq!(builder.spec(), "http:");
/// assert!(!builder.is_absolute_url());
/// assert!(!builder.is_relative_url());
///
/// builder.set_path("/foo/bar")?;
/// assert_eq!(builder.spec(), "http:/foo/bar");
/// assert!(!builder.is_absolute_url());
/// assert!(!builder.is_relative_url());
///
/// builder.set_hostname(Some("www.google.com"))?;
/// assert!(builder.is_absolute_url());
/// assert!(!builder.is_relative_url());
///
/// let url: Url = builder.try_into()?;
/// assert_eq!(url.spec(), "http://www.google.com/foo/bar");
///
/// # Ok(())
/// # }
/// ```
///
/// [`Url`]: struct.Url.html
/// [`RelativeUrl`]: struct.RelativeUrl.html
#[derive(Debug, Clone, PartialEq, Default)]
pub struct UrlBuilder {
    // All of these are percent decoded
    scheme: Option<Scheme>,
    host: Option<Host>,
    path: Path,
    fragment: Option<String>,

    // This remains percent encoded
    query: Option<String>,
}

impl UrlBuilder {
    /// Parses a URL spec to be parsed into a `UrlBuilder`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let mut builder = UrlBuilder::from_spec("https://www.google.com/")?;
    /// assert_eq!(builder.scheme(), Some(String::from("https")));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_spec(spec: &str) -> UrlResult<Self> {
        let mut builder: UrlBuilder = Default::default();

        let c0_re = regex(&format!("^[{0} ]|[{0} ]$", C0_CONTROL))?;
        if c0_re.is_match(spec) {
            return Err(UrlError::new(
                "Url starts or ends with an invalid character.",
                spec,
            ));
        }

        let ws_re = regex("[\t\n]")?;
        if ws_re.is_match(spec) {
            return Err(UrlError::new(
                "Url contains an invalid whitespace character.",
                spec,
            ));
        }

        let mut start_pos = 0;
        let mut end_pos = spec.len();

        // First parse out the optional end bits.
        builder.fragment = parse_fragment(spec, &mut start_pos, &mut end_pos)?;
        builder.query = parse_query(spec, &mut start_pos, &mut end_pos)?;

        // Parse out scheme bits.
        builder.scheme = parse_scheme(spec, &mut start_pos, &mut end_pos)?;

        builder.host = parse_host(spec, &mut start_pos, &mut end_pos)?;

        builder.path = if start_pos == end_pos {
            if builder.host.is_some() {
                Path::from("/")
            } else {
                Default::default()
            }
        } else {
            parse_path(spec, &mut start_pos, &mut end_pos)?
        };

        assert_eq!(start_pos, end_pos);

        Ok(builder)
    }

    /// Normalises the path component of the URL.
    ///
    /// Removes any path components consisting of just `.` and components
    /// consisting of `..` will remove the preceeding path component if there is
    /// one. If the path is already absolute then any `..` components left at
    /// the start of the path are dropped. They remain if the path is relative.
    ///
    /// # Examples
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let mut builder = UrlBuilder::from_spec("/foo/../bar/")?;
    /// builder.normalize();
    /// assert_eq!(builder.spec(), "/bar/");
    ///
    /// builder.set_path("/foo/../../bar")?;
    /// builder.normalize();
    /// assert_eq!(builder.spec(), "/bar");
    ///
    /// builder.set_path("foo/../../bar")?;
    /// builder.normalize();
    /// assert_eq!(builder.spec(), "../bar");
    ///
    /// # Ok(())
    /// # }
    pub fn normalize(&mut self) {
        self.path.normalize();
    }

    /// Serializes the current state of the builder into a string.
    pub fn spec(&self) -> String {
        self.to_string()
    }

    /// Tests whether this builder contains components that can make an absolute
    /// URL.
    pub fn is_absolute_url(&self) -> bool {
        if self.scheme.is_none() {
            return false;
        }

        if self.host.is_none() {
            return false;
        }

        if self.path.is_relative() {
            return false;
        }

        if let Some(ref h) = self.host {
            match self.scheme {
                Some(Scheme::File) => {
                    if !h.hostname.is_empty() {
                        return false;
                    }
                }
                Some(Scheme::Special(_)) => {
                    if h.hostname.is_empty() {
                        return false;
                    }
                }
                _ => (),
            }
        } else {
            return false;
        }

        true
    }

    /// Tests whether this builder contains components that can make a relative
    /// URL.
    pub fn is_relative_url(&self) -> bool {
        if self.scheme.is_some() {
            return false;
        }

        if self.host.is_some() && !self.path.is_absolute() {
            return false;
        }

        true
    }

    /// Tests whether this builder contains a path that can be considered to
    /// reference a directory.
    pub fn is_directory(&self) -> bool {
        self.path.is_directory()
    }

    /// Joins two `UrlBuilder`'s together.
    ///
    /// Treats the `relative` `UrlBuilder` as a relative URL and the current
    /// `UrlBuilder` as the base URL to apply it to. No checks are made that
    /// the current is an absolute URL and the `relative` a relative URL but the
    /// results are undefined for the cases where that isn't the case.
    ///
    /// The basic pattern is to generate a new `UrlBuilder` preferring
    /// `relative`'s scheme and host if available, always using `relative`'s
    /// fragment and search and joining the paths.
    ///
    /// # Examples
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base = UrlBuilder::from_spec("https://www.google.com/foo/bar/?query#fragment")?;
    /// let relative = UrlBuilder::from_spec("../baz#newfragment")?;
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined.spec(), "https://www.google.com/foo/baz#newfragment");
    /// # Ok(())
    /// # }
    /// ```
    pub fn join(&self, relative: &UrlBuilder) -> UrlResult<UrlBuilder> {
        let mut new_builder: UrlBuilder = Default::default();

        new_builder.scheme = if relative.scheme.is_some() {
            relative.scheme.clone()
        } else {
            self.scheme.clone()
        };

        new_builder.host = if relative.host.is_some() {
            relative.host.clone()
        } else {
            self.host.clone()
        };

        new_builder.path = self.path.join(&relative.path)?;
        new_builder.fragment = relative.fragment.clone();
        new_builder.query = relative.query.clone();

        Ok(new_builder)
    }

    /// Generates a relative `UrlBuilder` between this and `base`.
    ///
    /// Tries to generate the simplest `UrlBuilder` which when joined with
    /// `base` will return a `UrlBuilder` that is identical to this.
    ///
    /// The exact `UrlBuilder` returned is not stable, i.e. future versions of
    /// this library may change exactly what is returned here.
    ///
    /// # Examples
    ///
    /// Note that this case manages to generate an identical relative `UrlBuilder`:
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base = UrlBuilder::from_spec("https://www.google.com/foo/bar/?query#fragment")?;
    /// let relative = UrlBuilder::from_spec("../baz#newfragment")?;
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined.spec(), "https://www.google.com/foo/baz#newfragment");
    ///
    /// let new_relative = joined.relative_to(&base)?;
    /// let new_joined = base.join(&new_relative)?;
    /// assert_eq!(new_joined, joined);
    ///
    /// assert_eq!(new_relative, relative);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// The relative `UrlBuilder` used to join however and so the generated
    /// relative `UrlBuilder` generated can differ and generally will be as
    /// short as possible:
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base = UrlBuilder::from_spec("https://www.microsoft.com/over/here")?;
    /// let relative = UrlBuilder::from_spec("//www.microsoft.com/over/there")?;
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined.spec(), "https://www.microsoft.com/over/there");
    ///
    /// let new_relative = joined.relative_to(&base)?;
    /// let new_joined = base.join(&new_relative)?;
    /// assert_eq!(new_joined, joined);
    ///
    /// assert_eq!(new_relative.spec(), "there");
    /// # Ok(())
    /// # }
    /// ```
    pub fn relative_to(&self, base: &UrlBuilder) -> UrlResult<UrlBuilder> {
        let mut result: UrlBuilder = Default::default();

        if self.scheme != base.scheme {
            result.scheme = self.scheme.clone();
        }

        if self.host != base.host {
            result.host = self.host.clone();
        }

        if result.scheme.is_some() || result.host.is_some() {
            result.path = self.path.clone();
        } else {
            result.path = self.path.relative_to(&base.path)?;
        }

        result.query = self.query.clone();
        result.fragment = self.fragment.clone();

        Ok(result)
    }

    /// Gets the current scheme.
    pub fn scheme(&self) -> Option<String> {
        self.scheme.as_ref().map(ToString::to_string)
    }

    /// Sets the builder's scheme.
    pub fn set_scheme(&mut self, scheme: Option<&str>) -> UrlResult<()> {
        self.scheme = scheme.and_then(|s| Scheme::from(s));
        Ok(())
    }

    /// Gets the builder's username.
    pub fn username(&self) -> Option<String> {
        self.host.as_ref().and_then(|h| h.username.clone())
    }

    /// Sets the builder's username.
    ///
    /// URLs cannot contain a username unless they also have a non-empty
    /// hostname so this method will return an error in that case.
    pub fn set_username(&mut self, username: Option<&str>) -> UrlResult<()> {
        if username.is_none() && self.host.is_none() {
            return Ok(());
        }

        match &mut self.host {
            Some(h) => {
                if username.is_some() && h.hostname.is_empty() {
                    Err(UrlError::new(
                        "Cannot set a username on a url with an empty hostname",
                        &self.spec(),
                    ))
                } else {
                    h.username = username.map(ToOwned::to_owned);
                    Ok(())
                }
            }
            None => {
                // username must contain Some at this point or the bailout above
                // would have triggered.
                Err(UrlError::new(
                    "Cannot set a username on a url with no hostname",
                    &self.spec(),
                ))
            }
        }
    }

    /// Gets the builder's password.
    pub fn password(&self) -> Option<String> {
        self.host.as_ref().and_then(|h| h.password.clone())
    }

    /// Sets the builder's password.
    ///
    /// URLs cannot contain a password unless they also have a non-empty
    /// hostname so this method will return an error in that case.
    pub fn set_password(&mut self, password: Option<&str>) -> UrlResult<()> {
        if password.is_none() && self.host.is_none() {
            return Ok(());
        }

        match &mut self.host {
            Some(h) => {
                if password.is_some() && h.hostname.is_empty() {
                    Err(UrlError::new(
                        "Cannot set a password on a url with an empty hostname",
                        &self.spec(),
                    ))
                } else {
                    h.password = password.map(ToOwned::to_owned);
                    Ok(())
                }
            }
            None => {
                // username must contain Some at this point or the bailout above
                // would have triggered.
                Err(UrlError::new(
                    "Cannot set a password on a url with no hostname",
                    &self.spec(),
                ))
            }
        }
    }

    /// Gets the builder's hostname.
    pub fn hostname(&self) -> Option<String> {
        self.host.as_ref().and_then(|h| Some(h.hostname.clone()))
    }

    /// Sets the builder's hostname.
    ///
    /// Setting the hostname to None or an empty string will also set the
    /// username, password and port to None.
    pub fn set_hostname(&mut self, hostname: Option<&str>) -> UrlResult<()> {
        match hostname {
            Some(h) => {
                if h.is_empty() || self.host.is_none() {
                    self.host = Some(Host {
                        username: None,
                        password: None,
                        hostname: h.to_owned(),
                        port: None,
                    });
                } else if let Some(ref mut t) = self.host {
                    t.hostname = h.to_owned();
                }
            }
            None => self.host = None,
        }

        Ok(())
    }

    /// Gets the builder's port.
    pub fn port(&self) -> Option<u32> {
        self.host.as_ref().and_then(|h| h.port)
    }

    /// Sets the builder's port.
    ///
    /// URLs cannot contain a port unless they also have a non-empty hostname
    /// so this method will return an error in that case.
    pub fn set_port(&mut self, port: Option<u32>) -> UrlResult<()> {
        if port.is_none() && self.host.is_none() {
            return Ok(());
        }

        match &mut self.host {
            Some(h) => {
                if port.is_some() && h.hostname.is_empty() {
                    Err(UrlError::new(
                        "Cannot set a port on a url with an empty hostname",
                        &self.spec(),
                    ))
                } else {
                    h.port = port;
                    Ok(())
                }
            }
            None => {
                // username must contain Some at this point or the bailout above
                // would have triggered.
                Err(UrlError::new(
                    "Cannot set a port on a url with no hostname",
                    &self.spec(),
                ))
            }
        }
    }

    /// Gets the builder's effective port.
    ///
    /// If a port is set in the builder then that is returned. If not a short
    /// table of known ports for schemes is used. None is returns if neither
    /// yielded a port.
    pub fn effective_port(&self) -> Option<u32> {
        self.port()
            .or_else(|| self.scheme.as_ref().and_then(Scheme::default_port))
    }

    /// Sets the builder's effective port.
    ///
    /// If the port given matches the default port for the current scheme then
    /// the builder's port is cleared, otherwise this is the same as setting
    /// the port directly.
    pub fn set_effective_port(&mut self, port: Option<u32>) -> UrlResult<()> {
        let default = self.scheme.as_ref().and_then(Scheme::default_port);
        if port == default {
            self.set_port(port)
        } else {
            self.set_port(None)
        }
    }

    /// Gets the builder's path.
    pub fn path(&self) -> String {
        self.path.to_string()
    }

    /// Sets the builder's path.
    pub fn set_path(&mut self, path: &str) -> UrlResult<()> {
        self.path = Path::from(path);
        Ok(())
    }

    /// Gets the builders query string.
    pub fn query(&self) -> Option<String> {
        self.query.clone()
    }

    /// Sets the builder's query string.
    pub fn set_query(&mut self, query: Option<&str>) -> UrlResult<()> {
        self.query = query.map(ToOwned::to_owned);
        Ok(())
    }

    /// Gete the builder's fragment string.
    pub fn fragment(&self) -> Option<String> {
        self.fragment.clone()
    }

    /// Sets the builder's fragment string.
    pub fn set_fragment(&mut self, fragment: Option<&str>) -> UrlResult<()> {
        self.fragment = fragment.map(ToOwned::to_owned);
        Ok(())
    }
}

/// These are method implementations used by `Url` and `UrlBuilder`.
impl UrlBuilder {
    fn url_protocol(&self) -> String {
        self.scheme().map_or(String::new(), |s| format!("{}:", s))
    }

    fn set_url_protocol(&mut self, scheme: &str) -> UrlResult<()> {
        if scheme.is_empty() {
            self.scheme = None;
            return Ok(());
        }

        if scheme.ends_with(':') {
            return self.set_url_protocol(&scheme[..scheme.len() - 1]);
        }

        self.set_scheme(Some(scheme))?;

        // The file protocol doesn't support any target so clear it now.
        if Some(Scheme::File) == self.scheme {
            self.host = None;
        }

        Ok(())
    }

    fn url_username(&self) -> String {
        self.username().unwrap_or_default()
    }

    fn set_url_username(&mut self, username: &str) -> UrlResult<()> {
        if username.is_empty() {
            self.set_username(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a username for a file url.",
                &self.spec(),
            ))
        } else {
            self.set_username(Some(username))
        }
    }

    fn url_password(&self) -> String {
        self.password().unwrap_or_default()
    }

    fn set_url_password(&mut self, password: &str) -> UrlResult<()> {
        if password.is_empty() {
            self.set_password(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a password for a file url.",
                &self.spec(),
            ))
        } else {
            self.set_password(Some(password))
        }
    }

    fn url_hostname(&self) -> String {
        self.hostname().unwrap_or_default()
    }

    fn set_url_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        if hostname.is_empty() {
            self.set_hostname(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a hostname for a file url.",
                &self.spec(),
            ))
        } else {
            self.set_hostname(Some(hostname))
        }
    }

    fn url_port(&self) -> String {
        self.port().map_or(String::new(), |p| p.to_string())
    }

    fn set_url_port(&mut self, port: &str) -> UrlResult<()> {
        if port.is_empty() {
            self.set_port(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a port for a file url.",
                &self.spec(),
            ))
        } else {
            match port.parse::<u32>() {
                Ok(p) => self.set_port(Some(p)),
                Err(_) => Err(UrlError::new("Unable to parse port number.", port)),
            }
        }
    }

    fn url_host(&self) -> String {
        self.host.as_ref().map_or(String::new(), Host::hostport)
    }

    fn set_url_host(&mut self, host: &str) -> UrlResult<()> {
        if host.is_empty() {
            self.set_hostname(None)
        } else {
            match host.find(':') {
                Some(i) => {
                    self.set_hostname(Some(&host[..i]))?;
                    self.set_url_port(&host[i + 1..])
                }
                None => {
                    self.set_hostname(Some(host))?;
                    self.set_port(None)
                }
            }
        }
    }

    fn url_pathname(&self) -> String {
        self.path.to_string()
    }

    fn set_url_pathname(&mut self, path: &str) -> UrlResult<()> {
        self.path = Path::from(path);
        Ok(())
    }

    fn url_search(&self) -> String {
        self.query
            .as_ref()
            .map_or(String::new(), |s| format!("?{}", s))
    }

    fn set_url_search(&mut self, search: &str) -> UrlResult<()> {
        if search.is_empty() {
            self.query = None
        } else if search.starts_with('?') {
            self.query = Some(search[1..].to_owned());
        } else {
            self.query = Some(search.to_owned());
        }

        Ok(())
    }

    fn url_hash(&self) -> String {
        self.fragment
            .as_ref()
            .map_or(String::new(), |f| format!("#{}", percent_encode(&f)))
    }

    fn set_url_hash(&mut self, hash: &str) -> UrlResult<()> {
        if hash.is_empty() {
            self.fragment = None;
        } else if hash.starts_with('#') {
            self.fragment = Some(hash[1..].to_owned());
        } else {
            self.fragment = Some(hash.to_owned());
        }

        Ok(())
    }
}

impl fmt::Display for UrlBuilder {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let Some(ref scheme) = self.scheme {
            f.write_fmt(format_args!("{}:", scheme))?;
        }

        if let Some(ref h) = self.host {
            f.write_str("//")?;
            f.write_str(&h.to_string())?;
        }

        self.path.fmt(f)?;

        if let Some(ref s) = self.query {
            f.write_fmt(format_args!("?{}", &percent_encode(&s)))?;
        }

        if let Some(ref frag) = self.fragment {
            f.write_fmt(format_args!("#{}", &percent_encode(&frag)))?;
        }

        Ok(())
    }
}

impl FromStr for UrlBuilder {
    type Err = UrlError;

    fn from_str(spec: &str) -> Result<Self, Self::Err> {
        UrlBuilder::from_spec(spec)
    }
}

impl TryFrom<UrlBuilder> for Url {
    type Error = UrlError;

    fn try_from(builder: UrlBuilder) -> Result<Url, Self::Error> {
        if builder.is_absolute_url() {
            Ok(Url { builder })
        } else {
            Err(UrlError::new(
                "Unable to build an absolute url from this builder.",
                &builder.spec(),
            ))
        }
    }
}

impl TryFrom<UrlBuilder> for RelativeUrl {
    type Error = UrlError;

    fn try_from(builder: UrlBuilder) -> Result<RelativeUrl, Self::Error> {
        if builder.is_relative_url() {
            Ok(RelativeUrl { builder })
        } else {
            Err(UrlError::new(
                "Unable to build a relative url from this builder.",
                &builder.spec(),
            ))
        }
    }
}

impl From<Url> for UrlBuilder {
    fn from(url: Url) -> UrlBuilder {
        url.builder
    }
}

impl From<RelativeUrl> for UrlBuilder {
    fn from(url: RelativeUrl) -> UrlBuilder {
        url.builder
    }
}

/// Represents an absolute URL.
///
/// The API largely matches the specification for [URL objects](https://developer.mozilla.org/en-US/docs/Web/API/URL)
/// in web pages with the exception that setting properties may return an error
/// if setting the property is invalid whereas the web API simply ignores such
/// attempts.
///
/// # Examples
///
/// ```
/// # use urlbuilder::UrlResult;
/// use urlbuilder::{UrlBuilder, Url};
/// use std::convert::TryFrom;
///
/// # fn main() -> UrlResult<()> {
/// // A few different ways of creating the same `Url`:
/// let spec = "https://www.google.com/foo#bar";
/// let url = Url::new(spec, None)?;
/// assert_eq!(url.href(), spec);
///
/// assert_eq!(Url::new("#bar", "https://www.google.com/foo")?, url);
///
/// assert_eq!(spec.parse::<Url>()?, url);
///
/// let mut builder: UrlBuilder = Default::default();
/// builder.set_scheme(Some("https"))?;
/// builder.set_hostname(Some("www.google.com"))?;
/// builder.set_path("/foo")?;
/// builder.set_fragment(Some("bar"))?;
/// assert_eq!(Url::try_from(builder)?, url);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Url {
    builder: UrlBuilder,
}

impl Url {
    /// Creates a new `Url` from a spec and optionally a spec to resolve
    /// against.
    ///
    /// The `spec` is first parsed. If it represents an absolute URL then a
    /// `Url` for that is returned. If it represents a relative URL and
    /// `base_spec` is provided and can be parsed to an absolute URL then a
    /// `Url` that represents the join of `spec` to `base_spec` is returned.
    /// Otherwise an error is thrown.
    ///
    /// # Examples
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::Url;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let url = Url::new("https://www.microsoft.com", None)?;
    /// assert_eq!(url.spec(), "https://www.microsoft.com/");
    ///
    /// let url = Url::new("#foo", "https://www.google.com")?;
    /// assert_eq!(url.spec(), "https://www.google.com/#foo");
    ///
    /// let url = Url::new("https://www.microsoft.com", "https://www.google.com")?;
    /// assert_eq!(url.spec(), "https://www.microsoft.com/");
    /// # Ok(())
    /// # }
    /// ```
    pub fn new<'a, O>(spec: &str, base_url: O) -> UrlResult<Self>
    where
        O: Into<Option<&'a str>>,
    {
        let spec_builder = spec.parse::<UrlBuilder>()?;
        if spec_builder.is_absolute_url() {
            spec_builder.try_into()
        } else if spec_builder.is_relative_url() {
            match base_url.into() {
                Some(s) => {
                    let base_builder = s.parse::<UrlBuilder>()?;
                    if base_builder.is_absolute_url() {
                        base_builder.join(&spec_builder)?.try_into()
                    } else {
                        Err(UrlError::new(
                            "Base specification did not parse into an absolute URL.",
                            s,
                        ))
                    }
                }
                None => Err(UrlError::new(
                    "Specification parsed as a relative URL but no base URL was provided.",
                    spec,
                )),
            }
        } else {
            Err(UrlError::new(
                "Specification did not parse as an absolute or relative URL.",
                spec,
            ))
        }
    }

    /// Returns the serialized spec for the current `Url`.
    pub fn spec(&self) -> String {
        self.builder.spec()
    }

    /// Returns the serialized spec for the current `Url`.
    pub fn href(&self) -> String {
        self.spec()
    }

    /// Joins a relative URL to this URL to create a new `Url`.
    ///
    /// Internally this joins the `Url`'s [`UrlBuilder`](struct.UrlBuilder.html)
    /// to `relative`'s [`UrlBuilder`](struct.UrlBuilder.html) and then converts
    /// the result into a `Url`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::{ Url, RelativeUrl };
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base: Url = "https://www.google.com/foo/bar/".parse()?;
    /// let relative: RelativeUrl = "../baz/bam".parse()?;
    ///
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined.spec(), "https://www.google.com/foo/baz/bam");
    /// # Ok(())
    /// # }
    /// ```
    pub fn join(&self, relative: &RelativeUrl) -> UrlResult<Self> {
        let builder = self.builder.join(&relative.builder)?;
        builder.try_into()
    }

    /// Creates a relative URL that can be joined to `base` to create a `Url`
    /// containing the current URL.
    ///
    /// # Examples
    ///
    /// ```
    /// # use urlbuilder::UrlResult;
    /// use urlbuilder::{ Url, RelativeUrl };
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base: Url = "https://www.google.com/foo/bar/".parse()?;
    /// let current: Url = "https://www.google.com/foo/baz/bam".parse()?;
    ///
    /// let relative = current.relative_to(&base)?;
    /// assert_eq!(relative.spec(), "../baz/bam");
    ///
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined, current);
    /// # Ok(())
    /// # }
    /// ```
    pub fn relative_to(&self, base: &Url) -> UrlResult<RelativeUrl> {
        let builder = self.builder.relative_to(&base.builder)?;
        builder.try_into()
    }

    /// Returns the current `Url`'s origin.
    ///
    /// Matches the web specification for [`origin`](https://developer.mozilla.org/en-US/docs/Web/API/URL/origin).
    pub fn origin(&self) -> String {
        assert!(
            self.builder.is_absolute_url(),
            "Url should be absolute to have an origin."
        );

        format!(
            "{}{}",
            self.builder.url_protocol(),
            self.builder
                .host
                .as_ref()
                .map_or(String::new(), ToString::to_string)
        )
    }
}

impl Url {
    /// Returns the current `Url`'s protocol.
    ///
    /// Matches the web specification for [`protocol`](https://developer.mozilla.org/en-US/docs/Web/API/URL/protocol).
    pub fn protocol(&self) -> String {
        self.builder.url_protocol()
    }

    /// Sets the current `Url`'s protocol.
    ///
    /// Matches the web specification for [`protocol`](https://developer.mozilla.org/en-US/docs/Web/API/URL/protocol).
    pub fn set_protocol(&mut self, scheme: &str) -> UrlResult<()> {
        self.builder.set_url_protocol(scheme)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s username.
    ///
    /// Matches the web specification for [`username`](https://developer.mozilla.org/en-US/docs/Web/API/URL/username).
    pub fn username(&self) -> String {
        self.builder.url_username()
    }

    /// Sets the current `Url`'s username.
    ///
    /// Matches the web specification for [`username`](https://developer.mozilla.org/en-US/docs/Web/API/URL/username).
    pub fn set_username(&mut self, username: &str) -> UrlResult<()> {
        self.builder.set_url_username(username)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s password.
    ///
    /// Matches the web specification for [`password`](https://developer.mozilla.org/en-US/docs/Web/API/URL/password).
    pub fn password(&self) -> String {
        self.builder.url_password()
    }

    /// Sets the current `Url`'s password.
    ///
    /// Matches the web specification for [`password`](https://developer.mozilla.org/en-US/docs/Web/API/URL/password).
    pub fn set_password(&mut self, password: &str) -> UrlResult<()> {
        self.builder.set_url_password(password)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s hostname.
    ///
    /// Matches the web specification for [`hostname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hostname).
    pub fn hostname(&self) -> String {
        self.builder.url_hostname()
    }

    /// Sets the current `Url`'s hostname.
    ///
    /// Matches the web specification for [`hostname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hostname).
    pub fn set_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        self.builder.set_url_hostname(hostname)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s port.
    ///
    /// Matches the web specification for [`port`](https://developer.mozilla.org/en-US/docs/Web/API/URL/port).
    pub fn port(&self) -> String {
        self.builder.url_port()
    }

    /// Sets the current `Url`'s port.
    ///
    /// Matches the web specification for [`port`](https://developer.mozilla.org/en-US/docs/Web/API/URL/port).
    pub fn set_port(&mut self, port: &str) -> UrlResult<()> {
        self.builder.set_url_port(port)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s host.
    ///
    /// Matches the web specification for [`host`](https://developer.mozilla.org/en-US/docs/Web/API/URL/host).
    pub fn host(&self) -> String {
        self.builder.url_host()
    }

    /// Sets the current `Url`'s host.
    ///
    /// Matches the web specification for [`host`](https://developer.mozilla.org/en-US/docs/Web/API/URL/host).
    pub fn set_host(&mut self, host: &str) -> UrlResult<()> {
        self.builder.set_url_host(host)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s pathname.
    ///
    /// Matches the web specification for [`pathname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/pathname).
    pub fn pathname(&self) -> String {
        self.builder.url_pathname()
    }

    /// Sets the current `Url`'s pathname.
    ///
    /// Matches the web specification for [`pathname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/pathname).
    pub fn set_pathname(&mut self, path: &str) -> UrlResult<()> {
        self.builder.set_url_pathname(path)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s search.
    ///
    /// Matches the web specification for [`search`](https://developer.mozilla.org/en-US/docs/Web/API/URL/search).
    pub fn search(&self) -> String {
        self.builder.url_search()
    }

    /// Sets the current `Url`'s search.
    ///
    /// Matches the web specification for [`search`](https://developer.mozilla.org/en-US/docs/Web/API/URL/search).
    pub fn set_search(&mut self, search: &str) -> UrlResult<()> {
        self.builder.set_url_search(search)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s hash.
    ///
    /// Matches the web specification for [`hash`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hash).
    pub fn hash(&self) -> String {
        self.builder.url_hash()
    }

    /// Sets the current `Url`'s hash.
    ///
    /// Matches the web specification for [`hash`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hash).
    pub fn set_hash(&mut self, hash: &str) -> UrlResult<()> {
        self.builder.set_url_hash(hash)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }
}

impl FromStr for Url {
    type Err = UrlError;

    fn from_str(spec: &str) -> Result<Self, Self::Err> {
        let builder: UrlBuilder = spec.parse()?;
        builder.try_into()
    }
}

impl fmt::Display for Url {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_str(&self.href())
    }
}

#[derive(Debug, Clone)]
pub struct RelativeUrl {
    builder: UrlBuilder,
}

impl RelativeUrl {
    /// Returns the serialized spec for the current `RelativeUrl`.
    pub fn spec(&self) -> String {
        self.to_string()
    }
}

impl RelativeUrl {
    /// Returns the current `RelativeUrl`'s username.
    ///
    /// Matches the web specification for [`username`](https://developer.mozilla.org/en-US/docs/Web/API/URL/username).
    pub fn username(&self) -> String {
        self.builder.url_username()
    }

    /// Sets the current `RelativeUrl`'s username.
    ///
    /// Matches the web specification for [`username`](https://developer.mozilla.org/en-US/docs/Web/API/URL/username).
    pub fn set_username(&mut self, username: &str) -> UrlResult<()> {
        self.builder.set_url_username(username)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s password.
    ///
    /// Matches the web specification for [`password`](https://developer.mozilla.org/en-US/docs/Web/API/URL/password).
    pub fn password(&self) -> String {
        self.builder.url_password()
    }

    /// Sets the current `RelativeUrl`'s password.
    ///
    /// Matches the web specification for [`password`](https://developer.mozilla.org/en-US/docs/Web/API/URL/password).
    pub fn set_password(&mut self, password: &str) -> UrlResult<()> {
        self.builder.set_url_password(password)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s hostname.
    ///
    /// Matches the web specification for [`hostname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hostname).
    pub fn hostname(&self) -> String {
        self.builder.url_hostname()
    }

    /// Sets the current `RelativeUrl`'s hostname.
    ///
    /// Matches the web specification for [`hostname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hostname).
    pub fn set_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        self.builder.set_url_hostname(hostname)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s port.
    ///
    /// Matches the web specification for [`port`](https://developer.mozilla.org/en-US/docs/Web/API/URL/port).
    pub fn port(&self) -> String {
        self.builder.url_port()
    }

    /// Sets the current `RelativeUrl`'s port.
    ///
    /// Matches the web specification for [`port`](https://developer.mozilla.org/en-US/docs/Web/API/URL/port).
    pub fn set_port(&mut self, port: &str) -> UrlResult<()> {
        self.builder.set_url_port(port)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s host.
    ///
    /// Matches the web specification for [`host`](https://developer.mozilla.org/en-US/docs/Web/API/URL/host).
    pub fn host(&self) -> String {
        self.builder.url_host()
    }

    /// Sets the current `RelativeUrl`'s host.
    ///
    /// Matches the web specification for [`host`](https://developer.mozilla.org/en-US/docs/Web/API/URL/host).
    pub fn set_host(&mut self, host: &str) -> UrlResult<()> {
        self.builder.set_url_host(host)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s pathname.
    ///
    /// Matches the web specification for [`pathname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/pathname).
    pub fn pathname(&self) -> String {
        self.builder.url_pathname()
    }

    /// Sets the current `RelativeUrl`'s pathname.
    ///
    /// Matches the web specification for [`pathname`](https://developer.mozilla.org/en-US/docs/Web/API/URL/pathname).
    pub fn set_pathname(&mut self, path: &str) -> UrlResult<()> {
        self.builder.set_url_pathname(path)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s search.
    ///
    /// Matches the web specification for [`search`](https://developer.mozilla.org/en-US/docs/Web/API/URL/search).
    pub fn search(&self) -> String {
        self.builder.url_search()
    }

    /// Sets the current `RelativeUrl`'s search.
    ///
    /// Matches the web specification for [`search`](https://developer.mozilla.org/en-US/docs/Web/API/URL/search).
    pub fn set_search(&mut self, search: &str) -> UrlResult<()> {
        self.builder.set_url_search(search)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s hash.
    ///
    /// Matches the web specification for [`hash`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hash).
    pub fn hash(&self) -> String {
        self.builder.url_hash()
    }

    /// Sets the current `RelativeUrl`'s hash.
    ///
    /// Matches the web specification for [`hash`](https://developer.mozilla.org/en-US/docs/Web/API/URL/hash).
    pub fn set_hash(&mut self, hash: &str) -> UrlResult<()> {
        self.builder.set_url_hash(hash)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }
}

impl FromStr for RelativeUrl {
    type Err = UrlError;

    fn from_str(spec: &str) -> Result<Self, Self::Err> {
        let builder: UrlBuilder = spec.parse()?;
        builder.try_into()
    }
}

impl fmt::Display for RelativeUrl {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.builder.fmt(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn build_path(parts: Vec<&str>) -> Path {
        Path {
            components: parts.iter().map(|p| String::from(*p)).collect(),
        }
    }

    fn builder_parse_change(spec: &str, expected: &str) -> UrlBuilder {
        let builder = spec.parse::<UrlBuilder>().unwrap();
        assert_eq!(
            &builder.spec(),
            expected,
            "Parsed spec should match expected."
        );
        let reparsed = builder.spec().parse::<UrlBuilder>().unwrap();
        assert_eq!(reparsed, builder, "Reparsed builder should match original.");
        builder
    }

    fn builder_parse(spec: &str) -> UrlBuilder {
        builder_parse_change(spec, spec)
    }

    #[test]
    fn builder_parse_absolute_urls() {
        let builder = builder_parse("http://foo:bar@www.example.com:24/foo/bar?zed#frag");
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_relative());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("http"))),
                host: Some(Host {
                    username: Some(String::from("foo")),
                    password: Some(String::from("bar")),
                    hostname: String::from("www.example.com"),
                    port: Some(24),
                }),
                path: build_path(vec!["", "foo", "bar"]),
                query: Some(String::from("zed")),
                fragment: Some(String::from("frag")),
            },
        );

        let builder = builder_parse_change("https://hello@foo", "https://hello@foo/");
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_relative());
        assert!(builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Special(String::from("https"))),
                host: Some(Host {
                    username: Some(String::from("hello")),
                    password: None,
                    hostname: String::from("foo"),
                    port: None,
                }),
                path: build_path(vec!["", ""]),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("file:///foo/bar");
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_relative());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    username: None,
                    password: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: build_path(vec!["", "foo", "bar"]),
                query: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn builder_parse_relative_urls() {
        let builder = builder_parse("//www/example");
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_relative());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    username: None,
                    password: None,
                    hostname: String::from("www"),
                    port: None,
                }),
                path: build_path(vec!["", "example"]),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("/www/example");
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_relative());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: build_path(vec!["", "www", "example"]),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("www/example/");
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert!(!builder.path.is_absolute());
        assert!(builder.path.is_relative());
        assert!(builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: build_path(vec!["www", "example", ""]),
                query: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn builder_parse_bad_urls() {
        let builder = builder_parse("file:");
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_empty());
        assert!(builder.path.is_relative());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: None,
                path: Default::default(),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("file://foo/bar/");
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(!builder.path.is_empty());
        assert!(builder.path.is_absolute());
        assert!(builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    username: None,
                    password: None,
                    hostname: String::from("foo"),
                    port: None,
                }),
                path: build_path(vec!["", "bar", ""]),
                query: None,
                fragment: None,
            }
        );
    }

    fn check_normalize(spec: &str, expected: &str) {
        let mut builder: UrlBuilder = spec.parse().unwrap();
        builder.normalize();
        assert_eq!(
            builder.spec(),
            expected,
            "Normalized spec should have matched expected."
        );
    }

    #[test]
    fn builder_path_normalize() {
        check_normalize(
            "https://www.google.com/foo/.././bar/",
            "https://www.google.com/bar/",
        );
        check_normalize(
            "https://www.google.com/foo/../bar",
            "https://www.google.com/bar",
        );
        check_normalize(
            "https://www.google.com/../bar/",
            "https://www.google.com/bar/",
        );
        check_normalize("foo/.././bar/", "bar/");
        check_normalize("foo/../bar", "bar");
        check_normalize("../bar/", "../bar/");
        check_normalize("../../../bar/../../", "../../../../");
        check_normalize("/../../../bar/../../", "/");
        check_normalize("/boo/bar/..", "/boo/");
        check_normalize("/boo/bar/../", "/boo/");
    }

    fn check_join_split(base: &str, relative: &str, expected: &str, after_split: &str) {
        let base_builder: UrlBuilder = base.parse().unwrap();
        let relative_builder: UrlBuilder = relative.parse().unwrap();

        let joined = base_builder.join(&relative_builder).unwrap();

        assert_eq!(
            joined.spec(),
            expected,
            "Joined spec should match expected spec.",
        );

        let split = joined.relative_to(&base_builder).unwrap();

        assert_eq!(
            split.spec(),
            after_split,
            "Split spec should match expected.",
        );
    }

    fn check_join_split_exact(base: &str, relative: &str, expected: &str) {
        check_join_split(base, relative, expected, relative);
    }

    fn check_join_split_change(base: &str, relative: &str, expected: &str, after_split: &str) {
        check_join_split(base, relative, expected, after_split);
    }

    #[test]
    fn builder_join_split() {
        check_join_split_exact(
            "http://foo/bar/#bozzy",
            "baz#bizzy",
            "http://foo/bar/baz#bizzy",
        );
        check_join_split_exact("https://foo/baz/#test", "//bar/boo", "https://bar/boo");
        check_join_split_exact("http://foo/bar/baz?test", "boo#fr", "http://foo/bar/boo#fr");
        check_join_split_exact("http://boo/bar/baz", "", "http://boo/bar/baz");
        check_join_split_exact("http://boo/bar/baz/", "", "http://boo/bar/baz/");
        check_join_split_exact("http://boo/bar/baz", "boo", "http://boo/bar/boo");
        check_join_split_exact("http://boo/bar/baz/", "boo", "http://boo/bar/baz/boo");
        check_join_split_change("http://boo/bar/baz/bad", "..", "http://boo/bar/", "../");
        check_join_split_exact("http://boo/bar/baz/bad", "../", "http://boo/bar/");
        check_join_split_change(
            "http://boo/bar/baz/bad/",
            "..",
            "http://boo/bar/baz/",
            "../",
        );
        check_join_split_exact("http://boo/bar/baz/bad/", "../", "http://boo/bar/baz/");
        check_join_split_exact("/", "foo/bar", "/foo/bar");
        check_join_split_change("/", "../foo/bar", "/foo/bar", "foo/bar");
    }
}
