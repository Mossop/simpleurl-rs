//! A crate for creating, parsing and manipulating absolute and relative URLs.
//!
//! This crate provides structs that support a subset of the [URL spec](https://url.spec.whatwg.org/).
//! If you need something that supports the full spec then (rust-url)[https://crates.io/crates/url]
//! seems like a good place to start.
//!
//! The chief goal for this crate was to provide full support for manipulating
//! relative URLs. In order to be spec compliant relative URLs can only really
//! be used in the presence of a known base URL.
//!
//! The lowest level of URL manipulation provided is the [`UrlBuilder`] which
//! allows you to build a URL from the precise components you want starting from
//! nothing. This can allow you to build an invalid URL though so the higher
//! level structs may be more useful.
//!
//! At the higher level this crate provides the [`Url`] and [`RelativeUrl`]
//! structs. Both use the [`UrlBuilder`] under the hood bug. [`Url`] ensures
//! that you always have a valid absolute URL and [`RelativeUrl`] ensures that
//! you always have a valid relative URL.
//!
//! The term `spec` is used frequently throughout the docs to mean a string of
//! characters that is intended to represent an absolute or relative URL.
//! [`UrlBuilder`], [`Url`] and [`RelativeUrl`] all provide a `spec()` method to
//! serialize their current URL into a spec. There are a few different ways to
//! parse a spec into a [`UrlBuilder`], [`Url`] or [`RelativeUrl`] but the main
//! route is through the [`FromStr`](https://doc.rust-lang.org/std/str/trait.FromStr.html) trait.
//!
//! # URL support
//!
//! The supported absolute URLs are of this form:
//!
//! ```text
//!   https://username:password@www.hostname.com:22/this/is/the/path?a+query+string#a_fragment
//!        |                                       |                |              |
//! scheme |               hostname                |      path      | query string | fragment
//! ```
//!
//! An absolute URL must have:
//! * A scheme (All schemes are treated as [special schemes](https://url.spec.whatwg.org/#special-scheme).)
//! * A hostname (may be the empty string).
//! * An absolute path (by default this is just `/`).
//!
//! The URL may also have a username, password, port, query string or fragment.
//!
//! The supported relative URLs are of this form:
//!
//! ```text
//! //username:password@www.hostname.com:22/this/is/the/path?a+query+string#a_fragment
//! |                                      |                |              |
//! |               hostname               |      path      | query string | fragment
//! ```
//!
//! The path is the only part that is required, but it will default to empty or
//! `/` if there is a hostname.
//!
//! These cover a pretty large proportion of the URLs in use. Notable URLs that
//! aren't covered are those with no notion of a host, such as blob or data
//! URLs.
//!
//! # Examples
//!
//! ```
//! # use simpleurl::UrlError;
//! use simpleurl::{Url, RelativeUrl};
//!
//! # fn main() -> Result<(), UrlError> {
//! let mut url: Url = "https://www.google.com/foo/bar".parse()?;
//! assert_eq!(url.spec(), "https://www.google.com/foo/bar");
//! assert_eq!(url.scheme(), "https");
//! url.set_hostname("www.example.com")?;
//! assert_eq!(url.spec(), "https://www.example.com/foo/bar");
//!
//! let mut relative: RelativeUrl = "/bar/foo".parse()?;
//! assert_eq!(relative.spec(), "/bar/foo");
//!
//! let joined = url.join(&relative)?;
//! assert_eq!(joined.spec(), "https://www.example.com/bar/foo");
//!
//! relative.set_hostname(Some("www.google.com"));
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

mod parser;

use parser::{percent_decode, percent_encode, CodepointSet, UrlParser};
use std::convert::{TryFrom, TryInto};
use std::error;
use std::fmt;
use std::str::FromStr;
use std::string::ToString;

/// Represents an error that occurred while parsing or manipulating a URL.
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

/// The default ports for the known non-file schemes.
const DEFAULT_PORTS: [(&str, u32); 6] = [
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
    Named(String),
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
            Some(Scheme::Named(lower.to_owned()))
        }
    }

    /// Gets the default port for this scheme. Only certain schemes have a known
    /// default port.
    fn default_port(&self) -> Option<u32> {
        match self {
            Scheme::Named(s) => {
                for info in &DEFAULT_PORTS {
                    if s == info.0 {
                        return Some(info.1);
                    }
                }

                None
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
            Scheme::Named(s) => f.write_str(&s),
            Scheme::File => f.write_str("file"),
        }
    }
}

/// Holds a username/password pair.
#[derive(Debug, Clone, PartialEq, Default)]
struct Authentication {
    username: String,
    password: String,
}

/// Holds the authentication, hostname and port of the URL.
///
/// There is always a hostname, the other fields are optional.
#[derive(Debug, Clone, PartialEq, Default)]
struct Host {
    authentication: Option<Authentication>,
    hostname: String,
    port: Option<u32>,
}

impl fmt::Display for Host {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let Some(auth) = &self.authentication {
            f.write_str(&percent_encode(&auth.username))?;

            if !auth.password.is_empty() {
                f.write_fmt(format_args!(":{}", &percent_encode(&auth.password)))?;
            }

            f.write_str("@")?;
        }

        f.write_str(&percent_encode(&self.hostname))?;

        if let Some(ref p) = self.port {
            f.write_fmt(format_args!(":{}", p))?;
        }

        Ok(())
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
    fn from_components(components: Vec<&str>) -> Path {
        Path {
            components: components.iter().map(|p| String::from(*p)).collect(),
        }
    }

    fn root_path() -> Path {
        Path::from_components(vec!["", ""])
    }

    /// Normalizes the path components.
    fn normalize(&mut self) {
        self.components = normalize(&self.components);
    }

    /// Joins one path to another. At a high level this is similar to being in
    /// this path in a filesystem and running `cd <relative>`.
    fn join(&self, relative: &Path) -> UrlResult<Path> {
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
    fn relative_to(&self, base_path: &Path) -> UrlResult<Path> {
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
    fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    /// Returns true if this is an absolute path (starts with `/`).
    fn is_absolute(&self) -> bool {
        match self.components.first() {
            Some(p) => p.is_empty(),
            None => false,
        }
    }

    /// Returns true if this references a directory (ends with `/`).
    fn is_directory(&self) -> bool {
        match self.components.last() {
            Some(p) => p.is_empty(),
            None => false,
        }
    }
}

impl FromStr for Path {
    type Err = UrlError;

    fn from_str(path: &str) -> Result<Self, Self::Err> {
        if path.is_empty() {
            Ok(Default::default())
        } else {
            let set = CodepointSet::from_included_set("\\\\/");
            Ok(Path {
                components: set.split(path).map(|p| percent_decode(&p)).collect(),
            })
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
/// # use simpleurl::UrlResult;
/// use std::convert::TryInto;
/// use simpleurl::{Url, UrlBuilder};
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
    /// # use simpleurl::UrlResult;
    /// use simpleurl::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let mut builder: UrlBuilder = "/foo/../bar/".parse()?;
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
        if let Some(ref h) = self.host {
            if h.hostname.is_empty() && (h.port.is_some() || h.authentication.is_some()) {
                false
            } else {
                self.scheme.is_some() && self.path.is_absolute()
            }
        } else {
            false
        }
    }

    /// Tests whether this builder contains components that can make a relative
    /// URL.
    pub fn is_relative_url(&self) -> bool {
        if let Some(ref h) = self.host {
            if h.hostname.is_empty() && h.port.is_some() {
                return false;
            }
        }

        if self.host.is_some() && !self.path.is_absolute() {
            return false;
        }

        self.scheme.is_none()
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
    /// results are undefined for other cases.
    ///
    /// # Examples
    ///
    /// ```
    /// # use simpleurl::UrlResult;
    /// use simpleurl::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base: UrlBuilder = "https://www.google.com/foo/bar/?query#fragment".parse()?;
    /// let relative: UrlBuilder = "../baz#newfragment".parse()?;
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined.spec(), "https://www.google.com/foo/baz#newfragment");
    /// # Ok(())
    /// # }
    /// ```
    pub fn join(&self, relative: &UrlBuilder) -> UrlResult<UrlBuilder> {
        if relative.is_absolute_url() {
            return Ok(relative.clone());
        }

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
    /// # use simpleurl::UrlResult;
    /// use simpleurl::UrlBuilder;
    ///
    /// # fn main() -> UrlResult<()> {
    /// let base: UrlBuilder = "https://www.google.com/foo/bar/?query#fragment".parse()?;
    /// let relative: UrlBuilder = "../baz#newfragment".parse()?;
    /// let joined = base.join(&relative)?;
    /// assert_eq!(joined.spec(), "https://www.google.com/foo/baz#newfragment");
    ///
    /// let new_relative = joined.relative_to(&base)?;
    /// let new_joined = base.join(&new_relative)?;
    /// assert_eq!(new_joined, joined);
    ///
    /// assert_eq!(new_relative, relative);
    ///
    /// let base: UrlBuilder = "https://www.microsoft.com/over/here".parse()?;
    /// let relative: UrlBuilder = "//www.microsoft.com/over/there".parse()?;
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
        self.host
            .as_ref()
            .and_then(|h| h.authentication.as_ref())
            .and_then(|a| Some(a.username.clone()))
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
                    match (&mut h.authentication, username) {
                        (Some(auth), Some(u)) => {
                            auth.username = u.to_owned();
                            Ok(())
                        }
                        (Some(_), None) => {
                            h.authentication = None;
                            Ok(())
                        }
                        (None, Some(u)) => {
                            h.authentication = Some(Authentication {
                                username: u.to_owned(),
                                password: String::new(),
                            });
                            Ok(())
                        }
                        (None, None) => Ok(()),
                    }
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
        self.host
            .as_ref()
            .and_then(|h| h.authentication.as_ref())
            .and_then(|a| Some(a.password.clone()))
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
                    match (&mut h.authentication, password) {
                        (Some(auth), Some(p)) => {
                            auth.password = p.to_owned();
                            Ok(())
                        }
                        (Some(_), None) => {
                            h.authentication = None;
                            Ok(())
                        }
                        (None, Some(p)) => {
                            h.authentication = Some(Authentication {
                                username: String::new(),
                                password: p.to_owned(),
                            });
                            Ok(())
                        }
                        (None, None) => Ok(()),
                    }
                }
            }
            None => {
                // password must contain Some at this point or the bailout above
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
                        authentication: None,
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
    /// table of known ports for schemes is used. None is returned if neither
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
        self.path = path.parse()?;
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
        UrlParser::parse_spec(spec)
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
/// This struct holds an absolute URL and will not allow modifying the URL into
/// something that is not an absolute URL.
///
/// # Examples
///
/// ```
/// # use simpleurl::UrlResult;
/// use simpleurl::{UrlBuilder, Url};
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
/// assert!(builder.is_absolute_url());
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
    /// # use simpleurl::UrlResult;
    /// use simpleurl::Url;
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
        let mut spec_builder = spec.parse::<UrlBuilder>()?;
        if spec_builder.is_absolute_url() {
            spec_builder.normalize();
            Ok(spec_builder.try_into()?)
        } else if spec_builder.is_relative_url() {
            match base_url.into() {
                Some(s) => {
                    let base_builder = s.parse::<UrlBuilder>()?;
                    if base_builder.is_absolute_url() {
                        let mut joined = base_builder.join(&spec_builder)?;
                        joined.normalize();
                        Ok(joined.try_into()?)
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
    /// # use simpleurl::UrlResult;
    /// use simpleurl::{ Url, RelativeUrl };
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
    /// # use simpleurl::UrlResult;
    /// use simpleurl::{ Url, RelativeUrl };
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

    /// Returns the current URL's scheme.
    pub fn scheme(&self) -> String {
        if let Some(ref s) = self.builder.scheme {
            return s.to_string();
        }

        panic!("Unreachable.");
    }

    /// Sets the scheme for the current URL.
    ///
    /// The sheme must not be empty.
    pub fn set_scheme(&mut self, scheme: &str) -> UrlResult<()> {
        self.builder.scheme = Scheme::from(scheme);

        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s username.
    pub fn username(&self) -> Option<String> {
        self.builder.username()
    }

    /// Sets the current `Url`'s username.
    pub fn set_username(&mut self, username: Option<&str>) -> UrlResult<()> {
        self.builder.set_username(username)?;
        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s password.
    pub fn password(&self) -> Option<String> {
        self.builder.password()
    }

    /// Sets the current `Url`'s password.
    pub fn set_password(&mut self, password: Option<&str>) -> UrlResult<()> {
        self.builder.set_password(password)?;
        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s hostname.
    pub fn hostname(&self) -> String {
        match self.builder.host {
            Some(ref h) => h.hostname.clone(),
            None => String::new(),
        }
    }

    /// Sets the current `Url`'s hostname.
    pub fn set_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        self.builder.set_hostname(Some(hostname))?;
        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s port.
    pub fn port(&self) -> Option<u32> {
        self.builder.port()
    }

    /// Sets the current `Url`'s port.
    pub fn set_port(&mut self, port: Option<u32>) -> UrlResult<()> {
        self.builder.set_port(port)?;
        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s path.
    pub fn path(&self) -> String {
        self.builder.path()
    }

    /// Sets the current `Url`'s path.
    pub fn set_path(&mut self, path: &str) -> UrlResult<()> {
        if !path.starts_with('/') {
            Err(UrlError::new(
                "Cannot give an absolute URL a relative path.",
                path,
            ))
        } else {
            self.builder.set_path(path)?;
            assert!(
                self.builder.is_absolute_url(),
                "URL must still be absolute after mutation."
            );
            Ok(())
        }
    }

    /// Returns the current `Url`'s query string.
    pub fn query(&self) -> Option<String> {
        self.builder.query()
    }

    /// Sets the current `Url`'s query string.
    pub fn set_query(&mut self, search: Option<&str>) -> UrlResult<()> {
        self.builder.set_query(search)?;
        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s fragment.
    pub fn fragment(&self) -> Option<String> {
        self.builder.fragment()
    }

    /// Sets the current `Url`'s fragment.
    pub fn set_fragment(&mut self, fragment: Option<&str>) -> UrlResult<()> {
        self.builder.set_fragment(fragment)?;
        assert!(
            self.builder.is_absolute_url(),
            "URL must still be absolute after mutation."
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

/// Represents a relative URL.
///
/// This struct holds a relative URL and will not allow modifying the URL into
/// something that is not a relative URL.
///
/// # Examples
///
/// ```
/// # use simpleurl::UrlResult;
/// use simpleurl::{UrlBuilder, RelativeUrl};
/// use std::convert::TryFrom;
///
/// # fn main() -> UrlResult<()> {
/// let spec = "//www.google.com/foo#bar";
/// let url: RelativeUrl = spec.parse()?;
/// assert_eq!(url.spec(), spec);
///
/// let mut builder: UrlBuilder = Default::default();
/// builder.set_hostname(Some("www.google.com"))?;
/// builder.set_path("/foo")?;
/// builder.set_fragment(Some("bar"))?;
/// assert!(builder.is_relative_url());
/// assert_eq!(RelativeUrl::try_from(builder)?, url);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, PartialEq)]
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
    pub fn username(&self) -> Option<String> {
        self.builder.username()
    }

    /// Sets the current `RelativeUrl`'s username.
    pub fn set_username(&mut self, username: Option<&str>) -> UrlResult<()> {
        self.builder.set_username(username)?;
        assert!(
            self.builder.is_relative_url(),
            "URL must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `Url`'s password.
    pub fn password(&self) -> Option<String> {
        self.builder.password()
    }

    /// Sets the current `RelativeUrl`'s password.
    pub fn set_password(&mut self, password: Option<&str>) -> UrlResult<()> {
        self.builder.set_password(password)?;
        assert!(
            self.builder.is_relative_url(),
            "URL must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s hostname.
    pub fn hostname(&self) -> Option<String> {
        self.builder.host.as_ref().map(|h| h.hostname.clone())
    }

    /// Sets the current `RelativeUrl`'s hostname.
    pub fn set_hostname(&mut self, hostname: Option<&str>) -> UrlResult<()> {
        self.builder.set_hostname(hostname)?;
        assert!(
            self.builder.is_relative_url(),
            "URL must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s port.
    pub fn port(&self) -> Option<u32> {
        self.builder.port()
    }

    /// Sets the current `RelativeUrl`'s port.
    pub fn set_port(&mut self, port: Option<u32>) -> UrlResult<()> {
        self.builder.set_port(port)?;
        assert!(
            self.builder.is_relative_url(),
            "URL must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s path.
    pub fn path(&self) -> String {
        self.builder.path()
    }

    /// Sets the current `RelativeUrl`'s path.
    pub fn set_path(&mut self, path: &str) -> UrlResult<()> {
        if self.builder.host.is_some() && !path.starts_with('/') {
            Err(UrlError::new(
                "Cannot give an URL with a host name a relative path.",
                path,
            ))
        } else {
            self.builder.set_path(path)?;
            assert!(
                self.builder.is_relative_url(),
                "URL must still be relative after mutation."
            );
            Ok(())
        }
    }

    /// Returns the current `RelativeUrl`'s query string.
    pub fn query(&self) -> Option<String> {
        self.builder.query()
    }

    /// Sets the current `RelativeUrl`'s query string.
    pub fn set_query(&mut self, search: Option<&str>) -> UrlResult<()> {
        self.builder.set_query(search)?;
        assert!(
            self.builder.is_relative_url(),
            "URL must still be relative after mutation."
        );
        Ok(())
    }

    /// Returns the current `RelativeUrl`'s fragment.
    pub fn fragment(&self) -> Option<String> {
        self.builder.fragment()
    }

    /// Sets the current `RelativeUrl`'s fragment.
    pub fn set_fragment(&mut self, fragment: Option<&str>) -> UrlResult<()> {
        self.builder.set_fragment(fragment)?;
        assert!(
            self.builder.is_relative_url(),
            "URL must still be relative after mutation."
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
    #![allow(clippy::cognitive_complexity)]
    use super::*;

    fn builder_parse_change(spec: &str, expected: &str) -> UrlResult<UrlBuilder> {
        let builder = spec.parse::<UrlBuilder>()?;
        assert_eq!(
            &builder.spec(),
            expected,
            "Parsed spec should match expected."
        );
        let reparsed = builder.spec().parse::<UrlBuilder>()?;
        assert_eq!(reparsed, builder, "Reparsed builder should match original.");
        Ok(builder)
    }

    fn builder_parse(spec: &str) -> UrlResult<UrlBuilder> {
        builder_parse_change(spec, spec)
    }

    #[test]
    fn builder_parse_absolute_urls() -> UrlResult<()> {
        let builder = builder_parse("http://foo:bar@www.example.com:24/foo/bar?zed#frag")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("http"))),
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("foo"),
                        password: String::from("bar"),
                    }),
                    hostname: String::from("www.example.com"),
                    port: Some(24),
                }),
                path: Path::from_components(vec!["", "foo", "bar"]),
                query: Some(String::from("zed")),
                fragment: Some(String::from("frag")),
            },
        );

        let builder = builder_parse_change("https://hello@foo", "https://hello@foo/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::Named(String::from("https"))),
                host: Some(Host {
                    authentication: Some(Authentication {
                        username: String::from("hello"),
                        password: String::new(),
                    }),
                    hostname: String::from("foo"),
                    port: None,
                }),
                path: Path::root_path(),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("file:///foo/bar")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::new(),
                    port: None,
                }),
                path: Path::from_components(vec!["", "foo", "bar"]),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("file:")?;
        assert!(!builder.is_absolute_url());
        assert!(!builder.is_relative_url());

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

        Ok(())
    }

    #[test]
    fn builder_parse_relative_urls() -> UrlResult<()> {
        let builder = builder_parse("//www/example")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("www"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "example"]),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("/www/example")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert!(builder.path.is_absolute());
        assert!(!builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["", "www", "example"]),
                query: None,
                fragment: None,
            }
        );

        let builder = builder_parse("www/example/")?;
        assert!(!builder.is_absolute_url());
        assert!(builder.is_relative_url());
        assert!(!builder.path.is_absolute());
        assert!(builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: None,
                host: None,
                path: Path::from_components(vec!["www", "example", ""]),
                query: None,
                fragment: None,
            }
        );

        Ok(())
    }

    #[test]
    fn builder_parse_bad_urls() -> UrlResult<()> {
        let builder = builder_parse("file://foo/bar/")?;
        assert!(builder.is_absolute_url());
        assert!(!builder.is_relative_url());
        assert!(!builder.path.is_empty());
        assert!(builder.path.is_absolute());
        assert!(builder.path.is_directory());

        assert_eq!(
            builder,
            UrlBuilder {
                scheme: Some(Scheme::File),
                host: Some(Host {
                    authentication: None,
                    hostname: String::from("foo"),
                    port: None,
                }),
                path: Path::from_components(vec!["", "bar", ""]),
                query: None,
                fragment: None,
            }
        );

        Ok(())
    }

    fn check_normalize(test: &str, expected: &str) -> UrlResult<()> {
        let mut path: Path = test.parse()?;
        path.normalize();
        assert_eq!(
            path.to_string(),
            expected,
            "Normalized spec should have matched expected."
        );

        Ok(())
    }

    #[test]
    fn builder_path_normalize() -> UrlResult<()> {
        check_normalize("/foo/.././bar/", "/bar/")?;
        check_normalize("/foo/../bar", "/bar")?;
        check_normalize("/../bar/", "/bar/")?;
        check_normalize("foo/.././bar/", "bar/")?;
        check_normalize("foo/../bar", "bar")?;
        check_normalize("../bar/", "../bar/")?;
        check_normalize("../../../bar/../../", "../../../../")?;
        check_normalize("/../../../bar/../../", "/")?;
        check_normalize("/boo/bar/..", "/boo/")?;
        check_normalize("/boo/bar/../", "/boo/")?;

        Ok(())
    }

    fn check_join_split(
        base: &str,
        relative: &str,
        expected: &str,
        after_split: &str,
    ) -> UrlResult<()> {
        let base_builder: UrlBuilder = base.parse()?;
        let relative_builder: UrlBuilder = relative.parse()?;

        let joined = base_builder.join(&relative_builder)?;

        assert_eq!(
            joined.spec(),
            expected,
            "Joined spec should match expected spec.",
        );

        let split = joined.relative_to(&base_builder)?;

        assert_eq!(
            split.spec(),
            after_split,
            "Split spec should match expected.",
        );

        Ok(())
    }

    fn check_join_split_exact(base: &str, relative: &str, expected: &str) -> UrlResult<()> {
        check_join_split(base, relative, expected, relative)
    }

    fn check_join_split_change(
        base: &str,
        relative: &str,
        expected: &str,
        after_split: &str,
    ) -> UrlResult<()> {
        check_join_split(base, relative, expected, after_split)
    }

    #[test]
    fn builder_join_split() -> UrlResult<()> {
        check_join_split_exact(
            "http://foo/bar/#bozzy",
            "baz#bizzy",
            "http://foo/bar/baz#bizzy",
        )?;
        check_join_split_exact("https://foo/baz/#test", "//bar/boo", "https://bar/boo")?;
        check_join_split_exact("http://foo/bar/baz?test", "boo#fr", "http://foo/bar/boo#fr")?;
        check_join_split_exact("http://boo/bar/baz", "", "http://boo/bar/baz")?;
        check_join_split_exact("http://boo/bar/baz/", "", "http://boo/bar/baz/")?;
        check_join_split_exact("http://boo/bar/baz", "boo", "http://boo/bar/boo")?;
        check_join_split_exact("http://boo/bar/baz/", "boo", "http://boo/bar/baz/boo")?;
        check_join_split_change("http://boo/bar/baz/bad", "..", "http://boo/bar/", "../")?;
        check_join_split_exact("http://boo/bar/baz/bad", "../", "http://boo/bar/")?;
        check_join_split_change(
            "http://boo/bar/baz/bad/",
            "..",
            "http://boo/bar/baz/",
            "../",
        )?;
        check_join_split_exact("http://boo/bar/baz/bad/", "../", "http://boo/bar/baz/")?;
        check_join_split_exact("/", "foo/bar", "/foo/bar")?;
        check_join_split_change("/", "../foo/bar", "/foo/bar", "foo/bar")?;

        Ok(())
    }
}
