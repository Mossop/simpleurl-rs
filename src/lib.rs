use regex::Regex;
use std::convert::{TryFrom, TryInto};
use std::error;
use std::fmt;
use std::str::FromStr;
use std::string::ToString;

const C0_CONTROL: &str = "\u{0000}-\u{001F}";
const URL_CODE_POINTS: &str =
    "0-9A-Za-z!$&'()*+,-\\./:;=?@_~\u{00A0}-\u{D7FF}\u{E000}-\u{10FFFD}--\
     [\u{FDD0}-\u{FDEF}\u{FFFE}\u{FFFF}\u{1FFFE}\u{1FFFF}\u{2FFFE}\u{2FFFF}\
     \u{3FFFE}\u{3FFFF}\u{4FFFE}\u{4FFFF}\u{5FFFE}\u{5FFFF}\u{6FFFE}\u{6FFFF}\
     \u{7FFFE}\u{7FFFF}\u{8FFFE}\u{8FFFF}\u{9FFFE}\u{9FFFF}\u{AFFFE}\u{AFFFF}\
     \u{BFFFE}\u{BFFFF}\u{CFFFE}\u{CFFFF}\u{DFFFE}\u{DFFFF}\u{EFFFE}\u{EFFFF}\
     \u{FFFFE}\u{FFFFF}\u{10FFFE}\u{10FFFF}]\
     ";
const PERCENT_ENCODED_BYTE: &str = "%[0-9a-fA-F]{2}";

fn percent_decode(data: &str) -> String {
    String::from(data)
}

fn percent_encode(data: &str) -> String {
    String::from(data)
}

#[derive(Debug)]
pub struct UrlError {
    spec: String,
    message: String,
}

impl UrlError {
    fn new(message: &str, spec: &str) -> Self {
        Self {
            spec: String::from(spec),
            message: String::from(message),
        }
    }
}

impl fmt::Display for UrlError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_fmt(format_args!("Url error: {}", self.message))
    }
}

impl error::Error for UrlError {}

pub type UrlResult<T> = Result<T, UrlError>;

pub fn regex(r: &str) -> UrlResult<Regex> {
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

const SPECIAL_SCHEMES: [(&str, u32); 6] = [
    ("ftp", 21),
    ("gopher", 70),
    ("http", 80),
    ("https", 443),
    ("ws", 80),
    ("wss", 443),
];

#[derive(Debug, Clone, PartialEq)]
enum Scheme {
    Special(String),
    NotSpecial(String),
    File,
}

impl Scheme {
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

    fn get_default_port(&self) -> Option<u32> {
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

#[derive(Debug, Clone, PartialEq, Default)]
struct Host {
    username: Option<String>,
    password: Option<String>,
    hostname: String,
    port: Option<u32>,
}

impl Host {
    fn get_hostport(&self) -> String {
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

        f.write_str(&self.get_hostport())
    }
}

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

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Path {
    components: Vec<String>,
}

impl Path {
    pub fn from(path: &str) -> Self {
        if path.is_empty() {
            Default::default()
        } else {
            Path {
                components: path.split('/').map(|p| percent_decode(p)).collect(),
            }
        }
    }

    fn normalize(&mut self) {
        self.components = normalize(&self.components);
    }

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

    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    pub fn is_absolute(&self) -> bool {
        match self.components.first() {
            Some(p) => p.is_empty(),
            None => false,
        }
    }

    pub fn is_relative(&self) -> bool {
        match self.components.first() {
            Some(p) => !p.is_empty(),
            None => true,
        }
    }

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

#[derive(Debug, Clone, PartialEq)]
pub struct UrlSearchParams {}

impl fmt::Display for UrlSearchParams {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        Ok(())
    }
}

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

fn map_match_to_string(option: Option<regex::Match>, _spec: &str) -> Option<String> {
    option.map(|m| String::from(m.as_str()))
}

fn map_match_to_u32(option: Option<regex::Match>, spec: &str) -> UrlResult<Option<u32>> {
    match option {
        Some(m) => match m.as_str().parse::<u32>() {
            Ok(p) => Ok(Some(p)),
            _ => Err(UrlError::new("Unable to parse port number", spec)),
        },
        None => Ok(None),
    }
}

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
                hostname: String::from(&captures[3]),
                port: map_match_to_u32(captures.get(4), spec)?,
            }))
        }
        None => Ok(Some(Default::default())),
    }
}

fn parse_path(spec: &str, start_pos: &mut usize, end_pos: &mut usize) -> UrlResult<Path> {
    if end_pos < start_pos {
        return Err(UrlError::new("Parse failure (end < start).", spec));
    }

    let search = &spec[*start_pos..*end_pos];
    *start_pos = *end_pos;

    Ok(Path::from(search))
}

fn parse_search(
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
    Ok(Some(String::from(&frag_match.as_str()[1..])))
}

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

#[derive(Debug, Clone, PartialEq, Default)]
pub struct UrlBuilder {
    // All of these are percent decoded
    scheme: Option<Scheme>,
    host: Option<Host>,
    path: Path,
    fragment: Option<String>,

    // This remains percent encoded
    search: Option<String>,
}

impl UrlBuilder {
    pub fn new(spec: &str) -> UrlResult<Self> {
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
        builder.search = parse_search(spec, &mut start_pos, &mut end_pos)?;

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

    pub fn normalize(&mut self) {
        self.path.normalize();
    }

    pub fn get_spec(&self) -> String {
        self.to_string()
    }

    pub fn is_valid(&self) -> bool {
        if self.host.is_some() && !self.path.is_absolute() {
            return false;
        }

        true
    }

    pub fn is_absolute_url(&self) -> bool {
        if !self.is_valid() {
            return false;
        }

        match self.scheme {
            Some(ref scheme) => match scheme {
                Scheme::File => {
                    if self.path.is_absolute() {
                        if let Some(ref h) = self.host {
                            h.hostname.is_empty()
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }
                _ => self.host.is_some(),
            },
            None => false,
        }
    }

    pub fn is_relative_url(&self) -> bool {
        if !self.is_valid() {
            return false;
        }

        self.scheme.is_none()
    }

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
        new_builder.search = relative.search.clone();

        Ok(new_builder)
    }

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

        result.search = self.search.clone();
        result.fragment = self.fragment.clone();

        Ok(result)
    }

    pub fn get_scheme(&self) -> Option<String> {
        self.scheme.as_ref().map(ToString::to_string)
    }

    pub fn set_scheme(&mut self, scheme: Option<&str>) -> UrlResult<()> {
        self.scheme = scheme.and_then(|s| Scheme::from(s));
        Ok(())
    }

    pub fn get_username(&self) -> Option<String> {
        self.host.as_ref().and_then(|h| h.username.clone())
    }

    pub fn set_username(&mut self, username: Option<String>) -> UrlResult<()> {
        match &mut self.host {
            Some(h) => {
                h.username = username;
                Ok(())
            }
            None => match username {
                Some(_) => Err(UrlError::new(
                    "Cannot set a username on a url with no hostname",
                    "",
                )),
                None => Ok(()),
            },
        }
    }

    pub fn get_password(&self) -> Option<String> {
        self.host.as_ref().and_then(|h| h.password.clone())
    }

    pub fn set_password(&mut self, password: Option<String>) -> UrlResult<()> {
        match &mut self.host {
            Some(h) => {
                h.password = password;
                Ok(())
            }
            None => match password {
                Some(_) => Err(UrlError::new(
                    "Cannot set a password on a url with no hostname",
                    "",
                )),
                None => Ok(()),
            },
        }
    }

    pub fn get_hostname(&self) -> Option<String> {
        self.host.as_ref().and_then(|h| Some(h.hostname.clone()))
    }

    pub fn set_hostname(&mut self, hostname: Option<String>) -> UrlResult<()> {
        match hostname {
            Some(h) => match &mut self.host {
                Some(t) => t.hostname = h,
                None => {
                    self.host = Some(Host {
                        username: None,
                        password: None,
                        hostname: h,
                        port: None,
                    })
                }
            },
            None => self.host = None,
        };

        Ok(())
    }

    pub fn get_port(&self) -> Option<u32> {
        self.host.as_ref().and_then(|h| h.port)
    }

    pub fn set_port(&mut self, port: Option<u32>) -> UrlResult<()> {
        match &mut self.host {
            Some(h) => {
                h.port = port;
                Ok(())
            }
            None => match port {
                Some(_) => Err(UrlError::new(
                    "Cannot set a port on a url with no hostname",
                    "",
                )),
                None => Ok(()),
            },
        }
    }

    pub fn get_active_port(&self) -> Option<u32> {
        self.get_port()
            .or_else(|| self.scheme.as_ref().and_then(Scheme::get_default_port))
    }

    pub fn set_active_port(&mut self, port: Option<u32>) -> UrlResult<()> {
        let default = self.scheme.as_ref().and_then(Scheme::get_default_port);
        if port == default {
            self.set_port(port)
        } else {
            self.set_port(None)
        }
    }

    pub fn get_path(&self) -> Path {
        self.path.clone()
    }

    pub fn set_path(&mut self, path: Path) -> UrlResult<()> {
        self.path = path;
        Ok(())
    }

    pub fn get_search(&self) -> Option<String> {
        self.search.clone()
    }

    pub fn set_search(&mut self, search: Option<String>) -> UrlResult<()> {
        self.search = search;
        Ok(())
    }

    pub fn get_fragment(&self) -> Option<String> {
        self.fragment.clone()
    }

    pub fn set_fragment(&mut self, fragment: Option<String>) -> UrlResult<()> {
        self.fragment = fragment;
        Ok(())
    }
}

impl UrlBuilder {
    fn get_url_protocol(&self) -> String {
        self.get_scheme()
            .map_or(String::new(), |s| format!("{}:", s))
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

    fn get_url_username(&self) -> String {
        self.get_username().unwrap_or_default()
    }

    fn set_url_username(&mut self, username: &str) -> UrlResult<()> {
        if username.is_empty() {
            self.set_username(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a username for a file url.",
                &self.get_spec(),
            ))
        } else {
            self.set_username(Some(String::from(username)))
        }
    }

    fn get_url_password(&self) -> String {
        self.get_password().unwrap_or_default()
    }

    fn set_url_password(&mut self, password: &str) -> UrlResult<()> {
        if password.is_empty() {
            self.set_password(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a password for a file url.",
                &self.get_spec(),
            ))
        } else {
            self.set_password(Some(String::from(password)))
        }
    }

    fn get_url_hostname(&self) -> String {
        self.get_hostname().unwrap_or_default()
    }

    fn set_url_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        if hostname.is_empty() {
            self.set_hostname(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a hostname for a file url.",
                &self.get_spec(),
            ))
        } else {
            self.set_hostname(Some(String::from(hostname)))
        }
    }

    fn get_url_port(&self) -> String {
        self.get_port().map_or(String::new(), |p| p.to_string())
    }

    fn set_url_port(&mut self, port: &str) -> UrlResult<()> {
        if port.is_empty() {
            self.set_port(None)
        } else if self.scheme == Some(Scheme::File) {
            Err(UrlError::new(
                "Cannot set a port for a file url.",
                &self.get_spec(),
            ))
        } else {
            match port.parse::<u32>() {
                Ok(p) => self.set_port(Some(p)),
                Err(_) => Err(UrlError::new("Unable to parse port number.", port)),
            }
        }
    }

    fn get_url_host(&self) -> String {
        self.host.as_ref().map_or(String::new(), Host::get_hostport)
    }

    fn set_url_host(&mut self, host: &str) -> UrlResult<()> {
        if host.is_empty() {
            self.set_hostname(None)
        } else {
            match host.find(':') {
                Some(i) => {
                    self.set_hostname(Some(String::from(&host[..i])))?;
                    self.set_url_port(&host[i + 1..])
                }
                None => {
                    self.set_hostname(Some(String::from(host)))?;
                    self.set_port(None)
                }
            }
        }
    }

    fn get_url_pathname(&self) -> String {
        self.path.to_string()
    }

    fn set_url_pathname(&mut self, path: &str) -> UrlResult<()> {
        self.path = Path::from(path);
        Ok(())
    }

    fn get_url_search(&self) -> String {
        self.search
            .as_ref()
            .map_or(String::new(), |s| format!("?{}", s))
    }

    fn set_url_search(&mut self, search: &str) -> UrlResult<()> {
        if search.is_empty() {
            self.search = None
        } else if search.starts_with('?') {
            self.search = Some(String::from(&search[1..]));
        } else {
            self.search = Some(String::from(search));
        }

        Ok(())
    }

    fn get_url_hash(&self) -> String {
        self.fragment
            .as_ref()
            .map_or(String::new(), |f| format!("#{}", percent_encode(&f)))
    }

    fn set_url_hash(&mut self, hash: &str) -> UrlResult<()> {
        if hash.is_empty() {
            self.fragment = None;
        } else if hash.starts_with('#') {
            self.fragment = Some(String::from(&hash[1..]));
        } else {
            self.fragment = Some(String::from(hash));
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

        if let Some(ref s) = self.search {
            f.write_fmt(format_args!("?{}", &percent_encode(&s)))?;
        }

        if let Some(ref frag) = self.fragment {
            f.write_fmt(format_args!("#{}", &percent_encode(&frag)))?;
        }

        Ok(())
    }
}

impl TryFrom<&str> for UrlBuilder {
    type Error = UrlError;

    fn try_from(spec: &str) -> Result<Self, Self::Error> {
        UrlBuilder::new(spec)
    }
}

impl FromStr for UrlBuilder {
    type Err = UrlError;

    fn from_str(spec: &str) -> Result<Self, Self::Err> {
        UrlBuilder::try_from(spec)
    }
}

impl TryInto<Url> for UrlBuilder {
    type Error = UrlError;

    fn try_into(self) -> Result<Url, Self::Error> {
        if self.is_relative_url() {
            Ok(Url { builder: self })
        } else {
            Err(UrlError::new(
                "Unable to build an absolute url.",
                &self.get_spec(),
            ))
        }
    }
}

impl TryInto<RelativeUrl> for UrlBuilder {
    type Error = UrlError;

    fn try_into(self) -> Result<RelativeUrl, Self::Error> {
        if self.is_absolute_url() {
            Ok(RelativeUrl { builder: self })
        } else {
            Err(UrlError::new(
                "Unable to build a relative url.",
                &self.get_spec(),
            ))
        }
    }
}

#[derive(Debug, Clone)]
pub struct Url {
    builder: UrlBuilder,
}

impl Url {
    pub fn new(spec: &str, base_url: Option<&str>) -> UrlResult<Self> {
        match base_url {
            Some(s) => Url::try_from(s)?.join(&RelativeUrl::try_from(spec)?),
            None => Url::try_from(spec),
        }
    }

    pub fn get_builder(&self) -> UrlBuilder {
        self.builder.clone()
    }

    pub fn get_spec(&self) -> String {
        self.builder.get_spec()
    }

    pub fn get_href(&self) -> String {
        self.get_spec()
    }

    pub fn join(&self, relative: &RelativeUrl) -> UrlResult<Self> {
        let builder = self.builder.join(&relative.builder)?;
        builder.try_into()
    }

    pub fn relative_to(&self, base: &Url) -> UrlResult<RelativeUrl> {
        let builder = self.builder.relative_to(&base.builder)?;
        builder.try_into()
    }

    pub fn get_origin(&self) -> String {
        assert!(
            self.builder.is_absolute_url(),
            "Url should be absolute to have an origin."
        );

        format!(
            "{}{}",
            self.builder.get_url_protocol(),
            self.builder
                .host
                .as_ref()
                .map_or(String::new(), ToString::to_string)
        )
    }
}

impl Url {
    pub fn get_protocol(&self) -> String {
        self.builder.get_url_protocol()
    }

    pub fn set_protocol(&mut self, scheme: &str) -> UrlResult<()> {
        self.builder.set_url_protocol(scheme)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_username(&self) -> String {
        self.builder.get_url_username()
    }

    pub fn set_username(&mut self, username: &str) -> UrlResult<()> {
        self.builder.set_url_username(username)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_password(&self) -> String {
        self.builder.get_url_password()
    }

    pub fn set_password(&mut self, password: &str) -> UrlResult<()> {
        self.builder.set_url_password(password)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_hostname(&self) -> String {
        self.builder.get_url_hostname()
    }

    pub fn set_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        self.builder.set_url_hostname(hostname)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_port(&self) -> String {
        self.builder.get_url_port()
    }

    pub fn set_port(&mut self, port: &str) -> UrlResult<()> {
        self.builder.set_url_port(port)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_host(&self) -> String {
        self.builder.get_url_host()
    }

    pub fn set_host(&mut self, host: &str) -> UrlResult<()> {
        self.builder.set_url_host(host)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_pathname(&self) -> String {
        self.builder.get_url_pathname()
    }

    pub fn set_pathname(&mut self, path: &str) -> UrlResult<()> {
        self.builder.set_url_pathname(path)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_search(&self) -> String {
        self.builder.get_url_search()
    }

    pub fn set_search(&mut self, search: &str) -> UrlResult<()> {
        self.builder.set_url_search(search)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }

    pub fn get_hash(&self) -> String {
        self.builder.get_url_hash()
    }

    pub fn set_hash(&mut self, hash: &str) -> UrlResult<()> {
        self.builder.set_url_hash(hash)?;
        assert!(
            self.builder.is_absolute_url(),
            "Url must still be absolute after mutation."
        );
        Ok(())
    }
}

impl TryFrom<&str> for Url {
    type Error = UrlError;

    fn try_from(spec: &str) -> Result<Self, Self::Error> {
        let builder = UrlBuilder::try_from(spec)?;
        builder.try_into()
    }
}

impl FromStr for Url {
    type Err = UrlError;

    fn from_str(spec: &str) -> Result<Self, Self::Err> {
        Url::try_from(spec)
    }
}

impl fmt::Display for Url {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_str(&self.get_href())
    }
}

#[derive(Debug, Clone)]
pub struct RelativeUrl {
    builder: UrlBuilder,
}

impl RelativeUrl {
    pub fn new(spec: &str) -> UrlResult<Self> {
        RelativeUrl::try_from(spec)
    }

    pub fn get_builder(&self) -> UrlBuilder {
        self.builder.clone()
    }
}

impl RelativeUrl {
    pub fn get_username(&self) -> String {
        self.builder.get_url_username()
    }

    pub fn set_username(&mut self, username: &str) -> UrlResult<()> {
        self.builder.set_url_username(username)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_password(&self) -> String {
        self.builder.get_url_password()
    }

    pub fn set_password(&mut self, password: &str) -> UrlResult<()> {
        self.builder.set_url_password(password)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_hostname(&self) -> String {
        self.builder.get_url_hostname()
    }

    pub fn set_hostname(&mut self, hostname: &str) -> UrlResult<()> {
        self.builder.set_url_hostname(hostname)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_port(&self) -> String {
        self.builder.get_url_port()
    }

    pub fn set_port(&mut self, port: &str) -> UrlResult<()> {
        self.builder.set_url_port(port)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_host(&self) -> String {
        self.builder.get_url_host()
    }

    pub fn set_host(&mut self, host: &str) -> UrlResult<()> {
        self.builder.set_url_host(host)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_pathname(&self) -> String {
        self.builder.get_url_pathname()
    }

    pub fn set_pathname(&mut self, path: &str) -> UrlResult<()> {
        self.builder.set_url_pathname(path)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_search(&self) -> String {
        self.builder.get_url_search()
    }

    pub fn set_search(&mut self, search: &str) -> UrlResult<()> {
        self.builder.set_url_search(search)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }

    pub fn get_hash(&self) -> String {
        self.builder.get_url_hash()
    }

    pub fn set_hash(&mut self, hash: &str) -> UrlResult<()> {
        self.builder.set_url_hash(hash)?;
        assert!(
            self.builder.is_relative_url(),
            "Url must still be relative after mutation."
        );
        Ok(())
    }
}

impl TryFrom<&str> for RelativeUrl {
    type Error = UrlError;

    fn try_from(spec: &str) -> Result<Self, Self::Error> {
        let builder = UrlBuilder::try_from(spec)?;
        builder.try_into()
    }
}

impl FromStr for RelativeUrl {
    type Err = UrlError;

    fn from_str(spec: &str) -> Result<Self, Self::Err> {
        RelativeUrl::try_from(spec)
    }
}

impl fmt::Display for RelativeUrl {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.get_builder().fmt(f)
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
            &builder.get_spec(),
            expected,
            "Parsed spec should match expected."
        );
        let reparsed = builder.get_spec().parse::<UrlBuilder>().unwrap();
        assert_eq!(builder, reparsed, "Reparsed builder should match original.");
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
                search: Some(String::from("zed")),
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
                search: None,
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
                search: None,
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
                search: None,
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
                search: None,
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
                search: None,
                fragment: None,
            }
        );
    }

    #[test]
    fn builder_parse_bad_urls() {
        let builder = builder_parse("file:");
        assert!(builder.is_valid());
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
                search: None,
                fragment: None,
            }
        );

        let builder = builder_parse("file://foo/bar/");
        assert!(builder.is_valid());
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
                search: None,
                fragment: None,
            }
        );
    }

    fn check_normalize(spec: &str, expected: &str) {
        let mut builder = UrlBuilder::new(spec).unwrap();
        builder.normalize();
        assert_eq!(
            builder.get_spec(),
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
        let base_builder = UrlBuilder::new(base).unwrap();
        let relative_builder = UrlBuilder::new(relative).unwrap();

        let joined = base_builder.join(&relative_builder).unwrap();

        assert_eq!(
            joined.get_spec(),
            expected,
            "Joined spec should match expected spec.",
        );

        let split = joined.relative_to(&base_builder).unwrap();

        assert_eq!(
            split.get_spec(),
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
