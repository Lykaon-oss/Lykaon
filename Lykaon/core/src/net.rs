//! M4-10 (Appendix K 7.8): the network sentences' engine.
//!
//! The client side: one hand-written HTTP/1.1 request over a TCP stream,
//! with TLS from rustls when the scheme is secure (the default; S61). The
//! spec's defaults hold here: 30-second whole-request timeout, up to 5
//! redirects for GET, 3 attempts for GET failures before any byte was
//! sent (waits of 1, 2 and 4 seconds), other methods never retried. The
//! response is a record with status (whole), body (text) and headers
//! (map of text to text); a status of 400 or more is NOT a failure. The
//! only failures are connection-level, with the kinds the spec names:
//! not found (DNS), other (refused, and tls-prefixed for a TLS
//! verification failure), timed out, bad format.

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

/// The compile-time address (G62-G66): the scheme, the host words, the
/// optional port and the resolved place path.
#[derive(Clone, Debug)]
pub struct Address {
    /// true = https (the default, "secure"); false = http ("plain").
    pub secure: bool,
    pub host: String,
    pub port: u16,
    /// The place's path, always starting with "/" ("/" alone for no
    /// place; a page name resolved against the Page table at compile
    /// time, or "path a and b" segments joined).
    pub path: String,
}

/// The request method (G69). Lower case; the wire form is upper case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Method {
    Get,
    Post,
    Put,
    Delete,
    Patch,
}

impl Method {
    pub fn wire(self) -> &'static str {
        match self {
            Method::Get => "GET",
            Method::Post => "POST",
            Method::Put => "PUT",
            Method::Delete => "DELETE",
            Method::Patch => "PATCH",
        }
    }
}

/// One response (S60): a status of 400 or more is not a failure; the
/// record the sentence gives has status (whole), body (text) and
/// headers (map of text to text).
pub struct Response {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

/// A request-level failure with the kind the spec names (S61/S37).
/// The interpreter turns this into the ordinary kinded failure.
pub struct NetFail {
    pub kind: &'static str, // "not found" | "other" | "timed out" | "bad format"
    pub message: String,
}

impl NetFail {
    fn other(message: impl Into<String>) -> NetFail {
        NetFail {
            kind: "other",
            message: message.into(),
        }
    }
}

/// A header the sentence adds (with header NAME x): the words joined by
/// "-". Percent-encodes a query value (with query NAME x).
pub struct Request {
    pub method: Method,
    pub address: Address,
    pub data: Option<Data>,
    pub headers: Vec<(String, String)>,
    pub query: Vec<(String, String)>,
    /// S62: skip the certificate check (only legal inside Be careful).
    pub skip_tls: bool,
}

/// The with-data body (S60): text as text/plain; charset=utf-8, bytes
/// as application/octet-stream, a record/list/map as application/json.
pub enum Data {
    Text(String),
    Bytes(Vec<u8>),
    Json(String),
}

impl Data {
    fn content_type(&self) -> &'static str {
        match self {
            Data::Text(_) => "text/plain; charset=utf-8",
            Data::Bytes(_) => "application/octet-stream",
            Data::Json(_) => "application/json",
        }
    }
    fn bytes(&self) -> Vec<u8> {
        match self {
            Data::Text(t) => t.as_bytes().to_vec(),
            Data::Bytes(b) => b.clone(),
            Data::Json(j) => j.as_bytes().to_vec(),
        }
    }
}

/// Percent-encode a query key or value (RFC 3986 unreserved stays).
pub fn percent_encode(s: &str) -> String {
    let mut out = String::new();
    for b in s.as_bytes() {
        let c = *b as char;
        if c.is_ascii_alphanumeric() || matches!(c, '-' | '.' | '_' | '~') {
            out.push(c);
        } else {
            out.push_str(&format!("%{:02X}", b));
        }
    }
    out
}

/// The full request (S60/S61): redirects for GET only, 3 attempts for
/// GET failures before any byte was sent (waits 1, 2, 4 s), a 30-second
/// whole-request deadline.
pub fn request(req: &Request) -> Result<Response, NetFail> {
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut current = req.address.clone();
    let mut redirects = 0u8;
    let mut attempts = 0u8;
    let mut response = loop {
        let sent = std::cell::Cell::new(false);
        let result = request_once(req, &current, deadline, &sent);
        match result {
            Ok(resp) => break resp,
            Err(e) => {
                // S61: 3 attempts for GET and for failures before any
                // byte was sent, with waits of 1, 2 and 4 seconds.
                let retryable = req.method == Method::Get && !sent.get();
                attempts += 1;
                if retryable && attempts < 3 {
                    let wait = match attempts {
                        1 => 1,
                        2 => 2,
                        _ => 4,
                    };
                    std::thread::sleep(Duration::from_secs(wait));
                    if Instant::now() >= deadline {
                        return Err(NetFail {
                            kind: "timed out",
                            message: "the request timed out".to_string(),
                        });
                    }
                    continue;
                }
                return Err(e);
            }
        }
    };
    // S61: up to 5 redirects followed for GET.
    while req.method == Method::Get
        && matches!(response.status, 301 | 302 | 303 | 307 | 308)
        && redirects < 5
    {
        let Some(loc) = response
            .headers
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case("location"))
            .map(|(_, v)| v.clone())
        else {
            break;
        };
        current = redirect_address(&current, &loc)?;
        redirects += 1;
        response = request_once(req, &current, deadline, &std::cell::Cell::new(false))?;
    }
    Ok(response)
}

/// A redirect Location: absolute-URL (scheme://host[:port]/path) or
/// relative (a path on the same host).
fn redirect_address(base: &Address, loc: &str) -> Result<Address, NetFail> {
    if let Some(rest) = loc.strip_prefix("https://") {
        return absolute_address(true, rest);
    }
    if let Some(rest) = loc.strip_prefix("http://") {
        return absolute_address(false, rest);
    }
    let mut a = base.clone();
    if let Some(stripped) = loc.strip_prefix('/') {
        a.path = percent_decode_path(stripped);
    } else {
        // relative to the current path's folder
        let base_dir = a.path.rsplit_once('/').map(|(d, _)| d).unwrap_or("");
        a.path = format!("{}/{}", base_dir, loc);
        a.path = percent_decode_path(a.path.trim_start_matches('/'));
    }
    Ok(a)
}

/// host[:port][/path] after the scheme.
fn absolute_address(secure: bool, rest: &str) -> Result<Address, NetFail> {
    let (hostport, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i + 1..]),
        None => (rest, ""),
    };
    let (host, port) = split_host_port(hostport, secure)?;
    Ok(Address {
        secure,
        host,
        port,
        path: percent_decode_path(path),
    })
}

/// Percent-decode a URL path (the response Location is encoded; our
/// paths are plain words).
fn percent_decode_path(p: &str) -> String {
    let bytes = p.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    // Byte-level hex check: slicing the &str at i+1..i+3 panics when the
    // bytes fall inside a multi-byte character (a malformed request path
    // could do exactly that - the M4 fuzz found it).
    let hex = |b: u8| -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            b'A'..=b'F' => Some(b - b'A' + 10),
            _ => None,
        }
    };
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let (Some(h), Some(l)) = (hex(bytes[i + 1]), hex(bytes[i + 2])) {
                out.push(h * 16 + l);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).to_string()
}

fn split_host_port(hostport: &str, secure: bool) -> Result<(String, u16), NetFail> {
    if let Some(rest) = hostport.rsplit_once(':') {
        if let Ok(p) = rest.1.parse::<u16>() {
            return Ok((rest.0.to_string(), p));
        }
    }
    Ok((hostport.to_string(), if secure { 443 } else { 80 }))
}

/// One wire round: connect (DNS first, so the failure kinds differ),
/// TLS when the scheme is secure, write the HTTP/1.1 request, read the
/// response. `sent` is set once bytes hit the socket (the retry rule).
fn request_once(
    req: &Request,
    addr: &Address,
    deadline: Instant,
    sent: &std::cell::Cell<bool>,
) -> Result<Response, NetFail> {
    let port = addr.port;
    // S61: DNS failure is not found; a refused connection is other.
    let addrs: Vec<_> = (addr.host.as_str(), port)
        .to_socket_addrs()
        .map_err(|_| NetFail {
            kind: "not found",
            message: format!("no address for {}", addr.host),
        })?
        .collect();
    let mut remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        return Err(NetFail {
            kind: "timed out",
            message: "the request timed out".to_string(),
        });
    }
    let mut stream: Result<TcpStream, NetFail> = Err(NetFail::other("no connection"));
    for a in &addrs {
        remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(NetFail {
                kind: "timed out",
                message: "the request timed out".to_string(),
            });
        }
        match TcpStream::connect_timeout(a, remaining.min(Duration::from_secs(5))) {
            Ok(s) => {
                stream = Ok(s);
                break;
            }
            Err(_) => continue,
        }
    }
    let mut tcp = stream?;
    tcp.set_read_timeout(Some(Duration::from_millis(
        deadline
            .saturating_duration_since(Instant::now())
            .as_millis()
            .max(1) as u64,
    )))
    .ok();
    tcp.set_write_timeout(Some(Duration::from_secs(5))).ok();
    sent.set(true);
    // The query parameters (with query NAME x) join the path.
    let mut path = addr.path.clone();
    if !req.query.is_empty() {
        let qs = req
            .query
            .iter()
            .map(|(k, v)| format!("{}={}", percent_encode(k), percent_encode(v)))
            .collect::<Vec<_>>()
            .join("&");
        let sep = if path.contains('?') { "&" } else { "?" };
        path = format!("{}{}{}", path, sep, qs);
    }
    let mut head = format!(
        "{} {} HTTP/1.1\r\nHost: {}\r\nUser-Agent: lykaon/0.1\r\nAccept: */*\r\n",
        req.method.wire(),
        path,
        host_header(addr),
    );
    // the body headers belong before the head's terminating blank line
    if let Some(d) = &req.data {
        let body = d.bytes();
        head.push_str(&format!("Content-Type: {}\r\n", d.content_type()));
        head.push_str(&format!("Content-Length: {}\r\n", body.len()));
    }
    for (k, v) in &req.headers {
        head.push_str(&format!("{}: {}\r\n", k, v));
    }
    head.push_str("Connection: close\r\n\r\n");
    let mut wire = head.into_bytes();
    if let Some(d) = &req.data {
        wire.extend_from_slice(&d.bytes());
    }
    let mut write_all = |buf: &[u8]| -> Result<(), NetFail> {
        let mut pos = 0;
        while pos < buf.len() {
            let n = write_stream(&mut tcp, &buf[pos..])?;
            pos += n;
        }
        Ok(())
    };
    if addr.secure {
        #[cfg(feature = "tls")]
        {
            let mut tls = tls_client(addr, req.skip_tls)?;
            write_all(&wire)?;
            return read_response(|buf| read_stream_tls(&mut tls, buf), deadline);
        }
        #[cfg(not(feature = "tls"))]
        {
            // the native runtime builds without TLS (logged); a secure
            // fetch there fails like any other network failure
            return Err(NetFail {
                kind: "other",
                message: "TLS is not built in this cut.".to_string(),
            });
        }
    }
    write_all(&wire)?;
    read_response(|buf| read_stream_plain(&mut tcp, buf), deadline)
}

fn write_stream(tcp: &mut TcpStream, buf: &[u8]) -> Result<usize, NetFail> {
    tcp.write(buf).map_err(|_| NetFail {
        kind: "other",
        message: "the connection failed".to_string(),
    })
}

fn read_stream_plain(tcp: &mut TcpStream, buf: &mut [u8]) -> Result<usize, NetFail> {
    match tcp.read(buf) {
        Ok(n) => Ok(n),
        Err(e) => {
            if e.kind() == std::io::ErrorKind::WouldBlock
                || e.kind() == std::io::ErrorKind::TimedOut
            {
                Err(NetFail {
                    kind: "timed out",
                    message: "the request timed out".to_string(),
                })
            } else {
                Err(NetFail {
                    kind: "other",
                    message: "the connection failed".to_string(),
                })
            }
        }
    }
}

#[cfg(feature = "tls")]
fn read_stream_tls(tls: &mut TlsStream, buf: &mut [u8]) -> Result<usize, NetFail> {
    match std::io::Read::read(tls, buf) {
        Ok(n) => Ok(n),
        Err(e) => {
            if e.kind() == std::io::ErrorKind::WouldBlock
                || e.kind() == std::io::ErrorKind::TimedOut
            {
                Err(NetFail {
                    kind: "timed out",
                    message: "the request timed out".to_string(),
                })
            } else {
                Err(NetFail {
                    kind: "other",
                    message: "the connection failed".to_string(),
                })
            }
        }
    }
}

fn host_header(addr: &Address) -> String {
    let default = (addr.secure && addr.port == 443) || (!addr.secure && addr.port == 80);
    if default {
        addr.host.clone()
    } else {
        format!("{}:{}", addr.host, addr.port)
    }
}

/// The rustls TLS client: the bundled root store with certificate
/// checking (S61), or the no-verification config (S62, only reachable
/// inside Be careful).
#[cfg(feature = "tls")]
pub struct TlsStream {
    conn: rustls::StreamOwned<rustls::ClientConnection, TcpStream>,
}

#[cfg(feature = "tls")]
fn tls_client(addr: &Address, skip_tls: bool) -> Result<TlsStream, NetFail> {
    let roots = rustls::RootCertStore {
        roots: webpki_roots::TLS_SERVER_ROOTS.to_vec(),
    };
    let builder = rustls::ClientConfig::builder();
    let config = if skip_tls {
        builder
            .dangerous()
            .with_custom_certificate_verifier(std::sync::Arc::new(NoVerify))
            .with_no_client_auth()
    } else {
        builder.with_root_certificates(roots).with_no_client_auth()
    };
    let config = std::sync::Arc::new(config);
    let name = rustls::pki_types::ServerName::try_from(addr.host.clone()).map_err(|_| NetFail {
        kind: "not found",
        message: format!("no address for {}", addr.host),
    })?;
    let conn = rustls::ClientConnection::new(config, name)
        .map_err(|e| NetFail::other(format!("tls: {e}")))?;
    let tcp = TcpStream::connect((addr.host.as_str(), addr.port)).map_err(|_| NetFail {
        kind: "other",
        message: "the connection was refused".to_string(),
    })?;
    Ok(TlsStream {
        conn: rustls::StreamOwned::new(conn, tcp),
    })
}

/// S62: the no-verification verifier (only reachable inside Be careful).
#[derive(Debug)]
#[cfg(feature = "tls")]
struct NoVerify;

#[cfg(feature = "tls")]
impl rustls::client::danger::ServerCertVerifier for NoVerify {
    fn verify_server_cert(
        &self,
        _end_entity: &rustls::pki_types::CertificateDer<'_>,
        _intermediates: &[rustls::pki_types::CertificateDer<'_>],
        _server_name: &rustls::pki_types::ServerName<'_>,
        _ocsp_response: &[u8],
        _now: rustls::pki_types::UnixTime,
    ) -> Result<rustls::client::danger::ServerCertVerified, rustls::Error> {
        Ok(rustls::client::danger::ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        _message: &[u8],
        _cert: &rustls::pki_types::CertificateDer<'_>,
        _dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
    }

    fn verify_tls13_signature(
        &self,
        _message: &[u8],
        _cert: &rustls::pki_types::CertificateDer<'_>,
        _dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
    }

    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        vec![
            rustls::SignatureScheme::RSA_PKCS1_SHA256,
            rustls::SignatureScheme::ECDSA_NISTP256_SHA256,
            rustls::SignatureScheme::ED25519,
            rustls::SignatureScheme::RSA_PSS_SHA256,
        ]
    }
}

#[cfg(feature = "tls")]
impl Write for TlsStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.conn.write(buf)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.conn.flush()
    }
}

#[cfg(feature = "tls")]
impl Read for TlsStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.conn.read(buf)
    }
}

/// Read one HTTP/1.1 response: the status line, the headers, then the
/// body (Content-Length, or chunked, or everything until close).
fn read_response(
    mut read: impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
    deadline: Instant,
) -> Result<Response, NetFail> {
    let mut buf: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 8192];
    // headers: read until \r\n\r\n
    let header_end = loop {
        if let Some(i) = find_header_end(&buf) {
            break i;
        }
        if Instant::now() >= deadline {
            return Err(NetFail {
                kind: "timed out",
                message: "the request timed out".to_string(),
            });
        }
        let n = read(&mut chunk)?;
        if n == 0 {
            // closed before a full header block: bad format
            return Err(NetFail {
                kind: "bad format",
                message: "the response is not a valid HTTP message".to_string(),
            });
        }
        buf.extend_from_slice(&chunk[..n]);
        if buf.len() > 64 * 1024 {
            return Err(NetFail {
                kind: "bad format",
                message: "the response headers are too large".to_string(),
            });
        }
    };
    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = head.split("\r\n");
    let status_line = lines.next().unwrap_or("");
    let status = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse::<u16>().ok())
        .ok_or_else(|| NetFail {
            kind: "bad format",
            message: "the response is not a valid HTTP message".to_string(),
        })?;
    let mut headers: Vec<(String, String)> = Vec::new();
    for line in lines {
        if line.is_empty() {
            continue;
        }
        if let Some((k, v)) = line.split_once(':') {
            headers.push((k.trim().to_ascii_lowercase(), v.trim().to_string()));
        }
    }
    let mut body = buf[header_end + 4..].to_vec();
    let chunked = headers
        .iter()
        .any(|(k, v)| k == "transfer-encoding" && v.to_ascii_lowercase().contains("chunked"));
    let content_length = headers
        .iter()
        .find(|(k, _)| k == "content-length")
        .and_then(|(_, v)| v.parse::<usize>().ok());
    if chunked {
        read_chunked(&mut read, &mut body, deadline)?;
    } else if let Some(len) = content_length {
        read_to_len(&mut read, &mut body, len, deadline)?;
    } else {
        // read until close
        loop {
            if Instant::now() >= deadline {
                return Err(NetFail {
                    kind: "timed out",
                    message: "the request timed out".to_string(),
                });
            }
            let n = read(&mut chunk)?;
            if n == 0 {
                break;
            }
            body.extend_from_slice(&chunk[..n]);
        }
    }
    Ok(Response {
        status,
        headers,
        body,
    })
}

fn find_header_end(buf: &[u8]) -> Option<usize> {
    buf.windows(4).position(|w| w == b"\r\n\r\n")
}

fn read_to_len(
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
    body: &mut Vec<u8>,
    len: usize,
    deadline: Instant,
) -> Result<(), NetFail> {
    let mut chunk = [0u8; 8192];
    while body.len() < len {
        if Instant::now() >= deadline {
            return Err(NetFail {
                kind: "timed out",
                message: "the request timed out".to_string(),
            });
        }
        let n = read(&mut chunk)?;
        if n == 0 {
            break; // a short body is bad format only if it matters; keep
        }
        body.extend_from_slice(&chunk[..n]);
    }
    body.truncate(len);
    Ok(())
}

fn read_chunked(
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
    body: &mut Vec<u8>,
    deadline: Instant,
) -> Result<(), NetFail> {
    // parse chunk sizes from the byte stream; the simplest honest reader:
    // buffer everything, then decode
    let mut chunk = [0u8; 8192];
    loop {
        if Instant::now() >= deadline {
            return Err(NetFail {
                kind: "timed out",
                message: "the request timed out".to_string(),
            });
        }
        let n = read(&mut chunk)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..n]);
    }
    let raw = std::mem::take(body);
    let mut rest = &raw[..];
    loop {
        let line_end = rest
            .windows(2)
            .position(|w| w == b"\r\n")
            .ok_or_else(|| NetFail {
                kind: "bad format",
                message: "the response is not a valid HTTP message".to_string(),
            })?;
        let size_line = String::from_utf8_lossy(&rest[..line_end]);
        let size_str = size_line.split(';').next().unwrap_or("").trim();
        let size = usize::from_str_radix(size_str, 16).map_err(|_| NetFail {
            kind: "bad format",
            message: "the response is not a valid HTTP message".to_string(),
        })?;
        rest = &rest[line_end + 2..];
        if size == 0 {
            break;
        }
        if rest.len() < size + 2 {
            return Err(NetFail {
                kind: "bad format",
                message: "the response is not a valid HTTP message".to_string(),
            });
        }
        body.extend_from_slice(&rest[..size]);
        rest = &rest[size + 2..];
    }
    Ok(())
}

// ---- server side (S64-S74): one HTTP/1.1 server ---------------------------

/// The server reads one request head from a stream (bounded), then the
/// body. The handler answers with a response.
pub struct ServerRequest {
    pub method: String,
    /// The path's segments, percent-decoded, without the leading "/".
    pub segments: Vec<String>,
    pub query: Vec<(String, String)>,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

#[derive(Clone)]
pub struct ServerResponse {
    pub status: u16,
    pub content_type: String,
    pub body: Vec<u8>,
    /// Extra headers written verbatim (the session Set-Cookie).
    pub extra_headers: Vec<(String, String)>,
}

/// Read one request from a stream; None when the connection closed
/// cleanly before a request (the client went away).
pub fn read_server_request(
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
) -> Result<Option<ServerRequest>, NetFail> {
    let mut buf: Vec<u8> = Vec::new();
    read_server_request_buffered(&mut buf, read)
}

/// Read one request while carrying the bytes after it in `buf` (HTTP/1.1
/// keep-alive: the next request may already be in the socket). Consumed
/// bytes are removed from `buf`, leftovers stay for the next call.
pub fn read_server_request_buffered(
    buf: &mut Vec<u8>,
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
) -> Result<Option<ServerRequest>, NetFail> {
    let mut chunk = [0u8; 8192];
    let header_end = loop {
        if let Some(i) = find_header_end(buf) {
            break i;
        }
        let n = read(&mut chunk)?;
        if n == 0 {
            return Ok(None);
        }
        buf.extend_from_slice(&chunk[..n]);
        // S70: 64 KiB of headers by default; larger gets status 431
        if buf.len() > 64 * 1024 {
            return Err(NetFail {
                kind: "other",
                message: "431".to_string(),
            });
        }
    };
    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = head.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_ascii_uppercase();
    let target = parts.next().unwrap_or("/").to_string();
    let mut headers: Vec<(String, String)> = Vec::new();
    for line in lines {
        if line.is_empty() {
            continue;
        }
        if let Some((k, v)) = line.split_once(':') {
            headers.push((k.trim().to_ascii_lowercase(), v.trim().to_string()));
        }
    }
    let mut body = buf[header_end + 4..].to_vec();
    // S70: 10 MiB of body by default; larger gets status 413
    let content_length = headers
        .iter()
        .find(|(k, _)| k == "content-length")
        .and_then(|(_, v)| v.parse::<usize>().ok())
        .unwrap_or(0);
    if content_length > 10 * 1024 * 1024 {
        return Err(NetFail {
            kind: "other",
            message: "413".to_string(),
        });
    }
    while body.len() < content_length {
        let n = read(&mut chunk)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..n]);
    }
    body.truncate(content_length);
    // drop exactly this request's bytes, keep anything after them
    let used = (header_end + 4 + content_length).min(buf.len());
    buf.drain(..used);
    // the target: path?query
    let (path, query) = match target.split_once('?') {
        Some((p, q)) => (p, parse_query(q)),
        None => (target.as_str(), Vec::new()),
    };
    let segments: Vec<String> = path
        .trim_start_matches('/')
        .split('/')
        .filter(|s| !s.is_empty())
        .map(|s| percent_decode_path(s))
        .collect();
    Ok(Some(ServerRequest {
        method,
        segments,
        query,
        headers,
        body,
    }))
}

/// Parse a query string into key/value pairs (both percent-decoded).
fn parse_query(q: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for pair in q.split('&') {
        if pair.is_empty() {
            continue;
        }
        let (k, v) = match pair.split_once('=') {
            Some((k, v)) => (k, v),
            None => (pair, ""),
        };
        out.push((url_decode(k), url_decode(v)));
    }
    out
}

pub fn url_decode(s: &str) -> String {
    percent_decode_path(s).replace('+', " ")
}

/// Write one HTTP/1.1 response, closing the connection (the pre-K cut).
pub fn write_server_response(
    write: &mut impl FnMut(&[u8]) -> Result<(), NetFail>,
    resp: &ServerResponse,
) -> Result<(), NetFail> {
    write_server_response_keep(write, resp, false)
}

/// Write one HTTP/1.1 response; `keep_alive` writes Connection: keep-alive
/// (M4-S74: keep-alive is the default), otherwise Connection: close.
pub fn write_server_response_keep(
    write: &mut impl FnMut(&[u8]) -> Result<(), NetFail>,
    resp: &ServerResponse,
    keep_alive: bool,
) -> Result<(), NetFail> {
    let mut head = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: {}\r\n",
        resp.status,
        status_text(resp.status),
        resp.content_type,
        resp.body.len(),
        if keep_alive { "keep-alive" } else { "close" },
    );
    for (k, v) in &resp.extra_headers {
        head.push_str(&format!("{}: {}\r\n", k, v));
    }
    head.push_str("\r\n");
    write(head.as_bytes())?;
    if !resp.body.is_empty() {
        write(&resp.body)?;
    }
    Ok(())
}

fn status_text(status: u16) -> &'static str {
    match status {
        200 => "OK",
        201 => "Created",
        204 => "No Content",
        301 => "Moved Permanently",
        302 => "Found",
        400 => "Bad Request",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        413 => "Payload Too Large",
        431 => "Request Header Fields Too Large",
        500 => "Internal Server Error",
        _ => "OK",
    }
}

// ---- the server's connection: plain TCP or TLS (S64) -----------------------

pub enum ServerConn {
    Plain(TcpStream),
    #[cfg(feature = "tls")]
    Tls(std::rc::Rc<std::cell::RefCell<rustls::StreamOwned<rustls::ServerConnection, TcpStream>>>),
}

impl ServerConn {
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize, NetFail> {
        match self {
            ServerConn::Plain(tcp) => tcp.read(buf).map_err(|e| io_fail(&e)),
            #[cfg(feature = "tls")]
            ServerConn::Tls(rc) => {
                let mut s = rc.borrow_mut();
                std::io::Read::read(&mut *s, buf).map_err(|e| io_fail(&e))
            }
        }
    }

    pub fn write(&mut self, buf: &[u8]) -> Result<(), NetFail> {
        match self {
            ServerConn::Plain(tcp) => tcp.write_all(buf).map_err(|e| io_fail(&e)),
            #[cfg(feature = "tls")]
            ServerConn::Tls(rc) => {
                let mut s = rc.borrow_mut();
                std::io::Write::write_all(&mut *s, buf).map_err(|e| io_fail(&e))
            }
        }
    }

    pub fn flush(&mut self) -> Result<(), NetFail> {
        match self {
            ServerConn::Plain(tcp) => tcp.flush().map_err(|e| io_fail(&e)),
            #[cfg(feature = "tls")]
            ServerConn::Tls(rc) => {
                let mut s = rc.borrow_mut();
                std::io::Write::flush(&mut *s).map_err(|e| io_fail(&e))
            }
        }
    }

    pub fn set_timeouts(&mut self, read: Option<Duration>) {
        match self {
            ServerConn::Plain(tcp) => {
                tcp.set_read_timeout(read).ok();
                tcp.set_write_timeout(Some(Duration::from_secs(10))).ok();
            }
            #[cfg(feature = "tls")]
            ServerConn::Tls(rc) => {
                let mut s = rc.borrow_mut();
                let tcp = s.get_ref();
                tcp.set_read_timeout(read).ok();
                tcp.set_write_timeout(Some(Duration::from_secs(10))).ok();
            }
        }
    }

    /// M4-S73/D13 (route A): the parked live sessions read and write
    /// without blocking, so the accept loop can poll them all.
    pub fn set_nonblocking(&mut self, on: bool) {
        match self {
            ServerConn::Plain(tcp) => {
                tcp.set_nonblocking(on).ok();
            }
            #[cfg(feature = "tls")]
            ServerConn::Tls(rc) => {
                let mut s = rc.borrow_mut();
                let tcp = s.get_ref();
                tcp.set_nonblocking(on).ok();
            }
        }
    }
}

fn io_fail(e: &std::io::Error) -> NetFail {
    if e.kind() == std::io::ErrorKind::WouldBlock || e.kind() == std::io::ErrorKind::TimedOut {
        NetFail {
            kind: "timed out",
            message: "the connection went idle".to_string(),
        }
    } else {
        NetFail {
            kind: "other",
            message: "the connection failed".to_string(),
        }
    }
}

/// Accept one TLS connection over a TCP stream (the handshake happens
/// lazily on the first read/write; a bad client fails there).
#[cfg(feature = "tls")]
pub fn tls_accept(config: &std::sync::Arc<rustls::ServerConfig>, tcp: TcpStream) -> ServerConn {
    let conn =
        rustls::ServerConnection::new(std::sync::Arc::clone(config)).expect("valid server config");
    ServerConn::Tls(std::rc::Rc::new(std::cell::RefCell::new(
        rustls::StreamOwned::new(conn, tcp),
    )))
}

/// The TLS server config from PEM certificate + key bytes (S64: rustls
/// with the certificate file C and the key file K).
#[cfg(feature = "tls")]
pub fn tls_server_config(
    cert_pem: &[u8],
    key_pem: &[u8],
) -> Result<std::sync::Arc<rustls::ServerConfig>, NetFail> {
    let certs = rustls_pemfile::certs(&mut &cert_pem[..])
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| NetFail {
            kind: "other",
            message: "the certificate file is not valid PEM".to_string(),
        })?;
    if certs.is_empty() {
        return Err(NetFail {
            kind: "other",
            message: "the certificate file holds no certificate".to_string(),
        });
    }
    let key = rustls_pemfile::private_key(&mut &key_pem[..])
        .map_err(|_| NetFail {
            kind: "other",
            message: "the key file is not valid PEM".to_string(),
        })?
        .ok_or_else(|| NetFail {
            kind: "other",
            message: "the key file holds no private key".to_string(),
        })?;
    let config = rustls::ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .map_err(|_| NetFail {
            kind: "other",
            message: "the certificate and the key do not match".to_string(),
        })?;
    Ok(std::sync::Arc::new(config))
}

// ---- WebSocket server side (S73) -------------------------------------------

/// True when a request is a WebSocket upgrade for this server.
pub fn is_ws_upgrade(method: &str, headers: &[(String, String)]) -> bool {
    method == "GET"
        && headers
            .iter()
            .any(|(k, v)| k == "upgrade" && v.to_ascii_lowercase().contains("websocket"))
}

/// The 101 handshake response, from the request's Sec-WebSocket-Key.
pub fn ws_handshake_response(headers: &[(String, String)]) -> Result<String, NetFail> {
    let key = headers
        .iter()
        .find(|(k, _)| k == "sec-websocket-key")
        .map(|(_, v)| v.clone())
        .ok_or_else(|| NetFail {
            kind: "bad format",
            message: "the upgrade request has no key".to_string(),
        })?;
    Ok(format!(
        "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {}\r\n\r\n",
        ws_accept_key(key.trim())
    ))
}

/// The live connection's stream, shared between the server loop and the
/// running body (WsSend writes, WsRecv reads).
pub struct WsStream {
    pub conn: ServerConn,
}

// ---- WebSocket (S73): the upgrade handshake and text frames ---------------

/// The SHA-1 of some bytes (the hand-written hasher's public face;
/// shared with the session-cookie value).
pub fn sha1(data: &[u8]) -> [u8; 20] {
    let mut hasher = Sha1::new();
    hasher.update(data);
    hasher.finalize()
}

/// A WebSocket ACCEPT key: base64 of SHA-1(key + the magic GUID).
pub fn ws_accept_key(client_key: &str) -> String {
    const MAGIC: &str = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
    let mut hasher = Sha1::new();
    hasher.update(client_key.as_bytes());
    hasher.update(MAGIC.as_bytes());
    let digest = hasher.finalize();
    base64_encode(&digest)
}

pub fn base64_encode(data: &[u8]) -> String {
    const TABLE: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::new();
    for chunk in data.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = *chunk.get(1).unwrap_or(&0) as u32;
        let b2 = *chunk.get(2).unwrap_or(&0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(TABLE[(n >> 18) as usize & 63] as char);
        out.push(TABLE[(n >> 12) as usize & 63] as char);
        if chunk.len() > 1 {
            out.push(TABLE[(n >> 6) as usize & 63] as char);
        } else {
            out.push('=');
        }
        if chunk.len() > 2 {
            out.push(TABLE[n as usize & 63] as char);
        } else {
            out.push('=');
        }
    }
    out
}

/// A client WebSocket key: 16 random bytes base64-encoded.
pub fn ws_client_key(random: &[u8; 16]) -> String {
    base64_encode(random)
}

/// Encode one client-to-server text frame (the client MUST mask).
pub fn ws_client_frame(text: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(0x81); // FIN + text
    let len = text.len();
    if len < 126 {
        out.push(0x80 | len as u8); // masked
    } else if len <= 0xFFFF {
        out.push(0x80 | 126);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else {
        out.push(0x80 | 127);
        out.extend_from_slice(&(len as u64).to_be_bytes());
    }
    // a fixed masking key of zeros is legal for this client (the mask
    // only hides proxies); logged as a cut in the deviations file
    let mask = [0u8; 4];
    out.extend_from_slice(&mask);
    for (i, b) in text.iter().enumerate() {
        out.push(b ^ mask[i % 4]);
    }
    out
}

/// Read one frame from the stream: returns (opcode, payload). opcode 1
/// = text, 8 = close. Payloads over 1 MiB are a bad format failure.
pub fn ws_read_frame(
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
) -> Result<Option<(u8, Vec<u8>)>, NetFail> {
    let mut h = [0u8; 2];
    read_exact(read, &mut h)?;
    let opcode = h[0] & 0x0F;
    let masked = h[1] & 0x80 != 0;
    let mut len = (h[1] & 0x7F) as u64;
    if len == 126 {
        let mut e = [0u8; 2];
        read_exact(read, &mut e)?;
        len = u16::from_be_bytes(e) as u64;
    } else if len == 127 {
        let mut e = [0u8; 8];
        read_exact(read, &mut e)?;
        len = u64::from_be_bytes(e);
    }
    if len > 1024 * 1024 {
        return Err(NetFail {
            kind: "bad format",
            message: "the frame is too large".to_string(),
        });
    }
    let mask = if masked {
        let mut m = [0u8; 4];
        read_exact(read, &mut m)?;
        Some(m)
    } else {
        None
    };
    let mut payload = vec![0u8; len as usize];
    read_exact(read, &mut payload)?;
    if let Some(m) = mask {
        for (i, b) in payload.iter_mut().enumerate() {
            *b ^= m[i % 4];
        }
    }
    if opcode == 8 {
        return Ok(None); // closed
    }
    Ok(Some((opcode, payload)))
}

/// The byte count of the frame whose header sits at the front of `head`
/// (None while the header itself is still incomplete). A length over
/// 1 MiB is a bad-format failure (S73). Public for the live-session
/// poll: a complete frame in a session's pending buffer counts as
/// readable even when the socket answers nothing.
pub fn ws_frame_total(head: &[u8]) -> Result<Option<usize>, NetFail> {
    if head.len() < 2 {
        return Ok(None);
    }
    let short = (head[1] & 0x7F) as u64;
    let mut len = short;
    let mut ext = 0usize;
    if short == 126 {
        if head.len() < 4 {
            return Ok(None);
        }
        len = u16::from_be_bytes([head[2], head[3]]) as u64;
        ext = 2;
    } else if short == 127 {
        if head.len() < 10 {
            return Ok(None);
        }
        let mut e = [0u8; 8];
        e.copy_from_slice(&head[2..10]);
        len = u64::from_be_bytes(e);
        ext = 8;
    }
    if len > 1024 * 1024 {
        return Err(NetFail {
            kind: "bad format",
            message: "the frame is too large".to_string(),
        });
    }
    let masked = head[1] & 0x80 != 0;
    Ok(Some(2 + ext + if masked { 4 } else { 0 } + len as usize))
}

/// Pull the (opcode, payload) of the frame at the front of `data`; the
/// caller has checked the byte count with ws_frame_total first. The
/// bytes are NOT drained here (the caller drains the whole frame).
fn ws_frame_take(data: &[u8]) -> Result<(u8, Vec<u8>), NetFail> {
    let opcode = data[0] & 0x0F;
    let masked = data[1] & 0x80 != 0;
    let mut pos = 2usize;
    let len = match data[1] & 0x7F {
        126 => {
            pos += 2;
            u16::from_be_bytes([data[2], data[3]]) as usize
        }
        127 => {
            pos += 8;
            let mut e = [0u8; 8];
            e.copy_from_slice(&data[2..10]);
            u64::from_be_bytes(e) as usize
        }
        n => n as usize,
    };
    let mask = if masked {
        let m = [data[pos], data[pos + 1], data[pos + 2], data[pos + 3]];
        pos += 4;
        Some(m)
    } else {
        None
    };
    let mut payload = data[pos..pos + len].to_vec();
    if let Some(m) = mask {
        for (i, b) in payload.iter_mut().enumerate() {
            *b ^= m[i % 4];
        }
    }
    Ok((opcode, payload))
}

/// Read one frame through a leftover buffer, without blocking (M4-S73,
/// the parked live sessions): `pending` is consumed first and refilled
/// from `read`. A read that answers nothing yet (kind "timed out")
/// leaves `pending` as it is and answers kind "busy" - the frame is on
/// its way and the caller parks. Ok(None) is a close frame; a closed
/// connection answers kind "closed".
pub fn ws_read_frame_buffered(
    pending: &mut Vec<u8>,
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
) -> Result<Option<(u8, Vec<u8>)>, NetFail> {
    loop {
        if !pending.is_empty() {
            if let Some(total) = ws_frame_total(pending)? {
                if pending.len() >= total {
                    let (opcode, payload) = ws_frame_take(pending)?;
                    pending.drain(..total);
                    if opcode == 8 {
                        return Ok(None); // closed
                    }
                    return Ok(Some((opcode, payload)));
                }
            }
        }
        let mut chunk = [0u8; 4096];
        match read(&mut chunk) {
            Ok(0) => {
                return Err(NetFail {
                    kind: "closed",
                    message: "the connection closed".to_string(),
                });
            }
            Ok(n) => pending.extend_from_slice(&chunk[..n]),
            // a WouldBlock read folds into "timed out" (io_fail); that is
            // the no-data-yet answer of the poll loop
            Err(e) if e.kind == "timed out" => {
                return Err(NetFail {
                    kind: "busy",
                    message: "the frame is not here yet".to_string(),
                });
            }
            Err(e) => return Err(e),
        }
    }
}

/// A server-to-client text frame (unmasked).
pub fn ws_server_frame(text: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(0x81);
    let len = text.len();
    if len < 126 {
        out.push(len as u8);
    } else if len <= 0xFFFF {
        out.push(126);
        out.extend_from_slice(&(len as u16).to_be_bytes());
    } else {
        out.push(127);
        out.extend_from_slice(&(len as u64).to_be_bytes());
    }
    out.extend_from_slice(text);
    out
}

fn read_exact(
    read: &mut impl FnMut(&mut [u8]) -> Result<usize, NetFail>,
    buf: &mut [u8],
) -> Result<(), NetFail> {
    let mut pos = 0;
    while pos < buf.len() {
        let n = read(&mut buf[pos..])?;
        if n == 0 {
            return Err(NetFail {
                kind: "other",
                message: "the connection closed".to_string(),
            });
        }
        pos += n;
    }
    Ok(())
}

// ---- SHA-1 (RFC 3174), hand-written for the WebSocket handshake only ------

struct Sha1 {
    state: [u32; 5],
    buf: [u8; 64],
    buf_len: usize,
    total: u64,
}

impl Sha1 {
    fn new() -> Sha1 {
        Sha1 {
            state: [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0],
            buf: [0; 64],
            buf_len: 0,
            total: 0,
        }
    }

    fn update(&mut self, mut data: &[u8]) {
        self.total += data.len() as u64;
        if self.buf_len > 0 {
            let take = (64 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == 64 {
                let block = self.buf;
                self.compress(&block);
                self.buf_len = 0;
            }
        }
        while data.len() >= 64 {
            let (block, rest) = data.split_at(64);
            let mut b = [0u8; 64];
            b.copy_from_slice(block);
            self.compress(&b);
            data = rest;
        }
        if !data.is_empty() {
            self.buf[..data.len()].copy_from_slice(data);
            self.buf_len = data.len();
        }
    }

    fn finalize(mut self) -> [u8; 20] {
        let bits = self.total * 8;
        self.update(&[0x80]);
        while self.buf_len != 56 {
            self.update(&[0]);
        }
        // the 8 length bytes; update() would count them, so write the
        // block directly
        self.buf[56..60].copy_from_slice(&((bits >> 32) as u32).to_be_bytes());
        self.buf[60..64].copy_from_slice(&(bits as u32).to_be_bytes());
        let block = self.buf;
        self.compress(&block);
        let mut out = [0u8; 20];
        for (i, w) in self.state.iter().enumerate() {
            out[i * 4..i * 4 + 4].copy_from_slice(&w.to_be_bytes());
        }
        out
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[i * 4],
                block[i * 4 + 1],
                block[i * 4 + 2],
                block[i * 4 + 3],
            ]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let (mut a, mut b, mut c, mut d, mut e) = (
            self.state[0],
            self.state[1],
            self.state[2],
            self.state[3],
            self.state[4],
        );
        for (i, &wi) in w.iter().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | ((!b) & d), 0x5A827999u32),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
                _ => (b ^ c ^ d, 0xCA62C1D6),
            };
            let tmp = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(wi);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = tmp;
        }
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
    }
}

// A network failure is the ordinary anonymous failure in this cut (the
// file-sentence posture of M4-5, logged): the kinds above name where the
// failure came from; the run stops with TErr::Signal either way.

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression (M4 fuzz): a percent escape inside a multi-byte character
    /// used to slice the string at a non-char boundary and panic. A
    /// malformed request path reaches this through read_server_request.
    #[test]
    fn percent_decode_never_panics_on_multibyte_text() {
        for p in [
            "%",
            "%a",
            "%zz",
            "%é",
            "a%😀b",
            "😀%4",
            "%41😀",
            "%e9%80%80",
        ] {
            let _ = percent_decode_path(p);
            let _ = url_decode(p);
        }
        assert_eq!(percent_decode_path("%41%42"), "AB");
        assert_eq!(percent_decode_path("a%2Fb"), "a/b");
    }

    /// The same bytes through the HTTP request parser: a bad path is a
    /// request (percent-decoded with replacement characters), never a panic.
    #[test]
    fn server_request_path_with_bad_escapes_does_not_panic() {
        let raw = b"GET /a%zz\xF0\x9F\x98\x80%4 HTTP/1.1\r\nHost: x\r\n\r\n".to_vec();
        let mut cursor = 0usize;
        let mut carry = Vec::new();
        let mut read = |buf: &mut [u8]| -> Result<usize, NetFail> {
            if cursor >= raw.len() {
                return Ok(0);
            }
            let take = buf.len().min(raw.len() - cursor);
            buf[..take].copy_from_slice(&raw[cursor..cursor + take]);
            cursor += take;
            Ok(take)
        };
        let got = read_server_request_buffered(&mut carry, &mut read);
        let req = match got {
            Ok(Some(r)) => r,
            Ok(None) => panic!("the connection should hold a request"),
            Err(e) => panic!("unexpected failure: {}", e.kind),
        };
        assert_eq!(req.method, "GET");
    }
}
