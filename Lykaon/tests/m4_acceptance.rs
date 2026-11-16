//! M4-12: the Appendix K acceptance tests (M4-T30..M4-T32) and their
//! load measurements.
//!
//! Acceptance A (M4-T30): a hello server answers 10,000 requests over 64
//! connections; every answer is status 200 with the body `hello from Lykaon`.
//! Requests per second are measured and reported, never promised.
//!
//! Acceptance B (M4-T31): 1,000 files read by 8 tasks and summed equal the
//! sum read by one task.
//!
//! Acceptance C (M4-T32): 50 live chat clients, every message reaching all
//! others. This one is BLOCKED by the standing eager-task cut (M4-D13's
//! scheduler is not implemented; a live block runs inline and the accept
//! loop serves one connection at a time, so a second live client is never
//! accepted). The test is kept `#[ignore]`d with that exact reason and is
//! logged in LYKAON_DEVIATIONS.md rather than claimed green.
//!
//! Run: cargo test --test m4_acceptance -- --nocapture

use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::{Duration, Instant};

use lykaon::run_source;

/// Spawn a server program on its own thread and wait until the port answers.
fn serve_bg(src: String, port: u16) -> std::thread::JoinHandle<()> {
    let handle = std::thread::spawn(move || {
        let _ = run_source(&src, "m4accept.lykaon", "");
    });
    let deadline = Instant::now() + Duration::from_secs(20);
    while Instant::now() < deadline {
        if TcpStream::connect(("127.0.0.1", port)).is_ok() {
            return handle;
        }
        std::thread::sleep(Duration::from_millis(25));
    }
    panic!("the acceptance server on port {port} never started");
}

fn free_port(start: u16) -> u16 {
    // a quiet fixed range with a probe: the first port nothing holds
    for port in start..start + 500 {
        if std::net::TcpListener::bind(("127.0.0.1", port)).is_err() {
            continue;
        }
        // the probe listener is dropped here, so the server can take it
        return port;
    }
    panic!("no free port near {start}");
}

/// One HTTP/1.1 response read off a keep-alive connection.
struct Resp {
    status: u16,
    body: String,
}

/// Read exactly one response (headers + Content-Length body). The stream is
/// reused for the next request (M4-S74 keep-alive).
fn read_response(stream: &mut TcpStream) -> Resp {
    let mut buf: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        if let Some(i) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break i;
        }
        let n = stream.read(&mut chunk).expect("read response head");
        assert!(n > 0, "the connection closed before a response");
        buf.extend_from_slice(&chunk[..n]);
    };
    let head = String::from_utf8_lossy(&buf[..head_end]).to_string();
    let mut status = 0u16;
    let mut content_length = 0usize;
    for (i, line) in head.split("\r\n").enumerate() {
        if i == 0 {
            status = line
                .split_whitespace()
                .nth(1)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
        } else if let Some((k, v)) = line.split_once(':') {
            if k.eq_ignore_ascii_case("content-length") {
                content_length = v.trim().parse().unwrap_or(0);
            }
        }
    }
    let mut body = buf[head_end + 4..].to_vec();
    while body.len() < content_length {
        let n = stream.read(&mut chunk).expect("read response body");
        assert!(n > 0, "the connection closed inside a response body");
        body.extend_from_slice(&chunk[..n]);
    }
    body.truncate(content_length);
    Resp {
        status,
        body: String::from_utf8_lossy(&body).to_string(),
    }
}

/// Acceptance A: 10,000 requests over 64 connections (M4-T30).
#[test]
fn m4_12_acceptance_a_http_10000_requests_over_64_connections() {
    let port = free_port(24001);
    let program = format!(
        "Serve on port {port}.\n\
         \x20   When someone gets home.\n\
         \x20       Respond with hello from Lykaon.\n"
    );
    // the server runs until the test process ends (the acceptance server
    // never ends by itself - Appendix K)
    let _server = serve_bg(program, port);

    const CONNECTIONS: usize = 64;
    const REQUESTS: usize = 10_000;
    let per = REQUESTS / CONNECTIONS; // 156
    let extra = REQUESTS % CONNECTIONS; // 16 connections do one more

    let started = Instant::now();
    let mut results: Vec<(usize, Result<(), String>)> = Vec::new();
    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for c in 0..CONNECTIONS {
            let n = per + if c < extra { 1 } else { 0 };
            handles.push(scope.spawn(move || {
                let mut stream = TcpStream::connect(("127.0.0.1", port))
                    .map_err(|e| format!("connection {c}: {e}"))?;
                stream.set_read_timeout(Some(Duration::from_secs(120))).ok();
                for r in 0..n {
                    stream
                        .write_all(b"GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n")
                        .map_err(|e| format!("connection {c} request {r}: {e}"))?;
                    let resp = read_response(&mut stream);
                    if resp.status != 200 {
                        return Err(format!(
                            "connection {c} request {r}: status {}",
                            resp.status
                        ));
                    }
                    if resp.body != "hello from Lykaon" {
                        return Err(format!("connection {c} request {r}: body {:?}", resp.body));
                    }
                }
                // the client closes: the server moves to the next connection
                Ok(())
            }));
        }
        for (c, h) in handles.into_iter().enumerate() {
            match h.join() {
                Ok(r) => results.push((c, r)),
                Err(_) => results.push((c, Err("the client thread panicked".to_string()))),
            }
        }
    });
    let elapsed = started.elapsed();
    let mut failures: Vec<String> = Vec::new();
    for (_, r) in results {
        if let Err(e) = r {
            failures.push(e);
        }
    }
    assert!(failures.is_empty(), "acceptance A failures: {failures:#?}");

    let seconds = elapsed.as_secs_f64();
    let rps = REQUESTS as f64 / seconds;
    println!(
        "acceptance A: {REQUESTS} requests over {CONNECTIONS} connections in {seconds:.3} s = {rps:.0} requests/second"
    );
    // the measurement is reported, never promised (Appendix K)
    assert!(rps > 0.0);
}

/// Acceptance B: 1,000 files read by 8 tasks, summed (M4-T31).
#[test]
fn m4_12_acceptance_b_1000_files_read_by_8_tasks() {
    // a name the language can spell (plain letters and digits only)
    let folder_name = format!("lykaonacceptb{}", std::process::id());
    let folder = std::env::temp_dir().join(&folder_name);
    let _ = std::fs::remove_dir_all(&folder);
    std::fs::create_dir_all(&folder).unwrap();
    const FILES: usize = 1000;
    for i in 1..=FILES {
        std::fs::write(folder.join(format!("f{i}")), "1\n").unwrap();
    }
    // a read plus one count per file, with the word-form reference the
    // language can spell (M4-G31/G33): file fN in folder NAME in temporary folder
    let read = |i: usize| {
        format!(
            "    Read file f{i} in folder {folder_name} in temporary folder.\n    Add 1 to Hits.\n"
        )
    };

    // one task reads all 1,000 files
    let mut one_task = String::from("Hits is counter.\nStart task onlyreader.\n");
    for i in 1..=FILES {
        one_task.push_str(&read(i));
    }
    one_task.push_str("Wait for onlyreader.\nSay Hits.\n");
    let (out_one, code_one) = run_source(&one_task, "one.lykaon", "");
    assert_eq!(code_one, 0, "{out_one}");
    assert_eq!(out_one.trim(), "1000", "{out_one}");

    // eight tasks read 125 files each
    let mut eight = String::from("Hits is counter.\n");
    for t in 0..8 {
        eight.push_str(&format!("Start task reader{t}.\n"));
        for k in 0..125 {
            eight.push_str(&read(t * 125 + k + 1));
        }
    }
    for t in 0..8 {
        eight.push_str(&format!("Wait for reader{t}.\n"));
    }
    eight.push_str("Say Hits.\n");
    let (out_eight, code_eight) = run_source(&eight, "eight.lykaon", "");
    assert_eq!(code_eight, 0, "{out_eight}");
    assert_eq!(out_eight.trim(), "1000", "{out_eight}");

    assert_eq!(
        out_one.trim(),
        out_eight.trim(),
        "the 8-task sum must equal the one-task sum"
    );
    println!("acceptance B: 1 task sum = 8 task sum = {}", out_one.trim());
    let _ = std::fs::remove_dir_all(&folder);
}

/// Acceptance C: 50 live chat clients, every message reaching all others
/// exactly once (M4-T32). The chat program stores each upgraded
/// connection in a shared top-level list (a connection value, M4-S73/D13)
/// and forwards every received frame to every stored connection; the
/// parked live sessions run on the server's accept loop, so all 50
/// connections are live at the same time (a client's block parks at
/// Receive and never blocks the loop). The test also drops one client
/// and proves the server keeps serving the others.
#[test]
fn m4_12_acceptance_c_chat_50_live_clients() {
    // The shape the acceptance requires, written against the language as
    // specified (M4-S73): a live page whose block sends each received
    // message to every other live connection.
    let port = free_port(24501);
    let program = format!(
        "Page chat page is chat.\n\
         Changeable connections is list of nothing.\n\
         Serve on port {port}.\n\
         \x20   When someone opens live chat page.\n\
         \x20       Add connection to connections.\n\
         \x20       Repeat forever.\n\
         \x20           Receive from connection.\n\
         \x20           If it is not missing.\n\
         \x20               message is it.\n\
         \x20               For each other in connections.\n\
         \x20                   Send message to other.\n"
    );
    let _server = serve_bg(program, port);

    const CLIENTS: usize = 50;
    const MESSAGES: usize = 5;
    // all 50 clients connect and finish the upgrade first, so every
    // connection is in the program's list before the first message
    let mut streams: Vec<TcpStream> = Vec::new();
    for _ in 0..CLIENTS {
        streams.push(ws_connect(port));
    }
    // the upgrade response reaches the client before the session's first
    // pass has run; give every session its registering round
    std::thread::sleep(Duration::from_millis(500));
    // every client sends M tagged messages: c<i>-<seq>
    for i in 0..CLIENTS {
        let s = &mut streams[i];
        for k in 0..MESSAGES {
            let text = format!("c{i}-{k}");
            let payload = text.as_bytes();
            let mut f = vec![0x81u8, 0x80 | payload.len() as u8, 0, 0, 0, 0];
            f.extend_from_slice(payload);
            s.write_all(&f).expect("the client can write its message");
        }
    }
    // every client must receive every one of the 50*MESSAGES tagged
    // messages exactly once (its own broadcasts included: the chat
    // program forwards to every stored connection)
    let expected: Vec<String> = (0..CLIENTS)
        .flat_map(|i| (0..MESSAGES).map(move |k| format!("c{i}-{k}")))
        .collect();
    let deadline = Instant::now() + Duration::from_secs(120);
    let mut received: Vec<Vec<String>> = vec![Vec::new(); CLIENTS];
    let mut pendings: Vec<Vec<u8>> = vec![Vec::new(); CLIENTS];
    let mut done = vec![false; CLIENTS];
    while Instant::now() < deadline && done.iter().any(|d| !d) {
        for i in 0..CLIENTS {
            if done[i] {
                continue;
            }
            read_ws_frames(&mut streams[i], &mut pendings[i], &mut received[i]);
            if received[i].len() >= expected.len() {
                done[i] = true;
            }
        }
    }
    let mut failures: Vec<String> = Vec::new();
    for i in 0..CLIENTS {
        if !done[i] {
            failures.push(format!(
                "client {i}: got {} of {} messages",
                received[i].len(),
                expected.len()
            ));
            continue;
        }
        // the full multiset, each exactly once
        let mut want: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for m in &expected {
            *want.entry(m.clone()).or_insert(0) += 1;
        }
        for m in &received[i] {
            match want.get_mut(m) {
                Some(n) if *n > 0 => *n -= 1,
                _ => failures.push(format!("client {i}: unexpected {m:?}")),
            }
        }
        for (m, n) in &want {
            if *n > 0 {
                failures.push(format!("client {i}: {m} missing ({n}x)"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "acceptance C chat failures (first 10 of {}): {:#?}",
        failures.len(),
        failures.iter().take(10).collect::<Vec<_>>()
    );
    println!(
        "acceptance C: {CLIENTS} live clients, {MESSAGES} messages each, every client received all {} messages exactly once",
        expected.len()
    );

    // one client drops: the server keeps serving the others (the
    // dropped session's Receive gives missing on close, the session
    // ends, and the broadcast skips the dead connection)
    drop(streams.remove(0));
    drop(pendings.remove(0));
    std::thread::sleep(Duration::from_millis(800));
    let mut probe = ws_connect(port);
    let text = "after the drop";
    let payload = text.as_bytes();
    let mut f = vec![0x81u8, 0x80 | payload.len() as u8, 0, 0, 0, 0];
    f.extend_from_slice(payload);
    probe.write_all(&f).unwrap();
    // the probe hears its own message back: the server is still live
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut got = false;
    let mut pending: Vec<u8> = Vec::new();
    let mut frames: Vec<String> = Vec::new();
    while Instant::now() < deadline && !got {
        read_ws_frames(&mut probe, &mut pending, &mut frames);
        got = frames.iter().any(|t| t == text);
        std::thread::sleep(Duration::from_millis(25));
    }
    assert!(got, "the server did not answer after one client dropped");
    let _ = &streams;
    let _ = &pendings;
}

/// One WebSocket client connection: the upgrade request and the 101.
fn ws_connect(port: u16) -> TcpStream {
    let mut s = TcpStream::connect(("127.0.0.1", port)).expect("connect");
    s.set_read_timeout(Some(Duration::from_millis(200))).ok();
    s.write_all(
        b"GET /chat HTTP/1.1\r\nHost: 127.0.0.1\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n",
    )
    .unwrap();
    let mut buf = Vec::new();
    let mut chunk = [0u8; 1];
    while !buf.ends_with(b"\r\n\r\n") {
        let n = s.read(&mut chunk).expect("the upgrade response");
        assert!(n > 0, "the connection closed during the upgrade");
        buf.push(chunk[0]);
    }
    let head = String::from_utf8_lossy(&buf).to_string();
    assert!(head.starts_with("HTTP/1.1 101"), "{head}");
    s
}

/// Read every complete text frame off the socket into `out`; the short
/// read timeout keeps the poll loop going without blocking the test.
fn read_ws_frames(s: &mut TcpStream, pending: &mut Vec<u8>, out: &mut Vec<String>) {
    let mut chunk = [0u8; 8192];
    if let Ok(n) = s.read(&mut chunk) {
        if n > 0 {
            pending.extend_from_slice(&chunk[..n]);
        }
    }
    loop {
        // one server frame: FIN + text, short (the messages are words)
        if pending.len() < 2 {
            return;
        }
        if pending[0] & 0x0F == 8 {
            return; // the server closed
        }
        assert_eq!(pending[0] & 0x80, 0x80, "expected a finished frame");
        assert_eq!(pending[1] & 0x80, 0, "server frames are not masked");
        let len = (pending[1] & 0x7F) as usize;
        if pending.len() < 2 + len {
            return;
        }
        let text = String::from_utf8_lossy(&pending[2..2 + len]).to_string();
        out.push(text);
        pending.drain(..2 + len);
    }
}
