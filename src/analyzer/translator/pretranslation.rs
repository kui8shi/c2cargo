pub(super) fn get_function_definition_check_header() -> &'static str {
    r#"
fn check_header(header: &str, prelude: &str, cppflags: &Vec<String>) -> bool {
    let test_prog = format!(
        "{}\n#include <{}>\nint main() {{ return 0; }}",
        prelude, header
    );

    let mut cmd = std::process::Command::new("cc");
    cmd.args(&["-E", "-x", "c", "-"]);
    for flag in cppflags {
        cmd.arg(flag);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    let mut child = cmd.spawn().expect("failed to spawn cc for header check");
    {
        let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
        stdin
            .write_all(test_prog.as_bytes())
            .expect("failed to write to cc stdin");
    }
    let status = child.wait().expect("failed to wait on cc header check");
    status.success()
}"#
}

pub(super) fn get_function_definition_check_library() -> &'static str {
    r#"
fn check_library(
    function_name: &str,
    search_libs: &[&str],
    other_libs: &[&str],
    ldflags: &Vec<String>,
    try_std: bool,
) -> Result<Option<String>, ()> {
    let test_prog = format!(
        "char {0} (void); int main (void) {{ return {0} (); }}",
        function_name
    );

    let try_link = |libs: &[&str]| -> bool {
        let mut cmd = std::process::Command::new("cc");
        cmd.args(&["-x", "c", "-", "-o", "/dev/null"]);
        for lib in libs {
            cmd.arg(format!("-l{}", lib));
        }
        for lib in other_libs {
            cmd.arg(lib);
        }
        for flag in ldflags {
            cmd.arg(flag);
        }
        cmd.stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        let mut child = cmd.spawn().expect("failed to spawn cc for link test");
        {
            let mut stdin = child
                .stdin
                .take()
                .expect("failed to open stdin for cc link test");
            stdin
                .write_all(test_prog.as_bytes())
                .expect("failed to write test program");
        }
        let status = child.wait().expect("failed to wait on cc link test");
        status.success()
    };

    if try_std {
        if try_link(&[]) {
            return Ok(None); // none required
        }
    }

    for &lib in search_libs {
        if try_link(&[lib]) {
            return Ok(Some(format!("-l{}", lib)));
        }
    }

    Err(()) // none
}"#
}

pub(super) fn get_function_definition_check_decl() -> &'static str {
    r#"
fn check_decl(symbol: &str, prelude: &str, cppflags: &Vec<String>) -> bool {
    let test_prog = format!(
        "{0}\nint main() {{ 
            #ifndef {1}
              (void) {1}; 
            #endif
            return 0; 
        }}",
        prelude, symbol
    );

    let mut cmd = std::process::Command::new("cc");
    cmd.args(&["-c", "-x", "c", "-", "-o", "/dev/null"]);
    for flag in cppflags {
        cmd.arg(flag);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    let mut child = cmd.spawn().expect("failed to spawn cc for decl check");
    {
        use std::io::Write;
        let mut stdin = child.stdin.take().expect("failed to open stdin");
        stdin
            .write_all(test_prog.as_bytes())
            .expect("failed to write to stdin");
    }
    let status = child.wait().expect("failed to wait on cc declaration check");
    status.success()
}"#
}

pub(super) fn get_function_body_ac_init() -> &'static str {
r#"  {
    // Package Metadata from Cargo
    let package_name = env!("CARGO_PKG_NAME");
    let package_version = env!("CARGO_PKG_VERSION");
    let package_bugreport = env!("CARGO_PKG_REPOSITORY");
    let package_url = env!("CARGO_PKG_HOMEPAGE");
    // Calculated Package Vars
    let package_tarname = package_name.to_lowercase().replace("_", "-");
    let package_string = format!("{} {}", package_name, package_version);
    // Directory Defaults
    let prefix = PathBuf::from("/usr/local");
    let exec_prefix = prefix.clone();
    let datarootdir = prefix.join("share");
    let datadir = datarootdir.clone();
    let sysconfdir = prefix.join("etc");
    let sharedstatedir = prefix.join("com");
    let localstatedir = prefix.join("var");
    let runstatedir = localstatedir.join("run");
    let docdir = datarootdir.join("doc").join(&package_tarname);
    // Paths
    let bindir = exec_prefix.join("bin");
    let sbindir = exec_prefix.join("sbin");
    let libexecdir = exec_prefix.join("libexec");
    let includedir = prefix.join("include");
    let oldincludedir = PathBuf::from("/usr/include");
    let infodir = datarootdir.join("info");
    let libdir = exec_prefix.join("lib");
    let localedir = datarootdir.join("locale");
    let mandir = datarootdir.join("man");
    // System Environment
    let srcdir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // Platform Specifics
    let exe_ext = if cfg!(windows) { ".exe" } else { "" };
    let path_separator = if cfg!(windows) { ";" } else { ":" };
  }
"#
}
