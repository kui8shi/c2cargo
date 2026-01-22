pub(super) fn get_function_definition_check_header() -> &'static str {
    r#"
fn check_header(cc: &str, header: &str, prelude: &str, cppflags: &[String]) -> bool {
    let test_prog = format!(
        "{}\n#include <{}>\nint main() {{ return 0; }}",
        prelude, header
    );

    let mut cmd = std::process::Command::new(cc);
    cmd.args(&["-E", "-x", "c", "-"]);
    for flag in cppflags {
        cmd.arg(flag);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Ok(mut child) = cmd.spawn() {
        {
            use std::io::Write;
            let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
            stdin
                .write_all(test_prog.as_bytes())
                .expect("failed to write to cc stdin");
        }
        let status = child.wait().expect("failed to wait on cc header check");
        status.success()
    } else {
        false
    }
}"#
}

pub(super) fn get_function_definition_check_library() -> &'static str {
    r#"
fn check_library(
    cc: &str,
    function_name: &str,
    search_libs: &[&str],
    other_libs: &[&str],
    ldflags: &[String],
    try_std: bool,
) -> Result<Option<String>, ()> {
    let test_prog = format!(
        "char {0} (void); int main (void) {{ return {0} (); }}",
        function_name
    );

    let try_link = |libs: &[&str]| -> bool {
        let mut cmd = std::process::Command::new(cc);
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
        if let Ok(mut child) = cmd.spawn() {
            {
                use std::io::Write;
                let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
                stdin
                    .write_all(test_prog.as_bytes())
                    .expect("failed to write to cc stdin");
            }
            let status = child.wait().expect("failed to wait on cc link test");
            status.success()
        } else {
            false
        }
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
fn check_decl(cc: &str, symbol: &str, prelude: &str, cppflags: &[String]) -> bool {
    let test_prog = format!(
        "{0}\nint main() {{
            #ifndef {1}
              (void) {1};
            #endif
            return 0;
        }}",
        prelude, symbol
    );

    let mut cmd = std::process::Command::new(cc);
    cmd.args(&["-c", "-x", "c", "-", "-o", "/dev/null"]);
    for flag in cppflags {
        cmd.arg(flag);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Ok(mut child) = cmd.spawn() {
        {
            use std::io::Write;
            let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
            stdin
                .write_all(test_prog.as_bytes())
                .expect("failed to write to cc stdin");
        }
        let status = child.wait().expect("failed to wait on cc declaration check");
        status.success()
    } else {
        false
    }
}"#
}

pub(super) fn get_function_definition_check_func() -> &'static str {
    r#"
fn check_func(cc: &str, function_name: &str, ldflags: &[String]) -> bool {
    let test_prog = format!(
        "char {0} (void); int main (void) {{ return {0} (); }}",
        function_name
    );

    let mut cmd = std::process::Command::new(cc);
    cmd.args(&["-x", "c", "-", "-o", "/dev/null"]);
    for flag in ldflags {
        cmd.arg(flag);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Ok(mut child) = cmd.spawn() {
        {
            use std::io::Write;
            let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
            stdin
                .write_all(test_prog.as_bytes())
                .expect("failed to write to cc stdin");
        }
        let status = child.wait().expect("failed to wait on cc func check");
        status.success()
    } else {
        false
    }
}"#
}

pub(super) fn get_function_definition_check_compile() -> &'static str {
    r#"
fn check_compile(cc: &str, cflags: &[String], cppflags: &[String], code: &str) -> bool {
    let mut cmd = std::process::Command::new(cc);
    cmd.args(&["-c", "-x", "c", "-", "-o", "/dev/null"]);
    for flag in cflags {
        cmd.arg(flag);
    }
    for flag in cppflags {
        cmd.arg(flag);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Ok(mut child) = cmd.spawn() {
        {
            use std::io::Write;
            let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
            stdin
                .write_all(code.as_bytes())
                .expect("failed to write to cc stdin");
        }
        let status = child.wait().expect("failed to wait on cc compile check");
        status.success()
    } else {
        false
    }
}"#
}

pub(super) fn get_function_definition_check_link() -> &'static str {
    r#"
fn check_link(cc: &str, cflags: &[String], ldflags: &[String], libs: &[String], code: &str) -> bool {
    let mut cmd = std::process::Command::new(cc);
    cmd.args(&["-x", "c", "-", "-o", "/dev/null"]);
    for flag in cflags {
        cmd.arg(flag);
    }
    for flag in ldflags {
        cmd.arg(flag);
    }
    for lib in libs {
        cmd.arg(lib);
    }
    cmd.stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Ok(mut child) = cmd.spawn() {
        {
            use std::io::Write;
            let mut stdin = child.stdin.take().expect("failed to open stdin for cc");
            stdin
                .write_all(code.as_bytes())
                .expect("failed to write to cc stdin");
        }
        let status = child.wait().expect("failed to wait on cc link check");
        status.success()
    } else {
        false
    }
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

pub(super) fn get_function_body_am_init_automake() -> &'static str {
    r#"  {
    // Reference AC_INIT variables for package and version
    let package = package_tarname.clone();
    let version = package_version.to_string();

    // Source include path
    let am__isrc = "-I.".to_string();
    // Platform-specific cygpath
    let cygpath_w = if cfg!(windows) { "cygpath -w" } else { "echo" }.to_string();
    // Directory creation
    let mkdir_p = "mkdir -p".to_string();
    // Archive tools
    let amtar = "tar".to_string();
    let am__tar = if cfg!(target_os = "linux") {
        "tar --format=ustar -chf - \"$$tardir\"".to_string()
    } else {
        "tar chf - \"$$tardir\"".to_string()
    };
    let am__untar = "tar -xf -".to_string();
    // Tag generators
    let ctags = "ctags".to_string();
    let etags = "etags".to_string();
    let cscope = "cscope".to_string();
    // Auxiliary variables
    let am__rm_f_notfound = String::new();
    let am__xargs_n = String::new();
    // AM_MISSING_PROG tools
    let aclocal = "aclocal".to_string();
    let autoconf = "autoconf".to_string();
    let automake = "automake".to_string();
    let autoheader = "autoheader".to_string();
    let makeinfo = "makeinfo".to_string();
    // AM_PROG_INSTALL_SH
    let install_sh = srcdir.join("install-sh").to_string_lossy().to_string();
    let install_strip_program = " -c -s".to_string();
    // AM_SET_LEADING_DOT
    let am__leading_dot = ".".to_string();
    // AM_SET_DEPDIR
    let depdir = ".deps".to_string();
    // AM_MAKE_INCLUDE
    let am__include = "include".to_string();
    let am__quote = String::new();
    // AM_DEP_TRACK
    let amdepbackslash = "\\".to_string();
    let am__nodep = "_no".to_string();
    // _AM_DEPENDENCIES for various compilers
    let ccdepmode = "depmode=gcc3".to_string();
    let cxxdepmode = "depmode=gcc3".to_string();
    let objcdepmode = "depmode=gcc3".to_string();
    let objcxxdepmode = "depmode=gcc3".to_string();
  }
"#
}

pub(super) fn get_expansion_ac_includes_default() -> &'static str {
    r#"#include <stdio.h>
#ifdef HAVE_SYS_TYPES_H
# include <sys/types.h>
#endif
#ifdef HAVE_SYS_STAT_H
# include <sys/stat.h>
#endif
#ifdef STDC_HEADERS
# include <stdlib.h>
# include <stddef.h>
#else
# ifdef HAVE_STDLIB_H
#  include <stdlib.h>
# endif
#endif
#ifdef HAVE_STRING_H
# if !defined STDC_HEADERS && defined HAVE_MEMORY_H
#  include <memory.h>
# endif
# include <string.h>
#endif
#ifdef HAVE_STRINGS_H
# include <strings.h>
#endif
#ifdef HAVE_INTTYPES_H
# include <inttypes.h>
#endif
#ifdef HAVE_STDINT_H
# include <stdint.h>
#endif
#ifdef HAVE_UNISTD_H
# include <unistd.h>
#endif
"#
}
