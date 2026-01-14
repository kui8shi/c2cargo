use std::path::{Component, Path, PathBuf};

pub(crate) mod enumerate;
pub(crate) mod glob;
pub(crate) mod llm_analysis;

pub(crate) fn is_c_extension(ext: &std::ffi::OsStr) -> bool {
    ext == "c" || ext == "cc" || ext == "cpp"
}

pub(crate) fn is_h_extension(ext: &std::ffi::OsStr) -> bool {
    ext == "h" || ext == "hh" || ext == "hpp"
}

pub(crate) fn normalize_path(path: &Path) -> PathBuf {
    let mut components = path.components().peekable();
    let mut ret = if let Some(c @ Component::Prefix(..)) = components.peek() {
        let buf = PathBuf::from(c.as_os_str());
        components.next();
        buf
    } else {
        PathBuf::new()
    };

    for component in components {
        match component {
            Component::CurDir => {}, // Ignore '.'
            Component::ParentDir => {
                ret.pop(); // Resolve '..' by popping the last element
            }
            Component::Normal(c) => {
                ret.push(c);
            }
            Component::RootDir => {
                ret.push(component.as_os_str());
            }
            Component::Prefix(_) => unreachable!()
        }
    }
    ret
}
