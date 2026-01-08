pub(crate) mod enumerate;
pub(crate) mod glob;
pub(crate) mod llm_analysis;

pub(crate) fn is_c_extension(ext: &std::ffi::OsStr) -> bool {
    ext == "c" || ext == "cc" || ext == "cpp"
}

pub(crate) fn is_h_extension(ext: &std::ffi::OsStr) -> bool {
    ext == "h" || ext == "hh" || ext == "hpp"
}
