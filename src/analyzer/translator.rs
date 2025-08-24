use autotools_parser::ast::MayM4;

use super::Analyzer;

impl Analyzer {
    /// translate top commands
    pub fn translate(&self) {
        for &top in &self.top_ids {
            if let MayM4::Macro(m4_macro) = &self.get_node(top).cmd.0 {
                if m4_macro.name == "AC_INIT" {
                    let (_, exported) = self.examine_chunk_io(&[top]);
                    continue;
                }
            }
        }
    }
}
