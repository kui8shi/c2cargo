use std::collections::HashMap;

use autotools_parser::m4_macro::VarUsage;

use super::Analyzer;

impl Analyzer {
    /// doc
    pub fn analyze_build_options(&self) {
        let mut build_options = HashMap::new();
        if let Some(v) = self.macro_calls.get("AC_ARG_WITH") {
            for (_, m4_macro) in v {
                let vars = m4_macro
                    .effects
                    .as_ref()
                    .unwrap()
                    .shell_vars
                    .as_ref()
                    .unwrap();
                for var in vars
                    .iter()
                    .filter(|s| s.name != "withval" && s.attrs.usage == VarUsage::Defined)
                {
                    build_options.insert(
                        var.name.strip_prefix("with_").unwrap().to_owned(),
                        var.name.to_owned(),
                    );
                }
            }
        }
        for (name, vars) in build_options {}
    }
}
