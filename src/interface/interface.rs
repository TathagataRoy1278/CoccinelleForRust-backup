// SPDX-License-Identifier: GPL-2.0

use crate::parsing_cocci::get_constants;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct CoccinelleForRust {
    /// Path of Semantic Patch File path
    #[arg(short, long)]
    pub coccifile: String,

    /// Path of Rust Target file/folder path
    pub targetpath: String,

    /// Path of transformed file path
    #[arg(short, long)]
    pub output: Option<String>,

    /// rustfmt config file path
    #[arg(short, long)]
    pub rustfmt_config: Option<String>,

    //ignores files and folders with the string present
    #[arg(short, long, default_value_t = String::new())]
    pub ignore: String,

    #[arg(short, long)]
    pub debug: bool,

    #[arg(long)]
    pub apply: bool,

    #[arg(long)]
    pub suppress_diff: bool,

    #[arg(long)]
    pub suppress_formatting: bool,

    #[arg(long)]
    pub show_fmt_errors: bool,

    #[arg(short, long)]
    pub no_parallel: bool,

    /// Used only for development
    /// Do not use
    #[arg(long)]
    pub dots: Option<String>,

    /// strategy for identifying files that may be matched by the semantic patch
    #[arg(long, value_enum, default_value_t = get_constants::Scanner::CocciGrep)]
    pub worth_trying: get_constants::Scanner,

    /// Exports the cfg in current directory as cfg.png and opens it
    /// Note that this uses graphviz for writing and w3m for viewing
    #[arg(long)]
    pub show_cfg: bool,

    #[arg(long)]
    pub show_ctl: bool,
}
