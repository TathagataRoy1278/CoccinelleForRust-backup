// SPDX-License-Identifier: GPL-2.0

use clap::Parser;
use crate::parsing_cocci::get_constants;

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
    pub dots: String,

    /// strategy for identifying files that may be matched by the semantic patch
    #[arg(long, value_enum, default_value_t = get_constants::Scanner::CocciGrep)]
    pub worth_trying: get_constants::Scanner,
}
