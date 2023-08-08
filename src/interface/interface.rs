// SPDX-License-Identifier: GPL-2.0

use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct CoccinelleForRust {
    /// Path of Semantic Patch File path
    #[arg(short, long)]
    pub coccifile: String,

    /// Path of Rust Target file/folder path
    #[arg(short, long)]
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
    pub debug_cocci: bool,

    #[arg(long)]
    pub apply: bool,

    #[arg(long)]
    pub suppress_diff: bool,

    #[arg(long)]
    pub suppress_formatting: bool,

    #[arg(long)]
    pub no_parallel: bool,
}
