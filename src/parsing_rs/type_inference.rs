#![allow(unused)]
use itertools::Itertools;
use ra_hir_ty::display::HirDisplay;
use ra_ide::{AnalysisHost, Semantics};
use ra_ide_db::{base_db::SourceDatabaseExt, symbol_index::SymbolsDatabase, RootDatabase};
use ra_paths::AbsPathBuf;
use ra_project_model::{CargoConfig, ProjectManifest, ProjectWorkspace, RustLibSource};
use ra_rust_analyzer::cli::load_cargo::{load_workspace, LoadCargoConfig, ProcMacroServerChoice};
use ra_syntax::{ast, AstNode, SyntaxNode};
use ra_vfs::Vfs;
use std::path::Path;

use crate::commons::util::workrnode;

use super::ast_rs::Rnode;

pub fn gettypedb(targetpath: &str) -> (AnalysisHost, Vfs) {
    let root = Path::new(targetpath);
    let path_buf = &AbsPathBuf::assert(root.into());
    let manifest = ProjectManifest::discover_single(path_buf).unwrap();

    let mut cargo_config = CargoConfig::default();
    cargo_config.sysroot = Some(RustLibSource::Discover);
    let workspace = ProjectWorkspace::load(
        manifest,
        &cargo_config,
        &(|s| {
            println!("{}", s);
        }),
    )
    .unwrap();

    let load_cargo_config = LoadCargoConfig {
        load_out_dirs_from_check: true,
        prefill_caches: false,
        with_proc_macro_server: ProcMacroServerChoice::Sysroot,
    };

    let (host, vfs, _) =
        load_workspace(workspace, &Default::default(), &load_cargo_config).unwrap();
    //vfs.
    return (host, vfs);
    //let semantics = &mut Semantics::new(db);
}

pub fn set_types(rnode: &mut Rnode, semantics: &Semantics<'_, RootDatabase>, db: &RootDatabase) {
    workrnode(rnode, &mut |node| {
        //Checking if the node is an expression and if it is an expression
        //Then getting its type
        if !node.isexpr() {
            return true;
        }

        let ty = ast::Expr::cast(node.astnode().unwrap().clone())
            .and_then(|ex| semantics.type_of_expr(&ex.into()))
            .map(|ex| ex.original);
        match ty {
            Some(ty) => match ty.as_adt() {
                //adt stads for A Data Type which can be
                //Struct, Enum or Union
                Some(adt) => {
                    //Custom Data Type
                    let namespace = adt
                        .module(semantics.db)
                        .path_to_root(semantics.db)
                        .into_iter()
                        .rev()
                        .flat_map(|it| it.name(db).map(|name| name.display(db).to_string()))
                        .join("::");
                    let typename = adt.ty(semantics.db).display(semantics.db).to_string();

                    if namespace == "" {
                        node.wrapper.set_type(Some(typename));
                    } else {
                        node.wrapper.set_type(Some(format!("{}::{}", namespace, typename)));
                    }
                }
                None => {
                    //I am asuming everything non-ADT does
                    //not have to be explicitly imported and is a part of the language
                    //Subject to change TODO

                    let typename = ty.display(semantics.db).to_string();
                    node.wrapper.set_type(Some(typename));
                }
            },
            None => {
                node.wrapper.set_type(None);
            }
        }

        //This is for debugging types
        node.wrapper.get_type().is_some_and(|x| {
            //println!("{} : {}", node.getunformatted(), x);
            true
        });

        true
    });
}

#[allow(unused)]
pub fn t(targetpath: &str) {
    let root = Path::new(targetpath);
    let path_buf = &AbsPathBuf::assert(root.into());

    let manifest = ProjectManifest::discover_single(path_buf).unwrap();

    let mut cargo_config = CargoConfig::default();
    cargo_config.sysroot = Some(RustLibSource::Discover);
    let workspace = ProjectWorkspace::load(
        manifest,
        &cargo_config,
        &(|s| {
            println!("At {}", s);
        }),
    )
    .unwrap();

    let load_cargo_config = LoadCargoConfig {
        load_out_dirs_from_check: true,
        prefill_caches: false,
        with_proc_macro_server: ProcMacroServerChoice::Sysroot,
    };

    let (host, vfs, _) =
        load_workspace(workspace, &Default::default(), &load_cargo_config).unwrap();

    // Preparing running wrapper
    let db = host.raw_database();
    //host
    //db.modul
    let semantics = &mut Semantics::new(db);

    for source_root_id in db.local_roots().iter() {
        println!("Local root: {:#?}", source_root_id);
        let source_root = db.source_root(*source_root_id);
        //let krates = db.source_root_crates(*source_root_id);

        for file_id in source_root.iter() {
            let file = vfs.file_path(file_id);
            println!("Walking: {}", file.as_path().expect(""));

            let source_file = semantics.parse(file_id);
            let syntax = source_file.syntax();

            fn dfs(node: SyntaxNode, prefix: &str, semantics: &mut Semantics<'_, RootDatabase>) {
                println!("infinite");

                let _typename = ast::Expr::cast(node.clone())
                    .and_then(|ex| semantics.type_of_expr(&ex.into()))
                    .map(|ex| ex.original)
                    .map(|og| og.display(semantics.db).to_string())
                    .unwrap_or("[Ty ty]".to_string());
                println!("dem");
                let tyn = match ast::Expr::cast(node.clone()) {
                    Some(exp) => match semantics.type_of_expr(&exp) {
                        Some(ty) => ty.original.display(semantics.db).to_string(),
                        None => "no type".to_string(),
                    },
                    _ => "No expression".to_string(),
                };

                let num_children = node.children().count();

                if num_children == 0 {
                    println!(" {}  {:#?} ({})", &(prefix.to_owned() + "--"), node.kind(), tyn);
                } else {
                    println!(" {}  {:#?} ({})", &(prefix.to_owned() + "+-"), node.kind(), tyn);
                }
                println!("here");
                for child in node.children() {
                    if let Some(last_child) = node.children().last() {
                        if child == last_child {
                            dfs(child, &(prefix.to_owned() + "  "), semantics);
                        } else {
                            dfs(child, &(prefix.to_owned() + "| "), semantics);
                        }
                    }
                }
            }
            dfs(syntax.clone(), "", semantics);
        }
    }
}
