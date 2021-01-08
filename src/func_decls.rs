use crate::ast::{FunctionSignature};
use crate::capabilities::CapabilityExpr;
use crate::ty::{FromAst, Ty};
use crate::type_check::{Identifiable, Name, TypeContext, TypeError};
use crate::{ast, func_decls};
use std::fmt;
use std::fmt::Display;

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct FunctionType<'tc> {
    pub formal_args: Vec<FunctionFormalArg<'tc>>,
    pub return_type: &'tc Ty<'tc>,
    pub output_capability_constraints: Vec<ArgCapConstraint<'tc>>,
}

impl<'tc> FromAst<'tc, FunctionSignature> for FunctionType<'tc> {
    type Output = Self;

    fn from_ast(
        sig: &FunctionSignature,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        let formal_args: Result<Vec<FunctionFormalArg>, TypeError> = sig
            .args
            .iter()
            .map(|ast_arg| {
                Ok(FunctionFormalArg {
                    name: ast_arg.name.name,
                    ty: Ty::from_ast(&*ast_arg.ty, type_context)?,
                })
            })
            .into_iter()
            .collect();
        let output_capability_constraints: Result<Vec<ArgCapConstraint>, TypeError> = sig
            .output_cap_constraints
            .iter()
            .map(|ast_cap_const| ArgCapConstraint::from_ast(ast_cap_const, type_context))
            .into_iter()
            .collect();
        let func_ty = FunctionType {
            formal_args: formal_args?,
            return_type: Ty::from_ast(&*sig.return_ty, type_context)?,
            output_capability_constraints: output_capability_constraints?,
        };
        Ok(func_ty)
    }
}

impl Display for FunctionType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<TODO some func type>")
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct FunctionDeclaration<'tc> {
    pub name: Name,
    pub ty: FunctionType<'tc>,
}

impl<'tc> Identifiable<Name> for FunctionDeclaration<'tc> {
    fn get_id(&self) -> Name {
        self.name
    }
}

impl<'tc> FromAst<'tc, FunctionSignature> for FunctionDeclaration<'tc> {
    type Output = &'tc FunctionDeclaration<'tc>;

    fn from_ast(
        ast: &FunctionSignature,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        Ok(type_context.intern_func_decl(FunctionDeclaration {
            name: ast.name.name,
            ty: FunctionType::from_ast(ast, type_context)?,
        }))
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
pub struct FunctionFormalArg<'tc> {
    pub name: Name,
    pub ty: &'tc Ty<'tc>,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct ArgCapConstraint<'tc> {
    pub name: Name,
    pub constraints: Vec<CapConstraint<'tc>>,
}

impl<'tc> FromAst<'tc, ast::ArgCapConstraint> for func_decls::ArgCapConstraint<'tc> {
    type Output = func_decls::ArgCapConstraint<'tc>;

    fn from_ast(
        ast: &ast::ArgCapConstraint,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        let constraints: Result<Vec<func_decls::CapConstraint>, TypeError> = ast
            .constraints
            .iter()
            .map(|constraint| func_decls::CapConstraint::from_ast(constraint, type_context))
            .into_iter()
            .collect();
        Ok(func_decls::ArgCapConstraint {
            name: ast.for_arg.name,
            constraints: constraints?,
        })
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
pub enum CapConstraint<'tc> {
    Add(&'tc CapabilityExpr<'tc>),
    Sub(&'tc CapabilityExpr<'tc>),
}

impl<'tc> FromAst<'tc, ast::CapConstraint> for func_decls::CapConstraint<'tc> {
    type Output = func_decls::CapConstraint<'tc>;

    fn from_ast(
        ast: &ast::CapConstraint,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        Ok(match ast {
            ast::CapConstraint::Add(expr) => {
                func_decls::CapConstraint::Add(CapabilityExpr::from_ast(&*expr, type_context)?)
            }
            ast::CapConstraint::Sub(expr) => {
                func_decls::CapConstraint::Sub(CapabilityExpr::from_ast(&*expr, type_context)?)
            }
        })
    }
}
