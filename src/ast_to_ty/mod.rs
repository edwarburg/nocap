use std::ops::Deref;

use bumpalo::core_alloc::borrow::Borrow;

use crate::ast::{AstNode, Cap, CapKind, FunctionSignature};
use crate::ty::{
    ArgCapConstraint, CapabilityExpr, FunctionDeclaration, FunctionFormalArg, FunctionType, Ty,
    TypeConstructorInvocation,
};
use crate::typecheck::{TypeContext, TypeError};
use crate::{ast, ty};

pub trait FromAst<'tc, Ast> {
    type Output;

    fn from_ast(ast: &Ast, type_context: &'tc TypeContext<'tc>) -> Result<Self::Output, TypeError>;
}

impl<'tc> FromAst<'tc, ast::Ty> for Ty<'tc> {
    type Output = &'tc Ty<'tc>;

    fn from_ast(
        ast_ty: &ast::Ty,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        match &ast_ty.kind() {
            ast::TyKind::TyVar(v) => Ok(type_context.intern_ty(Ty::Variable(v.name))),
            ast::TyKind::TyConstInv(tci) => {
                let constructor = type_context
                    .lookup_type_constructor(tci.constructor.name)
                    .ok_or_else(|| format!("No type constructor named {}", tci.constructor.name))?;
                let type_parameter_bindings = Vec::new();
                let capabilities: Option<&'tc CapabilityExpr<'tc>> = tci
                    .capabilities
                    .borrow()
                    .as_ref()
                    .map(|ast_cap| CapabilityExpr::from_ast(ast_cap.deref(), type_context))
                    .transpose()?;
                let new_tci = TypeConstructorInvocation {
                    constructor,
                    type_parameter_bindings,
                    capabilities,
                };
                Ok(type_context.intern_ty(Ty::TyConInv(new_tci)))
            }
        }
    }
}

impl<'tc> FromAst<'tc, ast::Cap> for CapabilityExpr<'tc> {
    type Output = &'tc CapabilityExpr<'tc>;

    fn from_ast(ast: &Cap, type_context: &'tc TypeContext<'tc>) -> Result<Self::Output, TypeError> {
        Ok(type_context.intern_cap_expr(match &ast.kind {
            CapKind::CapRef(cap) => CapabilityExpr::Cap(
                type_context
                    .lookup_cap_decl(cap.name)
                    .ok_or_else(|| format!("unknown capability: {}", cap.name))?,
            ),
            CapKind::And(lhs, rhs) => {
                let lhs = CapabilityExpr::from_ast(lhs, type_context)?;
                let rhs = CapabilityExpr::from_ast(rhs, type_context)?;
                CapabilityExpr::And(lhs, rhs)
            }
            CapKind::Or(lhs, rhs) => {
                let lhs = CapabilityExpr::from_ast(lhs, type_context)?;
                let rhs = CapabilityExpr::from_ast(rhs, type_context)?;
                CapabilityExpr::Or(lhs, rhs)
            }
        }))
    }
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

impl<'tc> FromAst<'tc, ast::ArgCapConstraint> for ty::ArgCapConstraint<'tc> {
    type Output = ty::ArgCapConstraint<'tc>;

    fn from_ast(
        ast: &ast::ArgCapConstraint,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        let constraints: Result<Vec<ty::CapConstraint>, TypeError> = ast
            .constraints
            .iter()
            .map(|constraint| ty::CapConstraint::from_ast(constraint, type_context))
            .into_iter()
            .collect();
        Ok(ty::ArgCapConstraint {
            name: ast.for_arg.name,
            constraints: constraints?,
        })
    }
}

impl<'tc> FromAst<'tc, ast::CapConstraint> for ty::CapConstraint<'tc> {
    type Output = ty::CapConstraint<'tc>;

    fn from_ast(
        ast: &ast::CapConstraint,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<Self::Output, TypeError> {
        Ok(match ast {
            ast::CapConstraint::Add(expr) => {
                ty::CapConstraint::Add(CapabilityExpr::from_ast(&*expr, type_context)?)
            }
            ast::CapConstraint::Sub(expr) => {
                ty::CapConstraint::Sub(CapabilityExpr::from_ast(&*expr, type_context)?)
            }
        })
    }
}
