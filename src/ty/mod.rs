use core::fmt;
use core::fmt::{Display, Formatter};
use core::result::Result;
use core::result::Result::Ok;

use crate::ast;
use crate::ast_to_ty::FromAst;
pub use crate::ty::capabilities::*;
pub use crate::ty::func_decls::*;
pub use crate::ty::type_constructors::*;
use crate::typecheck::{Name, TypeContext, TypeError};

mod capabilities;
mod func_decls;
mod type_constructors;

/// The type checker's view of a type. Interned in TypeContext.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub enum Ty<'tc> {
    Variable(Name),
    TyConInv(TypeConstructorInvocation<'tc>),
    Func(FunctionType<'tc>),
    Bottom,
    Unit,
}

impl<'tc> Ty<'tc> {
    pub fn from_func_sig(
        sig: &ast::FunctionSignature,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<&'tc Ty<'tc>, TypeError> {
        Ok(type_context.intern_ty(Ty::Func(FunctionType::from_ast(sig, type_context)?)))
    }

    pub fn apply_constraint(
        &'tc self,
        constraint: &'tc CapConstraint<'tc>,
        tc: &'tc TypeContext<'tc>,
    ) -> Ty<'tc> {
        match self {
            Ty::TyConInv(tci) => {
                match constraint {
                    CapConstraint::Add(added_caps) => {
                        let new_caps = if let Some(existing_caps) = tci.capabilities {
                            tc.intern_cap_expr(CapabilityExpr::And(existing_caps, added_caps))
                        } else {
                            added_caps
                        };
                        // TODO simplify constraints. eg, this could result in A & (A & B).
                        Ty::TyConInv(TypeConstructorInvocation {
                            capabilities: Some(new_caps),
                            ..tci.clone()
                        })
                    }
                    CapConstraint::Sub(_) => {
                        unimplemented!("subtracting capability constraints")
                    }
                }
            }
            Ty::Bottom => Ty::Bottom,
            _ => self.clone(),
        }
    }
}

impl<'tc> Display for Ty<'tc> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use Ty::*;
        match self {
            Variable(name) => write!(f, "{}", name)?,
            TyConInv(tci) => write!(f, "{}", tci)?,
            Func(func_type) => write!(f, "{}", func_type)?,
            Bottom => write!(f, "<bottom>")?,
            Unit => write!(f, "()")?,
        }
        Ok(())
    }
}
