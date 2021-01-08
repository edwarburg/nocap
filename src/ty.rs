use crate::ast;
use crate::ast::AstNode;
use crate::capabilities::CapabilityExpr;
use crate::func_decls::{CapConstraint, FunctionType};
use crate::type_check::{AssignabilityJudgment, Assignable, Name, TypeContext, TypeError};
use crate::type_constructors::TypeConstructorInvocation;
use core::fmt;
use core::fmt::{Display, Formatter};
use core::option::Option::None;
use core::result::Result;
use core::result::Result::Ok;

/// The type checker's view of a type. Interned in TypeContext.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub enum Ty<'tc> {
    Variable(Name),
    TyConInv(TypeConstructorInvocation<'tc>),
    Func(FunctionType<'tc>),
    Bottom,
}

impl<'tc> Ty<'tc> {
    pub fn from_ast(
        expr: &ast::Ty,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<&'tc Ty<'tc>, TypeError> {
        match &expr.kind() {
            ast::TyKind::TyVar(v) => Ok(type_context.intern_ty(Ty::Variable(v.name))),
            ast::TyKind::TyConstInv(tci) => {
                let constructor = type_context
                    .lookup_type_constructor(tci.constructor.name)
                    .ok_or_else(|| format!("No type constructor named {}", tci.constructor.name))?;
                // TODO do type parameters and capabilities
                let type_parameter_bindings = Vec::new();
                let capabilities = None;
                let new_tci = TypeConstructorInvocation {
                    constructor,
                    type_parameter_bindings,
                    capabilities,
                };
                Ok(type_context.intern_ty(Ty::TyConInv(new_tci)))
            }
        }
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

impl Assignable for Ty<'_> {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        match (from, to) {
            (Ty::Bottom, _) => AssignabilityJudgment::Assignable,
            (Ty::Variable(_from_name), Ty::Variable(_to_name)) => {
                unimplemented!("type variable assignability");
            }
            (Ty::TyConInv(from_tci), Ty::TyConInv(to_tci)) => from_tci.assignable_to(to_tci),
            // TODO assignability of function types
            _ => {
                AssignabilityJudgment::not_assignable(format!("{} not assignable to {}", from, to))
            }
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
        }
        Ok(())
    }
}
