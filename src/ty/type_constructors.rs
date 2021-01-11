use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::hash::{Hash, Hasher};

use crate::ty::CapabilityExpr;
use crate::ty::Ty;
use crate::typecheck::{Identifiable, Name};

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct TypeParameterDeclaration {
    name: Name,
}

#[derive(Debug, Clone)]
pub struct TypeConstructor {
    pub(crate) name: Name,
    pub(crate) type_parameters: Vec<TypeParameterDeclaration>,
}

impl TypeConstructor {
    fn new(name: Name) -> TypeConstructor {
        TypeConstructor {
            name,
            type_parameters: Vec::default(),
        }
    }
}

impl Display for TypeConstructor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

// TODO derive this delegation somehow?
impl PartialEq for TypeConstructor {
    fn eq(&self, other: &Self) -> bool {
        self.name.eq(other.name)
    }
}

impl Eq for TypeConstructor {}

impl PartialOrd for TypeConstructor {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.name.partial_cmp(other.name)
    }
}

impl Ord for TypeConstructor {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(other.name)
    }
}

impl Hash for TypeConstructor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

impl Identifiable<Name> for TypeConstructor {
    fn get_id(&self) -> Name {
        self.name
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct TypeParameterBinding<'tc> {
    pub for_declaration: &'tc TypeParameterDeclaration,
    pub bound_to: Ty<'tc>,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct TypeConstructorInvocation<'tc> {
    pub constructor: &'tc TypeConstructor,
    pub type_parameter_bindings: Vec<TypeParameterBinding<'tc>>,
    pub capabilities: Option<&'tc CapabilityExpr<'tc>>,
}

impl Display for TypeConstructorInvocation<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.constructor.name)?;
        if !self.type_parameter_bindings.is_empty() {
            write!(f, "<")?;
            let last = self.type_parameter_bindings.len() - 1;
            for (i, binding) in self.type_parameter_bindings.iter().enumerate() {
                write!(f, "{}", binding.bound_to)?;
                if i != last {
                    write!(f, ", ")?;
                }
            }
            write!(f, ">")?;
        }
        if let Some(caps) = self.capabilities {
            write!(f, "[{}]", caps)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ty::capabilities::CapabilityExpr::Or;
    use crate::ty::capabilities::{CapabilityDeclaration, CapabilityExpr};
    use crate::ty::type_constructors::{TypeConstructor, TypeConstructorInvocation};
    use crate::typecheck::test_utils::{assert_assignable_to, assert_not_assignable_to};
    use crate::typecheck::{Arenas, TypeContext};

    macro_rules! with_fixture {
        ($fix:ident, $body:block) => {
            let arenas = Arenas::default();
            let tc = TypeContext::new(&arenas);
            let $fix = Fixture::new(&tc);
            $body
        };
    }

    struct Fixture<'tc> {
        tc: &'tc TypeContext<'tc>,
        const_foo: &'tc TypeConstructor,
        const_bar: &'tc TypeConstructor,
        cap_a: &'tc CapabilityDeclaration,
        cap_b: &'tc CapabilityDeclaration,
        capex_a: &'tc CapabilityExpr<'tc>,
        capex_b: &'tc CapabilityExpr<'tc>,
        inv_foo: TypeConstructorInvocation<'tc>,
        inv_bar: TypeConstructorInvocation<'tc>,
        inv_foo_cap_a: TypeConstructorInvocation<'tc>,
        inv_foo_cap_b: TypeConstructorInvocation<'tc>,
        inv_foo_cap_a_or_cap_b: TypeConstructorInvocation<'tc>,
        inv_bar_cap_a: TypeConstructorInvocation<'tc>,
        inv_bar_cap_b: TypeConstructorInvocation<'tc>,
    }

    impl<'tc> Fixture<'tc> {
        fn new(tc: &'tc TypeContext<'tc>) -> Fixture<'tc> {
            let foo = tc.intern_type_constructor(TypeConstructor::new("Foo"));
            let bar = tc.intern_type_constructor(TypeConstructor::new("Bar"));
            let cap_a = tc.intern_cap_decl(CapabilityDeclaration::new("A"));
            let cap_b = tc.intern_cap_decl(CapabilityDeclaration::new("B"));
            let capex_a = tc.intern_cap_expr(CapabilityExpr::Cap(cap_a));
            let capex_b = tc.intern_cap_expr(CapabilityExpr::Cap(cap_b));
            Fixture {
                tc: &tc,
                const_foo: foo,
                const_bar: bar,
                cap_a,
                cap_b,
                capex_a,
                capex_b,
                // TODO validate bindings.len() == constructor.type_parameters.len()?
                inv_foo: TypeConstructorInvocation {
                    constructor: foo,
                    type_parameter_bindings: vec![],
                    capabilities: None,
                },
                inv_bar: TypeConstructorInvocation {
                    constructor: bar,
                    type_parameter_bindings: vec![],
                    capabilities: None,
                },
                inv_foo_cap_a: TypeConstructorInvocation {
                    constructor: foo,
                    type_parameter_bindings: vec![],
                    capabilities: Some(capex_a),
                },
                inv_foo_cap_b: TypeConstructorInvocation {
                    constructor: foo,
                    type_parameter_bindings: vec![],
                    capabilities: Some(capex_b),
                },
                inv_foo_cap_a_or_cap_b: TypeConstructorInvocation {
                    constructor: foo,
                    type_parameter_bindings: vec![],
                    capabilities: Some(tc.intern_cap_expr(Or(capex_a, capex_b))),
                },
                inv_bar_cap_a: TypeConstructorInvocation {
                    constructor: bar,
                    type_parameter_bindings: vec![],
                    capabilities: Some(capex_a),
                },
                inv_bar_cap_b: TypeConstructorInvocation {
                    constructor: bar,
                    type_parameter_bindings: vec![],
                    capabilities: Some(capex_b),
                },
            }
        }
    }

    #[test]
    fn foo_assignable_to_foo() {
        with_fixture!(fix, {
            assert_assignable_to(&fix.inv_foo, &fix.inv_foo);
        });
    }

    #[test]
    fn foo_not_assignable_to_bar() {
        with_fixture!(fix, {
            assert_not_assignable_to(&fix.inv_foo, &fix.inv_bar);
        });
    }

    #[test]
    fn foo_cap_a_assignable_to_foo_cap_a() {
        with_fixture!(fix, {
            assert_assignable_to(&fix.inv_foo_cap_a, &fix.inv_foo_cap_a);
        });
    }

    #[test]
    fn foo_cap_a_not_assignable_to_foo_cap_b() {
        with_fixture!(fix, {
            assert_not_assignable_to(&fix.inv_foo_cap_a, &fix.inv_foo_cap_b);
        });
    }

    #[test]
    fn foo_cap_a_assignable_to_foo() {
        with_fixture!(fix, {
            assert_assignable_to(&fix.inv_foo_cap_a, &fix.inv_foo);
        });
    }

    #[test]
    fn foo_cap_a_assignable_to_foo_cap_a_or_cap_b() {
        with_fixture!(fix, {
            assert_assignable_to(&fix.inv_foo_cap_a, &fix.inv_foo_cap_a_or_cap_b);
        });
    }

    #[test]
    fn foo_cap_a_or_cap_b_not_assignable_to_foo_cap_a() {
        with_fixture!(fix, {
            assert_not_assignable_to(&fix.inv_foo_cap_a_or_cap_b, &fix.inv_foo_cap_a);
        });
    }
}
