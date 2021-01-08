// TODO remove, lots of stuff in flux right now and tired of unused field warnings...
#![allow(dead_code)]

mod ast;
mod capabilities;
#[macro_use]
mod symbol_table;
mod func_decls;
mod ty;
mod type_check;
mod type_constructors;

// use std::collections::HashMap;
// use std::marker::PhantomData;
//
// /// master struct that contains everything we know about types
// struct TypeContext<'tcxt> {
//     inflated_types: HashMap<Fqn, InflatedType<'tcxt>>,
//     layouts: HashMap<Fqn, ValueLayout<'tcxt>>,
// }
//
// impl TypeContext<'_> {
//     fn new<'a>() -> TypeContext<'a> {
//         TypeContext {
//             inflated_types: HashMap::default(),
//             layouts: HashMap::default(),
//         }
//     }
//
//     fn new_with_prelude<'a>() -> TypeContext<'a> {
//         let mut it = Self::new();
//         it.load_prelude();
//         it
//     }
//
//     fn load_prelude(&mut self) {}
// }
//
// // TODO interning on Ident/Fqn strings
//
// /// An identifier, eg, `foo`
// struct Ident(String);
//
// /// A fully qualified name, eg, `com.warburg.foo`
// struct Fqn(String);
//
// impl Fqn {
//     fn last(&self) -> Ident {
//         Ident(self.0.split(".").last().unwrap().to_string())
//     }
// }
//
// /// A type expression, like `bool`, `Foo`, `Foo<T>[C]`, `Foo<Bar>[Yeet]`, etc
// enum TypeExpression {
//     Simple { name: Fqn }, // TODO type parameters, capabilities
// }
//
// /// A description of what we know about this type's sizes by component
// enum TypeSizing {
//     Static {
//         component_sizes: Vec<ComponentSizing>,
//     },
//     Dynamic,
// }
//
// impl TypeSizing {
//     /// A layout depends on the representation we've chosen for this type; it may layout the value differently depending on it
//     fn layout<'tcxt>(
//         &self,
//         tcxt: &'tcxt TypeContext,
//         representation: &TypeRepresentation,
//     ) -> Option<ValueLayout<'tcxt>> {
//         match self {
//             TypeSizing::Static { component_sizes } => {
//                 unimplemented!();
//             }
//             TypeSizing::Dynamic => None, // TODO can we provide a layout for dynamically sized types?
//         }
//     }
// }
//
// /// The sizing of a single component
// struct ComponentSizing {
//     field_name: Fqn,
//     sizing: TypeSizing,
// }
//
// enum TypeRepresentation {
//     Naive,
//     Padded,
//     // TODO C for interop
// }
//
// struct ValueLayout<'tcxt> {
//     sections: Vec<LayoutSection<'tcxt>>,
// }
//
// enum LayoutSection<'tcxt> {
//     Padding { bytes: usize },
//     Value { layout: &'tcxt ValueLayout<'tcxt> },
// }
//
// /// The inflated/reified version of a type, fully resolved with all the information we know about it.
// enum InflatedType<'tcxt> {
//     Simple {
//         name: Fqn,
//         sizing: TypeSizing,
//         representation: TypeRepresentation,
//         use_param: PhantomData<&'tcxt ()>,
//     },
// }
//
// impl InflatedType<'_> {
//     fn sizing(&self) -> &TypeSizing {
//         self.sizing()
//     }
//
//     fn layout<'tcxt>(&self, tcxt: &'tcxt TypeContext) -> Option<ValueLayout<'tcxt>> {
//         return match self {
//             InflatedType::Simple {
//                 name: _name,
//                 sizing: _sizing,
//                 representation,
//                 use_param: _use_param,
//             } => self.sizing().layout(tcxt, representation),
//         };
//     }
// }
