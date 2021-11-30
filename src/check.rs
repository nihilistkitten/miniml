//! Type check an expression.

use std::collections::{HashMap, HashSet};
use std::fmt::Display;

use crate::ast;

/// A Ml type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Unit,
    Int,
    Bool,
    Arrow(Box<Self>, Box<Self>),
    Product(Box<Self>, Box<Self>),

    /// A type variable, distinguished by a counter.
    Var(usize),

    Forall(usize, Box<Self>),
}

/// Construct a unique string to represent a type variable by repeating a char.
fn display_type_var(var: usize) -> String {
    let div = var / 26 + 1; // number of repetitions we need
    let ucode = (var % 26) + 96; // unicode for the character to repeat
                                 // this is 96 because the first type var is 1

    let bytes = vec![ucode.try_into().expect("mod 26 gives a u8"); div];
    String::from_utf8(bytes).expect("our string is valid utf-8")
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::Unit => "unit",
            Self::Int => "int",
            Self::Bool => "bool",
            Self::Arrow(left, right) => return write!(f, "({} -> {})", left, right),
            Self::Product(left, right) => return write!(f, "({} x {})", left, right),
            Self::Var(n) => return write!(f, "'{}", display_type_var(*n)),
            Self::Forall(x, t) => return write!(f, "∀{}: {}", display_type_var(*x), t),
        };
        write!(f, "{}", message)
    }
}

/// Substitute the first type var for the second.
#[derive(Debug)]
struct Subst(HashMap<usize, Type>);

impl Subst {
    fn new() -> Self {
        Self(HashMap::default())
    }

    fn merge(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self
    }

    fn apply(&self, to: Type) -> Type {
        match to {
            Type::Unit | Type::Int | Type::Bool => to,
            Type::Arrow(left, right) => Type::Arrow(box self.apply(*left), box self.apply(*right)),
            Type::Product(left, right) => {
                Type::Product(box self.apply(*left), box self.apply(*right))
            }
            Type::Var(tau) => self.0.get(&tau).map_or(to, Clone::clone),
            Type::Forall(x, box tau) => Type::Forall(x, box self.apply(tau)),
        }
    }
}

/// An accumulator of type substitutions that also stores an inferred type.
struct SubstAccum {
    subs: Subst,
    ty: Type,
}

impl From<(Subst, Type)> for SubstAccum {
    fn from((subst, ty): (Subst, Type)) -> Self {
        Self { subs: subst, ty }
    }
}

impl From<Type> for SubstAccum {
    fn from(ty: Type) -> Self {
        Self {
            subs: Subst::new(),
            ty,
        }
    }
}

impl From<SubstAccum> for (Subst, Type) {
    fn from(sa: SubstAccum) -> Self {
        (sa.subs, sa.ty)
    }
}

impl SubstAccum {
    /// Unify self's type with other, merging the resulting substitutions.
    fn unify(self, other: Type) -> Subst {
        let subs = self.ty.unify(other);
        self.subs.merge(subs)
    }
}

impl<T: Into<HashMap<usize, Type>>> From<T> for Subst {
    fn from(val: T) -> Self {
        Self(val.into())
    }
}

mod tc {
    use super::{HashMap, HashSet, Subst, Type};

    /// A type context.
    ///
    /// This is a collection type which allows safe exterior mutability without exposing interior
    /// mutability of the wrapped `HashMap`'s items. It does so by assemblying essentially a linked
    /// list of insertions and removals via `with_inserted`, the only method which allows mutation.
    /// It allows read-only access to the inner data via the `Deref` trait.
    #[derive(Debug)]
    pub(super) struct TypeContext<'a> {
        inner: HashMap<&'a str, Type>,
    }

    impl<'a> TypeContext<'a> {
        pub fn new() -> Self {
            Self {
                inner: HashMap::default(),
            }
        }

        /// Determine the free variables of all types in the context.
        pub fn all_free_vars(&self) -> HashSet<usize> {
            self.inner.iter().flat_map(|(_, t)| t.free_vars()).collect()
        }

        pub fn apply_to_all(&mut self, subs: &Subst) {
            for t in self.inner.values_mut() {
                let to_sub = std::mem::replace(t, Type::Var(1));
                *t = subs.apply(to_sub);
            }
        }

        /// Temporarily insert key and value and run f, then restore the old context.
        ///
        /// Returns back the inserted value, and also returns the output of f.
        pub fn with_inserted<T>(
            &mut self,
            key: &'a str,
            value: Type,
            f: impl FnOnce(&mut Self) -> T,
        ) -> (Type, T) {
            let old = self.inner.insert(key, value);
            let res = f(self);
            let value = if let Some(old_value) = old {
                self.inner.insert(key, old_value)
            } else {
                self.inner.remove(key)
            }
            .expect("cannot pop from a context without pushing first");
            (value, res)
        }

        /// Get a reference to the type context's wrapped hashmap.
        pub const fn inner(&self) -> &HashMap<&'a str, Type> {
            &self.inner
        }
    }

    impl<'a, T: Into<HashMap<&'a str, Type>>> From<T> for TypeContext<'a> {
        fn from(val: T) -> Self {
            Self { inner: val.into() }
        }
    }

    impl<'a> std::ops::Deref for TypeContext<'a> {
        type Target = HashMap<&'a str, Type>;

        fn deref(&self) -> &Self::Target {
            self.inner()
        }
    }
}

use tc::TypeContext;

impl Type {
    /// Compute the free variables of a type.
    fn free_vars(&self) -> HashSet<usize> {
        self.free_vars_impl().collect()
    }

    fn free_vars_impl(&self) -> Box<dyn Iterator<Item = usize> + '_> {
        match self {
            Self::Unit | Self::Int | Self::Bool => box std::iter::empty(),
            Self::Arrow(left, right) | Self::Product(left, right) => {
                box left.free_vars_impl().chain(right.free_vars_impl())
            }
            Self::Var(n) => box std::iter::once(*n),
            Self::Forall(x, box t) => box t.free_vars_impl().filter(|&y| y != *x),
        }
    }

    /// Unify self with other.
    fn unify(self, other: Self) -> Subst {
        match (self, other) {
            (Self::Var(a), Self::Var(b)) => {
                if a == b {
                    Subst::new()
                } else {
                    [(a, Self::Var(b))].into()
                }
            }

            (Self::Var(a), tau) | (tau, Self::Var(a)) => {
                if tau.free_vars().contains(&a) {
                    panic!()
                } else {
                    [(a, tau)].into()
                }
            }

            (Self::Unit, Self::Unit) | (Self::Int, Self::Int) | (Self::Bool, Self::Bool) => {
                Subst::new()
            }

            (
                Self::Arrow(box self_left, box mut self_right),
                Self::Arrow(box other_left, box mut other_right),
            )
            | (
                Self::Product(box self_left, box mut self_right),
                Self::Product(box other_left, box mut other_right),
            ) => {
                let left_subs = self_left.unify(other_left);

                self_right = left_subs.apply(self_right);
                other_right = left_subs.apply(other_right);

                left_subs.merge(self_right.unify(other_right))
            }

            (left, right) => panic!("could not merge {} with {}", left, right),
        }
    }

    fn generalize(mut self, ctx: &mut TypeContext) -> Self {
        let ctx_free_vars = ctx.all_free_vars();
        let inner_free_vars = self.free_vars();

        let unbound_free_vars = inner_free_vars.difference(&ctx_free_vars);

        for typ in unbound_free_vars {
            self = Self::Forall(*typ, box self);
        }

        self
    }

    fn instantiate(self) -> Self {
        if let Self::Forall(x, box inner) = self {
            let new_ident = get_fresh_ident();
            let subst: Subst = [(x, Self::Var(new_ident))].into();
            subst.apply(inner.instantiate())
        } else {
            self
        }
    }
}

impl<'a> ast::Value<'a> {
    fn infer(&self, ctx: &mut TypeContext<'a>) -> SubstAccum {
        match self {
            Self::Unit => Type::Unit.into(),
            Self::Num(_) => Type::Int.into(),
            Self::Bool(_) => Type::Bool.into(),
            Self::Lookup(x) => ctx
                .get(x)
                .expect(&("unbound variable ".to_string() + x))
                .clone()
                .instantiate()
                .into(),
            Self::Fn(param, box rule) => {
                let sigma = Type::Var(get_fresh_ident());
                let (sigma, (subs, tau)) =
                    ctx.with_inserted(param, sigma, |c| rule.infer_impl(c).into());

                let sigma = subs.apply(sigma);
                (subs, Type::Arrow(box sigma, box tau)).into()
            }
        }
    }
}

impl ast::Binop {
    fn infer<'a>(
        &self,
        left: &ast::Expn<'a>,
        right: &ast::Expn<'a>,
        ctx: &mut TypeContext<'a>,
    ) -> SubstAccum {
        if let Self::Appl = self {
            let mut fn_type = left.infer_impl(ctx);

            let arg_type = right.infer_impl(ctx);
            fn_type.ty = arg_type.subs.apply(fn_type.ty);

            let out_type = Type::Var(get_fresh_ident());

            let subs = fn_type.unify(Type::Arrow(box arg_type.ty, box out_type.clone()));
            let out_type = subs.apply(out_type);

            (subs.merge(arg_type.subs), out_type).into()
        } else {
            let argument_type = match self {
                Self::Arith(_) | Self::Order(_) => Type::Int,
                Self::Logic(_) => Type::Bool,
                Self::Appl => unreachable!("appl checked above"),
            };

            // clone is cheap because the type is trivial
            let subs = left.infer_impl(ctx).unify(argument_type.clone());

            let subs = right.infer_impl(ctx).unify(argument_type).merge(subs);

            dbg!(&subs);

            let ret_type = match self {
                Self::Arith(_) => Type::Int,
                Self::Order(_) | Self::Logic(_) => Type::Bool,
                Self::Appl => unreachable!("appl checked above"),
            };
            (subs, ret_type).into()
        }
    }
}

impl ast::Unop {
    fn infer<'a>(&self, on: &ast::Expn<'a>, ctx: &mut TypeContext<'a>) -> SubstAccum {
        match self {
            Self::Neg => (on.infer_impl(ctx).unify(Type::Int), Type::Int).into(),
            Self::Not => (on.infer_impl(ctx).unify(Type::Bool), Type::Bool).into(),
        }
    }
}

impl<'a> ast::Let<'a> {
    fn infer(
        &self,
        defn: &ast::Expn<'a>,
        body: &ast::Expn<'a>,
        ctx: &mut TypeContext<'a>,
    ) -> SubstAccum {
        match self {
            Self::Fun(ident, param) => {
                let param_type = Type::Var(get_fresh_ident());
                let ret_type = Type::Var(get_fresh_ident());

                // cheap clones because non-recursive types
                let tau = Type::Arrow(box param_type.clone(), box ret_type.clone());

                let (tau, (_, inferred)) = ctx.with_inserted(ident, tau, |c| {
                    c.with_inserted(param, param_type, |c| defn.infer_impl(c))
                });

                let generalized_tau = ret_type.unify(inferred.ty).apply(tau).generalize(ctx);

                ctx.with_inserted(ident, generalized_tau, |c| body.infer_impl(c))
                    .1
            }
            Self::Val(ident) => {
                let sigma = defn.infer_impl(ctx).ty.generalize(ctx);
                ctx.with_inserted(ident, sigma, |c| body.infer_impl(c)).1
            }
        }
    }
}

impl<'a> ast::Expn<'a> {
    /// Infer the type of the expn.
    pub fn infer(&self) -> Type {
        self.infer_impl(&mut TypeContext::new()).ty
    }

    fn infer_impl(&self, ctx: &mut TypeContext<'a>) -> SubstAccum {
        let ret = match self {
            Self::If {
                cond,
                then_exp,
                else_exp,
            } => {
                cond.infer_impl(ctx).ty.unify(Type::Bool);

                let (if_subst, if_type) = then_exp.infer_impl(ctx).into();
                let (else_subst, else_type) = else_exp.infer_impl(ctx).into();
                let subs = if_type.clone().unify(else_type);
                (subs.merge(if_subst).merge(else_subst), if_type).into()
            }
            Self::Let { kind, defn, body } => kind.infer(defn, body, ctx),
            Self::Binop {
                op,
                box left,
                box right,
            } => op.infer(left, right, ctx),
            Self::Unop { op, box on } => op.infer(on, ctx),
            Self::Value(v) => v.infer(ctx),
            Self::Pair(box left, box right) => {
                let (left_subs, left_type) = left.infer_impl(ctx).into();
                let (right_subs, right_type) = right.infer_impl(ctx).into();
                (
                    left_subs.merge(right_subs),
                    Type::Product(box left_type, box right_type),
                )
                    .into()
            }
        };
        ctx.apply_to_all(&ret.subs);
        ret
    }
}

// global mutable state shouldn't be shared across threads (and so rust needs us to do this)
thread_local!(static COUNTER: std::cell::RefCell<usize> = 0.into());

/// Generate a fresh var identifier.
fn get_fresh_ident() -> usize {
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
        *c.borrow()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    mod infer {
        use super::*;
        use crate::{err::MlResult, parse::to_expn};

        macro_rules! infer_tests { ($($name:ident: $input:expr, $expected:expr)*) => {
            $(
                #[test]
                fn $name() -> MlResult<()> {
                    assert_eq!(to_expn($input)?.infer(), $expected);
                    Ok(())
                }
            )*
        }}

        infer_tests! {
            unit: "()", Type::Unit
            num: "3", Type::Int
            boolean: "true", Type::Bool
            plus: "3 + 4", Type::Int
            eq: "3 == 4", Type::Bool
            andalso: "true andalso false", Type::Bool
            not: "!true", Type::Bool
            not_eq: "!(3 == 4)", Type::Bool
            if_simple: "if true then 1 else 2", Type::Int
            if_complex: "if 1 == 2 then true else false", Type::Bool
            appl: "(fn x => true) 5", Type::Bool
            let_val: "let val x = 5 in 3 end", Type::Int
            let_val_bool: "let val x = 5 in true end", Type::Bool
            let_fun: "let fun foo x = 4 in foo true end", Type::Int
            fn_add: "fn x => x + x", Type::Arrow(box Type::Int, box Type::Int)
            fn_if: "fn x => if true then 2 else x + x", Type::Arrow(box Type::Int, box Type::Int)
            then_else_same_type: "fn x => if true then 2 else x", Type::Arrow(box Type::Int, box Type::Int)
            param_inference: "fn x => (x 3) + (x 3)", Type::Arrow(
                box Type::Arrow(box Type::Int, box Type::Int), box Type::Int
            )
            pair: "(3, true)", Type::Product(box Type::Int, box Type::Bool)

            // unfortunately relies on implementation details to check equivalence; in particular,
            // the fact that the first type var constructed has identifier `1` is a consequence of
            // the implementation of `get_fresh_ident`
            fn_simple: "fn x => true", Type::Arrow(box Type::Var(1), box Type::Bool)

            // lookup: "x", Type::Var(1)  // unbound var; should error
        }
    }

    mod free_vars {
        use super::*;

        macro_rules! free_vars_tests { ($($name:ident: $input:expr, $expected:expr)*) => {
            $(
                #[test]
                fn $name() {
                    let fvs = $input.free_vars();
                    assert_eq!(fvs, $expected.into());
                }
            )*
        }}

        free_vars_tests! {
            var: Type::Var(2), [2]
            unit: Type::Unit, []
            arrow_same: Type::Arrow(box Type::Var(4), box Type::Var(4)), [4]
            arrow_diff: Type::Arrow(box Type::Var(2), box Type::Var(4)), [2, 4]
        }
    }
}
