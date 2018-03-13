use codespan::{ByteIndex, CodeMap, FileName};

use syntax::core::SourceMeta;
use syntax::translation::ToCore;
use syntax::parse;

use super::*;

fn parse(fresh: &mut FreshState, src: &str) -> RcRawTerm {
    let mut codemap = CodeMap::new();
    let filemap = codemap.add_filemap(FileName::virtual_("test"), src.into());
    let (concrete_term, errors) = parse::term(&filemap);
    assert!(errors.is_empty());

    concrete_term.to_core(fresh)
}

fn parse_infer(fresh: &mut FreshState, src: &str) -> RcTerm {
    let expr = parse(fresh, src);
    infer(fresh, &Context::new(), &expr).unwrap().0
}

mod normalize {
    use super::*;

    #[test]
    fn var() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let var = Term::Var(SourceMeta::default(), Var::Free(Name::user("x"))).into();

        assert_eq!(
            normalize(&mut fresh, &context, &var),
            Err(InternalError::UndefinedName {
                var_span: ByteSpan::default(),
                name: Name::user("x"),
            }),
        );
    }

    #[test]
    fn ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = parse_infer(&mut fresh, r"Type");

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            Value::Universe(Level::ZERO).into()
        );
    }

    #[test]
    fn lam() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = parse_infer(&mut fresh, r"\x : Type => x");

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            Value::Lam(Scope::bind(
                Named::new(Name::user("x"), Value::Universe(Level::ZERO).into()),
                Neutral::Var(Var::Free(Name::user("x"))).into(),
            )).into(),
        );
    }

    #[test]
    fn pi() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = parse_infer(&mut fresh, r"(x : Type) -> x");

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            Value::Pi(Scope::bind(
                Named::new(Name::user("x"), Value::Universe(Level::ZERO).into()),
                Neutral::Var(Var::Free(Name::user("x"))).into(),
            )).into(),
        );
    }

    #[test]
    fn lam_app() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = parse_infer(&mut fresh, r"\(x : Type -> Type) (y : Type) => x y");

        let x = Name::user("x");
        let y = Name::user("y");
        let ty_arr: RcValue = Value::Pi(Scope::bind(
            Named::new(Name::user("_"), Value::Universe(Level::ZERO).into()),
            Value::Universe(Level::ZERO).into(),
        )).into();

        assert_alpha_eq!(
            normalize(
                &mut fresh,
                &context,
                &given_expr,
            ).unwrap(),
            Value::Lam(Scope::bind(
                Named::new(x.clone(), ty_arr),
                Value::Lam(Scope::bind(
                    Named::new(y.clone(), Value::Universe(Level::ZERO).into()),
                    Neutral::App(
                        Neutral::Var(Var::Free(x)).into(),
                        Term::Var(SourceMeta::default(), Var::Free(y)).into(),
                    ).into(),
                )).into(),
            )).into(),
        );
    }

    #[test]
    fn pi_app() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = parse_infer(&mut fresh, r"(x : Type -> Type) -> (y : Type) -> x y");

        let x = Name::user("x");
        let y = Name::user("y");
        let ty_arr: RcValue = Value::Pi(Scope::bind(
            Named::new(Name::user("_"), Value::Universe(Level::ZERO).into()),
            Value::Universe(Level::ZERO).into(),
        )).into();

        assert_alpha_eq!(
            normalize(
                &mut fresh,
                &context,
                &given_expr,
            ).unwrap(),
            Value::Pi(Scope::bind(
                Named::new(x.clone(), ty_arr),
                Value::Pi(Scope::bind(
                    Named::new(y.clone(), Value::Universe(Level::ZERO).into()),
                    Neutral::App(
                        Neutral::Var(Var::Free(x)).into(),
                        Term::Var(SourceMeta::default(), Var::Free(y)).into(),
                    ).into(),
                )).into(),
            )).into(),
        );
    }

    // Passing `Type` to the polymorphic identity function should yeild the type
    // identity function
    #[test]
    fn id_app_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"(\(a : Type 1) (x : a) => x) Type";
        let expected_expr = r"\x : Type => x";

        let given_expr = parse_infer(&mut fresh, given_expr);
        let expected_expr = parse_infer(&mut fresh, expected_expr);

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }

    // Passing `Type` to the `Type` identity function should yeild `Type`
    #[test]
    fn id_app_ty_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"(\(a : Type 2) (x : a) => x) (Type 1) Type";
        let expected_expr = r"Type";

        let given_expr = parse_infer(&mut fresh, given_expr);
        let expected_expr = parse_infer(&mut fresh, expected_expr);

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }

    // Passing `Type -> Type` to the `Type` identity function should yeild
    // `Type -> Type`
    #[test]
    fn id_app_ty_arr_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"(\(a : Type 2) (x : a) => x) (Type 1) (Type -> Type)";
        let expected_expr = r"Type -> Type";

        let given_expr = parse_infer(&mut fresh, given_expr);
        let expected_expr = parse_infer(&mut fresh, expected_expr);

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }

    // Passing the id function to itself should yield the id function
    #[test]
    fn id_app_id() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"
            (\(a : Type 1) (x : a) => x)
                ((a : Type) -> a -> a)
                (\(a : Type) (x : a) => x)
        ";
        let expected_expr = r"\(a : Type) (x : a) => x";

        let given_expr = parse_infer(&mut fresh, given_expr);
        let expected_expr = parse_infer(&mut fresh, expected_expr);

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }

    // Passing the id function to the 'const' combinator should yeild a
    // function that always returns the id function
    #[test]
    fn const_app_id_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"
            (\(a : Type 1) (b : Type 2) (x : a) (y : b) => x)
                ((a : Type) -> a -> a)
                (Type 1)
                (\(a : Type) (x : a) => x)
                Type
        ";
        let expected_expr = r"\(a : Type) (x : a) => x";

        let given_expr = parse_infer(&mut fresh, given_expr);
        let expected_expr = parse_infer(&mut fresh, expected_expr);

        assert_alpha_eq!(
            normalize(&mut fresh, &context, &given_expr).unwrap(),
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }
}

mod infer {
    use super::*;

    #[test]
    fn free() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = parse(&mut fresh, r"x");

        assert_eq!(
            infer(&mut fresh, &context, &given_expr),
            Err(TypeError::UndefinedName {
                var_span: ByteSpan::new(ByteIndex(1), ByteIndex(2)),
                name: Name::user("x"),
            }),
        );
    }

    #[test]
    fn ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type 1";
        let given_expr = r"Type";

        let expected_ty = parse_infer(&mut fresh, expected_ty);
        let given_expr = parse(&mut fresh, given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn ty_levels() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type 1";
        let given_expr = r"Type 0 : Type 1 : Type 2 : Type 3";

        let expected_ty = parse_infer(&mut fresh, expected_ty);
        let given_expr = parse(&mut fresh, given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn ann_ty_id() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type -> Type";
        let given_expr = r"(\a => a) : Type -> Type";

        let expected_ty = parse_infer(&mut fresh, expected_ty);
        let given_expr = parse(&mut fresh, given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn ann_arrow_ty_id() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(Type -> Type) -> (Type -> Type)";
        let given_expr = r"(\a => a) : (Type -> Type) -> (Type -> Type)";

        let expected_ty = parse_infer(&mut fresh, expected_ty);
        let given_expr = parse(&mut fresh, given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn ann_id_as_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"(\a => a) : Type";

        let given_expr = parse(&mut fresh, given_expr);

        match infer(&mut fresh, &context, &given_expr) {
            Err(TypeError::UnexpectedFunction { .. }) => {},
            other => panic!("unexpected result: {:#?}", other),
        }
    }

    #[test]
    fn app() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type 1";
        let given_expr = r"(\a : Type 1 => a) Type";

        let expected_ty = parse_infer(&mut fresh, expected_ty);
        let given_expr = parse(&mut fresh, given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn app_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let given_expr = r"Type Type";

        let given_expr = parse(&mut fresh, given_expr);

        assert_eq!(
            infer(&mut fresh, &context, &given_expr),
            Err(TypeError::ArgAppliedToNonFunction {
                fn_span: ByteSpan::new(ByteIndex(1), ByteIndex(5)),
                arg_span: ByteSpan::new(ByteIndex(6), ByteIndex(10)),
                found: Value::Universe(Level::ZERO.succ()).into(),
            }),
        )
    }

    #[test]
    fn lam() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a : Type) -> Type";
        let given_expr = r"\a : Type => a";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn pi() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type 1";
        let given_expr = r"(a : Type) -> a";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn id() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a : Type) -> a -> a";
        let given_expr = r"\(a : Type) (x : a) => x";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn id_ann() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a : Type) -> a -> a";
        let given_expr = r"(\a (x : a) => x) : (A : Type) -> A -> A";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    // Passing `Type` to the polymorphic identity function should yeild the type
    // identity function
    #[test]
    fn id_app_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_expr = r"Type -> Type";
        let given_expr = r"(\(a : Type 1) (x : a) => x) Type";

        let expected_expr = parse_infer(&mut fresh, &expected_expr);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }

    // Passing `Type` to the `Type` identity function should yeild `Type`
    #[test]
    fn id_app_ty_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_expr = r"Type 1";
        let given_expr = r"(\(a : Type 2) (x : a) => x) (Type 1) Type";

        let expected_expr = parse_infer(&mut fresh, &expected_expr);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_expr).unwrap(),
        );
    }

    #[test]
    fn id_app_ty_arr_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type 1";
        let given_expr = r"(\(a : Type 2) (x : a) => x) (Type 1) (Type -> Type)";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn id_app_arr_pi_ty() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"Type -> Type";
        let given_expr = r"(\(a : Type 1) (x : a) => x) (Type -> Type) (\x => x)";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn apply() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a b : Type) -> (a -> b) -> a -> b";
        let given_expr = r"\(a b : Type) (f : a -> b) (x : a) => f x";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn const_() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a b : Type) -> a -> b -> a";
        let given_expr = r"\(a b : Type) (x : a) (y : b) => x";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn const_flipped() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a b : Type) -> a -> b -> b";
        let given_expr = r"\(a b : Type) (x : a) (y : b) => y";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn flip() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a b c : Type) -> (a -> b -> c) -> (b -> a -> c)";
        let given_expr = r"\(a b c : Type) (f : a -> b -> c) (y : b) (x : a) => f x y";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    #[test]
    fn compose() {
        let mut fresh = FreshState::new();
        let context = Context::new();

        let expected_ty = r"(a b c : Type) -> (b -> c) -> (a -> b) -> (a -> c)";
        let given_expr = r"\(a b c : Type) (f : b -> c) (g : a -> b) (x : a) => f (g x)";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

        assert_alpha_eq!(
            infer(&mut fresh, &context, &given_expr).unwrap().1,
            normalize(&mut fresh, &context, &expected_ty).unwrap(),
        );
    }

    mod church_encodings {
        use super::*;

        #[test]
        fn and() {
            let mut fresh = FreshState::new();
            let context = Context::new();

            let expected_ty = r"Type -> Type -> Type 1";
            let given_expr = r"\(p q : Type) => (c : Type) -> (p -> q -> c) -> c";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

            assert_alpha_eq!(
                infer(&mut fresh, &context, &given_expr).unwrap().1,
                normalize(&mut fresh, &context, &expected_ty).unwrap(),
            );
        }

        #[test]
        fn and_intro() {
            let mut fresh = FreshState::new();
            let context = Context::new();

            let expected_ty = r"
                (p q : Type) -> p -> q ->
                    ((c : Type) -> (p -> q -> c) -> c)
            ";
            let given_expr = r"
                \(p q : Type) (x : p) (y : q) =>
                    \c : Type => \f : (p -> q -> c) => f x y
            ";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

            assert_alpha_eq!(
                infer(&mut fresh, &context, &given_expr).unwrap().1,
                normalize(&mut fresh, &context, &expected_ty).unwrap(),
            );
        }

        #[test]
        fn and_proj_left() {
            let mut fresh = FreshState::new();
            let context = Context::new();

            let expected_ty = r"
                (p q : Type) ->
                    ((c : Type) -> (p -> q -> c) -> c) -> p
            ";
            let given_expr = r"
                \(p q : Type) (pq : (c : Type) -> (p -> q -> c) -> c) =>
                    pq p (\x y => x)
            ";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

            assert_alpha_eq!(
                infer(&mut fresh, &context, &given_expr).unwrap().1,
                normalize(&mut fresh, &context, &expected_ty).unwrap(),
            );
        }

        #[test]
        fn and_proj_right() {
            let mut fresh = FreshState::new();
            let context = Context::new();

            let expected_ty = r"
                (p q : Type) -> ((c : Type) -> (p -> q -> c) -> c) -> q
            ";
            let given_expr = r"
                \(p q : Type) (pq : (c : Type) -> (p -> q -> c) -> c) =>
                    pq q (\x y => y)
            ";

        let expected_ty = parse_infer(&mut fresh, &expected_ty);
        let given_expr = parse(&mut fresh, &given_expr);

            assert_alpha_eq!(
                infer(&mut fresh, &context, &given_expr).unwrap().1,
                normalize(&mut fresh, &context, &expected_ty).unwrap(),
            );
        }
    }
}

mod check_module {
    use library;
    use codespan_reporting;

    use super::*;

    #[test]
    fn check_prelude() {
        let mut codemap = CodeMap::new();
        let mut fresh = FreshState::new();
        let filemap = codemap.add_filemap(FileName::virtual_("test"), library::PRELUDE.into());

        let (concrete_module, errors) = parse::module(&filemap);
        assert!(errors.is_empty());

        let module = concrete_module.to_core(&mut fresh);
        if let Err(err) = check_module(&mut fresh, &module) {
            codespan_reporting::emit(&codemap, &err.to_diagnostic());
            panic!("type error!")
        }
    }
}
