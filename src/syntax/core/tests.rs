use codespan::{CodeMap, FileName};
use nameless::FreshState;

use syntax::parse;
use syntax::translation::ToCore;

use super::*;

fn parse(fresh: &mut FreshState, src: &str) -> RcRawTerm {
    let mut codemap = CodeMap::new();
    let filemap = codemap.add_filemap(FileName::virtual_("test"), src.into());

    let (concrete_term, errors) = parse::term(&filemap);
    assert!(errors.is_empty());

    concrete_term.to_core(fresh)
}

mod alpha_eq {
    use super::*;

    #[test]
    fn var() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(parse(&mut fresh, r"x"), parse(&mut fresh, r"x"));
    }

    #[test]
    #[should_panic]
    fn var_diff() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(parse(&mut fresh, r"x"), parse(&mut fresh, r"y"));
    }

    #[test]
    fn ty() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(parse(&mut fresh, r"Type"), parse(&mut fresh, r"Type"));
    }

    #[test]
    fn lam() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(
            parse(&mut fresh, r"\x : Type => x"),
            parse(&mut fresh, r"\a : Type => a")
        );
    }

    #[test]
    fn pi() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(
            parse(&mut fresh, r"(x : Type) -> x"),
            parse(&mut fresh, r"(a : Type) -> a")
        );
    }

    #[test]
    fn lam_app() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(
            parse(&mut fresh, r"\x : Type -> Type => x Type"),
            parse(&mut fresh, r"\a : Type -> Type => a Type")
        );
    }

    #[test]
    fn pi_app() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(
            parse(&mut fresh, r"(x : Type -> Type) -> x Type"),
            parse(&mut fresh, r"(a : Type -> Type) -> a Type")
        );
    }

    #[test]
    fn lam_lam_app() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(
            parse(&mut fresh, r"\x : Type -> Type => \y : Type => x y"),
            parse(&mut fresh, r"\a : Type -> Type => \b : Type => a b"),
        );
    }

    #[test]
    fn pi_pi_app() {
        let mut fresh = FreshState::new();

        assert_alpha_eq!(
            parse(&mut fresh, r"(x : Type -> Type) -> (y : Type) -> x y"),
            parse(&mut fresh, r"(a : Type -> Type) -> (b : Type) -> a b"),
        );
    }
}
