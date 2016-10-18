#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"
#include "atsparcc.hats"
#include "atsutils.hats"

staload "infer.sats"
staload "sexp.sats"
staload "list.sats"
staload "string.sats"
staload "stream.sats"
staload "set.sats"
staload "avl.sats"
staload "maybe.sats"

#define ::  ListCons
#define nil ListNil 

(******************************)

implement show_any<tvar> (v) = 
	case+ v of 
	| VarName v             => ignoret (show v)
	| VarIndex (mb, idx, n) => ignoret (show n; show "("; show<nat> mb; show "."; show<nat> idx; show ")")

implement show_any<tcst> (c) = 
	case+ c of 
	| CstInt n    => ignoret (show n)
	| CstBool b   => ignoret (show b)
	| CstString s => ignoret (show s)

implement show_any<term> (t) = let 
	implement show_sep<> () = show ""
	implement show<list(@(tvar,term))> (bindings: list (@(tvar, term))): void = 
		case+ bindings of 
		| nil () => show_end<> ()
		| binding :: nil () => ignoret (show binding.0; show "="; show binding.1; show_end<> ())
		| binding :: bindings => ignoret (show binding.0; show "="; show binding.1; show_sep<> (); show bindings)

in 
	case+ t of 
	| TMVar v             => ignoret (show "Var("; show v; show ")")
	| TMCst c             => ignoret (show "Cst("; show c; show ")")
	| TMLam (args, b)     => ignoret (show "Lam("; show args; show "=>"; show b; show ")")
	| TMLet (bindings, b) => ignoret (show "Let("; show bindings; show "=>"; show b; show ")")
	| TMFix (f, args, b)  => ignoret (show "Fix("; show f; show args; show b; show ")")
	| TMApp (f, args)     => ignoret (show "App("; show f; show "@"; show args; show ")")
	| TMIf (p, t, f)      => ignoret (show "If("; show p; show t; show f; show ")")
end

implement show_any<aterm> (t) = let 
	implement show_sep<> () = show ""
in 
	case+ t of 
	| ATMVar v         => ignoret (show "Var("; show v; show ")")
	| ATMCst c         => ignoret (show "Cst("; show c; show ")")
	| ATMLam b         => ignoret (show "Lam("; show b; show ")")
	| ATMLet (args, b) => ignoret (show "Let("; show args; show "=>"; show b; show ")")
	| ATMFix b         => ignoret (show "Fix("; show b; show ")")
	| ATMApp (f, args) => ignoret (show "App("; show f; show "@"; show args; show ")")
	| ATMIf (p, t, f)  => ignoret (show "If("; show p; show t; show f; show ")")
end

(******************************)

implement order_compare<tvar> (x, y) = 
	case+ (x, y) of 
	| (VarName x, VarName y) => cmp<string> (x, y)
	| (VarIndex (xmb, xidx, xn), VarIndex (ymb, yidx, yn)) => cmp<@(int,int,string)> (@(xmb, xidx, xn), @(ymb, yidx, yn))
	| (_, _) => order_compare_addr<tvar> (x, y) 

implement order_compare<tcst> (x, y) = 
	case+ (x, y) of 
	| (CstInt x, CstInt y)       => cmp<int> (x, y)
	| (CstBool x, CstBool y)     => cmp<bool> (x, y)
	| (CstString x, CstString y) => cmp<string> (x, y)
	| (_, _) => order_compare_addr (x, y)

implement order_compare<term> (x, y) = 
	case+ (x, y) of 
	| (TMVar vx, TMVar vy)                     => cmp<tvar> (vx, vy)
	| (TMCst cx, TMCst cy)                     => cmp<tcst> (cx, cy)
	| (TMLam (ax, bx), TMLam (ay, by))         => cmp<@(list(tvar),term)> (@(ax, bx), @(ay, by))
	| (TMLet (ax, bx), TMLet (ay, by))         => cmp<@(list(@(tvar,term)),term)> (@(ax, bx), @(ay, by))
	| (TMFix (ax, bx, cx), TMFix (ay, by, cy)) => cmp<@(list(tvar),term)> (@(ax :: bx, cx), @(ay :: by, cy))
	| (TMApp (ax, bx), TMApp (ay, by))         => cmp<list(term)> (ax :: bx, ay :: by)
	| (TMIf (ax, bx, cx) , TMIf (ay, by, cy))  => cmp<@(term,term,term)> (@(ax, bx, cx), @(ay, by, cy))
	| (_, _)                                   => order_compare_addr<term> (x, y)

implement order_compare<aterm> (x, y) = 
	case+ (x, y) of 
	| (ATMVar vx, ATMVar vy)                    => cmp<tvar> (vx, vy)
	| (ATMCst cx, ATMCst cy)                    => cmp<tcst> (cx, cy)
	| (ATMLam x, ATMLam y)                      => cmp<aterm> (x, y)
	| (ATMLet (ax, bx), ATMLet (ay, by))        => cmp<@(list(aterm),aterm)> (@(ax, bx), @(ay, by))
	| (ATMFix x, ATMFix y)                      => cmp<aterm> (x, y)
	| (ATMApp (ax, bx), ATMApp (ay, by))        => cmp<list(aterm)> (ax :: bx, ay :: by)
	| (ATMIf (ax, bx, cx) , ATMIf (ay, by, cy)) => cmp<@(aterm,aterm,aterm)> (@(ax, bx, cx), @(ay, by, cy))
	| (_, _)                                    => order_compare_addr<aterm> (x, y)

(******************************)

implement parse_term (sexp) = let 
	fun pcst (sexp: sexp): term = 
		case- sexp of 
		| SString s => TMCst (CstString s)
		| SInt n    => TMCst (CstInt n)
		| SBool b   => TMCst (CstBool b)

	and ptvar (sexp: sexp): tvar = 
		case- sexp of 
		| SSymbol s => VarName s

	and pvar (sexp: sexp): term = 
		TMVar (ptvar sexp)

	and plam (sexp: sexp): term = 
		case- sexp of 
		| SList (SSymbol "lam" :: SList args :: body :: nil ()) => 
			TMLam (args \map (lam s =<cloref1> ptvar s), pterm body)

	and pbinding (sexp: sexp): @(tvar, term) = 
		case- sexp of 
		| SList (SSymbol v :: t :: nil ()) => @(VarName v, pterm t)

	and plet (sexp: sexp): term = 
		case- sexp of 
		| SList (SSymbol "let" :: SList bindings :: body :: nil ()) => 
			TMLet (bindings \map (lam b =<cloref1> pbinding b), pterm body)

	and pfix (sexp: sexp): term = 
		case- sexp of 
		| SList (SSymbol "fix" :: SSymbol f :: SList args :: body :: nil ()) => 
			TMFix (VarName f, args \map (lam arg =<cloref1> ptvar arg), pterm body)

	and papp (sexp: sexp): term = 
		case- sexp of 
		| (SList (f :: body)) => 
			TMApp (pterm f, body \map (lam t =<cloref1> pterm t))

	and pif (sexp: sexp): term = 
		case- sexp of 
		| SList (SSymbol "if" :: p :: t :: f :: nil ()) => 
			TMIf (pterm p, pterm t, pterm f)

	and pterm (sexp: sexp): term = 
		case- sexp of 
		| SString _                  => pcst sexp
		| SInt _                     => pcst sexp
		| SBool _                    => pcst sexp
		| SSymbol _                  => pvar sexp
		| SList (SSymbol "lam" :: _) => plam sexp
		| SList (SSymbol "let" :: _) => plet sexp
		| SList (SSymbol "if" :: _)  => pif sexp
		| SList (SSymbol "fix" :: _) => pfix sexp
		| SList (t :: nil ())        => pterm t
		| SList (ts) when len ts > 1 => papp sexp
in 
	pterm sexp
end 

(******************************)

implement aterm_open (t, xs) = let 
	(* this is the "open with term" operation described in Arthur Chargueraud's Locally Nameless Rep *)
	fun open (t: aterm, mbinder: nat, xs: list aterm): aterm = 
		case+ t of 
		| ATMVar (VarIndex (mb, idx, name)) when mb \eq<nat> mbinder => xs[idx]
		| ATMApp (f, args) => ATMApp (open (f, mbinder, xs), args \map (lam arg =<cloref1> open (arg, mbinder, xs)))
		| ATMLam b         => ATMLam (open (b, mbinder + 1, xs))
		| ATMFix b         => ATMFix (open (b, mbinder + 1, xs))
		| ATMLet (args, b) => ATMLet (args \map (lam arg =<cloref1> open (arg, mbinder, xs)), open (b, mbinder + 1, xs))
		| ATMIf (p, t, f)  => ATMIf  (open (p, mbinder, xs), open (t, mbinder, xs), open (f, mbinder, xs))
		| _                => t 

in
	open (t, 0, xs)
end 

implement aterm_close (t, xs) = let 
	fun close (t: aterm, xs: list tvar, mbinder: nat): aterm =
		case+ t of 
		| ATMVar (VarName x) => 
			(case+ find (xs, VarName x) of 
			| Just idx   => ATMVar (VarIndex (mbinder, idx, x))
			| Nothing () => t 
			)
		| ATMApp (f, args) => ATMApp (close (f, xs, mbinder), args \map (lam arg =<cloref1> close (arg, xs, mbinder)))
		| ATMLam b         => ATMLam (close (b, xs, mbinder + 1))
		| ATMFix b         => ATMFix (close (b, xs, mbinder + 1))
		| ATMLet (args, b) => ATMLet (args \map (lam arg =<cloref1> close (arg, xs, mbinder)), close (b, xs, mbinder + 1))
		| ATMIf (p, t, f)  => ATMIf (close (p, xs, mbinder), close (t, xs, mbinder), close (f, xs, mbinder))
		| _                => t 
in 
	close (t, xs, 0)
end

implement term_alpha (term) = let 

	typedef tybind = @(tvar, term)

	fun normalize (t: term): aterm = 
		case+ t of 
		| TMVar v             => ATMVar v
		| TMCst c             => ATMCst c
		| TMLam (args, b)     => ATMLam (aterm_close (normalize b, args))
		| TMFix (f, args, b)  => ATMFix (aterm_close (normalize b, f :: args))
		| TMLet (bindings, b) => ATMLet (bindings \map (lam (x:tybind):aterm =<cloref1> normalize x.1), 
										 aterm_close (normalize b, bindings \map<tybind,tvar> (lam (x:tybind) =<cloref1> x.0)))
		| TMApp (f, args)     => ATMApp (normalize f, args \map (lam arg =<cloref1> normalize arg))
		| TMIf (p, t, f)      => ATMIf (normalize p, normalize t, normalize f)

in 
	normalize term 
end