#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"
#include "atsparcc.hats"
#include "atsutils.hats"

staload "untyped.sats"
staload "sexp.sats"
staload "string.sats"
staload "list.sats"
staload "stream.sats"
staload "set.sats"
staload "avl.sats"
staload "maybe.sats"

#define ::  ListCons
#define nil ListNil

//#define NONE 0
//#define REDEX 1
//#define TRACK 2

(******************************)

implement show_any<tvar> (tvar) = 
	case+ tvar of 
	| VarName v => ignoret (show v)
	| VarIndex v => ignoret (show v)

implement show_any<term> (term) = 
	case+ term of 
	| TMVar v        => ignoret (show "TMVar("; show v; show ")")
	| TMLam (v, t)   => ignoret (show "TMLam("; show v; show "."; show t; show ")")
	| TMApp (t1, t2) => ignoret (show "TMApp("; show t1; show "("; show t2; show "))")

implement show_any<aterm> (term) = 
	case+ term of 
//	| ATVar v        => ignoret (show "ATVar("; show v; show ")")
//	| ATLam t        => ignoret (show "ATLam("; show t; show ")")
//	| ATApp (t1, t2) => ignoret (show "ATApp("; show t1; show "("; show t2; show "))")
	| ATVar v        => ignoret (show v)
	| ATLam t        => ignoret (show "\\."; show t)
	| ATApp (t1, t2) => ignoret (show "("; show t1; show " "; show t2; show ")")


implement show_any<cterm> (term) = let 
	overload + with string_concat 

	val red: string = "\033[31m" 
	val blue: string = "\033[34m"
	val off: string = "\033[0m"

in 
	case+ term of 
//	| CTVar v           => ignoret (show "CTVar("; show v; show ")")
//	| CTLam t           => ignoret (show "CTLam("; show t; show ")")
//	| CTApp (t1, t2, c) => 
//		ifcase 
//		| c = 0 => ignoret (show "CTApp("; show t1; show "("; show t2; show "))")
//		| c = 1 => ignoret (show red; show "CTApp("; show t1; show "("; show t2; show "))"; show off)
//		| c = 2 => ignoret (show blue; show "CTApp("; show t1; show "("; show t2; show "))"; show off)
	| CTVar v           => ignoret (show v)
	| CTLam t           => ignoret (show "\\."; show t)
	| CTApp (t1, t2, c) => 
		ifcase 
		| c = 0 => ignoret (show "("; show t1; show " "; show t2; show ")")
		| c = 1 => ignoret (show red; show "("; show off; show t1; show " "; show t2; show red; show ")"; show off)
		| c = 2 => ignoret (show blue; show "("; show off; show t1; show " "; show t2; show blue; show ")"; show off)

end


(******************************)

implement order_compare<tvar> (a, b) = 
	case+ (a, b) of 
	| (VarName x, VarName y)   => cmp<string> (x, y)
	| (VarIndex x, VarIndex y) => cmp<int> ($UNSAFE.cast{int} x, $UNSAFE.cast{int} y)
	| (_, _)                   => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b) // address

 
implement order_compare<term> (a, b) = 
	case+ (a, b) of 
	| (TMVar a, TMVar b)               => cmp (a, b)
	| (TMLam (a, ta), TMLam (b, tb))   => if cmp (a, b) != 0 then cmp (a, b) else cmp (ta, tb)
	| (TMApp (a1, a2), TMApp (b1, b2)) => if cmp (a1, b1) != 0 then cmp (a1, b1) else cmp (a2, b2)
	| (_, _)                           => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b) // address

implement order_compare<aterm> (a, b) =
	case+ (a, b) of 
	| (ATVar a, ATVar b)               => cmp (a, b)
	| (ATLam a, ATLam b)               => cmp (a, b)
	| (ATApp (a1, a2), ATApp (b1, b2)) => if cmp (a1, b1) != 0 then cmp (a1, b1) else cmp (a2, b2)
	| (_, _)                           => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b) // address

implement order_compare<cterm> (a, b) =
	case+ (a, b) of 
	| (CTVar a, CTVar b)                       => cmp (a, b)
	| (CTLam a, CTLam b)                       => cmp (a, b)
	| (CTApp (a1, a2, ac), CTApp (b1, b2, bc)) => if cmp (a1, b1) != 0 then cmp (a1, b1) else if cmp (a2, b2) != 0 then cmp (a2, b2) else cmp (ac, bc)
	| (_, _)                                   => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b) // address

(******************************)

implement parse_term (sexp) = let 
	fun parse_var (sexp: sexp): term = 
		case+ sexp of 
		| SSymbol s                   => TMVar (VarName s)
		| SString s                   => TMVar (VarName s)
		| SInt s                      => TMVar (VarName (string_from_int s))
		| SBool s                     => TMVar (VarName (if s then "true" else "false"))
//		| SList (SSymbol s :: nil ()) => TMVar (VarName s)
		| SList _                     => $raise LamParsingException ("parse_var") 

	fun parse_lam (sexp: sexp): term = 
		case+ sexp of 
		| SList (SSymbol k :: SSymbol v :: b :: nil ()) when k = "lam" => TMLam (VarName v, parse_term b)
		| _ =>> $raise LamParsingException ("parse_lam")

	fun parse_app (sexp: sexp): term = 
		case+ sexp of 
		| SList (a :: b :: nil ()) => TMApp (parse_term a, parse_term b)
		| _ =>> $raise LamParsingException ("parse_app")

in 
	case+ sexp of 
	| SList (SSymbol "lam" :: _)      =>  parse_lam sexp 
	| SList (xs) when list_len xs > 1 =>> parse_app sexp 
	| SList (x :: nil ())             =>> parse_term x
	| _                               =>> parse_var sexp                               
end

//implement parse_term_string (str) = 

(******************************)

implement term_size (t) = 
	case+ t of 
	| TMVar _        => 0
	| TMLam (_, t)   => 1 + term_size t
	| TMApp (t1, t2) => 1 + term_size t1 + term_size t2

implement term_subterm (t, p) = 
	case+ p of 
	| nil _   => t 
	| p :: ps => 
		case+ t of 
		| TMLam (_, t)  when p = 0 =>  term_subterm (t, ps)
		| TMApp (t1, _) when p = 0 =>  term_subterm (t1, ps)
		| TMApp (_, t2) when p = 1 =>  term_subterm (t2, ps)
		| _                        =>> $raise PathException ()

implement term_paths (t) = 
	case+ t of 
	| TMVar _                   => set_insert (set_make (), nil ())
	| TMLam (_, t)              => set_insert ((term_paths t) \set_map (lam p => 0 :: p), nil ())
	| TMApp (t1, t2)            =>
		set_insert (
			((term_paths t1) \set_map (lam p => 0 :: p)) 
				\set_union ((term_paths t2) \set_map (lam p => 1 :: p)),
			nil ())

implement term_freevars (t) = 
	case+ t of 
	| TMVar v        => set_insert (set_make (), v)
	| TMLam (v, t)   => set_delete (term_freevars t, v)
	| TMApp (t1, t2) => set_union  (term_freevars t1, term_freevars t2)

implement term_alpha (t) = let 
	(*
		S = \x.\y.\z.(x z)(y z)
		  = \.\.\.(2 0)(1 0)

		The environment is a stack, newly defined names will hide previous binding.
	*)

	fun normalize (env: list tvar, t: term): aterm =
		case+ t of 
		| TMVar v        =>
			(case+ list_find (env, v) of 
			| Nothing () => ATVar v
			| Just i     => ATVar (VarIndex i))
		| TMLam (v, t)   => ATLam (normalize (v :: env, t))
		| TMApp (t1, t2) => ATApp (normalize (env, t1), normalize (env, t2))

in 
	normalize (nil (), t)
end

(******************************)

implement aterm_shift (t, sh) = let 
	(*
		The function shift free indicies. 
		Cutoff is used to track how many lambdas so far, to 
		make sure bound indicies are not shifted. 
	*)

	fun shift (t: aterm, sh: int, lams: nat): aterm = 
		case+ t of 
		| ATVar (VarIndex x) => if x >= lams then ATVar (VarIndex (x + sh)) else t
		| ATVar _            => t
		| ATLam t            => ATLam (shift (t, sh, lams + 1))
		| ATApp (t1, t2)     => ATApp (shift (t1, sh, lams), shift (t2, sh, lams))
in 
	shift (t, sh, 0)
end
 
implement aterm_subst (t, sub) = let 
	(*
		The function does t[x -> sub].

		In the lambda case, 

		(\.t)[x -> sub] = \.t[x+1 -> shift(sub,1)]

		x => x+1 since the variable being replaced should be pointing to the same binder
		shift(sub,1) since the free variable should be pointing to the same binder
	*)

	fun subst (t: aterm, x: int, sub: aterm): aterm = 
		case+ t of 
		| ATVar (VarIndex v) => if v = x then sub else t
		| ATVar (VarName v)  => t
		| ATApp (t1, t2)     => ATApp (subst (t1, x, sub), subst (t2, x, sub))
		| ATLam (t)          => ATLam (subst (t, x+1, aterm_shift (sub, 1)))
in 
	subst (t, 0, sub)
end

implement aterm_subterm (t, p) =
	case+ p of 
	| nil ()  => t 
	| p :: ps => 
		case+ t of 
		| ATLam t      when p = 0 => aterm_subterm (t, ps)
		| ATApp (t, _) when p = 0 => aterm_subterm (t, ps)
		| ATApp (_, t) when p = 1 => aterm_subterm (t, ps)
		| _                       =>> $raise PathException ()

implement aterm_beta_redexes (t) = let 
	val f = lam t => aterm_beta_redexes t
in 
	case+ t of 
	| ATApp (ATLam t1, t2) =>  
		insert (((f t1) \map (lam p =<cloref1> 0 :: 0 :: p)) \set_union ((f t2) \map (lam p =<cloref1> 1 :: p)), nil ())
	| ATApp (t1, t2) => 
		((f t1) \map (lam p =<cloref1> 0 :: p)) \set_union ((f t2) \map (lam p =<cloref1> 1 :: p))
	| ATLam t => (f t) \map (lam p =<cloref1> 0 :: p)
	| ATVar _ => set_make ()
end

implement aterm_beta_reduce (t, p) = 
	(*
		In (\.t1)(t2), after substitution, there is one less lambda. 
		Free vars in t1 need to be shifted down by one 
		to refer to the same original lambdas in the context.
		Therefore, free vars in t2 need to be shifted up by one 
		beforehand. 
	*)

	case+ (t, p) of 
	(* top reduction *)
	| (ATApp (ATLam t1, t2), nil ()) => Just (aterm_shift (aterm_subst (t1, aterm_shift (t2, 1)), ~1))
	(* non-top reduction *)
	| (ATApp (t1, t2), 0 :: ps)      => maybe_bind (aterm_beta_reduce (t1, ps), lam t => ATApp (t, t2))
	| (ATApp (t1, t2), 1 :: ps)      => maybe_bind (aterm_beta_reduce (t2, ps), lam t => ATApp (t1, t))
	| (ATLam t, 0 :: ps)             => maybe_bind (aterm_beta_reduce (t, ps), lam t => ATLam t)
	(* no reduction *)
	| (_, _) =>> Nothing ()


//implement aterm_residual (t, redex, sub) = let 

//	fun cterm_collect (t: cterm, c: int): set path = 
//		case+ t of 
//		| CTApp (t1, t2, cc) => 
//			let 
//				val p1 = cterm_collect (t1, c) \set_map (lam p => 0 :: p)
//				val p2 = cterm_collect (t2, c) \set_map (lam p => 1 :: p)
//			in 
//				if cc = c 
//				then set_insert (p1 \set_union p2, nil ())
//				else p1 \set_union p2
//			end
//		| CTLam t => cterm_collect (t, c) \set_map (lam p => 0 :: p)
//		| CTVar _ => set_make ()


//	val marked = mark (mark (aterm_colorize t, sub, TRACK), redex, REDEX)

//	val _ = show t 
//	val _ = show ()
//	val _ = show marked 
//	val _ = show ()

//	val- Just reduced = cterm_beta_reduce (marked, redex)

//	val _ = show reduced 
//	val _ = show ()
//in 
//	cterm_collect (reduced, TRACK)
//end 

implement aterm_colorize (t) = 
	case+ t of 
	| ATVar v        => CTVar v
	| ATLam t        => CTLam (aterm_colorize t)
	| ATApp (t1, t2) => CTApp (aterm_colorize t1, aterm_colorize t2, 0)


implement cterm_mark (t, p, c) = 
	case+ (t, p) of 
	| (CTApp (CTLam t1, t2, _), nil ()) => CTApp (CTLam t1, t2, c)
	| (CTApp (t1, t2, cc), 0 :: ps) => CTApp (cterm_mark (t1, ps, c), t2, cc)
	| (CTApp (t1, t2, cc), 1 :: ps) => CTApp (t1, cterm_mark (t2, ps, c), cc)
	| (CTLam t, 0 :: ps) => CTLam (cterm_mark (t, ps, c))
	| (_, _) =>> $raise PathException ()

implement cterm_markall (t, ps, c) = let 
	val tt = ref<cterm> t 
	val _ = foreach (ps, lam p =<cloref1> !tt := cterm_mark (!tt, p, c))
in 
	!tt
end 

implement cterm_shift (t, sh) = let 
	fun shift (t: cterm, sh: int, lams: nat): cterm = 
		case+ t of 
		| CTVar (VarIndex x) => if x >= lams then CTVar (VarIndex (x + sh)) else t
		| CTVar _            => t
		| CTLam t            => CTLam (shift (t, sh, lams + 1))
		| CTApp (t1, t2, c)  => CTApp (shift (t1, sh, lams), shift (t2, sh, lams), c)
in 
	shift (t, sh, 0)
end

implement cterm_subst (t, sub) = let 
	fun subst (t: cterm, x: int, sub: cterm): cterm = 
		case+ t of 
		| CTVar (VarIndex v) => if v = x then sub else t
		| CTVar (VarName v)  => t
		| CTApp (t1, t2, c)  => CTApp (subst (t1, x, sub), subst (t2, x, sub), c)
		| CTLam (t)          => CTLam (subst (t, x+1, cterm_shift (sub, 1)))
in 
	subst (t, 0, sub)
end

//implement cterm_beta_reduce (t, p) = 
//	case+ (t, p) of 
//	| (CTApp (CTLam t1, t2, REDEX), nil ()) => Just (cterm_shift (cterm_subst (t1, cterm_shift (t2, 1)), ~1))
//	| (CTApp (t1, t2, c), 0 :: ps)          => maybe_bind (cterm_beta_reduce (t1, ps), lam t => CTApp (t, t2, c))
//	| (CTApp (t1, t2, c), 1 :: ps)          => maybe_bind (cterm_beta_reduce (t2, ps), lam t => CTApp (t1, t, c))
//	| (CTLam t, 0 :: ps)                    => maybe_bind (cterm_beta_reduce (t, ps), lam t => CTLam t)
//	| (_, _) =>> Nothing ()

implement cterm_develop (t, c) = let 
	fun reduce (t: cterm): cterm = 
		case+ t of 
		| CTApp (CTLam t1, t2, cc) when cc = c => reduce (cterm_shift (cterm_subst (t1, cterm_shift (t2, 1)), ~1))
		| CTApp (t1, t2, cc)                   => CTApp (reduce t1, reduce t2, cc)
		| CTLam t                              => CTLam (reduce t)
		| _                                    =>> t
in 
	reduce t
end 

implement cterm_church_rosser (t, pa, pb) = let 

	#define REDUCE 1 
	#define TRACK 2
	
	val t_pa = cterm_markall (cterm_markall (t, pb, TRACK), pa, REDUCE)
	val t_pa = cterm_develop (t_pa, REDUCE)

	val t_pb = cterm_markall (cterm_markall (t, pa, TRACK), pb, REDUCE)
	val t_pb = cterm_develop (t_pb, REDUCE)

	val _ = show "T => T1: "
	val _ = show t_pa 
	val _ = show ()
	val _ = show "T => T2: "
	val _ = show t_pb 
	val _ = show ()

	fun cterm_collect (t: cterm, c: int): set path = 
		case+ t of 
		| CTApp (t1, t2, cc) => 
			let 
				val p1 = cterm_collect (t1, c) \set_map (lam p => 0 :: p)
				val p2 = cterm_collect (t2, c) \set_map (lam p => 1 :: p)
			in 
				if cc = c 
				then set_insert (p1 \set_union p2, nil ())
				else p1 \set_union p2
			end
		| CTLam t => cterm_collect (t, c) \set_map (lam p => 0 :: p)
		| CTVar _ => set_make ()

	val _ = assertloc (cterm_develop (t_pa, TRACK) \eq cterm_develop (t_pb, TRACK))

	val _ = show "T1 => T1': "
	val _ = show (cterm_develop (t_pa, TRACK))
	val _ = show ()
	val _ = show "T2 => T2': "
	val _ = show (cterm_develop (t_pb, TRACK))
	val _ = show ()

in 
	(cterm_collect (t_pa, TRACK), cterm_collect (t_pb, TRACK))
end

////







implement aterm_breduce_leftmost (t) = 
	case+ t of 
	| ATVar _              => Nothing ()
	| ATLam (t)            => maybe_bind (aterm_breduce_leftmost t, lam t => ATLam t)
	| ATApp (ATLam t1, t2) => Just (aterm_shift (aterm_subst (t1, aterm_shift (t2, 1)), ~1))
	| ATApp (t1, t2)       =>>
		let 
			val bt1 = aterm_breduce_leftmost t1 
			val bt2 = aterm_breduce_leftmost t2 
		in 
			case+ (bt1, bt2) of 
			| (Just t1, _)           =>  Just (ATApp (t1, t2))
			| (Nothing _, Just t2)   =>  Just (ATApp (t1, t2))
			| (Nothing _, Nothing _) =>> Nothing ()
		end 


implement aterm_bnorm (t) = let 
	val bt = aterm_breduce_leftmost t 
in 
	case+ bt of 
	| Nothing _ => t 
	| Just t    => aterm_bnorm t 
end 







