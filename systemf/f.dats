#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "f.sats"
staload "list.sats"
staload "show.sats"
staload "maybe.sats"


#define DEBUG false


staload "order.sats"
implement order_eq<typ> (x, y) = 
	case+ (x, y) of 
	| (TyFreeVar x, TyFreeVar y) => x \order_eq<int> y 
	| (TyBoundVar x, TyBoundVar y) => x \order_eq<int> y 
	| (TyForAll x, TyForAll y) => x \order_eq<typ> y 
	| (TyArrow (x1, x2), TyArrow (y1, y2)) => (x1 \order_eq<typ> y1) andalso (x2 \order_eq<typ> y2)
	| (_, _) => false

implement fresh = let 
	val seed = ref<int> 0
in 
	lam () => (!seed := !seed + 1; !seed)
end

implement {a} fold_type (typ, fr, bo, fa, ar) = let 
	val fold = lam typ =<cloref1> fold_type (typ, fr, bo, fa, ar)
in 
	case+ typ of 
	| TyFreeVar n      => fr n 
	| TyBoundVar n     => bo n 
	| TyForAll typ     => fa (fold typ)
	| TyArrow (t1, t2) => ar (fold t1, fold t2)
end

implement {a} fold_term (term, fr, bo, la, tla, ap, tap) = let 
	val fold = lam term =<cloref1> fold_term (term, fr, bo, la, tla, ap, tap)
in 
	case+ term of 
	| TmFreeVar n         => fr n
	| TmBoundVar n        => bo n
	| TmLam (typ, term)   => la (typ, fold term)
	| TmTyLam term        => tla (fold term)
	| TmApp (t1, t2)      => ap (fold t1, fold t2)
	| TmTyApp (term, typ) => tap (fold term, typ)
end


local 

	fun pid (id: int): void = 
		if id < 26 
		then print_char ($UNSAFE.cast{char} (id + 96))
		else print_int id

	fun size (t: term): int = 
		fold_term<int> (t, lam x => 1:int, 
						   lam x => 1:int, 
						   lam (x, y) => 1 + y:int, 
						   lam x => 1 + x:int, 
						   lam (x, y) => 1 + x + y:int, 
						   lam (x, y) => 1 + x:int)

	fun is_lam (t: term): bool = 
		case+ t of 
		| TmLam _   => true
		| TmTyLam _ => true
		| _         => false

	val red    : string = "\033[31m"
	val yellow : string = "\033[33m"
	val blue   : string = "\033[34m"
	val bold   : string = "\033[1m"
	val unbold : string = "\033[21m"
	val off    : string = "\033[0m"

in 

	implement show_any<typ> (typ) = 
		case+ typ of 
		| TyForAll (TyArrow (TyArrow (TyBoundVar 0, TyBoundVar 0), TyArrow (TyBoundVar 0, TyBoundVar 0))) => show_any "nat"
		| TyForAll (TyArrow (TyBoundVar 0, TyArrow (TyBoundVar 0, TyBoundVar 0))) => show_any "bool"
		| TyFreeVar n => pid n 
		| TyBoundVar n => (show_any blue; show_any<int> n; show_any off)
		| TyArrow (t1, t2) => (show_any "("; show_any t1; show_any " -> "; show_any t2; show_any ")")
		| TyForAll (t) => (show_any "∀."; show_any t)

	implement show_any<term> (term) = 
		case+ term of
		| TmFreeVar n         => pid n
		| TmBoundVar n        => (show_any red; show_any n; show_any off)
		| TmLam (typ, term)   => (show_any "𝛌["; show_any typ; show_any "]."; show_any term)
//		| TmLam (typ, term)   => (show_any "𝛌."; show_any term)
		| TmTyLam term        => (show_any "𝚲."; show_any term)
//		| TmTyLam term        => show_any term
		| TmApp (t1, t2)      => 
			(if is_lam t1
			 then (show_any "("; show_any t1; show_any ")")
			 else show_any t1; 
			 show_any "("; show_any t2; show_any ")")
//		| TmTyApp (term, _) => 
//			 if is_lam term
//			 then (show_any "("; show_any term; show_any ")")
//			 else show_any term
		| TmTyApp (term, typ) => 
			(if is_lam term
			 then (show_any "("; show_any term; show_any ")")
			 else show_any term;
			 show_any "["; show_any typ; show_any "]")

end



(* open a type binder in a type.
   turn bound type var `binder` to free var `subst`
*)
implement open_type_type (typ, binder, subst) = let 
	#define open open_type_type
in  
	case+ typ of 
	| TyFreeVar _      => typ
	| TyBoundVar n     => if n = binder then subst else typ 
	| TyForAll typ     => TyForAll (open (typ, binder + 1, subst))
	| TyArrow (t1, t2) => TyArrow (open (t1, binder, subst), open (t2, binder, subst))
end

(* open a term binder in a term.
   turn bound term var `binder` to free var `subst`
*)
implement open_term_term (term, binder, subst) = let 
	#define open open_term_term
in 
	case+ term of 
	| TmFreeVar n         => term
	| TmBoundVar n        => if n = binder then subst else term
	| TmLam (typ, term)   => TmLam (typ, open (term, binder + 1, subst))
	| TmTyLam term        => TmTyLam (open (term, binder, subst))
	| TmApp (t1, t2)      => TmApp (open (t1, binder, subst), open (t2, binder, subst))
	| TmTyApp (term, typ) => TmTyApp (open (term, binder, subst), typ)
end

(* open a type binder in a term.
   turn bound type var `binder` to free var `subst`
*)
implement open_term_type (term, binder, subst) = let 
	overload open with open_type_type
	overload open with open_term_type
in 
	case+ term of 
	| TmFreeVar n         => term
	| TmBoundVar n        => term
	| TmLam (typ, term)   => TmLam (open (typ, binder, subst), open (term, binder, subst))
	| TmTyLam term        => TmTyLam (open (term, binder + 1, subst))
	| TmApp (t1, t2)      => TmApp (open (t1, binder, subst), open (t2, binder, subst))
	| TmTyApp (term, typ) => TmTyApp (open (term, binder, subst), open (typ, binder, subst))
end

(* close a free type var in a type.
   abstract free type var `target` into bound type var `binder`
*)
implement close_type_type (typ, target, binder) = let 
	#define close close_type_type
in 
	case+ typ of 
	| TyFreeVar n      => if n = target then TyBoundVar binder else typ
	| TyBoundVar n     => typ
	| TyForAll typ     => TyForAll (close (typ, target, binder + 1))
	| TyArrow (t1, t2) => TyArrow (close (t1, target, binder), close (t2, target, binder))
end

(* close a free term var in a term.
   abstract free type var `target` into bound type var `binder`
*)
implement close_term_term (term, target, binder) = let 
	#define close close_term_term
in 
	case+ term of 
	| TmFreeVar n         => if n = target then TmBoundVar binder else term
	| TmBoundVar n        => term
	| TmLam (typ, term)   => TmLam (typ, close (term, target, binder + 1))
	| TmTyLam term        => TmTyLam (close (term, target, binder))
	| TmApp (t1, t2)      => TmApp (close (t1, target, binder), close (t2, target, binder))
	| TmTyApp (term, typ) => TmTyApp (close (term, target, binder), typ)
end

(* close a free type var in a term.
   abstract a free type var `target` into bound type var `binder`
*)
implement close_term_type (term, target, binder) = let 
	overload close with close_term_type
	overload close with close_type_type 
in 
	case+ term of 
	| TmFreeVar n         => term
	| TmBoundVar n        => term
	| TmLam (typ, term)   => TmLam (close (typ, target, binder), close (term, target, binder))
	| TmTyLam term        => TmTyLam (close (term, target, binder + 1))
	| TmApp (t1, t2)      => TmApp (close (t1, target, binder), close (t2, target, binder))
	| TmTyApp (term, typ) => TmTyApp (close (term, target, binder), close (typ, target, binder))
end

implement free_type_vars (typ) = let 
	#define nil ListNil 
	#define ::  ListCons
in 
	fold_type<list int> (typ, lam x => x :: nil (), lam x => nil (), lam x => x, lam (x, y) => list_concat (x, y))
end

implement free_term_vars (term) = let 
	#define nil ListNil 
	#define ::  ListCons
in 
	fold_term<list int> (term, lam x => x :: nil (), lam x => nil (), lam (x, y) => y, lam x => x, lam (x, y) => list_concat (x, y), lam (x, y) => x)
end

implement free_term_type_vars (term) = let 
	#define nil ListNil 
	#define ::  ListCons
	overload fv with free_type_vars
	overload fv with free_term_type_vars 
in 
	fold_term<list int> (term, lam x => nil (), lam x => nil (), lam (x, y) => list_concat (fv x, y), lam x => x, lam (x, y) => list_concat (x, y), lam (x, y) => list_concat (x, fv y))
end 

(* check if a type is locally closed: no `TyBoundVar` points to a non-exist binder *)
implement is_closed_type (typ) = 
	case+ typ of 
	| TyFreeVar _      => true
	| TyBoundVar _     => false
	| TyArrow (t1, t2) => is_closed_type t1 && is_closed_type t2
	| TyForAll typ     => is_closed_type (open_type_type (typ, 0, TyFreeVar (fresh ())))

(* check if a term is locally closed: no `TmBoundVar` or `TmBoundVar` points to a non-exist binder *)
implement is_closed_term (term) = 
	case+ term of 
	| TmFreeVar n         => true
	| TmBoundVar n        => false
	| TmLam (typ, term)   => is_closed_type typ && is_closed_term (open_term_term (term, 0, TmFreeVar (fresh ())))
	| TmTyLam term        => is_closed_term (open_term_type (term, 0, TyFreeVar (fresh ())))
	| TmApp (t1, t2)      => is_closed_term t1 && is_closed_term t2
	| TmTyApp (term, typ) => is_closed_type typ && is_closed_term term 

(* substitute a free term var in a term with `subst` *)
implement subst_term_term (term, target, subst) = 
	fold_term<term> (term, 
		 			 lam n           => if n = target then subst else TmFreeVar n,
		 			 lam n           => TmBoundVar n,
		 			 lam (typ, term) => TmLam (typ, term),
		 			 lam term        => TmTyLam term,
		 			 lam (t1, t2)    => TmApp (t1, t2),
		 			 lam (term, typ) => TmTyApp (term, typ))

(* substitute a free type var in a type with `subst` *)
implement subst_type_type (typ, target, subst) = 
	fold_type<typ> (typ, 
					lam n        => if n = target then subst else TyFreeVar n,
					lam n        => TyBoundVar n,
					lam typ      => TyForAll typ,
					lam (t1, t2) => TyArrow (t1, t2))

(* substitute a free type var in a term with `subst` *)
implement subst_term_type (term, target, subst) = let 
	val s = lam typ =<cloref1> subst_type_type (typ, target, subst)
in 
	fold_term<term> (term, 
					 lam n           => TmFreeVar n,
					 lam n           => TmBoundVar n,
					 lam (typ, term) => TmLam (s typ, term),
					 lam term        => TmTyLam term,
					 lam (t1, t2)    => TmApp (t1, t2),
					 lam (term, typ) => TmTyApp (term, s typ))
end

(* capture-avoiding substitution *)
implement term_cas (body, arg) = let 
	val x = fresh () 
in
	subst_term_term (open_term_term (body, 0, TmFreeVar x), x, arg)
end

(* capture-avoiding substitution *)
implement type_cas (body, arg) = let 
	val x = fresh () 
in
	subst_term_type (open_term_type (body, 0, TyFreeVar x), x, arg)
end




(* type checking *)
exception UnboundVar of term 
exception TypeError of (term, typ, typ)

implement typeof (term) = let 

	staload "assoclist.sats"

	fun check(env: assoclist (int, typ), term: term): typ = let 
//		val _ = if DEBUG then (show_any "typing: "; show_any term; show_any "\n")
	in 
		case- term of 
		| TmFreeVar n => 
			(case+ find<int,typ> (env, n) of
			| Just t => t 
			| Nothing _ => $raise UnboundVar term 
			)
		| TmLam (typ, body) => 
			let 
				val x = fresh () 
				val body = open_term_term (body, 0, TmFreeVar x)
				val tbody = check (insert<int,typ> (env, x, typ), body)
			in 
				TyArrow (typ, tbody)
			end
		| TmTyLam (body) => 
			let 
				val x = fresh ()
				val body = open_term_type (body, 0, TyFreeVar x)
				val tbody = check (env, body)
			in 
				TyForAll (close_type_type (tbody, x, 0))
			end
		| TmApp (body, arg) => 
			let 
				val targ = check (env, arg)
			in 
				case+ check (env, body) of 
				| TyArrow (t1, t2) => if t1 \order_eq targ then t2 else $raise TypeError (term, t1, targ) 
				| t => $raise TypeError (body, TyArrow (targ, TyFreeVar (fresh ())), t)
			end
		| TmTyApp (body, arg) => 
			let 
				val tbody = check (env, body)
			in 
				case+ tbody of 
				| TyForAll t => open_type_type (t, 0, arg)
				| t => $raise TypeError (body, TyForAll (TyFreeVar (fresh ())), t)
			end

	end

in 
	try
		check (make<int,typ> (), term)
	with
	| ~UnboundVar term => (show_any term; $raise UnboundVar term)
	| ~TypeError (term, expect, actual) => 
		(
			show_any term;
			show_any "\n\texpected => ";
			show_any expect;
			show_any "\n\tactual   => ";
			show_any actual;
			show_any "\n";
			$raise TypeError (term, expect, actual)
		)
end




(* one step reduction of the head redex *)
implement reduce_head (term) =  
	case+ term of 
	| TmApp (TmLam (_, body), arg) => 
		let 
			val ret = term_cas (body, arg)
			val _ = if DEBUG then (show_any "redex => "; show_any term; show_any "\n      => "; show_any ret; show_any "\n")
		in 
			Just ret
		end 
	| TmTyApp (TmTyLam body, arg) => 
		let 
			val ret = type_cas (body, arg)
			val _ = if DEBUG then (show_any "redex => "; show_any term; show_any "\n      => "; show_any ret; show_any "\n")
		in 
			Just ret 
		end
	| _ => Nothing ()


(* one step reduction of any outermost, leftmost redex *)
implement reduce_full (term) = let 
//	val _ = if DEBUG then (show_any "reducing: "; show_any term; show_any "\n")
in 
	case+ term of 
	| TmApp (t1, t2) => 
		(case+ reduce_full t1 of 
		| Just t1 => Just (TmApp (t1, t2))
		| Nothing _ => 
		case+ reduce_full t2 of 
		| Just t2 => Just (TmApp (t1, t2))
		| Nothing _ => reduce_head (TmApp (t1, t2))
		)
	| TmLam (typ, term) => 
		let 
			val x = fresh ()
		in 
			case+ reduce_full (open_term_term (term, 0, TmFreeVar x)) of 
			| Nothing _ => Nothing ()
			| Just t => Just (TmLam (typ, close_term_term (t, x, 0)))
		end
	| TmTyApp (t1, typ) => 
		(case+ reduce_full t1 of 
		| Just t => Just (TmTyApp (t, typ))
		| Nothing _ => reduce_head (TmTyApp (t1, typ))
		)
	| TmTyLam term => 
		let 
			val x = fresh ()
//			val term = reduce_full (open_term_type (term, 0, TyFreeVar x))
		in 
			case+ reduce_full (open_term_type (term, 0, TyFreeVar x)) of 
			| Nothing _ => Nothing ()
			| Just t => Just (TmTyLam (close_term_type (t, x, 0)))
		end
	| _ => Nothing ()
end

implement church<nat> (n) = let 
	val a = TyBoundVar 0
	val z = TmBoundVar 0

	(* 𝚲a.𝛌s[a->a].𝛌z[a].z *)
	val zero = TmTyLam (TmLam (TyArrow (a, a), TmLam (a, z)))
in
	if n = 0 
	then zero 
	else succ (church<nat> (n-1))
end

implement unchurch<nat> (term) = let 
	fun count (t: term): nat = 
		case- t of 
		| TmBoundVar 0            => 0
		| TmApp (TmBoundVar 1, t) => 1 + count t
in 
	case- eval term of 
	| TmTyLam (TmLam (TyArrow (TyBoundVar 0, TyBoundVar 0), TmLam (TyBoundVar 0, n))) => count n
end

implement church<bool> (t) = 
	if t
	then TmTyLam (TmLam (TyBoundVar 0, TmLam (TyBoundVar 0, TmBoundVar 0)))
	else TmTyLam (TmLam (TyBoundVar 0, TmLam (TyBoundVar 0, TmBoundVar 1)))

implement unchurch<bool> (t) = 
	case- eval t of 
	| TmTyLam (TmLam (TyBoundVar 0, TmLam (TyBoundVar 0, TmBoundVar 0))) => true
	| TmTyLam (TmLam (TyBoundVar 0, TmLam (TyBoundVar 0, TmBoundVar 1))) => false




(* beta-normal form *)
implement eval (term) = let 
	val _ = if DEBUG then (show_any "eval => "; show_any term; show_any "\n")
in 
	case+ reduce_full term of 
	| Nothing _ => term 
	| Just term => eval term 
end

implement app (t1, t2)  = TmApp (t1, t2)
implement tyapp (t1, t) = TmTyApp (t1, t)
implement arr (t1, t2)  = TyArrow (t1, t2)

infixl (=) >> 
infixr (=) ~>

implement succ (term)      = tm_succ >> term
implement add (x, y)       = tm_add >> x >> y 
implement mul (x, y)       = tm_mul >> x >> y
implement exp (x, y)       = tm_exp >> x >> y
implement ackermann (x, y) = tm_ackermann >> x >> y


(* ∀a.a->a->a *)
implement ty_bool = let val a  = TyBoundVar 0 in TyForAll (a ~> a ~> a) end

(* ∀a.(a->a)->a->a *)
implement ty_nat = let val a = TyBoundVar 0 in TyForAll ((a ~> a) ~> a ~> a) end

(* 𝛌n[nat].𝚲a.𝛌s[a->a].𝛌z[a].s(n[a]sz) *)
implement tm_succ = let 
	val a = TyBoundVar 0
	val n = TmBoundVar 2
	val s = TmBoundVar 1
	val z = TmBoundVar 0
in 
	TmLam (ty_nat, TmTyLam (TmLam (a ~> a, TmLam (a, s >> (n >> a >> s >> z)))))
end

(* 𝚲a.𝛌x[a].x->x *)
implement tm_id = TmTyLam (TmLam (TyBoundVar 0, TmBoundVar 0))

(* 𝚲a.𝛌p[bool].𝛌x[a].𝛌y[a].p[a](x)(y) *)
implement tm_ite = let 
	val a = TyBoundVar 0
	val p = TmBoundVar 2
	val x = TmBoundVar 1 
	val y = TmBoundVar 0
in 
	TmTyLam (TmLam (ty_bool, TmLam (a, TmLam (a, p >> a >> x >> y))))
end

(* 𝛌x[nat].𝛌y[nat].y[nat](tm_succ)x                  <- very slow
   𝛌x[nat].𝛌y[nat].𝚲a.𝛌s[a->a].𝛌z[a].x[a](s)(y[a]sz) <- a bit quicker

   basically, a church numeral `x` is applying `succ` x time on a term `z` that we call `zero`. 
   so applying `x` times of `succ` on `y` yields `x + y`
*)
implement tm_add = let 
	val x = TmBoundVar 3
	val y = TmBoundVar 2
	val s = TmBoundVar 1 
	val z = TmBoundVar 0
	val a = TyBoundVar 0
in 
    (* this is too slow 
    *)
//	TmLam (ty_nat, TmLam (ty_nat, TmApp (TmApp (TmTyApp (y, ty_nat), tm_succ), x)))
	eval (TmLam (ty_nat, TmLam (ty_nat, TmTyLam (TmLam (a ~> a, TmLam (a, x >> a >> s >> (y >> a >> s >> z)))))))
end

(* 𝛌x[nat].𝛌y[nat].y[nat](tm_add(x))(church<nat> 0)  <- very slow
   𝛌x[nat].𝛌y[nat].𝚲a.𝛌s[a->a].𝛌z[a].y[a](x[a]s)z    <- a bit quicker
*)
implement tm_mul = let 
	val x = TmBoundVar 3
	val y = TmBoundVar 2
	val s = TmBoundVar 1
	val z = TmBoundVar 0
//	val m = TmBoundVar 0
	val a = TyBoundVar 0
	val shift = lam (x:term):term => let val- TmBoundVar n = x in TmBoundVar (n+1) end 

//	val zero = 
//		TmTyLam (
//			TmLam (TyArrow (TyBoundVar 0, TyBoundVar 0), 
//				TmLam (TyBoundVar 0, TmBoundVar 0)))
in 
//	eval (TmLam (ty_nat, TmLam (ty_nat, TmApp (TmApp (TmTyApp (y, ty_nat), TmApp (tm_add, x)), zero))))
	eval (TmLam (ty_nat, TmLam (ty_nat, TmTyLam (TmLam (a ~> a, TmLam (a, y >> a >> (x >> a >> s) >> z))))))
end

implement tm_ackermann = let 
	
	val one = 
		TmTyLam (
			TmLam (TyBoundVar 0 ~> TyBoundVar 0, 
				TmLam (TyBoundVar 0, TmBoundVar 1 >> TmBoundVar 0)))

	val A = TmBoundVar 1
	val b = TmBoundVar 0

	// f = 𝛌A[nat->nat].𝛌b[nat].succ(b)[nat]A(church<nat> 1)
	val f = TmLam (ty_nat ~> ty_nat, TmLam (ty_nat, tm_succ >> b >> ty_nat >> A >> one))

	// Ack(a,b) = 𝛌a[nat].𝛌b[nat].a[nat->nat](f)(succ)(b)
	val a = TmBoundVar 1
	val b = TmBoundVar 0
in 
	eval (TmLam (ty_nat, TmLam (ty_nat, a >> (ty_nat ~> ty_nat) >> f >> tm_succ >> b)))
end

(* 𝛌x[nat].𝛌y[nat].y[nat](tm_mul(x))(church<nat> 1)
   𝛌x[nat].𝛌y[nat].𝚲a.𝛌s[a->a].𝛌z[a].y[a](1[a](x[a]s)z)(sz)    <- a bit quicker
*)
implement tm_exp = let
	val x = TmBoundVar 1
	val y = TmBoundVar 0

	val one = 
		TmTyLam (
			TmLam (TyBoundVar 0 ~> TyBoundVar 0, 
				TmLam (TyBoundVar 0, TmBoundVar 1 >> TmBoundVar 0)))
in 
	eval (TmLam (ty_nat, TmLam (ty_nat, y >> ty_nat >> (tm_mul >> x) >> one)))
end






implement main0 () = {

//	val tid = TyForAll (TyArrow (TyBoundVar 0, TyBoundVar 0))
//	val _ = show_any tid 
//	val _ = show_any (open_type_type (tid, ~1, TyFreeVar (fresh ())))

//	val id1 = TmTyApp (id, TyFreeVar (fresh ()))
//	val id2 = TmApp (id1, church<nat> 0)
//	val _ = show_any id2 
//	val _ = show_any "\n"
//	val _ = show_any (reduce_full id2)

//	val _ = show_any (succ (church<nat> 0))
//	val _ = show_any "\n"
//	val _ = show_any (reduce_full (succ (church<nat> 0)))
//	val _ = show_any "\n"

//	val _ = show_any (reduce_full (TmApp (TmTyApp (id, TyFreeVar (fresh ())), (succ (church<nat> 0)))))
//	val _ = show_any "\n"

//	val _ = show_any (reduce_cbv (TmApp (TmTyApp (id, TyFreeVar (fresh ())), (succ (church<nat> 0)))))

//	val _ = assertloc (unchurch<nat> (succ (church<nat> 0)) = 1)
//	val _ = show_any ( (church<nat> 0))
//	val _ = show_any "\n"
//	val _ = show_any (reduce_full (church<nat> 1))
//	val _ = show_any "\n"

//	val _ = show_any (church<nat> 2)
//	val _ = show_any "\n"
//	val _ = show_any (reduce_full (church<nat> 2))
//	val _ = show_any "\n"

//	val _ = show_any (typeof (church<nat> 3))
//	val _ = show_any "\n"
//	val _ = show_any (typeof (church<bool> true))
//	val _ = show_any "\n"
//	val _ = show_any (typeof tm_id)
//	val _ = show_any "\n"
//	val _ = show_any (typeof tm_ite)
//	val _ = show_any (reduce_full (church<nat> 3))
//	val _ = show_any "\n"
//	val _ = show_any (typeof tm_succ)
//	val _ = show_any "\n"

//	val _ = show_any (reduce (succ(church<nat> 0)))
//	val _ = show_any "\n"

//	val c = church<nat> 2
//	val _ = show_any (reduce_full c)
//	val _ = show_any "\n"
//	val _ = show_any<nat> (unchurch<nat> c)
//	val _ = show_any "\n"
//	val _ = show_any (typeof tm_exp)
//	val _ = show_any "\n"
	val _ = show_any (typeof tm_exp)
	val _ = show_any "\n"
//	val _ = show_any (eval (ackermann (church<nat> 2, church<nat> 1)))

	val _ = show_any<nat> (unchurch<nat> (exp (church<nat> 3, church<nat> 2)))
//	val _ = show_any tm_mul
	val _ = show_any "\n"
//	val _ = show_any<nat> (unchurch<nat> (exp (church<nat> 2, church<nat> 5)))

//	val _ = show_any (reduce_full (TmLam (ty_nat, TmLam (ty_nat, TmApp (TmApp (tm_add, TmBoundVar 1), TmBoundVar 0)))))
//	val _ = show_any "\n"

//	val x = fresh ()
//	val y = fresh ()

//	val- TmLam (_, body) = tm_add
//	val t = open_term_term (body, 0, TmFreeVar x)
//	val _ = (show_any t; show_any "\n")

//	val- TmLam (_, body) = t
//	val t = open_term_term (body, 0, TmFreeVar y)
//	val _ = (show_any t; show_any "\n")

//	val t = subst_term_term (t, x, TmBoundVar 0)
//	val _ = (show_any t; show_any "\n")

//	val t = subst_term_term (t, y, TmBoundVar 1)
//	val _ = (show_any t; show_any "\n")

//	val _ = show_any (typeof tm_add)
//	val _ = show_any "\n"
//	val _ = show_any<nat> (unchurch<nat> (add (church<nat> 3, church<nat> 5)))


//	val _ = assertloc (unchurch<nat> (succ (succ (succ (church<nat> 0)))) = 3)
}

//