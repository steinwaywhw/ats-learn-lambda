#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "maybe.sats"
staload "map.sats"
staload "list.sats"

staload "unifier.sats"
staload "generalizer.sats"

staload _ = "unifier.dats"
staload _ = "generalizer.dats"

dynload "unifier.dats"

datatype term = 
| TermVar of string 
| TermApp of (term, term)
| TermLam of (string, term)
| TermLet of (string, term, term)

datatype ty (a:t@ype) = 
| TyVar of a 
| TyArrow of (a, a)

assume structure (a:t@ype) = ty a

implement {a} struct_iter (s, f) = 
	case+ s of 
	| TyVar a        => f a
	| TyArrow (a, b) => (f a; f b)

implement {a,b} struct_iter2 (s1, s2, f) = let 
	exception Iter2 of (structure a, structure b)
in 
	case+ (s1, s2) of 
	| (TyVar a, TyVar b)                   => f (a, b)
	| (TyArrow (a1, b1), TyArrow (a2, b2)) => (f (a1, a2); f (b1, b2))
	| (_, _)                               => $raise Iter2 (s1, s2)
end

implement {a,b} struct_map (s, f) = 
	case+ s of 
	| TyVar a => TyVar (f a)
	| TyArrow (a, b) => TyArrow (f a, f b)

implement {a,b} struct_fold (s, base, f) = 
	case+ s of 
	| TyVar a => f (a, base)
	| TyArrow (a, b) => f (b, f (a, base))


typedef env = map (string, univar)

extern fun decode (ty univar): ty string 

extern fun typeof (env, term): ty univar
implement typeof (env, term) = 
	case+ term of 
	| TermVar v => instantiate (map_get (env, v))



implement main0 () = () where {

	fun print_ty (s: ty univar): void = 
		case+ s of 
		| TyVar v => (print_string "var"; print_int (get_id v))
		| TyArrow (s1, s2) => (print_string "app("; print_int (get_id s1); print_string ","; print_int (get_id s2); print_string ")")



	val x = fresh (Nothing (), 0)
	val w = fresh (Nothing (), 0)
	val m = fresh (Just (TyBase 42), 0)
	val y = fresh (Just (TyArrow (m, w)), 0)
	val z = fresh (Just (TyArrow (x, x)), 0)

	val b = unify (y, z)

	val _ = assertloc (is_equiv (w, m))

	val _ = case+ get_struct w of 
			| Nothing _ => ()
			| Just x => print_ty x

}
