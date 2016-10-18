#include "atsutils.hats"
#include "share/atspre_staload.hats"

staload "unifier.sats"
dynload "unifier.dats"
staload _ = "unifier.dats"
staload _ = "unionfind.dats"

staload "maybe.sats"

datatype ty (a:t@ype) = 
| TyVar of a 
| TyBase of int 
| TyArrow of (a, a)

assume structure (a:t@ype) = ty a

exception ExceptionIter

implement {a,b} struct_iter2 (s1, s2, f) = 
	case+ (s1, s2) of 
	| (TyVar a, TyVar b) => f (a, b)
	| (TyBase a, TyBase b) => if a = b then () else $raise ExceptionIter 
	| (TyArrow (a1, b1), TyArrow (a2, b2)) => (f (a1, a2); f (b1, b2))
	| (_, _) => $raise ExceptionIter

implement main0 () = () where {
	val x = fresh (Nothing (), 0)
	val w = fresh (Nothing (), 0)
	val m = fresh (Just (TyBase 42), 0)
	val y = fresh (Just (TyArrow (m, w)), 0)
	val z = fresh (Just (TyArrow (x, x)), 0)

	val b = unify (y, z)

	val _ = assertloc (equiv (y, z))

}
