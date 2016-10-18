#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"

staload "unionfind.sats"


(* LOCAL-IN-END *)
local

datatype pt (a:t@ype) = 
| Link of (ref (pt a))
| Info of (ref int, ref a)

assume point (a:t@ype) = ref (pt a)

fun {a:t@ype} addr_of (p: point a): ptr = 
	$UNSAFE.cast{ptr} p (* given point = ref pt, returns address of pt *)

fun {a:t@ype} link (p: point a, l: point a): void =
	!p := Link l

fun {a:t@ype} repr (p: point a): point a = 
	case+ !p of 
	| Info _ => p
	| Link pp => 
		let 
			val ppp = repr pp 
			val _ = if addr_of ppp != addr_of pp then link (p, ppp)
		in 
			ppp 
		end

(* LOCAL-IN-END *)
in 

implement {a} fresh (desc) = 
	ref<pt a> (Info (ref<int> 1, ref<a> desc))

implement {a} get_desc (p) = 
	case+ !p of 
	| Info (_, desc) => !desc
	| Link p => 
		case+ !p of 
		| Info (_, desc) => !desc
		| Link p => get_desc (repr p)

implement {a} set_desc (p, desc) = 
	case+ !p of 
	| Info (_, cell) => !cell := desc
	| Link p => 
		case+ !p of 
		| Info (_, cell) => !cell := desc 
		| Link p => set_desc (repr p, desc)

implement {a} union (p1, p2, f) = let 
	val p1 = repr p1 
	val p2 = repr p2 
in 
	if not (is_equiv (p1, p2))
	then 
		case- (!p1, !p2) of
		| (Info (w1, d1), Info (w2, d2)) => 
			if !w1 >= !w2 
			then (link (p2, p1); !w1 := !w1 + !w2; !d1 := f (!d1, !d2))
			else (link (p1, p2); !w2 := !w1 + !w2; !d2 := f (!d1, !d2))
end 

implement {a} is_equiv (p1, p2) = 
	addr_of (repr p1) = addr_of (repr p2)

implement {a} is_repr (p) = 
	case+ !p of 
	| Info _ => false 
	| Link _ => true 

(* LOCAL-IN-END *)
end

