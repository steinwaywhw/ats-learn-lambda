#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "unifier.sats"
staload "list.sats"
staload "maybe.sats"
staload "map.sats"

staload UF = "unionfind.sats"
staload _  = "unionfind.dats"


datatype descriptor = Desc of (int, int, maybe (structure variable))
assume variable = $UF.point descriptor


(* LOACL-IN-END *)
local

fun desc_id (d: descriptor): int = 
	case+ d of 
	| Desc (id, _, _) => id 

fun desc_rank (d: descriptor): int = 
	case+ d of 
	| Desc (_, rank, _) => rank 

fun desc_struct (d: descriptor): maybe (structure variable) =
	case+ d of 
	| Desc (_, _, s) => s


(* LOACL-IN-END *)
in 

implement fresh = let 
	val seed = ref<int> 0
in 
	lam (s, rank) => 
		let 
			val desc = Desc (!seed, rank, s)
			val _ = !seed := !seed + 1
		in 
			$UF.fresh desc 
		end 
end 

implement get_id (v) = 
	case+ $UF.find v of 
	| Desc (id, _, _) => id 

implement get_struct (v) = 
	case+ $UF.find v of 
	| Desc (_, _, s) => s

implement set_struct (v, s) = 
	case+ $UF.find v of 
	| Desc (id, rank, _) => $UF.change (v, Desc (id, rank, s))

implement has_struct (v) = 
	case+ $UF.find v of 
	| Desc (_, _, s) => 
	case+ s of 
	| Nothing _ => false 
	| Just _    => true

implement get_rank (v) = 
	case+ $UF.find v of 
	| Desc (_, rank, _) => rank

implement set_rank (v, r) = 
	case+ $UF.find v of 
	| Desc (id, _, s) => $UF.change (v, Desc (id, r, s))

implement adjust_rank (v, r) = 
	if r < get_rank v then set_rank (v, r)

implement {} unify (v1, v2) = let 
	fun unify_descriptor (d1: descriptor, d2: descriptor): descriptor = 
		case+ (d1, d2) of 
		| (Desc (id, r1, s1), Desc (_, r2, s2)) => Desc (id, min (r1, r2), unify_structure (s1, s2))

	and unify_structure (s1: maybe (structure variable), s2: maybe (structure variable)): maybe (structure variable) = 
		case+ (s1, s2) of 
		| (Just s1, Just s2) => let val _ = struct_iter2<variable,variable> (s1, s2, lam (s1, s2) => unify (s1, s2)) in Just s1 end
		| (Just s, _)        => Just s 
		| (_, Just s)        => Just s 
		| (_, _)             => Nothing ()
in 
	$UF.union (lam (d1, d2) => unify_descriptor (d1, d2), v1, v2)
end

implement equiv (v1, v2) = 
	$UF.equiv (v1, v2)

implement is_repr (v) = 
	$UF.is_repr v


implement occurs_check (v) = let 
	val visited = ref<map(int,bool)> (map_make<int, bool> ())

	exception Cycle of variable

	fun check (v: variable):<cloref1> void = 
		// is young? 

		case+ map_find (!visited, get_id v) of 
		| Just b => if b = false then $raise Cycle (v) else ()
		| Nothing () => 
			let 
				val _ = !visited := map_insert (!visited, get_id v, false)
			in 
				case+ get_struct v of 
				| Nothing _ => ()
				| Just s    => (struct_iter (s, check); !visited := map_update (!visited, get_id v, true))
			end 

in 
	try (check v; false)
	with ~Cycle v => true
end



(* LOACL-IN-END *)
end




