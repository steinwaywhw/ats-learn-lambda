#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "unifier.sats"
staload "list.sats"
staload "maybe.sats"
staload "map.sats"

staload UF = "unionfind.sats"
staload _  = "unionfind.dats"




(* LOACL-IN-END *)
local

val seed = ref<int> 0

exception unifier_cycle_exn of univar


datatype descriptor = Desc of (int, rank, maybe (structure univar))
assume univar = $UF.point descriptor

fun desc_id (d: descriptor): int = 
	case+ d of 
	| Desc (id, _, _) => id 

fun desc_rank (d: descriptor): int = 
	case+ d of 
	| Desc (_, rank, _) => rank 

fun desc_struct (d: descriptor): maybe (structure univar) =
	case+ d of 
	| Desc (_, _, s) => s

(* LOACL-IN-END *)
in 

implement counter = lam () => (!seed := !seed + 1; !seed)
implement reset   = lam () => !seed := 0

implement fresh (s, rank) = 
	$UF.fresh (Desc (counter (), rank, s)) 

implement get_id (v) = 
	desc_id ($UF.get_desc v) 

implement get_struct (v) = 
	desc_struct ($UF.get_desc v) 

implement set_struct (v, s) =
	let val desc = $UF.get_desc v  
	in $UF.set_desc (v, Desc (desc_id desc, desc_rank desc, s)) end

implement has_struct (v) = 
	case+ desc_struct ($UF.get_desc v) of 
	| Nothing _ => false 
	| Just _    => true

implement get_rank (v) = 
	desc_rank ($UF.get_desc v)

implement set_rank (v, r) = 
	let val desc = $UF.get_desc v
	in $UF.set_desc (v, Desc (desc_id desc, r, desc_struct desc)) end

implement adjust_rank (v, r) = 
	if r < get_rank v then set_rank (v, r)

implement {} unify (v1, v2) = let 
	fun unify_descriptor (d1: descriptor, d2: descriptor): descriptor = 
		case+ (d1, d2) of 
		| (Desc (id, r1, s1), Desc (_, r2, s2)) => Desc (id, min (r1, r2), unify_structure (s1, s2))

	and unify_structure (s1: maybe (structure univar), s2: maybe (structure univar)): maybe (structure univar) = 
		case+ (s1, s2) of 
		| (Just s1, Just s2) => let val _ = struct_iter2<univar,univar> (s1, s2, lam (v1, v2) => unify (v1, v2)) in Just s1 end
		| (Just s, _)        => Just s 
		| (_, Just s)        => Just s 
		| (_, _)             => Nothing ()
in 
	$UF.union (v1, v2, lam (d1, d2) => unify_descriptor (d1, d2))
end

implement is_equiv (v1, v2) = 
	get_id v1 = get_id v2

implement is_repr (v) = 
	$UF.is_repr v

implement {} occurs_check (v) = let 

	val visited = ref<map(int,bool)> (map_make<int, bool> ())

	fun check (v: univar):<cloref1> void = let 
		val _ = show_any !visited 
		val _ = print_newline ()
		val _ = print_string "checking: "
		val _ = print_int (get_id v)
		val _ = print_newline ()
	in
		case+ map_find (!visited, get_id v) of 
		| Just b => 
			if b = false
			then $raise unifier_cycle_exn v 
			else ()

		| Nothing () => 
			let 
				val _ = !visited := map_insert (!visited, get_id v, false)
			in 
				case+ get_struct v of 
				| Nothing _ => !visited := map_update (!visited, get_id v, true)
				| Just s    => (struct_iter<univar> (s, check); !visited := map_update (!visited, get_id v, true))
			end 
	end

in 
	try (check v; false)
	with ~unifier_cycle_exn v => true
end



(* LOACL-IN-END *)
end






