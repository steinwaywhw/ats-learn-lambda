
#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "map.sats"
staload "set.sats"
staload "list.sats"
staload "maybe.sats"

staload "generalizer.sats"
staload "unifier.sats"


(* LOCAL IN END *)
local 

typedef rank = int
assume ctx = $rec{current_rank = ref rank, 
			      vars = ref (map (rank, list univar))}


#define ::  ListCons 
#define nil ListNil

#define RANK_GENERIC (~1)
#define RANK_NO      (0)
#define RANK_BASE    (1)


fun register_at_rank (ctx: ctx, v: univar, r: rank): void = let 
	val _ = set_rank (v, r)
in
	case+ map_find (!(ctx.vars), r) of 
	| Nothing () => !(ctx.vars) := map_insert (!(ctx.vars), r, v :: nil ())
	| Just vs    => !(ctx.vars) := map_update (!(ctx.vars), r, v :: vs)
end

(* LOCAL IN END *)
in 

implement initgen () = 
	'{current_rank = ref<rank> RANK_NO, 
	  vars = ref<map(rank, list univar)> (map_make<rank, list univar> ())}

implement register (ctx, v) = 
	register_at_rank (ctx, v, !(ctx.current_rank)) 

implement enter (ctx) = 
	!(ctx.current_rank) := !(ctx.current_rank) + 1


implement generalize (v) = let 
	val visited = ref<set(int)> (set_make<int> ())

	val mark = lam v =<cloref1> !visited := set_insert (!visited, get_id v)
	val is_visited = lam v =<cloref1> set_member (!visited, get_id v)

	(* traverse type structure to find univars at GENERIC rank *)
	fun traverse (v: univar, quantifiers: list univar):<cloref1> list univar = 

		(* univar is not generic, no need to explore children *)
		if not (get_rank v = RANK_GENERIC) then quantifiers

		(* already visited, no need to explore children *)
		else if is_visited v then quantifiers

		(* it is generic, mark as visited, and explore children *)
		else 
			let val _ = mark v in
			case+ get_struct v of 
			| Nothing _ => v :: quantifiers
			| Just s    => struct_fold<univar, list univar> (s, quantifiers, traverse)
			end
in 
	Scheme (traverse (v, nil ()), v)
end


implement exit (ctx)  = let 
	

	val current_vars = map_get (!(ctx.vars), !(ctx.current_rank))
	val young        = ref<set(int)> (set_make<int> ())
	val visited      = ref<set(int)> (set_make<int> ())
	val sorted       = ref<map(int,list(univar))> (map_make<int, list univar> ())

	val mark = lam v =<cloref1> !young := set_insert (!visited, get_id v)
	val is_visited = lam v =<cloref1> set_member (!visited, get_id v)
	val is_young = lam v =<cloref1> set_member (!young, get_id v)

	(***********************************)
	(* 
		init will put all univars in the young set, and sorted map. 

		1. young **set** helps determine where the univar is registered at current rank quicker than list
		2. sorted help ensure that enumerating once is enough.
	*)

	val init_young  = lam (v:univar): void =<cloref1> !young := set_insert (!young, get_id v)
	val init_sorted = lam (v:univar): void =<cloref1> 
							let val r = get_rank v in 
							case+ map_find (!sorted, r) of 
							| Nothing _ => !sorted := map_insert (!sorted, r, v :: nil ())
							| Just vs   => !sorted := map_update (!sorted, r, v :: vs)
							end

	exception Cycle of univar

	val init = lam v =<cloref1> if occurs_check v then $raise Cycle v else (init_young v; init_sorted v)
	val _ = list_foreach (current_vars, lam v => init v)

	(***********************************)
	(* 
		adjust will update univars rank. it works as follows

		- check visited:
		  true  => it must have rank lower than target rank, since we start exploring from lower rank
		  false => 
			- mark as visited
			- adjust rank to target rank since it is
			  either a univar already at this rank
			  or its parent is at this rank and as a child

			  in any case, it should adjust to have target rank

			- for each young univar (univar registered at the current `let`)
				- adjust children to have at most target rank
				- adjust parent to have the max of children's rank

                  there is no need to children to have higher rank than parents
				  there is no need for parent to have higher rank than the max of its children
	*) 

	fun adjust (v: univar, target_rank: int): void = let 
		val _ = assert (get_rank v >= RANK_BASE)
	in 
		if is_visited v
		then assert (get_rank v <= target_rank)
		else 
			let 
				val _ = mark v
				val _ = adjust_rank (v, target_rank)

			(* we are only dealing with univars registered at current level *)	
			in if is_young v then 

				(* 
					if it has structure, we need to traverse its children to lower their rank
					and when coming back up, adjust the parent's rank. 
				*)
				case+ get_struct v of 
				| Nothing _ => ()
				| Just s    => 
					let val rank = 
						struct_fold (s, RANK_BASE,
							lam (v, ret) => let val _ = adjust (v, target_rank)
							in max (get_rank v, ret) end)
					in 
						adjust_rank (v, rank)
					end
			end
	end


	(* now iterate through ranked univars, and adjust their ranks *)
	fun loop (r: int): void = 
		if r <= !(ctx.current_rank) then 
		case+ map_find (!sorted, r) of 
		| Nothing () => loop (r+1)
		| Just vs    => list_foreach (vs, lam v => adjust (v, r))

	val _ = loop (RANK_BASE)

	(* 
		now, we need to 

		1. move the univars to correct pools (of ranks lower than current_rank)
		2. generalize univars (of ranks equal to current_rank)
	*)
	val relocate = lam v =<cloref1> register_at_rank (ctx, v, get_rank v)
	val gen      = lam v =<cloref1> set_rank (v, RANK_GENERIC)
	val quantifiers = list_filter (
						current_vars, 
						lam v => 
							if get_rank v < !(ctx.current_rank) 
							then (relocate v; false) 
							else (gen v; has_struct v))

	val _ = map_delete (!(ctx.vars), !(ctx.current_rank))
	val _ = !(ctx.current_rank) := !(ctx.current_rank) - 1

in 
	quantifiers
end

implement instantiate (ctx, scheme) = let 
	val visited = set_make<int> ()

	fun copy (v: univar):<cloref1> univar = 
		if get_rank v != RANK_GENERIC

		(* if it is not generic, return without copy *)
		then v 

		(* copy recursively*)
		else 
			if set_member (visited, get_id v)
			then v
			else let 
				val vv = fresh (Nothing (), !(ctx.current_rank))
				val _ = register (ctx, vv)
				val _ = set_insert (visited, get_id vv)
			in case+ get_struct v of 
				| Nothing _ => vv
				| Just s    => 
					let 
						val ss = struct_map (s, copy)
						val _ = set_struct (vv, Just ss)
					in vv end
			end
in 
	case+ scheme of 
	| Scheme (qs, body) => $tup(list_map (qs, copy), copy body)
end

end