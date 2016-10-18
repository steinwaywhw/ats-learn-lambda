#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "map.sats"
staload "set.sats"
staload "list.sats"
staload "maybe.sats"

staload "generalizer.sats"
staload UNI = "unifier.sats"

(*
	the context maintains two things. 

	1. the current rank, or the current level of `let` binding. 
	2. a pool of registered variables (with or without structures) sorted by rank.

	Note that, when a variable is firstly created and registered, it has current rank
	and is put into the right pool. But after unification, it will sit in the same pool
	but may have a smaller rank. 

	The `exit` function will look into the young generation, namely newly registered 
	variables in this `let` binding that are exiting, and try to fix the rank and figure
	out what can be generalized. 
*)
assume ctx = $rec{current_rank = ref int, 
			      vars = ref (map (int, list $UNI.variable))}

(* LOCAL IN END *)
local 

#define ::  ListCons 
#define nil ListNil

#define RANK_GENERIC (~1)
#define RANK_NO      (0)
#define RANK_BASE    (1)

(* for easier coding *)
typedef variable = $UNI.variable

fun register_at_rank (ctx: ctx, v: variable, r: int): void = let 
	val _ = $UNI.set_rank (v, r)
in
	case+ map_find (!(ctx.vars), r) of 
	| Nothing () => !(ctx.vars) := map_insert (!(ctx.vars), r, v :: nil ())
	| Just vs    => !(ctx.vars) := map_update (!(ctx.vars), r, v :: vs)
end

(* LOCAL IN END *)
in 

implement init () = 
	'{current_rank = ref<int> RANK_NO, vars = ref<map(int, list variable)> (map_make<int, list variable> ())}


implement register (ctx, v) = 
	register_at_rank (ctx, v, !(ctx.current_rank)) 

//implement trivial (body) = 
//	Scheme (ListNil (), body)

implement enter (ctx) = 
	!(ctx.current_rank) := !(ctx.current_rank) + 1


implement generalize (v) = let 
	val visited = ref<set(int)> (set_make<int> ())

	val mark = lam v =<cloref1> !visited := set_insert (!visited, $UNI.get_id v)
	val is_visited = lam v =<cloref1> set_member (!visited, $UNI.get_id v)

	(* traverse type structure to find variables at GENERIC rank *)
	fun traverse (v: variable, quantifiers: list variable):<cloref1> list variable = 

		(* variable is not generic, no need to explore children *)
		if not ($UNI.get_rank v = RANK_GENERIC) then quantifiers

		(* already visited, no need to explore children *)
		else if is_visited v then quantifiers

		(* it is generic, mark as visited, and explore children *)
		else 
			let val _ = mark v in
			case+ $UNI.get_struct v of 
			| Nothing _ => v :: quantifiers
			| Just s    => $UNI.struct_fold<variable, list variable> (s, quantifiers, traverse)
			end
in 
	Scheme (traverse (v, nil ()), v)
end



(*
	When enumerating variables to adjust rank, we should start with lower ranked 
	variables so that enumerating once is enough. We would like to adjust a variable's
	rank only once, all the way to the lowest rank it should have. If we do not enumerate
	from the lowest rank, we could possible adjust a variable's rank multiple times
	until it reaches the lowest rank. 

	Say, we have variables `va`, `vb` and `vc`, with ranks and their relations in the tree.

	```
	va(2) -> vb(3) -> vc(5)
	```

	If we start from `vb(3)`, we would adjust `vc(5)` to `vc(3)`, and one more enumerate to adjust 
	both `vb` and `vc` to rank 2. That's why we need to start from the lowest rank. 
*)
implement exit (ctx)  = let 
	

	val current_vars = map_get (!(ctx.vars), !(ctx.current_rank))
	val young        = ref<set(int)> (set_make<int> ())
	val visited      = ref<set(int)> (set_make<int> ())
	val sorted       = ref<map(int,list(variable))> (map_make<int, list variable> ())

	val mark = lam v =<cloref1> !young := set_insert (!visited, $UNI.get_id v)
	val is_visited = lam v =<cloref1> set_member (!visited, $UNI.get_id v)
	val is_young = lam v =<cloref1> set_member (!young, $UNI.get_id v)

	(***********************************)
	(* 
		init will put all variables in the young set, and sorted map. 

		1. young **set** helps determine where the variable is registered at current rank quicker than list
		2. sorted help ensure that enumerating once is enough.
	*)

	val init_young  = lam (v:variable): void =<cloref1> !young := set_insert (!young, $UNI.get_id v)
	val init_sorted = lam (v:variable): void =<cloref1> 
							let val r = $UNI.get_rank v in 
							case+ map_find (!sorted, r) of 
							| Nothing _ => !sorted := map_insert (!sorted, r, v :: nil ())
							| Just vs   => !sorted := map_update (!sorted, r, v :: vs)
							end

	exception Cycle of variable

	val init = lam v =<cloref1> if $UNI.occurs_check v then $raise Cycle v else (init_young v; init_sorted v)
	val _ = list_foreach (current_vars, lam v => init v)

	(***********************************)
	(* 
		adjust will update variables rank. it works as follows

		- check visited:
		  true  => it must have rank lower than target rank, since we start exploring from lower rank
		  false => 
			- mark as visited
			- adjust rank to target rank since it is
			  either a variable already at this rank
			  or its parent is at this rank and as a child

			  in any case, it should adjust to have target rank

			- for each young variable (variable registered at the current `let`)
				- adjust children to have at most target rank
				- adjust parent to have the max of children's rank

                  there is no need to children to have higher rank than parents
				  there is no need for parent to have higher rank than the max of its children
	*) 

	fun adjust (v: variable, target_rank: int): void = let 
		val _ = assert ($UNI.get_rank v >= RANK_BASE)
	in 
		if is_visited v
		then assert ($UNI.get_rank v <= target_rank)
		else 
			let 
				val _ = mark v
				val _ = $UNI.adjust_rank (v, target_rank)

			(* we are only dealing with variables registered at current level *)	
			in if is_young v then 

				(* 
					if it has structure, we need to traverse its children to lower their rank
					and when coming back up, adjust the parent's rank. 
				*)
				case+ $UNI.get_struct v of 
				| Nothing _ => ()
				| Just s    => 
					let val rank = 
						$UNI.struct_fold (s, RANK_BASE,
							lam (v, ret) => let val _ = adjust (v, target_rank)
							in max ($UNI.get_rank v, ret) end)
					in 
						$UNI.adjust_rank (v, rank)
					end
			end
	end


	(* now iterate through ranked variables, and adjust their ranks *)
	fun loop (r: int): void = 
		if r <= !(ctx.current_rank) then 
		case+ map_find (!sorted, r) of 
		| Nothing () => loop (r+1)
		| Just vs    => list_foreach (vs, lam v => adjust (v, r))

	val _ = loop (RANK_BASE)

	(* 
		now, we need to 

		1. move the variables to correct pools (of ranks lower than current_rank)
		2. generalize variables (of ranks equal to current_rank)
	*)
	val relocate = lam v =<cloref1> register_at_rank (ctx, v, $UNI.get_rank v)
	val gen      = lam v =<cloref1> $UNI.set_rank (v, RANK_GENERIC)
	val quantifiers = list_filter (
						current_vars, 
						lam v => 
							if $UNI.get_rank v < !(ctx.current_rank) 
							then (relocate v; false) 
							else (gen v; $UNI.has_struct v))

	val _ = map_delete (!(ctx.vars), !(ctx.current_rank))
	val _ = !(ctx.current_rank) := !(ctx.current_rank) - 1

in 
	quantifiers
end

implement instantiate (ctx, scheme) = let 
	val visited = set_make<int> ()

	fun copy (v: variable):<cloref1> variable = 
		if $UNI.get_rank v != RANK_GENERIC

		(* if it is not generic, return without copy *)
		then v 

		(* copy recursively*)
		else 
			if set_member (visited, $UNI.get_id v)
			then v
			else let 
				val vv = $UNI.fresh (Nothing (), !(ctx.current_rank))
				val _ = register (ctx, vv)
				val _ = set_insert (visited, $UNI.get_id vv)
			in case+ $UNI.get_struct v of 
				| Nothing _ => vv
				| Just s    => 
					let 
						val ss = $UNI.struct_map (s, copy)
						val _ = $UNI.set_struct (vv, Just ss)
					in vv end
			end
in 
	case+ scheme of 
	| Scheme (qs, body) => $tup(list_map (qs, copy), copy body)
end

end