
#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "solver.sats"
staload UNI = "unifier.sats"
staload GEN = "generalizer.sats"



implement solve (c) = let 
	val ctx = $GEN.init ()

	exception Unbound of termvar 
	exception Cycle 

	fun do (env: map (termvar, scheme), c: rawcstr): void = 
		case+ c of 
		| CstrTrue             => ()
		| CstrConj (c1, c2)    => (do (env, c1); do (env, c2))
		| CstrEq (v1, v2)      => $UNI.unify (v1, v2)
		| CstrExist (v, c)     => ($GEN.register (ctx, v); do (env, c))
		| CstrDef (term, v, c) => let val env = map_insert (env, term, $GEN.generalize v) in do (env, c) end
		| CstrInst (term, v, hook) => 
			(case+ map_find (env, term) of 
			| Nothing => $raise Unbound (term)
			| Just s  => 
				let 
					val (newvars, body) = $GEN.instantiate (ctx, s)
					val _ = !hook := newvars
				in 
					$UNI.unify (body, v)
				end
			)
		| CstrLet (hook, c1, ls, c2) => 
			let 
				val _ = $GEN.enter ctx
				val vs = list_map (ls, lam x => x.1)

				val _ = list_foreach (vs, lam v => $GEN.register (ctx, v))
				val _ = do (env, c1)

				val qs = $GEN.exit ctx
				val _ = !hook := qs 

				val process = 
					lam (l, env) =<cloref1> let 
						val (term, v, hook) = l 
						val scheme = $GEN.generalize v 
						val _ = !hook := scheme 
					in 
						map_insert (env, x, scheme)
					end

				val env = list_foldl (ls, env, process)
			in 
				do (env, c2)
			end
in 
	do (map_make<termvar, scheme> (), c)
end 
