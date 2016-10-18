



(*
	`rank` is a pointer to the `let` binder. It indicates the level at
	which a variable is bound. When a variable is created, it has the current
	rank maintained by a global context. 

	When unification is performed, ranks will be updated for equivalent 
	variables so that the smaller rank is kept. This is	because, if an 
	outer/older variable is unified with a inner/young/current variable, 
	then this young variable is essentially not owned by the current `let`, 
	thus can't be generalized. 

	After such unification, a type variables children need to update their ranks
	as well. For instance, 

		```
		(tz -> tapp) -> (tz -> tapp)
		lam x => let y = (lam z => x(z)) in y end

		T = let new tx(1) in tx(1) -> inst(ty)
			where ty = gen te
			where te = 
				let new tz(2) in 
				let new tapp(2) in 
				let tx(1) <=> ->(tz(2), tapp(2), 2) in    // unify, tx(1) <=> ->(tz(2), tapp(2), 1)  
				->(tz(2), tapp(2), 1)                     

			

		tx(1) <=> ->(tz(2), tapp(2), 2)
		      <=> ->(tz(2), tapp(2), 1)  <- after unification, rank 1 is used
		      <=> ->(tz(1), tapp(1), 1)  <- tz, tapp's rank need to be updated as well
		```



*)
staload UNI = "unifier.sats"
staload "list.sats"

datatype scheme = Scheme of (list $UNI.variable, $UNI.variable)
abstype ctx = ptr


fun init (): ctx
fun register (ctx, $UNI.variable): void 
fun enter (ctx): void
fun exit  (ctx): list $UNI.variable

fun generalize  ($UNI.variable): scheme
fun instantiate (ctx, scheme): $tup(list $UNI.variable, $UNI.variable)