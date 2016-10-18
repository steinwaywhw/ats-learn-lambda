


#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "easy.sats"
staload "string.sats"
staload "list.sats"
staload "maybe.sats"

#define ::  ListCons
#define nil ListNil 



exception Cycle  
exception Unbound of string 


(* constraint context *)

implement initctx () = $rec{curr_rank = ref<int> 0}
implement enter (ctx) = !(ctx.curr_rank) := !(ctx.curr_rank) + 1
implement exit (ctx) = !(ctx.curr_rank) := !(ctx.curr_rank) - 1


(* typing environment *)

implement {a} initenv () = nil{mapping a} ()

implement {a} lookup (env, name) = let 
	staload "order.sats"
in 
	case+ env of 
	| $tup(n, t) :: ms when order_eq (n, name) => Just t 
	| _ :: ms => lookup (ms, name) 
	| _ => Nothing ()
end

implement {a} extend (env, name, type) = 
	$tup(name, type) :: env


(* fresh variable pool *)

implement counter = let
	val seed = ref<int> 0
in 
	(lam () => let val _ = !seed := !seed + 1 in !seed end,
	 lam () => !seed := 0)
end

implement fresh (rank) = 
	ref (UnboundVar (counter.0 (), rank))

implement arrow (rank, t1, t2) = 
	ref (UnboundArr (counter.0 (), rank, t1, t2))


(* union find and accessor *)

implement equiv (t1, t2) = 
	id (repr t1) = id (repr t2)

implement rank (t) = 
	case- !(repr t) of 
	| UnboundVar (_, rank)       => rank
	| UnboundArr (_, rank, _, _) => rank

implement id (t) = 
	case- !(repr t) of 
	| UnboundVar (id, _)       => id
	| UnboundArr (id, _, _, _) => id 

implement set_rank (t, rank) = let 
	val r = repr t
in  
	case- !r of 
	| UnboundVar (id, _)         => !r := UnboundVar (id, rank)
	| UnboundArr (id, _, t1, t2) => !r := UnboundArr (id, rank, t1, t2)
end

implement is_repr (t) = 
	case+ !t of 
	| Link _ => false 
	| _      => true

implement repr (t) = 
	if is_repr t then t 
	else 
		let 
			val- Link r = !t
		in 
			if is_repr r then r 
			else let val target = repr r in (!r := !target; target) end
		end


(* unification *)

implement unify (t1, t2) = 
	if equiv (t1, t2) then ()
	else 
		let 
			val r1 = repr t1 
			val r2 = repr t2 
		in
			case+ (!r1, !r2) of 
			| (UnboundArr (_, _, t1a, t1b), UnboundArr (_, _, t2a, t2b)) => 
				let 
					val _ = unify (t1a, t2a)
					val _ = unify (t1b, t2b)
				in 
					if rank r1 < rank r2 then !r2 := Link r1 else !r1 := Link r2 
				end
			| (UnboundArr _, _) => 
				let val r = min (rank r1, rank r2) 
				in (!r2 := Link r1; set_rank (r1, r)) end 

			| (_, UnboundArr _) => 
				let val r = min (rank r1, rank r2)
				in (!r1 := Link r2; set_rank (r2, r)) end 

			| (_, _) => if rank r1 < rank r2 then !r2 := Link r1 else !r1 := Link r2 

		end

implement occurs_check (t) = let 
	val MARK = ~1900

	val mark = lam t =<cloref1> let val r = rank t in (set_rank (t, MARK); r) end 
	val marked = lam t =<cloref1> rank t = MARK 

	fun check (t: ranktype): void = 
		case- !(repr t) of 
		| UnboundVar _ => ()
		| UnboundArr (_, _, t1, t2) => 
			if marked t then $raise Cycle ()
			else 
				let 
					val old = mark t
					val _ = check t1 
					val _ = check t2 
				in 
					set_rank (t, old)
				end
in 
	try (check t; false)
	with ~Cycle () => true 
end


(* print and decode *)

implement show_ranktype (t) = let 
	overload p with print_string
	overload p with print_char
	overload p with print_int 
	overload p with print_newline

	fun pid (id: int): void = 
		if id < 26 
		then p ($UNSAFE.cast{char} (id + 96))
		else p id 

	fun pp (t: ranktype): void = 
		case+ !t of 
		| Link t => 
			(p "Lk > "; pp t)

		| UnboundVar (id, rank) => 
			(p "Var("; pid id; p ","; p rank; p ")")

		| UnboundArr (id, rank, t1, t2) => 
			(p "Arr("; pid id; p ","; p rank; p ","; pp t1; p ","; pp t2; p ")")
in 
	(pp t; p ())
end


implement decode (t) = let 
	fun tostr (id: int): string = 
		if id < 26
		then string_from_char ($UNSAFE.cast{char} (id + 96))
		else string_from_int id
in 
	case- !(repr t) of 
	| UnboundVar (id, _) => TypeVar (tostr id)
	| UnboundArr (_, _, t1, t2) => TypeArrow (decode t1, decode t2)
end

implement show_type (t) = let 
	overload p with print_string

	fun pp (t: type): void = 
		case+ t of 
		| TypeVar v => p v 
		| TypeArrow (t1, t2) => (p "("; pp t1; p " -> "; pp t2; p ")")
in 
 	(pp t; print_newline ())
end

implement show_term (t) = let 
	overload p with print_string 

	fun pp (t: term): void = 
		case+ t of 
		| TermVar name => p name
		| TermApp (t1, t2) => (pp t1; p "("; pp t2; p ")")
		| TermLam (name, t) => (p "λ"; p name; p "."; pp t)
		| TermFix (name, arg, t) => (p "fix "; p name; p " = "; p "λ"; p arg; p "."; pp t) 
		| TermLet (name, t1, t2) => (p "let "; p name; p " = "; pp t1; p " in "; pp t2)
in 
	(pp t; print_newline ())
end

(* generalization *)

implement adjust_rank (t, cutoff) = let 
	
	fun adjust (t: ranktype, cutoff: rank): rank = 
		case- !(repr t) of
		| UnboundVar _ => 
			if cutoff < rank t 
			then (set_rank (t, cutoff); cutoff)
			else rank t
		| UnboundArr (id, oldrank, t1, t2) => 
			let 
				val r1 = adjust (t1, min (oldrank, cutoff))
				val r2 = adjust (t2, min (oldrank, cutoff))
				val _ = set_rank (t, max (r1, r2))
			in 
				max (r1, r2)
			end

	val _ = adjust (t, cutoff)
in 
end

implement gen (t, curr_rank) = let 

	fun g (t: ranktype): void = let 
		val r = repr t 
	in 
		case- !r of
		| UnboundVar (id, rank) =>
			if rank > curr_rank 
			then !r := UnboundVar (id, GENERIC)
		| UnboundArr (id, rank, t1, t2) =>
			if rank > curr_rank 
			then (g t1; g t2)
	end
in 
	(adjust_rank (t, curr_rank + 1); g t; adjust_rank (t, curr_rank))
end

implement inst (t, curr_rank) = let 
	val env = ref<env int> (initenv<int> ())

	fun loop (t: ranktype): ranktype = 
		let val r = repr t in 
		case+ !r of 
		| UnboundVar (id, rank) when rank = GENERIC =>
			(case+ lookup (!env, id) of 
			| Just t     => t 
			| Nothing () => 
				let val t = fresh curr_rank in 
				(!env := extend (!env, id, t); t)
				end
			)
		| UnboundArr (id, rank, t1, t2) when rank = GENERIC => 
			(case+ lookup (!env, id) of 
			| Just t => t 
			| Nothing () => 
				let val t = arrow (curr_rank, loop t1, loop t2) in 
				(!env := extend (!env, id, t); t)
				end
			)
		| _ => r
		end
in 
	loop t
end


(* type checking and inference *)

implement typeof (env, ctx, t) = let 

	fun dotypeof (env: env string, ctx: ctx, t: term): ranktype = 
		case+ t of 
		| TermVar name => 
			(case+ lookup (env, name) of 
			| Just type  => inst (type, !(ctx.curr_rank)) 
			| Nothing () => $raise Unbound (name)
			)
		| TermLam (name, body) => 
			let 
				val tname = fresh (!(ctx.curr_rank))
				val env = extend (env, name, tname)
				val tbody = typeof (env, ctx, body)
			in 
				arrow (!(ctx.curr_rank), tname, tbody)
			end
		| TermFix (name, arg, body) => 
			let 
				val tname = fresh !(ctx.curr_rank)
				val targ = fresh !(ctx.curr_rank)
				val env = extend (env, name, tname)
				val env = extend (env, arg, targ)
				val tbody = typeof (env, ctx, body)

				
				val tfun = arrow (!(ctx.curr_rank), targ, tbody)
				val _ = unify (tname, tfun)
				val _ = adjust_rank (tfun, !(ctx.curr_rank))
			in 
				tname
			end 
		| TermLet (name, exp, body) => 
			let 
				val _ = enter ctx 
				val texp = typeof (env, ctx, exp)
				val _ = exit ctx 
//				val _ = (print_int !(ctx.curr_rank); print_string "=>\t"; show_ranktype texp)
				val _ = gen (texp, !(ctx.curr_rank))
//				val _ = (print_int !(ctx.curr_rank); print_string "\t"; show_ranktype texp)
				val env = extend (env, name, texp)
			in 
				typeof (env, ctx, body)
			end 
		| TermApp (t1, t2) => 
			let 
				val tfun = typeof (env, ctx, t1)
				val targ = typeof (env, ctx, t2)
				val tres = fresh !(ctx.curr_rank)
				val tarr = arrow (!(ctx.curr_rank), targ, tres)
//				val _ = print_string "unifying: \n"
//				val _ = (print_string "=>\t"; show_ranktype tfun)
//				val _ = (print_string "=>\t"; show_ranktype tarr)
				val _ = unify (tfun, tarr)
				val _ = if occurs_check tfun then $raise Cycle ()

				// very important!
				val _ = adjust_rank (tfun, !(ctx.curr_rank))
//				val _ = (print_string "=>\t"; show_ranktype tfun)

			in 
				tres
			end

//	val _ = (print_int !(ctx.curr_rank); print_string "\t"; show_term t)
	val type = dotypeof (env, ctx, t)
//	val _ = (print_string "\t"; show_ranktype type)
in 
	type
end

implement infer (t) = let 
	val env = initenv<string> ()
	val ctx = initctx ()
	val _ = counter.1 ()
	val _ = enter ctx 
	val rt = typeof (env, ctx, t)
	val _ = exit ctx 
in 
	decode rt 
end



//implement main0 () = {
//	val tx = fresh 1
//	val _ = unify (tx, arrow (1, tx, tx))
//	val _ = adjust_rank (tx, 1)
//	val _ = show_ranktype tx
//	val _ = if occurs_check tx then $raise Cycle ()
//}


implement main0 () = {

	val runtest = 
		lam (t, expected) =<cloref1> 
			(show_term t; show_type (infer t); print_string "expected: "; print_string expected; print_string "\n\n")

	val runtestexn = 
		lam (t, expected) =<cloref1> 
			try runtest (t, expected) with
			| ~Cycle () => print_string "Cycle\n\n"
			| ~Unbound name => (print_string "Unbound: "; print_string name; print_newline (); print_newline ())

	//λx.x
	//(a->a)
	val id = TermLam ("x", TermVar "x")
	val _ = runtest (id, "a->a")
	
	//λx.λy.x(y)
	//((b->c)->(b->c))
	val eta = TermLam ("x", TermLam ("y", TermApp (TermVar "x", TermVar "y")))
	val _ = runtest (eta, "((b->c)->(b->c))")

	//let x = λx.λy.x(y) in x
	//((d->e)->(d->e))
	val test1 = TermLet ("x", eta, TermVar "x")
	val _ = runtest (test1, "((d->e)->(d->e))")

	//let y = λz.z in y
	//(b->b)
	val test2 = TermLet ("y", TermLam ("z", TermVar "z"), TermVar "y")
	val _ = runtest (test2, "(b->b)")

	//λx.let y = λz.z in y
	//(a->(c->c))
	val test3 = TermLam ("x", TermLet ("y", TermLam ("z", TermVar "z"), TermVar "y"))
	val _ = runtest (test3, "(a->(c->c))")

	//λx.let y = λz.z in y(x)
	//(c->c)
	val test4 = TermLam ("x", TermLet ("y", TermLam ("z", TermVar "z"), TermApp (TermVar "y", TermVar "x")))
	val _ = runtest (test4, "(c->c)")

	//λx.x(x)
	//occurs check
	val test5 = TermLam ("x", TermApp (TermVar "x", TermVar "x"))
	val _ = runtestexn (test5, "occurs check")


	//let x = x in x
	//unbound var
	val test6 = TermLet ("x", TermVar "x", TermVar "x")
	val _ = runtestexn (test6, "unbound var")

	//let id = λx.x in id(id)
	//(c->c)
	val test7 = TermLet ("id", TermLam ("x", TermVar "x"), TermApp (TermVar "id", TermVar "id"))
	val _ = runtest (test7, "(c->c)")

	//let x = λx.λy.x(y) in let y = let z = x(λx.x) in z in y
	//(i->i)
	val test8 = TermLet ("x", 
					TermLam ("x", TermLam ("y", TermApp (TermVar "x", TermVar "y"))), 
					TermLet ("y", 
						TermLet ("z", 
							TermApp (TermVar "x", TermLam ("x", TermVar "x")), 
							TermVar "z"), 
						TermVar "y"))
	val _ = runtest (test8, "i->i")

	//λx.λy.let x = x(y) in λx.y(x)
	//(((d->e)->c)->((d->e)->(d->e)))
	val test9 = TermLam ("x", TermLam ("y", TermLet ("x", TermApp (TermVar "x", TermVar "y"), TermLam ("x", TermApp (TermVar "y", TermVar "x")))))
	val _ = runtest (test9, "(((d->e)->c)->((d->e)->(d->e)))")

	//λx.let y = x in y
	//(a->a)
	val test10 = TermLam ("x", TermLet ("y", TermVar "x", TermVar "y"))
	val _ = runtest (test10, "(a->a)")

	//λx.let y = λz.x in y
	//(a->(c->a))
	val test11 = TermLam ("x", TermLet ("y", TermLam ("z", TermVar "x"), TermVar "y"))
	val _ = runtest (test11, "(a->(c->a))")

	//λx.let y = λz.x(z) in y
	//((b->c)->(b->c))
	val test12 = TermLam ("x", TermLet ("y", TermLam ("z", TermApp (TermVar "x", TermVar "z")), TermVar "y"))
	val _ = runtest (test12, "((b->c)->(b->c))")

	//λx.λy.let x = x(y) in x(y)
	//((b->(b->d))->(b->d))
	val test13 = TermLam ("x", TermLam ("y", TermLet ("x", TermApp (TermVar "x", TermVar "y"), TermApp (TermVar "x", TermVar "y"))))
	val _ = runtest (test13, "((b->(b->d))->(b->d))")

	//λx.let y = x in y(y)
	//occurs check
	val test14 = TermLam ("x", TermLet ("y", TermVar "x", TermApp (TermVar "y", TermVar "y")))
	val _ = runtestexn (test14, "occurs check")

	//λx.let y = let z = x(λx.x) in z in y
	//(((b->b)->c)->c)
	val test15 = TermLam ("x", TermLet ("y", TermLet ("z", TermApp (TermVar "x", TermLam ("x", TermVar "x")), TermVar "z"), TermVar "y"))
	val _ = runtest (test15, "(((b->b)->c)->c)")


	val test16 = TermFix ("rec", "x", TermApp (TermVar "rec", TermVar "x"))
	val _ = runtest (test16, "unknow")
	//All Done

	
}

