#include "share/atspre_staload.hats"
#include "atsutils.hats"

staload "easy_base.sats"
staload "string.sats"
staload "list.sats"
staload "maybe.sats"

exception Cycle  
exception Unbound of string 
exception Unification of (ranktype, ranktype)
exception Iteration 

local (* LOCAL IN END *)

staload UNI = "unifier.sats"
staload UF = "unionfind.sats"
staload _ = "unifier.dats"
dynload "unifier.dats"
staload _ = "unionfind.dats"

#define ::  ListCons
#define nil ListNil 

#define GENERIC  ~1
#define NO_RANK   0
#define BASE_RANK 1


assume ranktype = $UNI.univar
assume ctx = $rec{curr_rank = ref int}
typedef mapping (a:t@ype) = $tup(a, ranktype)
assume env (a:t@ype) = list (mapping a)

datatype _struct (a:t@ype) = 
| StructBase  of int
| StructArrow of (a, a)
assume $UNI.structure (a:t@ype) = _struct a



in (* LOCAL IN END *)


(* constraint context *)

implement initctx () = $rec{curr_rank = ref<int> 0}
implement enter (ctx) = !(ctx.curr_rank) := !(ctx.curr_rank) + 1
implement exit (ctx) = !(ctx.curr_rank) := !(ctx.curr_rank) - 1


(* typing environment *)

implement {a} initenv () = let 
	val env = nil{mapping a} ()
in 
	env 
end

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


implement fresh (rank) = 
	$UNI.fresh (Nothing (), rank)

implement arrow (rank, t1, t2) = 
	$UNI.fresh (Just (StructArrow (t1, t2)), rank)

implement constant (t) = 
	$UNI.fresh (Just (StructBase t), NO_RANK)


(* structure *)

implement {a,b} $UNI.struct_iter2 (s1, s2, f) = 
	case+ (s1, s2) of 
	| (StructBase t1, StructBase t2) => if t1 = t2 then () else $raise Iteration ()
	| (StructArrow (a1, b1), StructArrow (a2, b2)) => (f (a1, a2); f (b1, b2))
	| (_, _) => $raise Iteration ()

implement {a} $UNI.struct_iter (s, f) = 
	case+ s of 
	| StructBase _ => ()
	| StructArrow (t1, t2) => (f t1; f t2)

//implement {a,b} $UNI.struct_map (s, f) = 
//	case+ s of 
//	| StructBase n => StructBase n
//	| StructArrow (t1, t2) => StructArrow (f t1, f t2)

//implement {a,b} $UNI.struct_fold (s, base, f) = 
//	case+ s of 
//	| StructBase _ => base 
//	| StructArrow (t1, t2) => f (t1, f (t2, base))


(* print and decode *)

//implement show_ranktype (t) = let 
//	overload p with print_string
//	overload p with print_char
//	overload p with print_int 
//	overload p with print_newline


//	datatype cc (a:t@ype) = 
//	| Link of ref (cc a)


//	fun pid (id: int): void = 
//		if id < 26 
//		then p ($UNSAFE.cast{char} (id + 96))
//		else p id 

//	fun pp (t: ranktype): void = 
//		case+ !t of 
//		| $UF.Link t => (p "Lk >"; pp t)
//		| $UF.Info (_, d) => 
//			let 
//				val id = $UNI.get_id t 
//				val rank = $UNI.get_rank t 
//			in 
//				case+ $UNI.get_struct t of 
//				| Nothing () => (p "Var("; pid id; p ","; p rank; p ")")
//				| Just s => 
//					case+ s of 
//					| StructBase n => (p "Base("; p n; p ","; p rank; p ")")
//					| StructArrow (t1, t2) => (p "Arr("; pid id; p ","; p rank; p ","; pp t1; p ","; pp t2; p ")")
//			end

//in 
//	(pp t; p ())
//end

implement show_ranktype (t) = let 
	val id = $UNI.get_id t 
	val rank = $UNI.get_rank t 

	overload p with print_int 
	overload p with print_string 
	overload p with print_newline 

in 
	(p id; p ","; p rank; p ";"; show_type (decode t))
end



implement decode (t) = let 
	fun tostr (id: int): string = 
		if id < 26
		then string_from_char ($UNSAFE.cast{char} (id + 96))
		else string_from_int id
in 
	case+ $UNI.get_struct t of 
	| Nothing _ => TypeVar (tostr ($UNI.get_id t))
	| Just s => 
		case+ s of 
		| StructBase t => TypeBase t 
		| StructArrow (t1, t2) => TypeArrow (decode t1, decode t2)
end

implement show_type (t) = let 
	overload p with print_string

	fun pp (t: type): void = 
		case+ t of 
		| TypeVar v => p v 
		| TypeArrow (t1, t2) => (p "("; pp t1; p " -> "; pp t2; p ")")
		| TypeBase t => 
			ifcase 
			| t = INT  => p "int"
			| t = BOOL => p "bool"
in 
 	(pp t; print_newline ())
end

implement show_term (t) = let 
	overload p with print_string 
	overload p with print_int 

	fun pp (t: term): void = 
		case+ t of 
		| TermVar name => p name
		| TermApp (t1, t2) => (pp t1; p "("; pp t2; p ")")
		| TermLam (name, t) => (p "λ"; p name; p "."; pp t)
		| TermFix (name, arg, t) => (p "fix "; p name; p " = "; p "λ"; p arg; p "."; pp t) 
		| TermLet (name, t1, t2) => (p "let "; p name; p " = "; pp t1; p " in "; pp t2)
		| TermInt n => p n 
		| TermBool b => if b then p "true" else p "false"
in 
	(pp t; print_newline ())
end


(* generalization *)

implement adjust_rank (t, cutoff) = let 
	
	fun adjust (t: ranktype, cutoff: rank): rank = 
		case+ $UNI.get_struct t of 
		| Nothing _ => ($UNI.adjust_rank (t, cutoff); $UNI.get_rank t)
		| Just s => 
			case+ s of 
			| StructBase _ => $UNI.get_rank t
			| StructArrow (t1, t2) => 
				let 
					val oldrank = $UNI.get_rank t 
					val r1 = adjust (t1, min (oldrank, cutoff))
					val r2 = adjust (t2, min (oldrank, cutoff))
					val _ = $UNI.set_rank (t, max (r1, r2))
				in 
					max (r1, r2)
				end

	val _ = adjust (t, cutoff)
in 
end

implement gen (t, curr_rank) = let 

	fun g (t: ranktype): void = 
		case+ $UNI.get_struct t of 
		| Nothing _ => if $UNI.get_rank t > curr_rank then $UNI.set_rank (t, GENERIC)
		| Just s => 
			if $UNI.get_rank t > curr_rank 
			then case+ s of 
				| StructBase _ => ()
				| StructArrow (t1, t2) => (g t1; g t2)
in 
	(adjust_rank (t, curr_rank + 1); g t; adjust_rank (t, curr_rank))
end


implement inst (t, curr_rank) = let 

	(* mapping from old id to new ranktype *)
	val env = ref<env int> (initenv<int> ())

	fun is_constant (t: ranktype): bool = 
		case+ $UNI.get_struct t of 
		| Nothing () => false 
		| Just s => 
			case+ s of 
			| StructBase _ => true 
			| _ => false

	fun loop (t: ranktype): ranktype = let 
		val id = $UNI.get_id t 
		val rank = $UNI.get_rank t 
	in 
		if is_constant t 
		then 
			let 
				val- Just (StructBase n) = $UNI.get_struct t 
			in 
				constant n 
			end 
		else 
			case+ $UNI.get_struct t of 
			| Nothing _ when rank = GENERIC => 
				(case+ lookup (!env, id) of 
				| Just t => t 
				| Nothing _ => 
					let val t = $UNI.fresh (Nothing (), curr_rank) in 
					(!env := extend (!env, id, t); t) 
					end
				)
			| Just s when rank = GENERIC => 
				(case+ lookup (!env, id) of
				| Just t => t 
				| Nothing _ => 
					case- s of 
					| StructArrow (t1, t2) => 
						let val t = arrow (curr_rank, loop t1, loop t2) in 
						(!env := extend (!env, id, t); t)
						end
				)

			| _ => t
	end
in 
	loop t
end


(* type checking and inference *)

implement typeof (env, ctx, t) = let 

	fun dotypeof (env: env string, ctx: ctx, t: term): ranktype = 
		case+ t of 
		| TermInt _ => constant INT
		| TermBool _ => constant BOOL
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
				val _ = $UNI.unify (tname, tfun)
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
				val _ = print_string "unifying: \n"
				val _ = (print_string "=>\t"; show_ranktype tfun)
				val _ = (print_string "=>\t"; show_ranktype tarr)
				val _ = $UNI.unify (tfun, tarr)
//				val _ = (print_string "=>\t"; show_type (decode tarr))
				val _ = if $UNI.occurs_check tfun then $raise Cycle ()

				// very important!
				val _ = adjust_rank (tfun, !(ctx.curr_rank))

			in 
				tres
			end

	val _ = (print_int !(ctx.curr_rank); print_string "\t"; show_term t)
	val type = dotypeof (env, ctx, t)
	val _ = (print_string "\t"; show_ranktype type)
in 
	type
end

implement infer (t) = let 
	val env = initenv<string> ()

	val env = extend (env, "+", arrow (NO_RANK, constant INT, arrow (NO_RANK, constant INT, constant INT)))


	val ctx = initctx ()
	val _ = $UNI.reset ()
	val _ = enter ctx 
	val rt = typeof (env, ctx, t)
	val _ = exit ctx 
in 
	decode rt 
end

end (* LOCAL IN END *)

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
	val _ = runtest (test16, "unknown")


	val test17 = TermLet ("x", TermLam ("x", TermLam ("y", TermApp (TermApp (TermVar "+", TermVar "x"), TermVar "y"))), TermApp (TermApp (TermVar "x", TermInt 10), TermInt 12))
	val _ = runtest (test17, "int")
	
}

