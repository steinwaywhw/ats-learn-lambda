staload "list.sats"
staload "maybe.sats"

(* syntax *)

datatype typ = 
| TyFreeVar  of int
| TyBoundVar of int 
| TyForAll   of typ 
| TyArrow    of (typ, typ)

datatype term = 
| TmFreeVar  of int 
| TmBoundVar of int 
| TmLam      of (typ, term)
| TmTyLam    of term 
| TmApp      of (term, term)
| TmTyApp    of (term, typ)


(* infrastructure *)

fun {a:t@ype} fold_type (typ, 
	 					 int -<cloref1> a, 
						 int -<cloref1> a, 
						 a -<cloref1> a, 
						 (a, a) -<cloref1> a): a 

fun {a:t@ype} fold_term (term,
						 int -<cloref1> a, 
						 int -<cloref1> a, 
						 (typ, a) -<cloref1> a, 
						 a -<cloref1> a, 
						 (a, a) -<cloref1> a, 
						 (a, typ) -<cloref1> a): a

fun open_type_type (typ, int, typ): typ 
fun open_term_term (term, int, term): term
fun open_term_type (term, int, typ): term 

fun close_type_type (typ, int, int): typ
fun close_term_term (term, int, int): term 
fun close_term_type (term, int, int): term 


fun free_type_vars (typ): list int 
fun free_term_vars (term): list int
fun free_term_type_vars (term): list int

val fresh: () -> int

fun subst_term_term (term, int, term): term 
fun subst_type_type (typ, int, typ): typ 
fun subst_term_type (term, int, typ): term


(* capture-avoiding substitutino *)

fun term_cas (term, term): term 
fun type_cas (term, typ): term 


(* predicates *)

fun is_closed_term (term): bool 
fun is_closed_type (typ): bool


(* statics *)

fun typeof (term): typ


(* dynamics *)

fun reduce_head (term): maybe term 
fun reduce_full (term): maybe term

fun eval (term): term


(* language *)

typedef nat = intGte 0

fun app (term, term): term 
fun tyapp (term, typ): term
fun arr (typ, typ): typ

symintr >> 
symintr ~> 

overload >> with app 
overload >> with tyapp 
overload ~> with arr

// infixr (+) >> 
// infixl (+) ~>

fun succ (term): term 
//fun pred (term): term 
fun add (term, term): term 
//fun min (term, term): term 
fun mul (term, term): term 
fun id (term): term 
fun ite (term, term, term): term 
fun exp (term, term): term 
fun ackermann (term, term): term 

//val tm_pred: term
val tm_succ: term 
val tm_id: term 
val tm_ite: term 
val tm_add: term 
//val tm_min: term 
val tm_mul: term 
val tm_exp: term
val tm_ackermann: term

val ty_bool: typ 
val ty_nat: typ

fun {a:t@ype} church (a): term 
fun {a:t@ype} unchurch (term): a

