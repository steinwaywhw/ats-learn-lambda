


#include "share/atspre_staload.hats"
staload "list.sats"
staload "maybe.sats"



datatype term = 
| TermVar of string
| TermApp of (term, term)
| TermLam of (string, term)
| TermFix of (string, string, term)
//| TermInt of int
//| TermBool of bool
| TermLet of (string, term, term)


//#define INT 1
//#define BOOL 2

datatype type = 
//| TypeBase  of int
| TypeVar   of string 
| TypeArrow of (type, type)

typedef rank = int
datatype desc = 
//| 
| UnboundVar of (int, rank)
| UnboundArr of (int, rank, ref desc, ref desc)
| Link       of ref desc
typedef ranktype = ref desc


typedef ctx = $rec{curr_rank = ref int}
typedef mapping (a:t@ype) = $tup(a, ranktype)
typedef env (a:t@ype) = list (mapping a)

fun {a:t@ype} initenv (): env a
fun {a:t@ype} lookup (env a, a): maybe ranktype 
fun {a:t@ype} extend (env a, a, ranktype): env a

fun initctx (): ctx 
fun enter (ctx): void
fun exit (ctx): void

#define GENERIC ~1

val counter: (() -> int, () -> void)
fun fresh (rank): ranktype
fun arrow (rank, ranktype, ranktype): ranktype 

//fun union (ranktype, ranktype): void 
fun repr (ranktype): ranktype 
fun is_repr (ranktype): bool
fun equiv (ranktype, ranktype): bool

fun rank (ranktype): rank 
fun set_rank (ranktype, rank): void
fun id (ranktype): int 

fun occurs_check (ranktype): bool 

fun unify (ranktype, ranktype): void 
fun adjust_rank (ranktype, rank): void 


fun show_ranktype (ranktype): void
fun show_type (type): void
fun show_term (term): void
fun decode (ranktype): type

fun gen (ranktype, rank): void 
fun inst (ranktype, rank): ranktype

fun typeof (env string, ctx, term): ranktype
fun infer (term): type


