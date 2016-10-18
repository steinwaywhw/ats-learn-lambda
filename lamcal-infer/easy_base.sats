#include "share/atspre_staload.hats"
staload "list.sats"
staload "maybe.sats"

datatype term = 
| TermVar of string
| TermApp of (term, term)
| TermLam of (string, term)
| TermFix of (string, string, term)
| TermInt of int
| TermBool of bool
| TermLet of (string, term, term)

#define INT 1
#define BOOL 2

datatype type = 
| TypeBase  of int
| TypeVar   of string 
| TypeArrow of (type, type)

typedef rank = int

abstype ranktype = ptr
abstype ctx = ptr
abstype env (a:t@ype) = ptr

fun {a:t@ype} initenv (): env a
fun {a:t@ype} lookup (env a, a): maybe ranktype 
fun {a:t@ype} extend (env a, a, ranktype): env a

fun initctx (): ctx 
fun enter (ctx): void
fun exit (ctx): void

fun fresh (rank): ranktype
fun arrow (rank, ranktype, ranktype): ranktype 
fun constant (int): ranktype
fun adjust_rank (ranktype, rank): void 


fun show_ranktype (ranktype): void
fun show_type (type): void
fun show_term (term): void
fun decode (ranktype): type

fun gen (ranktype, rank): void 
fun inst (ranktype, rank): ranktype

fun typeof (env string, ctx, term): ranktype
fun infer (term): type


