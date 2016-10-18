staload "parser.sats"

staload "list.sats"


typedef nat = intGte 0

exception LamParsingException of string

datatype tvar = 
| VarName  of (string)
| VarIndex of (nat, nat, string) (* two indices for multi-binders *)

datatype tcst =
| CstInt    of int
| CstBool   of bool
| CstString of string

datatype term = 
| TMVar of tvar 
| TMCst of tcst 
| TMLam of (list tvar, term)
| TMLet of (list @(tvar,term), term)
| TMFix of (tvar, list tvar, term)
| TMApp of (term, list term)
| TMIf  of (term, term, term)

datatype aterm = 
| ATMVar of tvar 
| ATMCst of tcst 
| ATMLam of aterm 
| ATMLet of (list aterm, aterm)
| ATMFix of aterm 
| ATMApp of (aterm, list aterm)
| ATMIf  of (aterm, aterm, aterm)
//| ATMRef of ref aterm 

datatype tmono = 
| TYVar    of tvar 
| TYBase   of int 
| TYArrow  of (list tmono, tmono)

datatype tpoly = 
| TYScheme of (list tvar, tmono)


datatype tconstraint = 
| TCEq of ()


staload "map.sats"
typedef tctx = map (tvar, tpoly)


//datetype atype = 
//| ATYVar   of tvar 
//| ATYBase  of int 
//| ATYArrow of 

staload "sexp.sats"

fun parse_term (sexp): term 

fun term_alpha (term): aterm 

fun aterm_open  (aterm, list aterm): aterm 
fun aterm_close (aterm, list tvar): aterm 

fun aterm_infer (aterm,)
//fun aterm_freevars (aterm): set tvar
//fun aterm_shift (aterm, int): aterm 
//fun aterm_subst (aterm, aterm): aterm 

//typedef path = list int 

//fun aterm_beta_reduce 