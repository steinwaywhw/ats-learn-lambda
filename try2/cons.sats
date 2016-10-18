staload "parser.sats"
staload "list.sats"

typedef nat = intGte 0
exception LamParsingException of string


datatype variable = 
| VarName of (string, int)

and constant = 
| CstInt  of int 
| CstBool of bool 
| CstStr  of string 
| CstUnit 

and binding = 
| BindValue of (pattern, expression)
| BindRecur of (pattern, expression)

and pattern =
| PatVar of variable 
| PatCst of constant
| PatAny

and basetype = 
| BaseInt 
| BaseBool
| BaseStr
| BaseUnit

and monotype = 
| TypeVar   of variable 
| TypeBase  of basetype 
| TypeArrow of (monotype, monotype)

and polytype = 
| TypeScheme of (list variable, constraint, monotype)

and constraint = 
| ConsEq   of (monotype, monotype)
| ConsConj of list constraint
| ConsExi  of (variable, constraint)
| ConsIns  of (variable, monotype)
| ConsLet  of (variable, polytype, constraint)

and expression = 
| ExprVar  of variable
| ExprCst  of constant 
| ExprLam  of (pattern, expression)
| ExprLet  of (list binding, expression)
| ExprApp  of (expression, expression)
| ExprIf   of (expression, expression, expression)

typedef program = list binding



fun generate_constraint (program): constraint


////

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