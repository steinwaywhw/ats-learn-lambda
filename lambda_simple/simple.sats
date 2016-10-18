

datatype ttype = 
| STBase of int 
| STFun of (ttype, ttype)

datatype tvar = 
| VarName  of string
| VarIndex of int 

datatype term = 
| TMInt  of int 
| TMBool of bool 
| TMUnit of ()
| TMVar  of tvar 
| TMLam  of (tvar, ttype, term)
| TMApp  of (term, term)

exception LamParsingException of string 

fun term_type_check (term): bool

staload "sexp.sats"

fun parse_simple_term (sexp): term

