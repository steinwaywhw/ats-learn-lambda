



staload UNI = "unifier.sats"
staload GEN = "generalizer.sats"


typedef variable = $UNI.variable 
typedef structure (a:t@ype) = $UNI.structure a
typedef scheme = $GEN.scheme

typedef termvar = string

datatype rawcstr =
| CstrTrue
| CstrConj of (rawcstr, rawcstr)
| CstrEq of (variable, variable)
| CstrExist of (variable, rawcstr)
| CstrInst of (termvar, variable, ref (list variable)) 
| CstrDef of (termvar, variable, rawcstr)
| CstrLet of (ref (list variable), rawcstr, list ($tup(termvar, variable, ref scheme)), rawcstr)


fun solve (rawcstr): void



(* interface *)

abstype constraint (a:t@ype) = ptr 

fun {a:t@ype}   cpure (a) = constraint a 
fun {a,b:t@ype} cconj (constraint a, constraint b): constraint ($tup(a, b))
fun {a,b:t@ype} cmap (constraint a, a -<cloref1> b): constraint b 
fun ceq (variable, variable): constraint (void)
fun {a:t@ype} cexist 
