 
staload "list.sats"
staload "maybe.sats"
staload UF = "unionfind.sats"

(* unification variable 

   it is either an atomic variable, 
   or a variable with structures, namely, a variable consists of 
   sub-variables. It will be represented as an union/find point whose
   payload is a descriptor 

   *)
abstype variable = ptr 

(* type structure
   
   if a unification variable is not atomic, then it has some structure
   like F(a,b,c). That means the structure need to be unified recursively.
   Thus it needs to provide iteration functions. Note that those a,b,c again
   are unification variables that may or may not have structures. 

   the user is expected to instantiate this abstract type, e.g.

   datatype types (a:t@ype) = 
   | Base of int 
   | One of a
   | Two of (a, a) 

   assume structure (a:t@ype) = types a 

   *)
abstype structure (a:t@ype) = ptr 

val fresh: (maybe (structure variable), int) -> variable
fun get_id      (variable): int 
fun get_struct  (variable): maybe (structure variable)
fun set_struct  (variable, maybe (structure variable)): void 
fun has_struct  (variable): bool
fun get_rank    (variable): int 
fun set_rank    (variable, int): void
fun adjust_rank (variable, int): void

fun {a,b:t@ype} struct_map   (structure a, a -<cloref1> b): structure b
fun {a:t@ype}   struct_iter  (structure a, a -<cloref1> void): void 
fun {a,b:t@ype} struct_iter2 (structure a, structure b, (a, b) -<cloref1> void): void 
fun {a,b:t@ype} struct_fold  (structure a, b, (a, b) -<cloref1> b): b


fun {} unify (variable, variable): void 
fun equiv    (variable, variable): bool 
fun is_repr  (variable): bool 


fun occurs_check (variable): bool

