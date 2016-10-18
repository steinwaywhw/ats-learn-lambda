
staload "list.sats"
staload "maybe.sats"
staload UF = "unionfind.sats"


abstype univar = ptr 
abstype structure (a:t@ype) = ptr 
typedef rank = int

val counter: () -> int 
val reset: () -> void

fun fresh (maybe (structure univar), rank): univar

fun get_id      (univar): int 
fun get_struct  (univar): maybe (structure univar)
fun set_struct  (univar, maybe (structure univar)): void 
fun has_struct  (univar): bool
fun get_rank    (univar): rank 
fun set_rank    (univar, rank): void
fun adjust_rank (univar, rank): void

fun {a,b:t@ype} struct_map   (structure a, a -<cloref1> b): structure b
fun {a:t@ype}   struct_iter  (structure a, a -<cloref1> void): void 
fun {a,b:t@ype} struct_iter2 (structure a, structure b, (a, b) -<cloref1> void): void 
fun {a,b:t@ype} struct_fold  (structure a, b, (a, b) -<cloref1> b): b

fun is_equiv (univar, univar): bool 
fun is_repr  (univar): bool 

fun {} unify (univar, univar): void 
fun {} occurs_check (univar): bool



