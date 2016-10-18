

abstype point (a:t@ype) = ptr

fun {a:t@ype} fresh (a): point a 
fun {a:t@ype} find  (point a): a 
fun {a:t@ype} union ((a, a) -<cloref1> a, point a, point a): void 
fun {a:t@ype} equiv (point a, point a): bool 
fun {a:t@ype} is_repr (point a): bool 
fun {a:t@ype} change (point a, a): void

