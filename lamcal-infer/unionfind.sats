

abstype point (a:t@ype) = ptr



fun {a:t@ype} fresh (a): point a
fun {a:t@ype} union (point a, point a, (a, a) -<cloref1> a): void 
fun {a:t@ype} get_desc  (point a): a 
fun {a:t@ype} set_desc (point a, a): void
fun {a:t@ype} is_equiv (point a, point a): bool 
fun {a:t@ype} is_repr (point a): bool 

