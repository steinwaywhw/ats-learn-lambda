


staload "unifier.sats"
staload "list.sats"

abstype ctx = ptr 

fun initgen (): ctx 
fun register (ctx, univar): void 
fun enter (ctx): void 
fun exit (ctx): void 

fun generalize (univar): void 
fun instantiate (univar): univar