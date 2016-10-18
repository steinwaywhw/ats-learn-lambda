staload "unionfind.sats"
staload _ = "unionfind.dats"



implement main0 () = () where {
	val p1 = fresh<int> 1
	val p2 = fresh<int> 2
	val p3 = fresh<int> 3 

	val _ = println! (equiv (p1, p2))

	val _ = union (p1, p2)
	val _ = println! (equiv (p1, p2))
	val _ = println! (equiv (p1, p3))
	val _ = println! (equiv (p2 ,p3))

	val _ = union (p2, p3)
	val _ = println! (equiv (p1, p2))
	val _ = println! (equiv (p1, p3))
	val _ = println! (equiv (p2 ,p3))


}