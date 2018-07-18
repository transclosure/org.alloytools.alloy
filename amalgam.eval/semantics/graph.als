sig Node {
	edge: set Node
}
run {one n:Node | one n.edge} for 2
