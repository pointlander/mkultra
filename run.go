// Copyright 2026 The mkultra. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Command mkultra is a branch-first evaluator for triage calculus,
// the tree calculus at https://treecalcul.us. It is a Go port of run.js.
//
// A tree is one node. Children are stored right to left, so the first
// argument in the calculus is the last slice element:
//
//	△        []
//	△ a      [a]
//	△ a b    [b, a]
//	△ a b c  [c, b, a]
//
// Application prepends the argument. A node with three or more children
// is a redex and contracts in place:
//
//	△ △ b c             → b
//	△ (△ x) b c         → x c (b c)
//	△ (△ w x) b △       → w
//	△ (△ w x) b (△ u)   → x u
//	△ (△ w x) b (△ u v) → b u v
package main

import (
	"fmt"
	"math/rand"
	"strings"
)

// A node is one tree. An empty kids slice is the leaf △.
type node struct {
	kids []*node
}

func leaf() *node { return &node{} }

// stem is △ a.
func stem(a *node) *node { return &node{kids: []*node{a}} }

// fork is △ a b.
func fork(a, b *node) *node { return &node{kids: []*node{b, a}} }

func (n *node) pop() *node {
	last := n.kids[len(n.kids)-1]
	n.kids = n.kids[:len(n.kids)-1]
	return last
}

func (n *node) push(xs ...*node) {
	n.kids = append(n.kids, xs...)
}

// pushKids appends other's children, not other itself.
// This is the JavaScript spread `push(...other)`.
func (n *node) pushKids(other *node) {
	n.kids = append(n.kids, other.kids...)
}

func (n *node) String() string {
	var b strings.Builder
	n.writeTo(&b)
	return b.String()
}

func (n *node) writeTo(b *strings.Builder) {
	b.WriteByte('[')
	for i, k := range n.kids {
		if i > 0 {
			b.WriteByte(',')
		}
		k.writeTo(b)
	}
	b.WriteByte(']')
}

// apply reduces fun applied to arg. fun and arg are not modified.
// Subtrees may be shared with the result the same way as in run.js.
func apply(fun, arg *node) *node {
	expression := &node{kids: make([]*node, 0, 1+len(fun.kids))}
	expression.push(arg)
	expression.pushKids(fun)

	todo := []*node{expression}
	for len(todo) > 0 {
		f := todo[len(todo)-1]
		todo = todo[:len(todo)-1]
		if len(f.kids) < 3 {
			continue
		}
		todo = append(todo, f)
		a := f.pop()
		b := f.pop()
		c := f.pop()
		switch len(a.kids) {
		case 0: // △ △ b c → b
			f.pushKids(b)
		case 1: // △ (△ x) b c → x c (b c)
			newPotRedex := &node{kids: make([]*node, 0, 1+len(b.kids))}
			newPotRedex.push(c)
			newPotRedex.pushKids(b)
			f.push(newPotRedex, c)
			f.pushKids(a.kids[0])
			todo = append(todo, newPotRedex)
		case 2: // △ (△ w x) b c, triage on c
			switch len(c.kids) {
			case 0: // → w
				f.pushKids(a.kids[1])
			case 1: // → x u
				f.push(c.kids[0])
				f.pushKids(a.kids[0])
			case 2: // → b u v
				f.push(c.kids[0], c.kids[1])
				f.pushKids(b)
			default:
				// c is not a value. run.js drops this redex.
			}
		default:
			// a is not a value. run.js drops this redex.
		}
	}
	return expression
}

// booleans builds false = △, true = △ △, and not = △ (△ true (△ △ false)) △.
func booleans() (not, f, t *node) {
	f = leaf()
	t = stem(leaf())
	not = fork(fork(t, fork(leaf(), f)), leaf())
	return not, f, t
}

// Node is a node in a tree
type Node struct {
	N [3]*Node
	H uint64
}

// Nodes is a tree full of nodes
func Nodes(depth int) *Node {
	node := &Node{}
	var add func(depth int, node *Node) *Node
	add = func(depth int, node *Node) *Node {
		if depth <= 0 {
			return node
		}
		node.N[0] = &Node{H: 1}
		add(depth-1, node.N[0])
		node.N[1] = &Node{H: 1}
		add(depth-1, node.N[1])
		node.N[2] = &Node{H: 1}
		add(depth-1, node.N[2])
		return node
	}
	return add(depth, node)
}

// Sample samples from the node
func Sample(rng *rand.Rand, nodes *Node) *node {
	if nodes.N[0] == nil {
		return leaf()
	}
	sum := uint64(0)
	for _, n := range nodes.N {
		sum += n.H
	}
	total, selected := uint64(0), uint64(rng.Intn(int(sum)))
	for i, n := range nodes.N {
		total += n.H
		if selected < total {
			switch i {
			case 0:
				return leaf()
			case 1:
				return stem(Sample(rng, nodes.N[1]))
			case 2:
				return fork(Sample(rng, nodes.N[2]), Sample(rng, nodes.N[2]))
			}
			break
		}
	}
	return nil
}

// Data generates data from the tree
func (n *node) Data() []byte {
	var d func(n *node, data *[]byte)
	d = func(n *node, data *[]byte) {
		if len(n.kids) == 1 {
			*data = append(*data, 0)
			d(n.kids[0], data)
		} else if len(n.kids) == 2 {
			*data = append(*data, 1)
			d(n.kids[1], data)
		}
	}
	data := []byte{}
	d(n, &data)
	return data
}

func main() {
	not, f, t := booleans()
	// [[]] = true
	fmt.Printf("apply(not, false) = %s\n", apply(not, f))
	// [] = false
	fmt.Printf("apply(not, true) = %s\n", apply(not, t))

	n1, n2 := Nodes(8), Nodes(8)
	rng := rand.New(rand.NewSource(1))
	for range 32 {
		a, b := Sample(rng, n1), Sample(rng, n2)
		fmt.Println(apply(a, b).Data())
	}
}
