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
	"bytes"
	"fmt"
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
func apply(fun, arg *node, fuel int) *node {
	out, _ := reduce(fun, arg, fuel)
	return out
}

// reduce is apply plus a flag that is true when a non-value was discarded
// instead of contracted. Callers that need a real normal form skip those.
// Reduction also stops after fuel contractions, or after fuel uses of the
// duplicating rule. A stopped term can still contain a redex.
func reduce(fun, arg *node, fuel int) (expression *node, discarded bool) {
	expression = &node{kids: make([]*node, 0, 1+len(fun.kids))}
	expression.push(arg)
	expression.pushKids(fun)

	todo, count, made := []*node{expression}, 0, 0
	for len(todo) > 0 && count < fuel {
		f := todo[len(todo)-1]
		todo = todo[:len(todo)-1]
		if len(f.kids) < 3 {
			continue
		}
		if made >= fuel {
			break
		}
		todo = append(todo, f)
		a := f.pop()
		b := f.pop()
		c := f.pop()
		switch len(a.kids) {
		case 0: // △ △ b c → b
			f.pushKids(b)
		case 1: // △ (△ x) b c → x c (b c)
			made++
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
				discarded = true
			}
		default:
			// a is not a value. run.js drops this redex.
			discarded = true
		}
		count++
	}
	return expression, discarded
}

// booleans builds false = △, true = △ △, and not = △ (△ true (△ △ false)) △.
func booleans() (not, f, t *node) {
	f = leaf()
	t = stem(leaf())
	not = fork(fork(t, fork(leaf(), f)), leaf())
	return not, f, t
}

// Data serializes a value in preorder: 0 is a stem, 1 is a fork.
// Leaves write nothing. A node that is not a value writes nothing.
func (n *node) Data() []byte {
	var d func(n *node, data *[]byte)
	d = func(n *node, data *[]byte) {
		if len(n.kids) == 1 {
			*data = append(*data, 0)
			d(n.kids[0], data)
		} else if len(n.kids) == 2 {
			*data = append(*data, 1)
			d(n.kids[0], data)
			d(n.kids[1], data)
		}
	}
	data := []byte{}
	d(n, &data)
	return data
}

// valueNodes reports whether n is a finished value of at most maxNodes
// nodes, and returns that node count. A node with three or more children
// is an unfinished redex.
func (n *node) valueNodes(maxNodes int) (int, bool) {
	if n == nil || maxNodes < 1 || len(n.kids) > 2 {
		return 0, false
	}
	total := 1
	for _, k := range n.kids {
		sub, ok := k.valueNodes(maxNodes - total)
		if !ok {
			return 0, false
		}
		total += sub
	}
	return total, true
}

// matches reports whether n is a finished value whose serialization is
// exactly target. A value that emits len(target) bytes has at most
// 2*len(target)+1 nodes, so anything larger is rejected early.
func matches(n *node, target []byte) bool {
	if _, ok := n.valueNodes(2*len(target) + 1); !ok {
		return false
	}
	return bytes.Equal(n.Data(), target)
}

// treesOf builds every tree of exactly n nodes from smaller trees.
// A tree is a leaf, a stem of one child, or a fork of two children.
func treesOf(n int, by [][]*node) []*node {
	out := make([]*node, 0, len(by[n-1]))
	for _, child := range by[n-1] {
		out = append(out, stem(child))
	}
	for left := 1; left <= n-2; left++ {
		right := n - 1 - left
		for _, a := range by[left] {
			for _, b := range by[right] {
				out = append(out, fork(a, b))
			}
		}
	}
	return out
}

// K is the number of nodes in the smallest pair of trees whose application
// reduces to a value that serializes to target. Pairs are enumerated in
// order of increasing size, so the first exact match is a minimum.
// Unfinished reductions are skipped. K returns -1 when target contains a
// byte other than 0 or 1, or when no pair within the size bound works.
func K(target []byte) int {
	_, _, size := smallest(target)
	return size
}

// smallest returns one minimum pair and its node count.
func smallest(target []byte) (a, b *node, size int) {
	const fuel = 1000
	for _, bit := range target {
		if bit > 1 {
			return nil, nil, -1
		}
	}
	// apply(△ △ spine, △) reproduces a spine value of this serialization.
	// That pair is an upper bound on the size K has to search.
	ones := 0
	for _, bit := range target {
		if bit == 1 {
			ones++
		}
	}
	limit := len(target) + ones + 4
	if limit < 4 {
		limit = 4
	}
	by := make([][]*node, limit)
	by[1] = []*node{leaf()}
	for total := 2; total <= limit; total++ {
		for sa := 1; sa < total; sa++ {
			for _, fun := range by[sa] {
				for _, arg := range by[total-sa] {
					out, discarded := reduce(fun, arg, fuel)
					if discarded || !matches(out, target) {
						continue
					}
					return fun, arg, total
				}
			}
		}
		if total < limit {
			by[total] = treesOf(total, by)
		}
	}
	return nil, nil, -1
}

func main() {
	not, f, t := booleans()
	// [[]] = true
	fmt.Printf("apply(not, false) = %s\n", apply(not, f, 1000))
	// [] = false
	fmt.Printf("apply(not, true) = %s\n", apply(not, t, 1000))

	target := []byte{1, 0, 0, 1, 0, 0, 1, 0, 0, 1}
	fmt.Println("k=", K(target))
}
