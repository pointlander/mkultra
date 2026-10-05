// Copyright 2026 The mkultra. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"bytes"
	"testing"
)

func TestNot(t *testing.T) {
	not, f, tru := booleans()
	if got := not.String(); got != "[[],[[[],[]],[[]]]]" {
		t.Fatalf("not = %s", got)
	}
	if got := apply(not, f, 1000).String(); got != "[[]]" {
		t.Fatalf("not false = %s, want [[]]", got)
	}
	if got := apply(not, tru, 1000).String(); got != "[]" {
		t.Fatalf("not true = %s, want []", got)
	}
	// The same trees can be applied again, as in run.js.
	if got := apply(not, f, 1000).String(); got != "[[]]" {
		t.Fatalf("not false again = %s, want [[]]", got)
	}
	if got := apply(not, apply(not, f, 1000), 1000).String(); got != "[]" {
		t.Fatalf("not (not false) = %s, want []", got)
	}
}

func TestInputsNotMutated(t *testing.T) {
	not, f, tru := booleans()
	beforeNot, beforeF, beforeT := not.String(), f.String(), tru.String()
	_ = apply(not, f, 1000)
	_ = apply(not, tru, 1000)
	if not.String() != beforeNot || f.String() != beforeF || tru.String() != beforeT {
		t.Fatalf("apply mutated an input: not %s f %s t %s", not, f, tru)
	}
}

func TestRules(t *testing.T) {
	// Distinct shapes so a rule that returns the wrong subtree fails.
	y := fork(leaf(), leaf())       // △ △ △ = [[],[]]
	z := stem(stem(leaf()))         // △ (△ △) = [[[]]]
	w := stem(leaf())               // △ △ = [[]]
	x := fork(stem(leaf()), leaf()) // △ (△ △) △ = [[],[[]]]
	u := leaf()                     // △ = []
	v := stem(stem(leaf()))         // △ (△ △) = [[[]]]

	cases := []struct {
		name string
		got  *node
		want string
	}{
		{
			name: "absorb-leaf",
			got:  apply(leaf(), y, 1000),
			want: "[[[],[]]]",
		},
		{
			name: "absorb-stem",
			got:  apply(stem(x), y, 1000),
			want: "[[[],[]],[[],[[]]]]",
		},
		{
			name: "K",
			// △ △ y z → y
			got:  apply(apply(stem(leaf()), y, 1000), z, 1000),
			want: "[[],[]]",
		},
		{
			name: "rule2",
			// △ (△ △) △ △ → △ △ (△ △)
			got:  apply(apply(stem(stem(leaf())), leaf(), 1000), leaf(), 1000),
			want: "[[[]],[]]",
		},
		{
			name: "rule3a",
			// △ (△ w x) y △ → w
			got:  apply(fork(fork(w, x), y), leaf(), 1000),
			want: "[[]]",
		},
		{
			name: "rule3b",
			// △ (△ w x) y (△ u) → x u = △ △ (△ △)
			got:  apply(fork(fork(w, x), y), stem(u), 1000),
			want: "[[[]],[]]",
		},
		{
			name: "rule3c",
			// △ (△ w x) y (△ u v) → y u v = △ (△ (△ △))
			got:  apply(fork(fork(w, x), y), fork(u, v), 1000),
			want: "[[[[]]]]",
		},
	}
	for _, tc := range cases {
		if tc.got.String() != tc.want {
			t.Errorf("%s = %s, want %s", tc.name, tc.got, tc.want)
		}
	}
}

// val is an independent algebraic evaluator used as an oracle.
// It follows the OCaml reference on https://treecalcul.us/implementation/.
type kind int

const (
	kindLeaf kind = iota
	kindStem
	kindFork
)

type val struct {
	k    kind
	a, b *val
}

func (v *val) String() string {
	switch v.k {
	case kindLeaf:
		return "[]"
	case kindStem:
		return "[" + v.a.String() + "]"
	case kindFork:
		return "[" + v.b.String() + "," + v.a.String() + "]"
	default:
		return "?"
	}
}

func (v *val) tree() *node {
	switch v.k {
	case kindLeaf:
		return leaf()
	case kindStem:
		return stem(v.a.tree())
	case kindFork:
		return fork(v.a.tree(), v.b.tree())
	default:
		panic("bad val")
	}
}

func applyVal(fun, arg *val) *val {
	switch fun.k {
	case kindLeaf:
		return &val{k: kindStem, a: arg}
	case kindStem:
		return &val{k: kindFork, a: fun.a, b: arg}
	case kindFork:
		switch fun.a.k {
		case kindLeaf:
			return fun.b
		case kindStem:
			return applyVal(applyVal(fun.a.a, arg), applyVal(fun.b, arg))
		case kindFork:
			switch arg.k {
			case kindLeaf:
				return fun.a.a
			case kindStem:
				return applyVal(fun.a.b, arg.a)
			case kindFork:
				return applyVal(applyVal(fun.b, arg.a), arg.b)
			}
		}
	}
	panic("unreachable")
}

func allVals(maxNodes int) [][]*val {
	out := make([][]*val, maxNodes+1)
	out[1] = []*val{{k: kindLeaf}}
	for n := 2; n <= maxNodes; n++ {
		for _, a := range out[n-1] {
			out[n] = append(out[n], &val{k: kindStem, a: a})
		}
		for left := 1; left <= n-2; left++ {
			right := n - 1 - left
			for _, a := range out[left] {
				for _, b := range out[right] {
					out[n] = append(out[n], &val{k: kindFork, a: a, b: b})
				}
			}
		}
	}
	return out
}

func TestK(t *testing.T) {
	// Minimum pair sizes, checked by enumerating every smaller pair.
	cases := []struct {
		target []byte
		want   int
	}{
		{[]byte{0}, 2},    // apply(△, △) = △ △
		{[]byte{0, 0}, 3}, // apply(△, △ △) = △ (△ △)
		{[]byte{1}, 3},    // apply(△ △, △) = △ △ △
		{nil, 4},          // apply(△ △ △, △) = △
	}
	for _, tc := range cases {
		if got := K(tc.target); got != tc.want {
			t.Errorf("K(%v) = %d, want %d", tc.target, got, tc.want)
		}
	}
}

func TestKExact(t *testing.T) {
	target := []byte{1, 0, 0, 1, 0, 0, 1, 0, 0, 1}
	fun, arg, got := smallest(target)
	if got != 15 {
		t.Fatalf("K(target) = %d, want 15", got)
	}
	out := apply(fun, arg, 1000)
	if !bytes.Equal(out.Data(), target) {
		t.Fatalf("witness serializes to %v", out.Data())
	}
	if K([]byte{2}) != -1 {
		t.Fatal("K of a byte outside {0,1} should be -1")
	}
	if quoteCost(target) != got {
		t.Fatalf("quote = %d, K = %d", quoteCost(target), got)
	}
}

func TestTerm(t *testing.T) {
	if got := fork(stem(leaf()), leaf()).term(); got != "△ (△ △) △" {
		t.Fatalf("term = %s", got)
	}
}

func TestCompressing(t *testing.T) {
	hits := compressing(11)
	if len(hits) == 0 {
		t.Fatal("expected a string shorter than its quote")
	}
	for i, h := range hits {
		if h.size >= quoteCost(h.data) {
			t.Fatalf("hit %d does not compress: size %d quote %d", i, h.size, quoteCost(h.data))
		}
		out := apply(h.fun, h.arg, 1000)
		if !bytes.Equal(out.Data(), h.data) {
			t.Fatalf("hit %d serializes to %v, stored %v", i, out.Data(), h.data)
		}
		if i > 0 {
			prev := hits[i-1]
			if prev.size > h.size || (prev.size == h.size && bytes.Compare(prev.data, h.data) > 0) {
				t.Fatalf("hits not ordered at %d", i)
			}
		}
	}
	if K(hits[0].data) != hits[0].size {
		t.Fatalf("K(%v) = %d, census %d", hits[0].data, K(hits[0].data), hits[0].size)
	}
}

func TestMatchesOracle(t *testing.T) {
	// Big enough to exercise every rule. Past this, the recursive
	// oracle overflows the stack on some terms.
	const maxNodes = 5
	bySize := allVals(maxNodes)
	var vals []*val
	for n := 1; n <= maxNodes; n++ {
		vals = append(vals, bySize[n]...)
	}
	for _, fun := range vals {
		for _, arg := range vals {
			want := applyVal(fun, arg).String()
			got := apply(fun.tree(), arg.tree(), 1000).String()
			if got != want {
				t.Fatalf("apply %s %s = %s, oracle %s", fun, arg, got, want)
			}
		}
	}
}
