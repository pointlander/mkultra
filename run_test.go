// Copyright 2026 The mkultra. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "testing"

func TestNot(t *testing.T) {
	not, f, tru := booleans()
	if got := not.String(); got != "[[],[[[],[]],[[]]]]" {
		t.Fatalf("not = %s", got)
	}
	if got := apply(not, f).String(); got != "[[]]" {
		t.Fatalf("not false = %s, want [[]]", got)
	}
	if got := apply(not, tru).String(); got != "[]" {
		t.Fatalf("not true = %s, want []", got)
	}
	// The same trees can be applied again, as in run.js.
	if got := apply(not, f).String(); got != "[[]]" {
		t.Fatalf("not false again = %s, want [[]]", got)
	}
	if got := apply(not, apply(not, f)).String(); got != "[]" {
		t.Fatalf("not (not false) = %s, want []", got)
	}
}

func TestInputsNotMutated(t *testing.T) {
	not, f, tru := booleans()
	beforeNot, beforeF, beforeT := not.String(), f.String(), tru.String()
	_ = apply(not, f)
	_ = apply(not, tru)
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
			got:  apply(leaf(), y),
			want: "[[[],[]]]",
		},
		{
			name: "absorb-stem",
			got:  apply(stem(x), y),
			want: "[[[],[]],[[],[[]]]]",
		},
		{
			name: "K",
			// △ △ y z → y
			got:  apply(apply(stem(leaf()), y), z),
			want: "[[],[]]",
		},
		{
			name: "rule2",
			// △ (△ △) △ △ → △ △ (△ △)
			got:  apply(apply(stem(stem(leaf())), leaf()), leaf()),
			want: "[[[]],[]]",
		},
		{
			name: "rule3a",
			// △ (△ w x) y △ → w
			got:  apply(fork(fork(w, x), y), leaf()),
			want: "[[]]",
		},
		{
			name: "rule3b",
			// △ (△ w x) y (△ u) → x u = △ △ (△ △)
			got:  apply(fork(fork(w, x), y), stem(u)),
			want: "[[[]],[]]",
		},
		{
			name: "rule3c",
			// △ (△ w x) y (△ u v) → y u v = △ (△ (△ △))
			got:  apply(fork(fork(w, x), y), fork(u, v)),
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
			got := apply(fun.tree(), arg.tree()).String()
			if got != want {
				t.Fatalf("apply %s %s = %s, oracle %s", fun, arg, got, want)
			}
		}
	}
}
