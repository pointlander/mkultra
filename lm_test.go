// Copyright 2026 The mkultra. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"math"
	"os"
	"strings"
	"testing"
)

func TestBookBody(t *testing.T) {
	raw, err := os.ReadFile("pg100.txt")
	if err != nil {
		t.Fatal(err)
	}
	body := bookBody(raw)
	if !strings.Contains(body, "THE SONNETS") {
		t.Fatal("body missing sonnets")
	}
	if strings.Contains(body, "START OF THE PROJECT GUTENBERG EBOOK") {
		t.Fatal("body still has the start banner")
	}
	if strings.Contains(body, "END OF THE PROJECT GUTENBERG EBOOK") {
		t.Fatal("body still has the end banner")
	}
	train, val := splitBody(body)
	if train+val != body {
		t.Fatal("split dropped or reordered bytes")
	}
	if len(train) == 0 || len(val) == 0 {
		t.Fatal("empty side of the split")
	}
	frac := float64(len(train)) / float64(len(body))
	if frac < 0.75 || frac > 0.85 {
		t.Fatalf("train fraction %f", frac)
	}
	if !strings.HasSuffix(train, "\n") {
		t.Fatal("train does not end on a newline")
	}
}

func TestBookBodyNoMarkers(t *testing.T) {
	const raw = "no markers here"
	if got := bookBody([]byte(raw)); got != raw {
		t.Fatalf("got %q", got)
	}
}

func TestPriorPrefersZero(t *testing.T) {
	m := newModel()
	if !(m.root.pseudo[0] > m.root.pseudo[1]) {
		t.Fatalf("pseudo = %v, want K(0) heavier than K(1)", m.root.pseudo)
	}
	sum := m.root.pseudo[0] + m.root.pseudo[1]
	if math.Abs(sum-priorStrength) > 1e-9 {
		t.Fatalf("pseudo sum %f", sum)
	}
}

func TestModelLearns(t *testing.T) {
	raw, err := os.ReadFile("pg100.txt")
	if err != nil {
		t.Fatal(err)
	}
	body := bookBody(raw)
	const n = 4000
	if len(body) < n {
		t.Fatalf("body length %d", len(body))
	}
	train, val := splitBody(body[:n])
	if len(train) == 0 || len(val) == 0 {
		t.Fatal("empty prefix split")
	}

	adapted := newModel()
	tr := adapted.score(train, true)
	if tr.bitsPerChar() >= 8 {
		t.Fatalf("train bits/char %.4f", tr.bitsPerChar())
	}
	if tr.accuracy() <= 0.5 {
		t.Fatalf("train accuracy %.4f", tr.accuracy())
	}
	va := adapted.score(val, false)
	if va.bitsPerChar() >= 8 {
		t.Fatalf("val bits/char %.4f", va.bitsPerChar())
	}
	if va.accuracy() <= 0.5 {
		t.Fatalf("val accuracy %.4f", va.accuracy())
	}

	frozen := newModel()
	pr := frozen.score(train, false)
	if !(tr.bits < pr.bits) {
		t.Fatalf("adapted %.4f bits, prior %.4f bits", tr.bits, pr.bits)
	}
}
