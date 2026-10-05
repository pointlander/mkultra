// Copyright 2026 The mkultra. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"log"
	"math"
	"os"
	"strings"
)

const (
	// contextBits is the longest suffix the model conditions on.
	// Eight bits is one byte, and the trie then holds at most 2^9 nodes.
	contextBits = 8
	// priorStrength is the total pseudocount at every context. Counts
	// replace it once a context has been seen that often.
	priorStrength = 8
	// censusLimit is the largest pair passed to census for the prior.
	censusLimit = 11
	// trainFraction is the front of the book used to update counts.
	trainFraction = 0.8
)

const (
	startMark = "*** START OF THE PROJECT GUTENBERG EBOOK THE COMPLETE WORKS OF WILLIAM SHAKESPEARE ***"
	endMark   = "*** END OF THE PROJECT GUTENBERG EBOOK THE COMPLETE WORKS OF WILLIAM SHAKESPEARE ***"
)

// bitCtx is one observed suffix. next[b] is that suffix followed by bit b.
// count is how often each next bit followed this suffix during training.
// pseudo sums to priorStrength and is fixed from the K prior.
type bitCtx struct {
	next   [2]*bitCtx
	count  [2]int
	pseudo [2]float64
}

// model is a mixture over the suffixes of the bits read so far.
// code maps a serialization to the smallest pair in the census.
type model struct {
	root *bitCtx
	code map[string]int
}

// stats is one prequential pass: the loss is charged before counts change.
type stats struct {
	chars   int
	bits    float64
	correct int
	nbits   int
}

func (s stats) bitsPerChar() float64 {
	if s.chars == 0 {
		return 0
	}
	return s.bits / float64(s.chars)
}

func (s stats) accuracy() float64 {
	if s.nbits == 0 {
		return 0
	}
	return float64(s.correct) / float64(s.nbits)
}

// bookBody returns the play text between the Gutenberg markers. The start
// marker's own line is dropped. Without both markers, raw is the body.
func bookBody(raw []byte) string {
	s := string(raw)
	i := strings.Index(s, startMark)
	j := strings.Index(s, endMark)
	if i < 0 || j < 0 || j < i {
		return s
	}
	rest := s[i+len(startMark) : j]
	if nl := strings.IndexByte(rest, '\n'); nl >= 0 {
		rest = rest[nl+1:]
	}
	return rest
}

// splitBody cuts off the front trainFraction of s, on a newline when one
// sits in the second half of that prefix.
func splitBody(s string) (train, val string) {
	n := len(s)
	if n < 2 {
		return s, ""
	}
	cut := int(trainFraction * float64(n))
	if cut < 1 {
		cut = 1
	}
	if cut >= n {
		cut = n - 1
	}
	if i := strings.LastIndexByte(s[:cut], '\n'); i > n/2 {
		cut = i + 1
	}
	return s[:cut], s[cut:]
}

// newModel builds the K prior from one census. Strings the census never
// produced fall back to quoteCost inside cost.
func newModel() *model {
	code := make(map[string]int)
	for key, prog := range census(censusLimit) {
		if len(key) == 0 {
			continue
		}
		code[key] = prog.size
	}
	m := &model{code: code}
	p0, p1 := pseudo(m.cost([]byte{0}), m.cost([]byte{1}))
	m.root = &bitCtx{pseudo: [2]float64{p0, p1}}
	return m
}

// cost is the census program size, or the quote cost when the census has
// no pair for bits.
func (m *model) cost(bits []byte) int {
	if k, ok := m.code[string(bits)]; ok {
		return k
	}
	return quoteCost(bits)
}

// pseudo splits priorStrength by the normalized weights 2^{-k}.
func pseudo(k0, k1 int) (p0, p1 float64) {
	w0 := math.Exp2(-float64(k0))
	w1 := math.Exp2(-float64(k1))
	sum := w0 + w1
	return priorStrength * w0 / sum, priorStrength * w1 / sum
}

// spawn is the node for ctx followed by bit. Its two extensions are copied
// apart so the +0 and +1 strings do not share a backing array.
func (m *model) spawn(ctx []byte, bit byte) *bitCtx {
	ext0 := make([]byte, len(ctx)+2)
	ext1 := make([]byte, len(ctx)+2)
	copy(ext0, ctx)
	copy(ext1, ctx)
	ext0[len(ctx)] = bit
	ext1[len(ctx)] = bit
	ext0[len(ctx)+1] = 0
	ext1[len(ctx)+1] = 1
	p0, p1 := pseudo(m.cost(ext0), m.cost(ext1))
	return &bitCtx{pseudo: [2]float64{p0, p1}}
}

// score walks text MSB first. Loss and accuracy use the mixture of every
// active suffix, weighted by 2^depth, before any count changes. When update
// is set, those counts then record the bit. Each call starts at the root,
// so a validation pass does not keep the training context.
func (m *model) score(text string, update bool) stats {
	active := []*bitCtx{m.root}
	spare := make([]*bitCtx, 0, contextBits+1)
	hist := make([]byte, 0, contextBits)
	var (
		loss    float64
		correct int
		nbits   int
	)
	for i := 0; i < len(text); i++ {
		b := text[i]
		for shift := 7; shift >= 0; shift-- {
			bit := (b >> uint(shift)) & 1
			var wsum, p1sum float64
			for depth, node := range active {
				w := float64(uint(1) << uint(depth))
				den := float64(node.count[0]+node.count[1]) + priorStrength
				p1 := (float64(node.count[1]) + node.pseudo[1]) / den
				wsum += w
				p1sum += w * p1
			}
			p1 := p1sum / wsum
			p := p1
			if bit == 0 {
				p = 1 - p1
			}
			loss += -math.Log2(p)
			nbits++
			if (p1 > 0.5) == (bit == 1) {
				correct++
			}
			if update {
				for _, node := range active {
					node.count[bit]++
				}
			}
			spare = spare[:0]
			spare = append(spare, m.root)
			limit := len(active)
			if limit > contextBits {
				limit = contextBits
			}
			for depth := 0; depth < limit; depth++ {
				node := active[depth]
				child := node.next[bit]
				if child == nil {
					// An unseen validation context drops out. Shorter
					// suffixes that do exist keep the mixture.
					if !update {
						break
					}
					var ctx []byte
					if depth > 0 {
						ctx = hist[len(hist)-depth:]
					}
					child = m.spawn(ctx, bit)
					node.next[bit] = child
				}
				spare = append(spare, child)
			}
			active, spare = spare, active
			if len(hist) == contextBits {
				copy(hist, hist[1:])
				hist[contextBits-1] = bit
			} else {
				hist = append(hist, bit)
			}
		}
	}
	return stats{chars: len(text), bits: loss, correct: correct, nbits: nbits}
}

// modelBook trains on the front of pg100.txt and scores the held-out tail.
func modelBook() {
	raw, err := os.ReadFile("pg100.txt")
	if err != nil {
		log.Fatal(err)
	}
	train, val := splitBody(bookBody(raw))
	seen := newModel()
	tr := seen.score(train, true)
	va := seen.score(val, false)
	fmt.Printf("train chars %d bits/char %.4f accuracy %.4f\n", tr.chars, tr.bitsPerChar(), tr.accuracy())
	fmt.Printf("val chars %d bits/char %.4f accuracy %.4f\n", va.chars, va.bitsPerChar(), va.accuracy())
}
