import Model3MaxSAT.Gadget
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

/-!
# The hard label space

The parameter `h` is the manuscript's `L - 1`; thus there are `h + 1`
levels and `4 ^ h` elements. Levels and positions are zero-based here.
Level zero consists of singleton blocks. A block at level d has the
interval-membership test `i / 4^d = j`.

This file defines the finite label space and its uniform average, together
with the induced edge colors. It proves only the local planted-label
satisfaction fact. It does NOT yet prove the block cardinalities, partitions,
laminarity, graph properties, arrival order, or the hard-distribution bound.
The complete online hard inputs are constructed in `HardInput.lean`;
`HardCounting`, `HardMembers`, `HardChildren`, and `HardConnected` establish
their structure, while `Main.lean` proves the upper bound.
-/

namespace Model3MaxSAT.Hard

abbrev Element (h : ℕ) := Fin (4 ^ h)

/-- The first coordinate is the block level, and the second its position. -/
abbrev Block (h : ℕ) := (d : Fin (h + 1)) × Fin (4 ^ (h - d.val))

abbrev Contains {h : ℕ} (B : Block h) (i : Element h) : Prop :=
  i.val / 4 ^ B.1.val = B.2.val

/-- A block and an element are different kinds of vertices, even at level 0. -/
abbrev Vertex (h : ℕ) := Block h ⊕ Element h

/-- Each edge has a block endpoint and an element endpoint in that block. -/
abbrev Edge (h : ℕ) := {p : Block h × Element h // Contains p.1 p.2}

/-- A fair Boolean label at every vertex. Uniformly averaging over this
finite function type is the independent-fair-label distribution. -/
abbrev Sample (h : ℕ) := Vertex h → Bool

/-- Blue means agreement of the two hidden labels, red means disagreement.
Colors on different edges are not sampled independently. -/
def color {h : ℕ} (ω : Sample h) (e : Edge h) : EdgeColor :=
  if ω (.inl e.val.1) == ω (.inr e.val.2) then .blue else .red

/-- Uniform finite expectation over hidden vertex labels. The distribution
on colored graphs is induced by `color`, with repeated outcomes retained. -/
noncomputable def uniformMean (h : ℕ) (f : Sample h → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card (Sample h) : ℝ)

/-- The hidden-label space is nonempty, so its uniform mean is normalized. -/
theorem uniformMean_one (h : ℕ) : uniformMean h (fun _ => 1) = 1 := by
  simp [uniformMean, Fintype.card_ne_zero]

/-- The sampled hidden labels satisfy each incidence edge. -/
theorem planted_edge_satisfied {h : ℕ} (ω : Sample h) (e : Edge h) :
    edgeSatisfied (color ω e) (ω (.inl e.val.1)) (ω (.inr e.val.2)) = true := by
  unfold color
  cases ω (.inl e.val.1) <;> cases ω (.inr e.val.2) <;> decide

#print axioms planted_edge_satisfied
#print axioms uniformMean_one

end Model3MaxSAT.Hard
