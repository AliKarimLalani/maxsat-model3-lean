import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The two-clauses-per-edge gadget

This file proves the local truth-table identity in Lemma 3 of the manuscript,
its weighted version, and its sum over a finite indexed collection of edges.
It does not yet prove that the gadget preserves online observations, or that
the associated formula has a particular optimum.

Boolean `false` corresponds to the graph sign -1, and `true` to +1.
The local truth-table proof uses kernel reduction through `decide`.
-/

namespace Model3MaxSAT

inductive EdgeColor where
  | blue
  | red
  deriving DecidableEq, Repr

/-- The natural-number indicator of a Boolean value. -/
def bval (b : Bool) : ℕ := if b then 1 else 0

/-- Blue edges require equal values, and red edges require unequal values. -/
def edgeSatisfied : EdgeColor → Bool → Bool → Bool
  | .blue, u, v => u == v
  | .red, u, v => !(u == v)

/-- The first clause of the ordered pair associated with an edge. -/
def firstClause : EdgeColor → Bool → Bool → Bool
  | .blue, u, v => u || !v
  | .red, u, v => u || v

/-- The second clause of the ordered pair associated with an edge. -/
def secondClause : EdgeColor → Bool → Bool → Bool
  | .blue, u, v => !u || v
  | .red, u, v => !u || !v

/-- Each clause pair earns one, plus one if its colored edge is satisfied. -/
theorem two_clauses_per_edge (c : EdgeColor) (u v : Bool) :
    bval (firstClause c u v) + bval (secondClause c u v) =
      1 + bval (edgeSatisfied c u v) := by
  cases c <;> cases u <;> cases v <;> decide

/-- Both clauses hold exactly when the colored edge is satisfied. -/
theorem both_clauses_iff_edge (c : EdgeColor) (u v : Bool) :
    (firstClause c u v = true ∧ secondClause c u v = true) ↔
      edgeSatisfied c u v = true := by
  cases c <;> cases u <;> cases v <;> decide

/-- The weighted identity is algebraic and needs no sign condition on `w`. -/
theorem weighted_two_clauses_per_edge
    (w : ℝ) (c : EdgeColor) (u v : Bool) :
    w * (bval (firstClause c u v) : ℝ) +
        w * (bval (secondClause c u v) : ℝ) =
      w + w * (bval (edgeSatisfied c u v) : ℝ) := by
  cases c <;> cases u <;> cases v <;>
    simp [bval, firstClause, secondClause, edgeSatisfied]

/-- Summing the weighted gadget identities gives the assignment-level payoff
identity. This statement is about a finite edge index type, not yet about the
syntactic MAXSAT reduction or its online simulation. -/
theorem sum_two_clauses_per_edge
    {E : Type*} [Fintype E]
    (w : E → ℝ) (c : E → EdgeColor) (left right : E → Bool) :
    (∑ e, (w e * (bval (firstClause (c e) (left e) (right e)) : ℝ) +
      w e * (bval (secondClause (c e) (left e) (right e)) : ℝ))) =
    (∑ e, w e) +
      ∑ e, w e * (bval (edgeSatisfied (c e) (left e) (right e)) : ℝ) := by
  calc
    _ = ∑ e, (w e +
        w e * (bval (edgeSatisfied (c e) (left e) (right e)) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _
      exact weighted_two_clauses_per_edge (w e) (c e) (left e) (right e)
    _ = _ := Finset.sum_add_distrib

#print axioms two_clauses_per_edge
#print axioms both_clauses_iff_edge
#print axioms weighted_two_clauses_per_edge
#print axioms sum_two_clauses_per_edge

end Model3MaxSAT
