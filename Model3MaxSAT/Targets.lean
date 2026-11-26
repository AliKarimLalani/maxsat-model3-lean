import Model3MaxSAT.Model
import Mathlib.Data.Real.Sqrt

/-!
# Main target propositions

These definitions state the desired results. Their unconditional proofs are
`randomized_model3_quantitative`, `randomized_model3_asymptotic`, and
`randomized_model3_no_better_guarantee` in `Main.lean`. The explicit support
and distributional theorems are also proved there. No proposition is installed
as an axiom.
-/

noncomputable section

universe u

namespace Model3MaxSAT

/-- Formula restrictions only, not membership in the hard distribution. -/
def RestrictedInput {n m : ℕ} (I : Input n m) : Prop :=
  I.formula.Unweighted ∧ I.formula.ExactTwo ∧
  I.formula.NoRepeatedClauses ∧ I.formula.Satisfiable

/-- This is equation (16), including its exact optimum and clause count.
The existential input is outside the expectation over the tape. -/
def QuantitativeUpperBound : Prop :=
  ∀ (Ξ : Type u) [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ)
    (L : ℕ), 0 < L →
    ∃ (n m : ℕ) (I : Input n m),
      RestrictedInput I ∧
      m = 2 * L * 4 ^ (L - 1) ∧
      I.formula.optimum = (2 * L * 4 ^ (L - 1) : ℕ) ∧
      (A n m).expectedPayoff I ≤
        ((3 : ℝ) / 4 + Real.sqrt 3 / (4 * Real.sqrt (L : ℝ))) *
          I.formula.optimum

/-- Arbitrarily large counterexamples, with a strict gap sufficient to
exclude every fixed additive loss. Proved in `Main.lean`. -/
def AsymptoticUpperBound : Prop :=
  ∀ (Ξ : Type u) [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ)
    (ε C T : ℝ), 0 < ε → 0 ≤ C → 0 ≤ T →
    ∃ (n m : ℕ) (I : Input n m),
      RestrictedInput I ∧
      0 < I.formula.optimum ∧ T ≤ I.formula.optimum ∧
      (A n m).expectedPayoff I <
        ((3 : ℝ) / 4 + ε) * I.formula.optimum - C

/-- Equivalent guarantee-based formulation of the pure upper bound.
Proved in `Main.lean`. This does not assert the matching lower bound. -/
def NoBetterGuarantee : Prop :=
  ∀ (Ξ : Type u) [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ)
    (r : ℝ), HasGuarantee A r → r ≤ (3 : ℝ) / 4

end Model3MaxSAT
