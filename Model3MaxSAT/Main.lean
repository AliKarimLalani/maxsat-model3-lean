import Model3MaxSAT.HardPayoffBridge
import Model3MaxSAT.Averaging
import Model3MaxSAT.Asymptotics
import Model3MaxSAT.CompetitiveRatio
import Model3MaxSAT.FinalBounds

/-!
# Randomized Model 3 MAXSAT: the complete upper-bound chain

All construction-specific inputs to the averaging argument are proved in
the imported hard-family modules. The final theorems below have no energy,
orthogonality, quantitative-bound, or finite-private-randomness assumptions.
-/

noncomputable section

universe u

open scoped BigOperators
open MeasureTheory

namespace Model3MaxSAT
open Hard FiniteProbability

/-- The explicit hard distribution also bounds the expected payoff averaged
over an arbitrary independent private probability space. -/
theorem randomized_hard_distributional {Ξ : Type u} [MeasurableSpace Ξ]
    (h : ℕ) (A : RandomizedStrategy Ξ (vertexCount h) (edgeCount h * 2)) :
    uniformMean h (fun ω => A.expectedPayoff (hardSAT h ω)) ≤
      (3 * ((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
        (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2 := by
  letI : IsProbabilityMeasure A.law := A.probability
  let B : ℝ := (3 * ((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
    (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2
  have hc : (0 : ℝ) < Fintype.card (Sample h) := by
    exact_mod_cast Fintype.card_pos
  have hb (ξ : Ξ) :
      (∑ ω, (hardSAT h ω).formula.payoff ((A.policy ξ).assignment (hardSAT h ω))) ≤
        (Fintype.card (Sample h) : ℝ) * B := by
    have hh := hardSAT_deterministic_mean_le (A.policy ξ)
    have hs := (div_le_iff₀ hc).mp hh
    simpa only [B, mul_comm] using hs
  have hs := integral_sum_le A.law
    (fun ω ξ => (hardSAT h ω).formula.payoff ((A.policy ξ).assignment (hardSAT h ω)))
    B (fun ω => A.integrable_payoff (hardSAT h ω)) hb
  change (∑ ω, A.expectedPayoff (hardSAT h ω)) /
    (Fintype.card (Sample h) : ℝ) ≤ B
  apply (div_le_iff₀ hc).mpr
  simpa only [mul_comm] using hs

/-- One fixed member of the explicit hard family is bad for each randomized
algorithm. The existential sample is outside the private-randomness integral. -/
theorem randomized_hard_input {Ξ : Type u} [MeasurableSpace Ξ]
    (h : ℕ) (A : RandomizedStrategy Ξ (vertexCount h) (edgeCount h * 2)) :
    ∃ ω : Sample h, A.expectedPayoff (hardSAT h ω) ≤
      ((3 : ℝ) / 4 + Real.sqrt 3 / (4 * Real.sqrt ((h + 1 : ℕ) : ℝ))) *
        (hardSAT h ω).formula.optimum := by
  obtain ⟨ω, hω⟩ := A.exists_input_of_deterministic_mean_bound (hardSAT h)
    ((3 * ((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
      (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2)
    (fun a => hardSAT_deterministic_mean_le a)
  refine ⟨ω, ?_⟩
  rw [hardSAT_optimum]
  have hL : (0 : ℝ) < ((h + 1 : ℕ) : ℝ) := by positivity
  rw [sat_bound_normalization _ _ hL] at hω
  simpa only [edgeCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_assoc] using hω

/-- Equation (16), with exact clause count and all hard-formula restrictions.
This is a proof of the target proposition, not an assumption of it. -/
theorem randomized_model3_quantitative : QuantitativeUpperBound.{u} := by
  intro Ξ _ A L hL
  let h := L - 1
  have hdepth : h + 1 = L := by dsimp [h]; omega
  obtain ⟨ω, hω⟩ := randomized_hard_input h (A (vertexCount h) (edgeCount h * 2))
  refine ⟨vertexCount h, edgeCount h * 2, hardSAT h ω,
    hardSAT_restricted h ω, ?_, ?_, ?_⟩
  · change ((h + 1) * 4 ^ h) * 2 = 2 * L * 4 ^ (L - 1)
    rw [hdepth]
    dsimp [h]
    ring
  · rw [hardSAT_optimum]
    simp only [edgeCount, hdepth, h, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    ring
  · simpa only [hdepth] using hω

/-- Arbitrarily large satisfiable exact-two-variable counterexamples exclude
every ratio above 3/4, including an input-independent additive loss. -/
theorem randomized_model3_asymptotic : AsymptoticUpperBound.{u} :=
  quantitative_implies_asymptotic randomized_model3_quantitative

theorem randomized_model3_no_better_guarantee : NoBetterGuarantee.{u} :=
  quantitative_implies_no_better_guarantee randomized_model3_quantitative

/-- The manuscript's infimum competitive ratio, for arbitrary private
probability spaces and an oblivious adversary. -/
theorem randomized_model3_competitiveRatio_le
    {Ξ : Type u} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ) :
    competitiveRatio A ≤ (3 : ℝ) / 4 :=
  competitiveRatio_le_three_quarters_of_noBetterGuarantee
    randomized_model3_no_better_guarantee A

theorem randomized_model3_no_additive_guarantee
    {Ξ : Type u} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ)
    (ε C : ℝ) (hε : 0 < ε) :
    ¬ HasAdditiveGuarantee A ((3 : ℝ) / 4 + ε) C :=
  quantitative_excludes_additive_guarantee randomized_model3_quantitative A ε C hε

#print axioms randomized_hard_distributional
#print axioms randomized_hard_input
#print axioms randomized_model3_quantitative
#print axioms randomized_model3_asymptotic
#print axioms randomized_model3_no_better_guarantee
#print axioms randomized_model3_competitiveRatio_le
#print axioms randomized_model3_no_additive_guarantee

end Model3MaxSAT
