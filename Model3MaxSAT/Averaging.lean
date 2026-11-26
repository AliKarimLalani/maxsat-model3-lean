import Model3MaxSAT.Payoff
import Model3MaxSAT.FiniteMean
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite-input averaging over arbitrary private randomness

The theorems in this file establish the averaging direction of Yao's
principle. They are general analytic lemmas: the deterministic input-sum
bound is an explicit hypothesis that must later be proved for the hard
family. They do not assert the MAXSAT upper bound independently.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Model3MaxSAT

/-- A finite sum of integrable payoffs can be averaged over an arbitrary
private probability space, without assuming a finite random tape. -/
theorem integral_sum_le
    {Ω Ξ : Type*} [Fintype Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : Ω → Ξ → ℝ) (B : ℝ)
    (hf : ∀ ω, Integrable (f ω) μ)
    (hbound : ∀ ξ, ∑ ω, f ω ξ ≤ (Fintype.card Ω : ℝ) * B) :
    ∑ ω, ∫ ξ, f ω ξ ∂μ ≤ (Fintype.card Ω : ℝ) * B := by
  classical
  calc
    _ = ∫ ξ, ∑ ω, f ω ξ ∂μ :=
      (integral_finset_sum Finset.univ (fun ω _ => hf ω)).symm
    _ ≤ ∫ _ : Ξ, (Fintype.card Ω : ℝ) * B ∂μ :=
      integral_mono (integrable_finset_sum Finset.univ (fun ω _ => hf ω))
        (integrable_const _) hbound
    _ = _ := by simp

/-- The selected input is outside the private-randomness integral.
This is the required oblivious-adversary quantifier order. -/
theorem exists_input_integral_le
    {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : Ω → Ξ → ℝ) (B : ℝ)
    (hf : ∀ ω, Integrable (f ω) μ)
    (hbound : ∀ ξ, ∑ ω, f ω ξ ≤ (Fintype.card Ω : ℝ) * B) :
    ∃ ω, (∫ ξ, f ω ξ ∂μ) ≤ B := by
  classical
  have hsum := integral_sum_le μ f B hf hbound
  have hsum' : (∑ ω, ∫ ξ, f ω ξ ∂μ) ≤ ∑ _ : Ω, B := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum'
  exact ⟨ω, hω⟩

/-- The same extraction theorem in the finite-mean interface used by the
energy argument. It keeps arbitrary private randomness unchanged. -/
theorem exists_input_integral_le_of_mean_le
    {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : Ω → Ξ → ℝ) (B : ℝ)
    (hf : ∀ ω, Integrable (f ω) μ)
    (hbound : ∀ ξ, FiniteProbability.mean (fun ω => f ω ξ) ≤ B) :
    ∃ ω, (∫ ξ, f ω ξ ∂μ) ≤ B := by
  apply exists_input_integral_le μ f B hf
  intro ξ
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have h := (div_le_iff₀ hcard).mp (hbound ξ)
  simpa only [mul_comm] using h

/-- Applied to actual MAXSAT payoffs, integrability is automatic from the
problem definition. The remaining input-sum hypothesis is precisely the
deterministic estimate that the hard-distribution proof must supply. -/
theorem RandomizedStrategy.exists_input_expectedPayoff_le
    {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ξ]
    {n m : ℕ} (A : RandomizedStrategy Ξ n m)
    (I : Ω → Input n m) (B : ℝ)
    (hbound : ∀ ξ, (∑ ω, (I ω).formula.payoff ((A.policy ξ).assignment (I ω)))
      ≤ (Fintype.card Ω : ℝ) * B) :
    ∃ ω, A.expectedPayoff (I ω) ≤ B := by
  letI : IsProbabilityMeasure A.law := A.probability
  exact exists_input_integral_le A.law
    (fun ω ξ => (I ω).formula.payoff ((A.policy ξ).assignment (I ω))) B
    (fun ω => A.integrable_payoff (I ω)) hbound

/-- Standard finite-distribution Yao averaging. A single distribution that
bounds every deterministic causal strategy also gives one fixed bad input
for each randomized causal strategy. The deterministic estimate is the
remaining construction-specific hypothesis, not an installed axiom. -/
theorem RandomizedStrategy.exists_input_of_deterministic_mean_bound
    {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ξ]
    {n m : ℕ} (A : RandomizedStrategy Ξ n m)
    (I : Ω → Input n m) (B : ℝ)
    (hdet : ∀ a : DeterministicStrategy n m,
      FiniteProbability.mean (fun ω => (I ω).formula.payoff (a.assignment (I ω))) ≤ B) :
    ∃ ω, A.expectedPayoff (I ω) ≤ B := by
  letI : IsProbabilityMeasure A.law := A.probability
  exact exists_input_integral_le_of_mean_le A.law
    (fun ω ξ => (I ω).formula.payoff ((A.policy ξ).assignment (I ω))) B
    (fun ω => A.integrable_payoff (I ω)) (fun ξ => hdet (A.policy ξ))

#print axioms integral_sum_le
#print axioms exists_input_integral_le
#print axioms exists_input_integral_le_of_mean_le
#print axioms RandomizedStrategy.exists_input_expectedPayoff_le
#print axioms RandomizedStrategy.exists_input_of_deterministic_mean_bound

end Model3MaxSAT
