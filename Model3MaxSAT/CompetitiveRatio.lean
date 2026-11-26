import Model3MaxSAT.Payoff
import Model3MaxSAT.Targets

/-! The exact infimum convention of equation (1) in the manuscript.
This file connects the guarantee formulation to that numerical ratio.
It does not assume or assert the main upper bound. -/

noncomputable section
open MeasureTheory

universe u

namespace Model3MaxSAT

theorem RandomizedStrategy.expectedPayoff_nonneg
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n m) (I : Input n m) :
    0 ≤ A.expectedPayoff I := by
  apply integral_nonneg
  intro ξ
  exact I.formula.payoff_nonneg _

/-- The set of expected payoff / optimum ratios over all finite inputs
with strictly positive optimum. -/
def inputRatios {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) : Set ℝ :=
  {r | ∃ (n m : ℕ) (I : Input n m), 0 < I.formula.optimum ∧
    r = (A n m).expectedPayoff I / I.formula.optimum}

/-- Equation (1): the adversary fixes the input outside the expectation. -/
def competitiveRatio {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) : ℝ := sInf (inputRatios A)

theorem inputRatios_nonneg {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) {r : ℝ} (hr : r ∈ inputRatios A) : 0 ≤ r := by
  obtain ⟨n,m,I,hopt,rfl⟩ := hr
  exact div_nonneg ((A n m).expectedPayoff_nonneg I) hopt.le

theorem inputRatios_bddBelow {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) : BddBelow (inputRatios A) :=
  ⟨0, fun _ hr => inputRatios_nonneg A hr⟩

theorem competitiveRatio_nonneg {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) : 0 ≤ competitiveRatio A :=
  Real.sInf_nonneg fun _ hr => inputRatios_nonneg A hr

/-- A concrete positive-optimum input prevents an empty infimum domain. -/
def unitInput : Input 1 1 where
  formula := {
    clause := fun _ => {
      literal := fun _ => some true
      nonempty := ⟨0, rfl⟩ }
    weight := fun _ => 1
    weight_nonneg := fun _ => zero_le_one }
  order := Equiv.refl _

theorem unitInput_optimum : unitInput.formula.optimum = 1 := by
  have hs : unitInput.formula.Satisfiable :=
    ⟨fun _ => true, fun _ => ⟨0, rfl⟩⟩
  rw [unitInput.formula.optimum_eq_totalWeight_of_satisfiable hs]
  simp [unitInput, Formula.totalWeight]

theorem inputRatios_nonempty {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) : (inputRatios A).Nonempty := by
  refine ⟨(A 1 1).expectedPayoff unitInput / unitInput.formula.optimum,
    1,1,unitInput,?_,rfl⟩
  rw [unitInput_optimum]
  exact zero_lt_one

theorem competitiveRatio_le_inputRatio {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) {n m : ℕ} (I : Input n m)
    (hopt : 0 < I.formula.optimum) :
    competitiveRatio A ≤ (A n m).expectedPayoff I / I.formula.optimum :=
  csInf_le (inputRatios_bddBelow A) ⟨n,m,I,hopt,rfl⟩

/-- Every algorithm achieves its infimum ratio on every positive-optimum
input. This does not assert that an input attaining the infimum exists. -/
theorem hasGuarantee_competitiveRatio {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) : HasGuarantee A (competitiveRatio A) := by
  intro n m I hopt
  exact (le_div_iff₀ hopt).mp (competitiveRatio_le_inputRatio A I hopt)

theorem hasGuarantee_iff_le_competitiveRatio
    {Ξ : Type*} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ) (r : ℝ) :
    HasGuarantee A r ↔ r ≤ competitiveRatio A := by
  constructor
  · intro hr
    apply le_csInf (inputRatios_nonempty A)
    rintro _ ⟨n,m,I,hopt,rfl⟩
    exact (le_div_iff₀ hopt).mpr (hr n m I hopt)
  · intro hr n m I hopt
    exact (le_div_iff₀ hopt).mp (hr.trans (competitiveRatio_le_inputRatio A I hopt))

/-- Once the upper bound on guarantees is proved, it is exactly the
manuscript's numerical competitive-ratio bound. This is an implication,
not a claimed proof of the main result. -/
theorem competitiveRatio_le_three_quarters_of_noBetterGuarantee
    (h : NoBetterGuarantee.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ) :
    competitiveRatio A ≤ (3 : ℝ) / 4 :=
  h Ξ A (competitiveRatio A) (hasGuarantee_competitiveRatio A)

#print axioms hasGuarantee_iff_le_competitiveRatio
#print axioms competitiveRatio_le_three_quarters_of_noBetterGuarantee

end Model3MaxSAT
