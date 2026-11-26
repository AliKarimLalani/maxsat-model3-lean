import Model3MaxSAT.Model

/-!
# Elementary payoff bounds and integrability

Every assignment earns between zero and the total clause weight. These
bounds establish that the finite supremum in `Formula.optimum` is bounded,
and that every measurable randomized payoff is integrable. In particular,
the expectation is not being used without checking integrability.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Model3MaxSAT

theorem Formula.totalWeight_nonneg {n m : ℕ} (F : Formula n m) :
    0 ≤ F.totalWeight := by
  exact Finset.sum_nonneg fun c _ => F.weight_nonneg c

theorem Formula.payoff_nonneg {n m : ℕ} (F : Formula n m)
    (b : Assignment n) : 0 ≤ F.payoff b := by
  classical
  unfold Formula.payoff
  apply Finset.sum_nonneg
  intro c _
  by_cases h : (F.clause c).Satisfied b
  · simpa only [h, if_true, mul_one] using F.weight_nonneg c
  · simp only [h, if_false, mul_zero, le_refl]

theorem Formula.payoff_le_totalWeight {n m : ℕ} (F : Formula n m)
    (b : Assignment n) : F.payoff b ≤ F.totalWeight := by
  classical
  unfold Formula.payoff Formula.totalWeight
  apply Finset.sum_le_sum
  intro c _
  by_cases h : (F.clause c).Satisfied b
  · simp only [h, if_true, mul_one, le_refl]
  · simpa only [h, if_false, mul_zero] using F.weight_nonneg c

theorem Formula.payoff_eq_totalWeight_of_satisfies {n m : ℕ}
    (F : Formula n m) (b : Assignment n)
    (h : ∀ c, (F.clause c).Satisfied b) : F.payoff b = F.totalWeight := by
  classical
  unfold Formula.payoff Formula.totalWeight
  apply Finset.sum_congr rfl
  intro c _
  simp only [h c, if_true, mul_one]

theorem Formula.payoff_le_optimum {n m : ℕ} (F : Formula n m)
    (b : Assignment n) : F.payoff b ≤ F.optimum := by
  apply le_ciSup
  refine ⟨F.totalWeight, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact F.payoff_le_totalWeight a

theorem Formula.optimum_le_totalWeight {n m : ℕ} (F : Formula n m) :
    F.optimum ≤ F.totalWeight := by
  exact ciSup_le fun b => F.payoff_le_totalWeight b

theorem Formula.optimum_eq_totalWeight_of_satisfiable {n m : ℕ}
    (F : Formula n m) (h : F.Satisfiable) : F.optimum = F.totalWeight := by
  obtain ⟨b, hb⟩ := h
  apply le_antisymm F.optimum_le_totalWeight
  rw [← F.payoff_eq_totalWeight_of_satisfies b hb]
  exact F.payoff_le_optimum b

/-- On an arbitrary private tape space, the payoff is integrable because
it is measurable and bounded by the fixed input's total clause weight. -/
theorem RandomizedStrategy.integrable_payoff
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n m) (I : Input n m) :
    Integrable (fun ξ => I.formula.payoff ((A.policy ξ).assignment I)) A.law := by
  letI : IsProbabilityMeasure A.law := A.probability
  apply (integrable_const I.formula.totalWeight).mono'
    (A.measurable_payoff I).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (I.formula.payoff_nonneg _)]
  exact I.formula.payoff_le_totalWeight _

#print axioms Formula.payoff_nonneg
#print axioms Formula.payoff_le_totalWeight
#print axioms Formula.optimum_eq_totalWeight_of_satisfiable
#print axioms RandomizedStrategy.integrable_payoff

end Model3MaxSAT
