import Model3MaxSAT.Targets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity.Basic

/-!
# Consequences of the quantitative hard-input theorem

These are general proof-composition lemmas. `Main.lean` supplies the proved
quantitative theorem and instantiates these implications to obtain unconditional
asymptotic, competitive-ratio, and additive-loss conclusions.
-/

noncomputable section

universe u

namespace Model3MaxSAT

/-- Choose a depth with small error and enough optimum to absorb any fixed
additive loss and exceed any requested optimum threshold. -/
theorem exists_large_depth (ε C T : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      Real.sqrt 3 / (4 * Real.sqrt (L : ℝ)) < ε / 2 ∧
      T ≤ 2 * (L : ℝ) ∧ C < (ε / 2) * (2 * (L : ℝ)) := by
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max (max ((Real.sqrt 3 / (2 * ε)) ^ 2) T) (C / ε) + 1)
  have hsq : (Real.sqrt 3 / (2 * ε)) ^ 2 < (L : ℝ) := by
    have : (Real.sqrt 3 / (2 * ε)) ^ 2 ≤
        max (max ((Real.sqrt 3 / (2 * ε)) ^ 2) T) (C / ε) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hT : T < (L : ℝ) := by
    have : T ≤ max (max ((Real.sqrt 3 / (2 * ε)) ^ 2) T) (C / ε) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hC : C / ε < (L : ℝ) := by
    have := le_max_right (max ((Real.sqrt 3 / (2 * ε)) ^ 2) T) (C / ε)
    linarith
  have hLreal : 0 < (L : ℝ) := lt_of_le_of_lt (sq_nonneg _) hsq
  have hLnat : 0 < L := Nat.cast_pos.mp hLreal
  have hsqrt : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 hLreal
  have hs : Real.sqrt 3 / (2 * ε) < Real.sqrt (L : ℝ) :=
    Real.lt_sqrt_of_sq_lt hsq
  have hden : 0 < 2 * ε := by linarith
  have hs' : Real.sqrt 3 < Real.sqrt (L : ℝ) * (2 * ε) :=
    (div_lt_iff₀ hden).mp hs
  refine ⟨L, hLnat, ?_, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * Real.sqrt (L : ℝ))).2
    nlinarith
  · linarith
  · have := (div_lt_iff₀ hε).mp hC
    nlinarith

/-- The finite hard-family optima grow at least linearly in the depth. -/
theorem hardOptimum_ge_twice_depth (L : ℕ) :
    2 * (L : ℝ) ≤ ((2 * L * 4 ^ (L - 1) : ℕ) : ℝ) := by
  have hpow : 0 < (4 : ℕ) ^ (L - 1) := pow_pos (by decide) _
  have hn := Nat.le_mul_of_pos_right (2 * L) hpow
  exact_mod_cast hn

/-- The actual asymptotic and additive-loss argument, conditional only on
the explicitly named quantitative target. No new axiom is introduced. -/
theorem quantitative_implies_asymptotic
    (hquant : QuantitativeUpperBound.{u}) : AsymptoticUpperBound.{u} := by
  intro Ξ _ A ε C T hε hC hT
  obtain ⟨L, hL, herr, hlarge, hconstant⟩ := exists_large_depth ε C T hε
  obtain ⟨n, m, I, hrestricted, hm, hopt, hbound⟩ := hquant Ξ A L hL
  have hopt_ge : 2 * (L : ℝ) ≤ I.formula.optimum := by
    rw [hopt]
    exact hardOptimum_ge_twice_depth L
  have hLreal : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hoptpos : 0 < I.formula.optimum := by linarith
  have hgap : C < (ε / 2) * I.formula.optimum := by
    have hmul := mul_le_mul_of_nonneg_left hopt_ge (by linarith : 0 ≤ ε / 2)
    exact lt_of_lt_of_le hconstant hmul
  have herrmul := mul_lt_mul_of_pos_right herr hoptpos
  refine ⟨n, m, I, hrestricted, hoptpos, le_trans hlarge hopt_ge, ?_⟩
  nlinarith

/-- The asymptotic counterexamples exclude every multiplicative guarantee
strictly greater than 3/4. -/
theorem asymptotic_implies_no_better_guarantee
    (hasym : AsymptoticUpperBound.{u}) : NoBetterGuarantee.{u} := by
  intro Ξ _ A r hr
  by_contra h
  have hε : 0 < r - (3 : ℝ) / 4 := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, m, I, _, hopt, _, hbad⟩ :=
    hasym Ξ A (r - (3 : ℝ) / 4) 0 0 hε le_rfl le_rfl
  have hgood := hr n m I hopt
  have heq : ((3 : ℝ) / 4 + (r - (3 : ℝ) / 4)) = r := by ring
  rw [heq, sub_zero] at hbad
  exact (not_lt_of_ge hgood) hbad

theorem quantitative_implies_no_better_guarantee
    (hquant : QuantitativeUpperBound.{u}) : NoBetterGuarantee.{u} :=
  asymptotic_implies_no_better_guarantee (quantitative_implies_asymptotic hquant)

/-- No input-independent additive constant, of either sign, can rescue
a multiplicative ratio above 3/4 once the asymptotic target is proved. -/
theorem asymptotic_excludes_additive_guarantee
    (hasym : AsymptoticUpperBound.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ)
    (ε C : ℝ) (hε : 0 < ε) :
    ¬ HasAdditiveGuarantee A ((3 : ℝ) / 4 + ε) C := by
  intro hgood
  obtain ⟨n, m, I, _, hopt, _, hbad⟩ :=
    hasym Ξ A ε (max C 0) 0 hε (le_max_right _ _) le_rfl
  have hclaimed := hgood n m I hopt
  have hmax : C ≤ max C 0 := le_max_left _ _
  linarith

theorem quantitative_excludes_additive_guarantee
    (hquant : QuantitativeUpperBound.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (A : RandomizedAlgorithm Ξ)
    (ε C : ℝ) (hε : 0 < ε) :
    ¬ HasAdditiveGuarantee A ((3 : ℝ) / 4 + ε) C :=
  asymptotic_excludes_additive_guarantee
    (quantitative_implies_asymptotic hquant) A ε C hε

#print axioms exists_large_depth
#print axioms hardOptimum_ge_twice_depth
#print axioms quantitative_implies_asymptotic
#print axioms asymptotic_implies_no_better_guarantee
#print axioms quantitative_implies_no_better_guarantee
#print axioms asymptotic_excludes_additive_guarantee
#print axioms quantitative_excludes_additive_guarantee

end Model3MaxSAT
