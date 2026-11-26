import Model3MaxSAT.FiniteMean
import Mathlib.Tactic.NormNum

/-!
# Finite second moments, energy increments and payoff bounds

These are proved algebraic/probabilistic lemmas for finite spaces. The
hard-family proof must instantiate the sums, the orthogonality hypothesis,
and the pointwise payoff inequality with its actual causal execution.
None of those hard-family obligations is asserted here without proof.
-/

noncomputable section
open scoped BigOperators
open Model3MaxSAT.FiniteProbability

namespace Model3MaxSAT.Energy

variable {Ω : Type*} [Fintype Ω]

theorem mean_sq_sum_of_orthogonal {ι : Type*} [Fintype ι]
    (Z : ι → Ω → ℝ)
    (horth : ∀ i j, i ≠ j → mean (fun ω => Z i ω * Z j ω) = 0) :
    mean (fun ω => (∑ i, Z i ω) ^ 2) = ∑ i, mean (fun ω => Z i ω ^ 2) := by
  classical
  calc
    _ = mean (fun ω => ∑ i, ∑ j, Z i ω * Z j ω) := by
      apply mean_congr
      intro ω
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, mean (fun ω => Z i ω * Z j ω) := by
      rw [mean_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mean_sum Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j _ hji
        exact horth i j (Ne.symm hji)
      · simp

/-- Four orthogonal children of equal size give the parent's old-total
second-moment bound. The factor four is the actual branching factor. -/
theorem four_child_second_moment (Z : Fin 4 → Ω → ℝ) (s : ℝ)
    (horth : ∀ i j, i ≠ j → mean (fun ω => Z i ω * Z j ω) = 0)
    (hchild : ∀ i, mean (fun ω => Z i ω ^ 2) ≤ 4 * (s / 4) ^ 2) :
    mean (fun ω => (∑ i, Z i ω) ^ 2) ≤ s ^ 2 := by
  rw [mean_sq_sum_of_orthogonal Z horth]
  calc
    _ ≤ ∑ _i : Fin 4, 4 * (s / 4) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hchild i)
    _ = s ^ 2 := by simp; ring

theorem signed_mul_le_abs (a y : ℝ) (hy : y ^ 2 = 1) : a * y ≤ |a| := by
  rcases sq_eq_one_iff.mp hy with h | h
  · simpa [h] using le_abs_self a
  · simpa [h] using neg_le_abs a

/-- A parent's choice may be arbitrarily correlated with T. Only its sign
condition is needed, so the newly revealed information is fully allowed. -/
theorem parent_second_moment [Nonempty Ω] (T y : Ω → ℝ) {s : ℝ}
    (hs : 0 ≤ s) (hy : ∀ ω, y ω ^ 2 = 1)
    (hT : mean (fun ω => T ω ^ 2) ≤ s ^ 2) :
    mean (fun ω => (T ω + s * y ω) ^ 2) ≤ 4 * s ^ 2 := by
  have hcross : mean (fun ω => T ω * y ω) ≤ s :=
    (mean_mono (fun ω => signed_mul_le_abs (T ω) (y ω) (hy ω))).trans
      (mean_abs_le_of_mean_sq_le T hs hT)
  have hexpand : mean (fun ω => (T ω + s * y ω) ^ 2) =
      mean (fun ω => T ω ^ 2) + 2 * s * mean (fun ω => T ω * y ω) + s ^ 2 := by
    calc
      _ = mean (fun ω => T ω ^ 2 + (2 * s) * (T ω * y ω) + s ^ 2) := by
        apply mean_congr
        intro ω
        nlinarith [hy ω]
      _ = _ := by rw [mean_add, mean_add, mean_const_mul, mean_const]
  rw [hexpand]
  nlinarith

/-- The energy increment caused by adding one common sign to every total
in a block. No positivity of the increment is asserted. -/
theorem energy_increment {ι : Type*} [Fintype ι] (H : ι → ℝ) (y : ℝ)
    (hy : y ^ 2 = 1) :
    (∑ i, ((H i + y) ^ 2 - H i ^ 2)) =
      (Fintype.card ι : ℝ) + 2 * y * ∑ i, H i := by
  calc
    _ = ∑ i, (1 + (2 * y) * H i) := by
      apply Finset.sum_congr rfl
      intro i _
      nlinarith
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum]

theorem expected_increment_le [Nonempty Ω] (T y : Ω → ℝ) {s : ℝ}
    (hs : 0 ≤ s) (hy : ∀ ω, y ω ^ 2 = 1)
    (hT : mean (fun ω => T ω ^ 2) ≤ s ^ 2) :
    mean (fun ω => s + 2 * y ω * T ω) ≤ 3 * s := by
  have hcross : mean (fun ω => T ω * y ω) ≤ s :=
    (mean_mono (fun ω => signed_mul_le_abs (T ω) (y ω) (hy ω))).trans
      (mean_abs_le_of_mean_sq_le T hs hT)
  have hrewrite : mean (fun ω => s + 2 * y ω * T ω) =
      s + 2 * mean (fun ω => T ω * y ω) := by
    calc
      _ = mean (fun ω => s + 2 * (T ω * y ω)) := by
        apply mean_congr
        intro ω
        ring
      _ = _ := by rw [mean_add, mean_const, mean_const_mul]
  rw [hrewrite]
  linarith

/-- Finite telescoping from a bound on each expected level increment.
The increments are allowed to be negative. -/
theorem telescoping_energy_bound (E : ℕ → Ω → ℝ) (L : ℕ) (K : ℝ)
    (hzero : ∀ ω, E 0 ω = 0)
    (hstep : ∀ d < L, mean (fun ω => E (d + 1) ω - E d ω) ≤ K) :
    mean (E L) ≤ (L : ℝ) * K := by
  induction L with
  | zero =>
      have h := mean_congr hzero
      simpa using h.le
  | succ L ih =>
      have hp := ih (fun d hd => hstep d (Nat.lt_succ_of_lt hd))
      have hl := hstep L (Nat.lt_succ_self L)
      rw [mean_sub] at hl
      rw [Nat.cast_succ]
      nlinarith

theorem sum_abs_sq_le {ι : Type*} [Fintype ι] (H : ι → ℝ) :
    (∑ i, |H i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, H i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => |H i|) (fun _ => (1 : ℝ))
  simpa only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, mul_comm] using h

/-- Cauchy–Schwarz over both element positions and input samples. -/
theorem mean_sum_abs_sq_le [Nonempty Ω] {ι : Type*} [Fintype ι] (H : ι → Ω → ℝ) :
    mean (fun ω => ∑ i, |H i ω|) ^ 2 ≤
      (Fintype.card ι : ℝ) * mean (fun ω => ∑ i, H i ω ^ 2) := by
  calc
    _ ≤ mean (fun ω => (∑ i, |H i ω|) ^ 2) := mean_sq_le_mean_sq _
    _ ≤ mean (fun ω => (Fintype.card ι : ℝ) * ∑ i, H i ω ^ 2) :=
      mean_mono (fun ω => sum_abs_sq_le (fun i => H i ω))
    _ = _ := mean_const_mul _ _

/-- Proposition 10's analytic step, with actual finite expectations.
The hard graph must separately prove its pointwise payoff and energy bound. -/
theorem payoff_from_energy [Nonempty Ω] {ι : Type*} [Fintype ι]
    (H : ι → Ω → ℝ) (P : Ω → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hpay : ∀ ω, P ω ≤
      (L * (Fintype.card ι : ℝ) + ∑ i, |H i ω|) / 2)
    (henergy : mean (fun ω => ∑ i, H i ω ^ 2) ≤
      3 * L * (Fintype.card ι : ℝ)) :
    mean P ≤ (L * (Fintype.card ι : ℝ) +
      (Fintype.card ι : ℝ) * Real.sqrt (3 * L)) / 2 := by
  let N : ℝ := Fintype.card ι
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have habs := mean_sum_abs_sq_le H
  have hmul := mul_le_mul_of_nonneg_left henergy hN
  have hsqrt := Real.sq_sqrt (show 0 ≤ 3 * L by positivity)
  have hroot := Real.sqrt_nonneg (3 * L)
  have hNroot : 0 ≤ N * Real.sqrt (3 * L) := mul_nonneg hN hroot
  have hbound : mean (fun ω => ∑ i, |H i ω|) ≤ N * Real.sqrt (3 * L) := by
    have hsq : mean (fun ω => ∑ i, |H i ω|) ^ 2 ≤
        (N * Real.sqrt (3 * L)) ^ 2 := by
      calc
        _ ≤ N * (3 * L * N) := habs.trans hmul
        _ = _ := by rw [mul_pow, hsqrt]; ring
    nlinarith
  have hmean := mean_mono hpay
  have hform : mean (fun ω => (L * (Fintype.card ι : ℝ) +
      ∑ i, |H i ω|) / 2) =
      (L * (Fintype.card ι : ℝ) + mean (fun ω => ∑ i, |H i ω|)) / 2 := by
    simp only [div_eq_mul_inv, mean_mul_const, mean_add, mean_const]
  rw [hform] at hmean
  dsimp [N] at hbound
  linarith

end Model3MaxSAT.Energy
