import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Finite uniform probability facts. These lemmas use actual normalized sums,
not hypotheses asserting any MAXSAT or MaxCC bound.
-/

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT.FiniteProbability

variable {Ω : Type*} [Fintype Ω]

def mean (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / (Fintype.card Ω : ℝ)

theorem mean_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) : mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

@[simp] theorem mean_zero : mean (fun _ : Ω => (0 : ℝ)) = 0 := by simp [mean]

@[simp] theorem mean_const [Nonempty Ω] (c : ℝ) : mean (fun _ : Ω => c) = c := by
  simp [mean, Fintype.card_ne_zero]

theorem mean_add (f g : Ω → ℝ) : mean (fun ω => f ω + g ω) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_sub (f g : Ω → ℝ) : mean (fun ω => f ω - g ω) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_neg (f : Ω → ℝ) : mean (fun ω => -f ω) = -mean f := by
  simp only [mean, Finset.sum_neg_distrib, neg_div]

theorem mean_const_mul (c : ℝ) (f : Ω → ℝ) : mean (fun ω => c * f ω) = c * mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring

theorem mean_mul_const (f : Ω → ℝ) (c : ℝ) : mean (fun ω => f ω * c) = mean f * c := by
  simp only [mean, ← Finset.sum_mul]
  ring

theorem mean_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    mean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem mean_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : mean f ≤ mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem mean_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ mean f := by
  simpa using mean_mono h

theorem mean_equiv (e : Ω ≃ Ω) (f : Ω → ℝ) : mean (fun ω => f (e ω)) = mean f := by
  unfold mean
  rw [Equiv.sum_comp e f]

theorem mean_eq_zero_of_flip (e : Ω ≃ Ω) (f : Ω → ℝ)
    (hf : ∀ ω, f (e ω) = -f ω) : mean f = 0 := by
  have h := mean_equiv e f
  rw [mean_congr hf, mean_neg] at h
  linarith

theorem mean_mul_cancel_of_flip (e : Ω ≃ Ω) (f g : Ω → ℝ)
    (hf : ∀ ω, f (e ω) = -f ω) (hg : ∀ ω, g (e ω) = g ω) :
    mean (fun ω => f ω * g ω) = 0 := by
  apply mean_eq_zero_of_flip e
  intro ω
  rw [hf, hg, neg_mul]

theorem mean_mul_sq_le (f g : Ω → ℝ) :
    mean (fun ω => f ω * g ω) ^ 2 ≤
      mean (fun ω => f ω ^ 2) * mean (fun ω => g ω ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω) f g
  unfold mean
  rw [div_pow, div_mul_div_comm]
  simpa only [sq] using div_le_div_of_nonneg_right h (sq_nonneg (Fintype.card Ω : ℝ))

theorem mean_sq_le_mean_sq [Nonempty Ω] (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun ω => f ω ^ 2) := by
  simpa only [mul_one, one_pow, mean_const] using mean_mul_sq_le f (fun _ => 1)

theorem mean_abs_le_sqrt_mean_sq [Nonempty Ω] (f : Ω → ℝ) :
    mean (fun ω => |f ω|) ≤ Real.sqrt (mean (fun ω => f ω ^ 2)) := by
  have h := mean_sq_le_mean_sq (fun ω => |f ω|)
  simp only [sq_abs] at h
  exact (Real.le_sqrt (mean_nonneg (fun ω => abs_nonneg _))
    (mean_nonneg (fun ω => sq_nonneg _))).2 h

theorem mean_abs_le_of_mean_sq_le [Nonempty Ω] (f : Ω → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (h : mean (fun ω => f ω ^ 2) ≤ a ^ 2) :
    mean (fun ω => |f ω|) ≤ a := by
  have h1 := mean_sq_le_mean_sq (fun ω => |f ω|)
  simp only [sq_abs] at h1
  have h0 := mean_nonneg (fun ω => abs_nonneg (f ω))
  nlinarith

end Model3MaxSAT.FiniteProbability
