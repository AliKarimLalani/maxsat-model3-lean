import Model3MaxSAT.HardMoments

noncomputable section
open scoped BigOperators
open Model3MaxSAT.FiniteProbability

namespace Model3MaxSAT.Hard

/-- The running total after the first d block levels (levels are zero-based). -/
def runningTotal {h : ℕ} (a : BlockPolicy h) (d : ℕ)
    (i : Element h) (ω : Sample h) : ℝ :=
  ∑ D : Block h, if D.1.val < d ∧ Contains D i then alignment a ω D else 0

def levelEnergy {h : ℕ} (a : BlockPolicy h) (d : ℕ) (ω : Sample h) : ℝ :=
  ∑ i : Element h, runningTotal a d i ω ^ 2

theorem sum_level_at_element {h : ℕ} (d : Fin (h + 1)) (i : Element h)
    (f : Block h → ℝ) :
    (∑ B : Block h, if B.1.val = d.val ∧ Contains B i then f B else 0) =
      f (blockAt d i) := by
  classical
  rw [Finset.sum_eq_single (blockAt d i)]
  · simp [blockAt, Contains]
  · intro B _ hB
    have hn : ¬ (B.1.val = d.val ∧ Contains B i) := by
      intro hb
      have he := eq_blockAt_of_contains B i hb.2
      have hd : B.1 = d := Fin.ext hb.1
      rw [hd] at he
      exact hB he.symm
    exact if_neg hn
  · simp

theorem sum_level_members {h : ℕ} (d : Fin (h + 1))
    (f : Block h → Element h → ℝ) :
    (∑ B : Block h, if B.1.val = d.val then
      ∑ i : Element h, if Contains B i then f B i else 0 else 0) =
      ∑ i : Element h, f (blockAt d i) i := by
  classical
  calc
    _ = ∑ B : Block h, ∑ i : Element h,
        if B.1.val = d.val ∧ Contains B i then f B i else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      by_cases hd : B.1.val = d.val
      · simp only [hd, true_and, if_true]
      · simp only [hd, false_and, if_false, Finset.sum_const_zero]
    _ = ∑ i : Element h, ∑ B : Block h,
        if B.1.val = d.val ∧ Contains B i then f B i else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_level_at_element d i (fun B => f B i)

theorem sum_level_mass {h : ℕ} (d : Fin (h + 1)) :
    (∑ B : Block h, if B.1.val = d.val then memberMass B else 0) =
      (4 ^ h : ℝ) := by
  simpa [memberMass, Element] using sum_level_members d (fun _ _ => (1 : ℝ))

theorem runningTotal_zero {h : ℕ} (a : BlockPolicy h) (i : Element h)
    (ω : Sample h) : runningTotal a 0 i ω = 0 := by
  simp [runningTotal]

theorem levelEnergy_zero {h : ℕ} (a : BlockPolicy h) (ω : Sample h) :
    levelEnergy a 0 ω = 0 := by simp [levelEnergy, runningTotal_zero]

theorem runningTotal_succ {h : ℕ} (a : BlockPolicy h) (d : Fin (h + 1))
    (i : Element h) (ω : Sample h) :
    runningTotal a (d.val + 1) i ω =
      runningTotal a d.val i ω + alignment a ω (blockAt d i) := by
  unfold runningTotal
  rw [← sum_level_at_element d i (alignment a ω), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hi : Contains B i
  · by_cases hlt : B.1.val < d.val
    · have hle : B.1.val < d.val + 1 := by omega
      have hne : B.1.val ≠ d.val := by omega
      simp [hlt, hle, hne]
    · by_cases heq : B.1.val = d.val
      · simp [heq]
      · have hn : ¬ B.1.val < d.val + 1 := by omega
        simp [hlt, heq, hn]
  · simp [hi]

/-- Exact sum of the block contributions at one level. -/
theorem levelEnergy_increment {h : ℕ} (a : BlockPolicy h)
    (d : Fin (h + 1)) (ω : Sample h) :
    levelEnergy a (d.val + 1) ω - levelEnergy a d.val ω =
      ∑ B : Block h, if B.1.val = d.val then
        memberMass B + 2 * alignment a ω B * beforeTotal a B ω else 0 := by
  have hright : (∑ B : Block h, if B.1.val = d.val then
      memberMass B + 2 * alignment a ω B * beforeTotal a B ω else 0) =
      ∑ i : Element h, (1 + 2 * alignment a ω (blockAt d i) *
        runningTotal a d.val i ω) := by
    calc
      _ = ∑ B : Block h, if B.1.val = d.val then
          ∑ i : Element h, if Contains B i then
            (1 + 2 * alignment a ω B * runningTotal a d.val i ω) else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro B _
        by_cases hd : B.1.val = d.val
        · rw [if_pos hd, if_pos hd]
          unfold memberMass beforeTotal
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : Contains B i
          · rw [if_pos hi, if_pos hi, if_pos hi]
            simp only [runningTotal, hd]
          · simp [hi]
        · rw [if_neg hd, if_neg hd]
      _ = _ := sum_level_members d _
  rw [hright]
  unfold levelEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [runningTotal_succ]
  have hy := alignment_sq a ω (blockAt d i)
  nlinarith

/-- A completion on element vertices is arbitrary, granting full benefit
of all information available at the end of the block phase. -/
def hardPayoff {h : ℕ} (a : BlockPolicy h) (z : Sample h → Element h → Bool)
    (ω : Sample h) : ℝ :=
  ∑ e : Edge h, (bval (edgeSatisfied (color ω e)
    (a.decision ω e.val.1) (z ω e.val.2)) : ℝ)

theorem edge_score_identity (η τ u v : Bool) :
    (bval (edgeSatisfied (labelColor η τ) u v) : ℝ) =
      (1 + (sign η * sign u) * (sign τ * sign v)) / 2 := by
  cases η <;> cases τ <;> cases u <;> cases v <;>
    norm_num [bval, edgeSatisfied, labelColor, sign]

theorem runningTotal_full {h : ℕ} (a : BlockPolicy h)
    (i : Element h) (ω : Sample h) :
    runningTotal a (h + 1) i ω =
      ∑ d : Fin (h + 1), alignment a ω (blockAt d i) := by
  classical
  calc
    _ = ∑ B : Block h, if Contains B i then alignment a ω B else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [B.1.isLt, true_and]
    _ = ∑ B : Block h, ∑ d : Fin (h + 1),
        if B.1.val = d.val ∧ Contains B i then alignment a ω B else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      symm
      rw [Finset.sum_eq_single B.1]
      · simp
      · intro d _ hd
        have hn : B.1.val ≠ d.val := fun he => hd (Fin.ext he.symm)
        simp [hn]
      · simp
    _ = ∑ d : Fin (h + 1), ∑ B : Block h,
        if B.1.val = d.val ∧ Contains B i then alignment a ω B else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      exact sum_level_at_element d i _

theorem hardPayoff_eq {h : ℕ} (a : BlockPolicy h)
    (z : Sample h → Element h → Bool) (ω : Sample h) :
    hardPayoff a z ω =
      ∑ i : Element h, (((h + 1 : ℕ) : ℝ) +
        runningTotal a (h + 1) i ω * (sign (ω (.inr i)) * sign (z ω i))) / 2 := by
  unfold hardPayoff
  rw [← Equiv.sum_comp (edgeEquiv h).symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ d : Fin (h + 1), (1 + alignment a ω (blockAt d i) *
        (sign (ω (.inr i)) * sign (z ω i))) / 2 := by
      apply Finset.sum_congr rfl
      intro d _
      exact edge_score_identity _ _ _ _
    _ = _ := by
      rw [runningTotal_full]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem hardPayoff_le {h : ℕ} (a : BlockPolicy h)
    (z : Sample h → Element h → Bool) (ω : Sample h) :
    hardPayoff a z ω ≤
      (((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
        ∑ i : Element h, |runningTotal a (h + 1) i ω|) / 2 := by
  rw [hardPayoff_eq]
  calc
    _ ≤ ∑ i : Element h, (((h + 1 : ℕ) : ℝ) +
        |runningTotal a (h + 1) i ω|) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hsign : (sign (ω (.inr i)) * sign (z ω i)) ^ 2 = 1 := by
        rw [mul_pow, sign_sq, sign_sq, mul_one]
      have hs := Energy.signed_mul_le_abs (runningTotal a (h + 1) i ω) _ hsign
      linarith
    _ = _ := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Element,
        Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- The concrete hard-family expected energy increment at one level. -/
theorem levelEnergy_increment_expected_le {h : ℕ} (a : BlockPolicy h)
    (d : Fin (h + 1)) :
    uniformMean h (fun ω => levelEnergy a (d.val + 1) ω - levelEnergy a d.val ω) ≤
      3 * (4 ^ h : ℝ) := by
  change mean (fun ω => levelEnergy a (d.val + 1) ω - levelEnergy a d.val ω) ≤ _
  calc
    _ = mean (fun ω => ∑ B : Block h, if B.1.val = d.val then
        memberMass B + 2 * alignment a ω B * beforeTotal a B ω else 0) :=
      mean_congr (levelEnergy_increment a d)
    _ = ∑ B : Block h, mean (fun ω => if B.1.val = d.val then
        memberMass B + 2 * alignment a ω B * beforeTotal a B ω else 0) :=
      mean_sum Finset.univ _
    _ ≤ ∑ B : Block h, if B.1.val = d.val then 3 * memberMass B else 0 := by
      apply Finset.sum_le_sum
      intro B _
      by_cases hd : B.1.val = d.val
      · simp only [if_pos hd]
        exact Energy.expected_increment_le (beforeTotal a B) (fun ω => alignment a ω B)
          (memberMass_nonneg B) (fun ω => alignment_sq a ω B)
          (beforeTotal_second_moment_mass a B)
      · simp only [if_neg hd, mean_zero, le_refl]
    _ = 3 * (∑ B : Block h, if B.1.val = d.val then memberMass B else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hd : B.1.val = d.val <;> simp [hd]
    _ = _ := by rw [sum_level_mass]

/-- Lemma 9 for the actual hard distribution and causal block policies. -/
theorem levelEnergy_expected_le {h : ℕ} (a : BlockPolicy h) :
    uniformMean h (levelEnergy a (h + 1)) ≤
      3 * ((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) := by
  have hh := Energy.telescoping_energy_bound (levelEnergy a) (h + 1)
    (3 * (4 ^ h : ℝ)) (levelEnergy_zero a)
    (fun d hd => levelEnergy_increment_expected_le a ⟨d, hd⟩)
  change mean (levelEnergy a (h + 1)) ≤ _
  calc
    _ ≤ ((h + 1 : ℕ) : ℝ) * (3 * (4 ^ h : ℝ)) := hh
    _ = _ := by ring

/-- Proposition 10 for the actual distribution, with an arbitrary favorable
completion on element vertices. No energy or orthogonality assumption remains. -/
theorem hardPayoff_expected_le {h : ℕ} (a : BlockPolicy h)
    (z : Sample h → Element h → Bool) :
    uniformMean h (hardPayoff a z) ≤
      (((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
        (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2 := by
  have hpay : ∀ ω, hardPayoff a z ω ≤
      (((h + 1 : ℕ) : ℝ) * (Fintype.card (Element h) : ℝ) +
        ∑ i : Element h, |runningTotal a (h + 1) i ω|) / 2 := by
    intro ω
    simpa only [Element, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      using hardPayoff_le a z ω
  have henergy : mean (fun ω => ∑ i : Element h, runningTotal a (h + 1) i ω ^ 2) ≤
      3 * ((h + 1 : ℕ) : ℝ) * (Fintype.card (Element h) : ℝ) := by
    simpa only [Element, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      using levelEnergy_expected_le a
  simpa only [Element, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    Energy.payoff_from_energy (fun i ω => runningTotal a (h + 1) i ω)
      (hardPayoff a z) (L := ((h + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _) hpay henergy

#print axioms levelEnergy_increment
#print axioms hardPayoff_le
#print axioms levelEnergy_expected_le
#print axioms hardPayoff_expected_le

end Model3MaxSAT.Hard
