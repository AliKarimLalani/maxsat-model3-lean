import Model3MaxSAT.HardCounting
import Model3MaxSAT.HardStructure
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT.Hard

/-- The four immediate children of a nonsingleton block. -/
def child {h : ℕ} (B : Block h) (hp : 0 < B.1.val) (k : Fin 4) : Block h :=
  ⟨⟨B.1.val - 1, by have hb := B.1.isLt; omega⟩,
    ⟨4 * B.2.val + k.val, by
      have hb := level_le_height B.1
      have he : h - (B.1.val - 1) = h - B.1.val + 1 := by omega
      rw [he, pow_succ]
      have hj := B.2.isLt
      have hk := k.isLt
      omega⟩⟩

@[simp] theorem child_level {h : ℕ} (B : Block h) (hp : 0 < B.1.val) (k : Fin 4) :
    (child B hp k).1.val = B.1.val - 1 := rfl

@[simp] theorem child_position {h : ℕ} (B : Block h) (hp : 0 < B.1.val) (k : Fin 4) :
    (child B hp k).2.val = 4 * B.2.val + k.val := rfl

theorem child_below {h : ℕ} (B : Block h) (hp : 0 < B.1.val) (k : Fin 4) :
    Below (child B hp k) B := by
  constructor
  · simp only [child_level]
    omega
  · change (4 * B.2.val + k.val) / 4 ^ (B.1.val - (B.1.val - 1)) = B.2.val
    have he : B.1.val - (B.1.val - 1) = 1 := by omega
    rw [he, pow_one]
    have hk := k.isLt
    omega

theorem child_contains_parent {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (k : Fin 4) {i : Element h} (hi : Contains (child B hp k) i) : Contains B i :=
  below_contains (child_below B hp k) hi

theorem child_injective {h : ℕ} (B : Block h) (hp : 0 < B.1.val) :
    Function.Injective (child B hp) := by
  intro k j hkj
  have he := congrArg (fun D : Block h => D.2.val) hkj
  change 4 * B.2.val + k.val = 4 * B.2.val + j.val at he
  exact Fin.ext (Nat.add_left_cancel he)

theorem exists_child_contains {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (i : Element h) (hi : Contains B i) :
    ∃ k : Fin 4, Contains (child B hp k) i := by
  let q := i.val / 4 ^ (B.1.val - 1)
  have hq : q / 4 = B.2.val := by
    have hh := div_pow_div_pow (i := i.val) (d := B.1.val - 1)
      (c := B.1.val) (by omega)
    have he : B.1.val - (B.1.val - 1) = 1 := by omega
    rw [he, pow_one] at hh
    exact hh.trans hi
  refine ⟨⟨q % 4, Nat.mod_lt _ (by decide)⟩, ?_⟩
  change q = 4 * B.2.val + q % 4
  have hm := Nat.mod_add_div q 4
  omega

theorem unique_child_contains {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (i : Element h) (hi : Contains B i) :
    ∃! k : Fin 4, Contains (child B hp k) i := by
  obtain ⟨k,hk⟩ := exists_child_contains B hp i hi
  refine ⟨k,hk,?_⟩
  intro j hj
  apply child_injective B hp
  exact contains_same_level_unique rfl hj hk

theorem contains_iff_child {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (i : Element h) :
    Contains B i ↔ ∃ k : Fin 4, Contains (child B hp k) i := by
  constructor
  · exact exists_child_contains B hp i
  · rintro ⟨k,hk⟩
    exact child_contains_parent B hp k hk

/-- Partitioning a parent sum into its four disjoint child sums. -/
theorem sum_children {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (f : Element h → ℝ) :
    (∑ i, if Contains B i then f i else 0) =
      ∑ k : Fin 4, ∑ i, if Contains (child B hp k) i then f i else 0 := by
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Contains B i
  · obtain ⟨k,hk,hunique⟩ := unique_child_contains B hp i hi
    rw [if_pos hi]
    calc
      _ = (if Contains (child B hp k) i then f i else 0) := by
        apply Finset.sum_eq_single k
        · intro j _ hj
          have hn : ¬ Contains (child B hp j) i := by
            intro hji
            exact hj (hunique j hji)
          simp [hn]
        · intro hknot
          exact False.elim (hknot (Finset.mem_univ k))
      _ = f i := by rw [if_pos hk]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro k _
    have hk : ¬ Contains (child B hp k) i := by
      intro hki
      exact hi (child_contains_parent B hp k hki)
    exact if_neg hk

theorem parent_size_four_children {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (k : Fin 4) : 4 ^ B.1.val = 4 * 4 ^ (child B hp k).1.val := by
  have he : B.1.val = (B.1.val - 1) + 1 := by omega
  rw [child_level]
  conv_lhs => rw [he, pow_succ]
  exact Nat.mul_comm _ _

#print axioms unique_child_contains
#print axioms sum_children

end Model3MaxSAT.Hard
