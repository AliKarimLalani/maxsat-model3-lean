import Model3MaxSAT.HardCounting

/-! Exact cardinalities and finite sums over the elements of a block. -/

open scoped BigOperators

namespace Model3MaxSAT.Hard

/-- The interval of element vertices belonging to a block. -/
def members {h : ℕ} (B : Block h) : Finset (Element h) :=
  Finset.univ.filter (Contains B)

@[simp] theorem mem_members {h : ℕ} (B : Block h) (i : Element h) :
    i ∈ members B ↔ Contains B i := by
  simp [members]

/-- The element at offset r in block B. -/
def blockElement {h : ℕ} (B : Block h) (r : Fin (4 ^ B.1.val)) : Element h :=
  ⟨B.2.val * 4 ^ B.1.val + r.val, by
    calc
      _ < B.2.val * 4 ^ B.1.val + 4 ^ B.1.val :=
        Nat.add_lt_add_left r.isLt _
      _ = (B.2.val + 1) * 4 ^ B.1.val := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 4 ^ (h - B.1.val) * 4 ^ B.1.val :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt B.2.isLt)
      _ = 4 ^ h := pow_split B.1⟩

theorem contains_blockElement {h : ℕ} (B : Block h)
    (r : Fin (4 ^ B.1.val)) : Contains B (blockElement B r) := by
  change (B.2.val * 4 ^ B.1.val + r.val) / 4 ^ B.1.val = B.2.val
  rw [Nat.mul_comm B.2.val, Nat.mul_add_div (by exact Nat.pow_pos (by decide))]
  simp [Nat.div_eq_of_lt r.isLt]

/-- Division identifies the block and remainder identifies the offset. -/
def memberEquiv {h : ℕ} (B : Block h) :
    {i : Element h // Contains B i} ≃ Fin (4 ^ B.1.val) where
  toFun i := ⟨i.val.val % 4 ^ B.1.val, Nat.mod_lt _ (by exact Nat.pow_pos (by decide))⟩
  invFun r := ⟨blockElement B r, contains_blockElement B r⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change B.2.val * 4 ^ B.1.val + i.val.val % 4 ^ B.1.val = i.val.val
    rw [← i.property]
    exact Nat.div_add_mod' _ _
  right_inv r := by
    apply Fin.ext
    exact Nat.mul_add_mod_of_lt r.isLt

theorem card_member_subtype {h : ℕ} (B : Block h) :
    Fintype.card {i : Element h // Contains B i} = 4 ^ B.1.val := by
  rw [Fintype.card_congr (memberEquiv B), Fintype.card_fin]

theorem members_card {h : ℕ} (B : Block h) :
    (members B).card = 4 ^ B.1.val := by
  rw [← Fintype.card_of_subtype (members B) (mem_members B)]
  exact card_member_subtype B

theorem members_nonempty {h : ℕ} (B : Block h) : (members B).Nonempty := by
  apply Finset.card_pos.mp
  rw [members_card]
  exact Nat.pow_pos (by decide)

theorem sum_members_const {h : ℕ} (B : Block h) (c : ℝ) :
    (∑ _i ∈ members B, c) = (4 ^ B.1.val : ℕ) * c := by
  simp only [Finset.sum_const, members_card, nsmul_eq_mul]

theorem sum_indicator_const {h : ℕ} (B : Block h) (c : ℝ) :
    (∑ i : Element h, if Contains B i then c else 0) =
      (4 ^ B.1.val : ℕ) * c := by
  calc
    _ = ∑ _i ∈ members B, c := by
      rw [members, Finset.sum_filter]
    _ = _ := sum_members_const B c

#print axioms contains_blockElement
#print axioms card_member_subtype
#print axioms members_card
#print axioms sum_indicator_const

end Model3MaxSAT.Hard
