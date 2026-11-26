import Model3MaxSAT.HardLabels

namespace Model3MaxSAT.Hard

theorem level_le_height {h : ℕ} (d : Fin (h + 1)) : d.val ≤ h := by omega

theorem pow_split {h : ℕ} (d : Fin (h + 1)) :
    4 ^ (h - d.val) * 4 ^ d.val = 4 ^ h := by
  rw [← pow_add, Nat.sub_add_cancel (level_le_height d)]

/-- The unique block at a specified level containing an element. -/
def blockAt {h : ℕ} (d : Fin (h + 1)) (i : Element h) : Block h :=
  ⟨d, ⟨i.val / 4 ^ d.val, by
    apply (Nat.div_lt_iff_lt_mul (by exact Nat.pow_pos (by decide))).2
    rw [pow_split d]
    exact i.isLt⟩⟩

theorem contains_blockAt {h : ℕ} (d : Fin (h + 1)) (i : Element h) :
    Contains (blockAt d i) i := rfl

theorem eq_blockAt_of_contains {h : ℕ} (B : Block h) (i : Element h)
    (hi : Contains B i) : blockAt B.1 i = B := by
  rcases B with ⟨d, j⟩
  change (⟨d, (blockAt d i).2⟩ : Block h) = ⟨d, j⟩
  congr 1
  exact Fin.ext hi

/-- One edge for each level and each element. -/
def edgeEquiv (h : ℕ) : Edge h ≃ (Fin (h + 1) × Element h) where
  toFun e := (e.val.1.1, e.val.2)
  invFun p := ⟨(blockAt p.1 p.2, p.2), rfl⟩
  left_inv e := by
    apply Subtype.ext
    exact Prod.ext (eq_blockAt_of_contains e.val.1 e.val.2 e.property) rfl
  right_inv p := rfl

theorem card_edges (h : ℕ) : Fintype.card (Edge h) = (h + 1) * 4 ^ h := by
  rw [Fintype.card_congr (edgeEquiv h), Fintype.card_prod]
  simp [Element]

/-- Every element has exactly one neighbor at each level. -/
theorem unique_block_per_level {h : ℕ} (d : Fin (h + 1)) (i : Element h) :
    ∃! B : Block h, B.1 = d ∧ Contains B i := by
  refine ⟨blockAt d i, ⟨rfl, rfl⟩, ?_⟩
  intro B hB
  have hh := eq_blockAt_of_contains B i hB.2
  rw [hB.1] at hh
  exact hh.symm

#print axioms card_edges
#print axioms unique_block_per_level

end Model3MaxSAT.Hard
