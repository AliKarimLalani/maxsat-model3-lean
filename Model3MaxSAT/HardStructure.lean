import Model3MaxSAT.HardLabels
import Mathlib.Data.Nat.Basic

/-! Concrete interval nesting for the four-ary hard family. -/

namespace Model3MaxSAT.Hard

def Below {h : ℕ} (D C : Block h) : Prop :=
  D.1.val ≤ C.1.val ∧
    D.2.val / 4 ^ (C.1.val - D.1.val) = C.2.val

instance {h : ℕ} (D C : Block h) : Decidable (Below D C) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem div_pow_div_pow {i d c : ℕ} (hle : d ≤ c) :
    i / 4 ^ d / 4 ^ (c - d) = i / 4 ^ c := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le hle]

theorem contains_iff_below {h : ℕ} (D C : Block h) (i : Element h)
    (hle : D.1.val ≤ C.1.val) (hi : Contains D i) :
    Contains C i ↔ Below D C := by
  have heq : i.val / 4 ^ C.1.val = D.2.val / 4 ^ (C.1.val - D.1.val) := by
    rw [← div_pow_div_pow hle, hi]
  change (i.val / 4 ^ C.1.val = C.2.val) ↔ _
  rw [heq]
  simp only [Below, hle, true_and]

theorem below_refl {h : ℕ} (C : Block h) : Below C C := by
  simp [Below]

theorem below_contains {h : ℕ} {D C : Block h} {i : Element h}
    (hDC : Below D C) (hi : Contains D i) : Contains C i :=
  (contains_iff_below D C i hDC.1 hi).mpr hDC

/-- The fixed order within the block phase: levels first, then positions. -/
def BeforeEq {h : ℕ} (E D : Block h) : Prop :=
  E.1.val < D.1.val ∨ (E.1.val = D.1.val ∧ E.2.val ≤ D.2.val)

theorem beforeEq_level_le {h : ℕ} {E D : Block h} (hED : BeforeEq E D) :
    E.1.val ≤ D.1.val := by
  rcases hED with hlt | ⟨heq, _⟩
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq

theorem beforeEq_refl {h : ℕ} (D : Block h) : BeforeEq D D :=
  Or.inr ⟨rfl, le_refl _⟩

theorem contains_same_level_unique {h : ℕ} {C D : Block h} {i : Element h}
    (heq : C.1.val = D.1.val) (hC : Contains C i) (hD : Contains D i) : C = D := by
  obtain ⟨c, C⟩ := C
  obtain ⟨d, D⟩ := D
  have hcd : c = d := Fin.ext heq
  subst d
  congr 1
  exact Fin.ext (hC.symm.trans hD)

theorem disjoint_same_level {h : ℕ} {C D : Block h}
    (heq : C.1.val = D.1.val) (hne : C ≠ D) {i : Element h}
    (hC : Contains C i) : ¬ Contains D i := by
  intro hD
  exact hne (contains_same_level_unique heq hC hD)

#print axioms contains_iff_below
#print axioms contains_same_level_unique

end Model3MaxSAT.Hard
