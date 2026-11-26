import Model3MaxSAT.Switching
import Model3MaxSAT.HardCounting
import Model3MaxSAT.Energy
import Model3MaxSAT.HardChildren
import Model3MaxSAT.HardMembers

noncomputable section
open scoped BigOperators
open Model3MaxSAT.FiniteProbability

namespace Model3MaxSAT.Hard

/-- The manuscript's strict pre-parent prefix is preserved in full, even
when some other parent-level blocks have already arrived. Their blocks are
disjoint from this parent, so none of their incident colors changes. -/
theorem flip_blockItem_before_parent {h : ℕ} (B : Block h) (hp : 0 < B.1.val)
    (k : Fin 4) (E : Block h) (ω : Sample h)
    (hbefore : BeforeEq E B) (hne : E ≠ B) :
    blockItem (flip (child B hp k) ω) E = blockItem ω E := by
  rcases hbefore with hlt | ⟨heq, _⟩
  · apply flip_blockItem
    rw [child_level]
    omega
  · have hnb : ¬ Below E (child B hp k) := by
      intro hb
      have hh := hb.1
      rw [child_level] at hh
      omega
    funext i
    by_cases hi : Contains E i
    · have hnc : ¬ Contains (child B hp k) i := by
        intro hci
        have hBi := child_contains_parent B hp k hci
        exact hne (contains_same_level_unique heq hi hBi)
      simp only [blockItem, if_pos hi]
      change some (labelColor (if Below E (child B hp k) then _ else _)
        (if Contains (child B hp k) i then _ else _)) = _
      rw [if_neg hnb, if_neg hnc]
    · simp only [blockItem, if_neg hi]

def beforeTotal {h : ℕ} (a : BlockPolicy h) (C : Block h) (ω : Sample h) : ℝ :=
  ∑ i : Element h, if Contains C i then
    ∑ D : Block h, if D.1.val < C.1.val ∧ Contains D i then alignment a ω D else 0
  else 0

def memberMass {h : ℕ} (C : Block h) : ℝ :=
  ∑ i : Element h, if Contains C i then 1 else 0

theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

theorem alignment_sq {h : ℕ} (a : BlockPolicy h) (ω : Sample h) (D : Block h) :
    alignment a ω D ^ 2 = 1 := by
  rw [alignment, mul_pow, sign_sq, sign_sq, mul_one]

theorem memberMass_nonneg {h : ℕ} (C : Block h) : 0 ≤ memberMass C := by
  unfold memberMass
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

theorem blockTotal_eq_before_add {h : ℕ} (a : BlockPolicy h)
    (C : Block h) (ω : Sample h) :
    blockTotal a C ω = beforeTotal a C ω + memberMass C * alignment a ω C := by
  have hlocal (i : Element h) (hi : Contains C i) :
      (∑ D : Block h, if D.1.val ≤ C.1.val ∧ Contains D i then alignment a ω D else 0) =
      (∑ D : Block h, if D.1.val < C.1.val ∧ Contains D i then alignment a ω D else 0) +
        alignment a ω C := by
    calc
      _ = ∑ D : Block h,
          ((if D.1.val < C.1.val ∧ Contains D i then alignment a ω D else 0) +
           (if D = C then alignment a ω C else 0)) := by
        apply Finset.sum_congr rfl
        intro D _
        by_cases heq : D = C
        · subst D
          rw [if_pos ⟨le_refl _, hi⟩,
            if_neg (show ¬ (C.1.val < C.1.val ∧ Contains C i) by omega),
            if_pos rfl, zero_add]
        · by_cases hsmall : D.1.val < C.1.val ∧ Contains D i
          · rw [if_pos ⟨Nat.le_of_lt hsmall.1, hsmall.2⟩,
              if_pos hsmall, if_neg heq, add_zero]
          · have hbig : ¬ (D.1.val ≤ C.1.val ∧ Contains D i) := by
              intro hD
              have hsame : D.1.val = C.1.val := by omega
              exact heq (contains_same_level_unique hsame hD.2 hi)
            rw [if_neg hbig, if_neg hsmall, if_neg heq, add_zero]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  unfold blockTotal beforeTotal memberMass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Contains C i
  · rw [if_pos hi, if_pos hi, if_pos hi, one_mul]
    exact hlocal i hi
  · rw [if_neg hi, if_neg hi, if_neg hi, zero_mul, add_zero]

theorem beforeTotal_zero_level {h : ℕ} (a : BlockPolicy h)
    (C : Block h) (hC : C.1.val = 0) (ω : Sample h) :
    beforeTotal a C ω = 0 := by
  unfold beforeTotal
  simp only [hC, Nat.not_lt_zero, false_and, if_false, Finset.sum_const_zero,
    ite_self]

/-- The old total of a parent is the sum of its four completed child totals. -/
theorem beforeTotal_eq_sum_children {h : ℕ} (a : BlockPolicy h)
    (C : Block h) (hp : 0 < C.1.val) (ω : Sample h) :
    beforeTotal a C ω = ∑ k : Fin 4, blockTotal a (child C hp k) ω := by
  unfold beforeTotal
  rw [sum_children C hp]
  apply Finset.sum_congr rfl
  intro k _
  unfold blockTotal
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Contains (child C hp k) i
  · rw [if_pos hi, if_pos hi]
    apply Finset.sum_congr rfl
    intro D _
    have hlev : (D.1.val < C.1.val) = (D.1.val ≤ (child C hp k).1.val) := by
      apply propext
      rw [child_level]
      omega
    simp only [hlev]
  · rw [if_neg hi, if_neg hi]

theorem memberMass_eq_pow {h : ℕ} (C : Block h) :
    memberMass C = (4 ^ C.1.val : ℕ) := by
  unfold memberMass
  simpa only [mul_one] using sum_indicator_const C 1

/-- The explicit child sizes are exactly one quarter of the parent's size. -/
theorem child_size_quarter {h : ℕ} (C : Block h) (hp : 0 < C.1.val) (k : Fin 4) :
    (4 ^ (child C hp k).1.val : ℕ) = ((4 ^ C.1.val : ℕ) : ℝ) / 4 := by
  have he := parent_size_four_children C hp k
  have her : ((4 ^ C.1.val : ℕ) : ℝ) = 4 * ((4 ^ (child C hp k).1.val : ℕ) : ℝ) := by
    exact_mod_cast he
  linarith

/-- Both second-moment bounds are proved simultaneously by induction on
the actual block level, using the concrete switching theorem. -/
theorem block_moments {h : ℕ} (a : BlockPolicy h) (C : Block h) :
    uniformMean h (fun ω => beforeTotal a C ω ^ 2) ≤ ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 ∧
    uniformMean h (fun ω => blockTotal a C ω ^ 2) ≤ 4 * ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 := by
  have hgeneral : ∀ d : ℕ, ∀ C : Block h, C.1.val = d →
      uniformMean h (fun ω => beforeTotal a C ω ^ 2) ≤ ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 ∧
      uniformMean h (fun ω => blockTotal a C ω ^ 2) ≤ 4 * ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro C hC
      have hT : uniformMean h (fun ω => beforeTotal a C ω ^ 2) ≤
          ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 := by
        by_cases hp : 0 < C.1.val
        · have hchildren (k : Fin 4) :
              mean (fun ω => blockTotal a (child C hp k) ω ^ 2) ≤
                4 * (((4 ^ C.1.val : ℕ) : ℝ) / 4) ^ 2 := by
            have hlt : (child C hp k).1.val < d := by rw [child_level]; omega
            have hb := (ih _ hlt (child C hp k) rfl).2
            rw [child_size_quarter C hp k] at hb
            exact hb
          have hb := Energy.four_child_second_moment
            (fun k ω => blockTotal a (child C hp k) ω)
            (((4 ^ C.1.val : ℕ) : ℝ))
            (fun i j hij => blockTotal_orthogonal a (child C hp i) (child C hp j)
              rfl (fun heq => hij (child_injective C hp heq))) hchildren
          have heq : (fun ω => beforeTotal a C ω ^ 2) =
              (fun ω => (∑ k : Fin 4, blockTotal a (child C hp k) ω) ^ 2) := by
            funext ω
            rw [beforeTotal_eq_sum_children a C hp]
          rw [heq]
          exact hb
        · have hz : C.1.val = 0 := Nat.eq_zero_of_not_pos hp
          have heq : (fun ω => beforeTotal a C ω ^ 2) = (fun _ : Sample h => (0 : ℝ)) := by
            funext ω
            rw [beforeTotal_zero_level a C hz, zero_pow (by decide : 2 ≠ 0)]
          rw [heq]
          exact (mean_zero.le).trans (sq_nonneg _)
      refine ⟨hT, ?_⟩
      have hM := Energy.parent_second_moment
        (beforeTotal a C) (fun ω => alignment a ω C)
        (s := ((4 ^ C.1.val : ℕ) : ℝ)) (Nat.cast_nonneg _)
        (fun ω => alignment_sq a ω C) hT
      have heq : (fun ω => blockTotal a C ω ^ 2) =
          (fun ω => (beforeTotal a C ω + ((4 ^ C.1.val : ℕ) : ℝ) * alignment a ω C) ^ 2) := by
        funext ω
        rw [blockTotal_eq_before_add, memberMass_eq_pow]
      rw [heq]
      exact hM
  exact hgeneral C.1.val C rfl

theorem beforeTotal_second_moment {h : ℕ} (a : BlockPolicy h) (C : Block h) :
    uniformMean h (fun ω => beforeTotal a C ω ^ 2) ≤ ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 :=
  (block_moments a C).1

theorem blockTotal_second_moment {h : ℕ} (a : BlockPolicy h) (C : Block h) :
    uniformMean h (fun ω => blockTotal a C ω ^ 2) ≤ 4 * ((4 ^ C.1.val : ℕ) : ℝ) ^ 2 :=
  (block_moments a C).2

theorem beforeTotal_second_moment_mass {h : ℕ} (a : BlockPolicy h) (C : Block h) :
    uniformMean h (fun ω => beforeTotal a C ω ^ 2) ≤ memberMass C ^ 2 := by
  rw [memberMass_eq_pow]
  exact beforeTotal_second_moment a C

#print axioms blockTotal_eq_before_add
#print axioms alignment_sq
#print axioms beforeTotal_eq_sum_children
#print axioms block_moments
#print axioms flip_blockItem_before_parent

end Model3MaxSAT.Hard
