import Model3MaxSAT.HardStructure
import Model3MaxSAT.FiniteMean

/-!
The concrete subtree-label switch preserves every full incidence row at
levels no later than the switched block. A row includes colors at every
named element endpoint, all of which are still future vertices in this
phase. Policies below are causal policies on this fixed hard-input family.
The bridge from a general MaxCC policy is a separate theorem.
-/

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT.Hard

def labelColor (u v : Bool) : EdgeColor :=
  if u == v then .blue else .red

theorem labelColor_not (u v : Bool) : labelColor (!u) (!v) = labelColor u v := by
  cases u <;> cases v <;> rfl

/-- All original incident edges at a named block vertex, including their
colors at named future element vertices. The uncolored skeleton is fixed. -/
def blockItem {h : ℕ} (ω : Sample h) (D : Block h) :
    Element h → Option EdgeColor :=
  fun i => if Contains D i then some (labelColor (ω (.inl D)) (ω (.inr i))) else none

def inSubtree {h : ℕ} (C : Block h) : Vertex h → Prop
  | .inl D => Below D C
  | .inr i => Contains C i

instance {h : ℕ} (C : Block h) (v : Vertex h) : Decidable (inSubtree C v) := by
  cases v <;> unfold inSubtree <;> infer_instance

/-- Flip every hidden vertex label inside the chosen child subtree. -/
def flip {h : ℕ} (C : Block h) (ω : Sample h) : Sample h :=
  fun v => if inSubtree C v then !(ω v) else ω v

theorem flip_flip {h : ℕ} (C : Block h) (ω : Sample h) :
    flip C (flip C ω) = ω := by
  funext v
  by_cases hv : inSubtree C v <;> simp [flip, hv]

def flipEquiv {h : ℕ} (C : Block h) : Sample h ≃ Sample h where
  toFun := flip C
  invFun := flip C
  left_inv := flip_flip C
  right_inv := flip_flip C

/-- The concrete full-observation switching lemma. No invariance of
observations is assumed: it follows from the interval containment relation. -/
theorem flip_blockItem {h : ℕ} (C D : Block h) (ω : Sample h)
    (hle : D.1.val ≤ C.1.val) :
    blockItem (flip C ω) D = blockItem ω D := by
  funext i
  by_cases hi : Contains D i
  · simp only [blockItem, if_pos hi]
    have hiff := contains_iff_below D C i hle hi
    by_cases hc : Contains C i
    · have hb : Below D C := hiff.mp hc
      change some (labelColor (if Below D C then _ else _)
        (if Contains C i then _ else _)) = _
      rw [if_pos hb, if_pos hc, labelColor_not]
    · have hb : ¬ Below D C := fun hb => hc (hiff.mpr hb)
      change some (labelColor (if Below D C then _ else _)
        (if Contains C i then _ else _)) = _
      rw [if_neg hb, if_neg hc]
  · simp only [blockItem, if_neg hi]

/-- A deterministic policy during the block phase of the fixed hard family.
Its causality condition exposes all earlier full incidence rows. -/
structure BlockPolicy (h : ℕ) where
  decision : Sample h → Block h → Bool
  causal : ∀ (ω ω' : Sample h) (D : Block h),
    (∀ E : Block h, BeforeEq E D → blockItem ω E = blockItem ω' E) →
      decision ω D = decision ω' D

theorem BlockPolicy.decision_flip {h : ℕ} (a : BlockPolicy h)
    (C D : Block h) (ω : Sample h) (hle : D.1.val ≤ C.1.val) :
    a.decision (flip C ω) D = a.decision ω D := by
  apply a.causal
  intro E hED
  exact flip_blockItem C E ω ((beforeEq_level_le hED).trans hle)

def sign (b : Bool) : ℝ := if b then 1 else -1

theorem sign_not (b : Bool) : sign (!b) = - sign b := by
  cases b <;> simp [sign]

def alignment {h : ℕ} (a : BlockPolicy h) (ω : Sample h) (D : Block h) : ℝ :=
  sign (ω (.inl D)) * sign (a.decision ω D)

theorem alignment_flip_of_below {h : ℕ} (a : BlockPolicy h)
    (C D : Block h) (ω : Sample h) (hb : Below D C) :
    alignment a (flip C ω) D = - alignment a ω D := by
  simp [alignment, a.decision_flip C D ω hb.1, flip, inSubtree, hb,
    sign_not, neg_mul]

theorem alignment_flip_of_not_below {h : ℕ} (a : BlockPolicy h)
    (C D : Block h) (ω : Sample h) (hle : D.1.val ≤ C.1.val)
    (hb : ¬ Below D C) :
    alignment a (flip C ω) D = alignment a ω D := by
  simp [alignment, a.decision_flip C D ω hle, flip, inSubtree, hb]

/-- The total after all assignments through the level of C, restricted
to elements in C. This is the manuscript's M_C. -/
def blockTotal {h : ℕ} (a : BlockPolicy h) (C : Block h) (ω : Sample h) : ℝ :=
  ∑ i : Element h, if Contains C i then
    ∑ D : Block h, if D.1.val ≤ C.1.val ∧ Contains D i then alignment a ω D else 0
  else 0

theorem blockTotal_flip_self {h : ℕ} (a : BlockPolicy h)
    (C : Block h) (ω : Sample h) :
    blockTotal a C (flip C ω) = - blockTotal a C ω := by
  unfold blockTotal
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Contains C i
  · rw [if_pos hi, if_pos hi]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D _
    by_cases hD : D.1.val ≤ C.1.val ∧ Contains D i
    · rw [if_pos hD, if_pos hD]
      exact alignment_flip_of_below a C D ω
        ((contains_iff_below D C i hD.1 hD.2).mp hi)
    · rw [if_neg hD, if_neg hD, neg_zero]
  · rw [if_neg hi, if_neg hi, neg_zero]

theorem blockTotal_flip_other {h : ℕ} (a : BlockPolicy h)
    (C C' : Block h) (ω : Sample h)
    (heq : C.1.val = C'.1.val) (hne : C ≠ C') :
    blockTotal a C' (flip C ω) = blockTotal a C' ω := by
  unfold blockTotal
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Contains C' i
  · rw [if_pos hi, if_pos hi]
    apply Finset.sum_congr rfl
    intro D _
    by_cases hD : D.1.val ≤ C'.1.val ∧ Contains D i
    · rw [if_pos hD, if_pos hD]
      have hle : D.1.val ≤ C.1.val := heq.symm ▸ hD.1
      apply alignment_flip_of_not_below a C D ω hle
      intro hb
      have hc := below_contains hb hD.2
      exact hne (contains_same_level_unique heq hc hi)
    · rw [if_neg hD, if_neg hD]
  · rw [if_neg hi, if_neg hi]

/-- Reindexing the actual hidden-label sample space by its subtree switch
preserves the uniform average. -/
theorem uniformMean_flip {h : ℕ} (C : Block h) (f : Sample h → ℝ) :
    uniformMean h (fun ω => f (flip C ω)) = uniformMean h f :=
  FiniteProbability.mean_equiv (flipEquiv C) f

/-- In particular, distinct siblings have zero mixed second moment. The
statement is slightly stronger: any distinct blocks on the same level do. -/
theorem blockTotal_orthogonal {h : ℕ} (a : BlockPolicy h)
    (C C' : Block h) (heq : C.1.val = C'.1.val) (hne : C ≠ C') :
    uniformMean h (fun ω => blockTotal a C ω * blockTotal a C' ω) = 0 := by
  exact FiniteProbability.mean_mul_cancel_of_flip (flipEquiv C)
    (blockTotal a C) (blockTotal a C')
    (blockTotal_flip_self a C) (fun ω => blockTotal_flip_other a C C' ω heq hne)

#print axioms flip_blockItem
#print axioms BlockPolicy.decision_flip
#print axioms blockTotal_flip_self
#print axioms blockTotal_flip_other
#print axioms uniformMean_flip
#print axioms blockTotal_orthogonal

end Model3MaxSAT.Hard
