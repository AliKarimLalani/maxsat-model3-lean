import Model3MaxSAT.HardCounting
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order

noncomputable section

namespace Model3MaxSAT.Hard

abbrev OrderedBlock (h : ℕ) := Lex (Block h)
abbrev OrderedVertex (h : ℕ) := Lex (OrderedBlock h ⊕ Element h)

def orderView (h : ℕ) : Vertex h ≃ OrderedVertex h where
  toFun v := toLex (Sum.map toLex id v)
  invFun v := Sum.map ofLex id (ofLex v)
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

abbrev vertexCount (h : ℕ) := Fintype.card (OrderedVertex h)

/-- Canonical increasing vertex enumeration: blocks in level/position order,
followed by all elements. Names are independent of sampled colors. -/
def vertexOrderIso (h : ℕ) : Fin (vertexCount h) ≃o OrderedVertex h :=
  monoEquivOfFin (OrderedVertex h) rfl

def vertexCode (h : ℕ) : Vertex h ≃ Fin (vertexCount h) :=
  (orderView h).trans (vertexOrderIso h).symm.toEquiv

theorem vertexCode_le_iff {h : ℕ} (v w : Vertex h) :
    vertexCode h v ≤ vertexCode h w ↔ orderView h v ≤ orderView h w :=
  (vertexOrderIso h).symm.map_rel_iff

theorem block_order_iff {h : ℕ} (B C : Block h) :
    (toLex B : OrderedBlock h) ≤ toLex C ↔ B.1.val < C.1.val ∨
      (B.1.val = C.1.val ∧ B.2.val ≤ C.2.val) := by
  rw [Sigma.Lex.le_def]
  constructor
  · rintro (h | ⟨heq, hp⟩)
    · exact Or.inl h
    · refine Or.inr ⟨congrArg Fin.val heq, ?_⟩
      cases B with
      | mk d j =>
        cases C with
        | mk e k =>
          dsimp at heq hp ⊢
          change d = e at heq
          subst e
          change j ≤ k at hp
          exact hp
  · rintro (h | ⟨heq, hp⟩)
    · exact Or.inl h
    · have heq' : B.1 = C.1 := Fin.ext heq
      refine Or.inr ⟨heq', ?_⟩
      cases B with
      | mk d j =>
        cases C with
        | mk e k =>
          dsimp at heq' hp ⊢
          subst e
          exact hp

theorem code_blocks_le_iff {h : ℕ} (B C : Block h) :
    vertexCode h (.inl B) ≤ vertexCode h (.inl C) ↔
      B.1.val < C.1.val ∨ (B.1.val = C.1.val ∧ B.2.val ≤ C.2.val) := by
  rw [vertexCode_le_iff]
  change (toLex (Sum.inl (toLex B)) : OrderedVertex h) ≤ toLex (Sum.inl (toLex C)) ↔ _
  rw [Sum.Lex.inl_le_inl_iff]
  exact block_order_iff B C

theorem code_block_lt_element {h : ℕ} (B : Block h) (i : Element h) :
    vertexCode h (.inl B) < vertexCode h (.inr i) := by
  change (vertexOrderIso h).symm (orderView h (.inl B)) <
    (vertexOrderIso h).symm (orderView h (.inr i))
  apply (vertexOrderIso h).symm.strictMono
  exact Sum.Lex.sep _ _

theorem code_element_not_le_block {h : ℕ} (i : Element h) (B : Block h) :
    ¬ vertexCode h (.inr i) ≤ vertexCode h (.inl B) :=
  not_le_of_gt (code_block_lt_element B i)

#print axioms code_blocks_le_iff
#print axioms code_block_lt_element

end Model3MaxSAT.Hard
