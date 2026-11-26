import Model3MaxSAT.HardInput
import Model3MaxSAT.HardMembers
import Mathlib.Logic.Relation

/-! Connectedness of the actual hard graph, including the one-level case. -/

noncomputable section

namespace Model3MaxSAT

/-- Undirected adjacency through one of the graph's named edges. -/
def CCGraph.Adjacent {n m : ℕ} (G : CCGraph n m) (u v : Fin n) : Prop :=
  ∃ e, (G.left e = u ∧ G.right e = v) ∨ (G.left e = v ∧ G.right e = u)

theorem CCGraph.adjacent_symmetric {n m : ℕ} (G : CCGraph n m) :
    Symmetric G.Adjacent := by
  intro u v
  rintro ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Every pair of vertices is joined by a finite undirected path. -/
def CCGraph.Connected {n m : ℕ} (G : CCGraph n m) : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adjacent u v

namespace Hard

def topBlock (h : ℕ) : Block h :=
  ⟨⟨h, Nat.lt_succ_self h⟩, ⟨0, by simp⟩⟩

theorem contains_topBlock {h : ℕ} (i : Element h) : Contains (topBlock h) i := by
  exact Nat.div_eq_of_lt i.isLt

theorem hardGraph_adjacent_member {h : ℕ} (ω : Sample h)
    (B : Block h) (i : Element h) (hi : Contains B i) :
    (hardGraph h ω).Adjacent (vertexCode h (.inl B)) (vertexCode h (.inr i)) := by
  let e : Edge h := ⟨(B, i), hi⟩
  refine ⟨edgeCode h e, Or.inl ?_⟩
  simp [hardGraph, e]

theorem hardGraph_reaches_top {h : ℕ} (ω : Sample h) (v : Vertex h) :
    Relation.ReflTransGen (hardGraph h ω).Adjacent
      (vertexCode h v) (vertexCode h (.inl (topBlock h))) := by
  have helement (i : Element h) :
      Relation.ReflTransGen (hardGraph h ω).Adjacent
        (vertexCode h (.inr i)) (vertexCode h (.inl (topBlock h))) := by
    apply Relation.ReflTransGen.single
    exact (hardGraph h ω).adjacent_symmetric
      (hardGraph_adjacent_member ω (topBlock h) i (contains_topBlock i))
  cases v with
  | inr i => exact helement i
  | inl B =>
    obtain ⟨i, hi⟩ := members_nonempty B
    have hBi := hardGraph_adjacent_member ω B i ((mem_members B i).mp hi)
    exact (Relation.ReflTransGen.single hBi).trans (helement i)

theorem hardGraph_connected (h : ℕ) (ω : Sample h) :
    (hardGraph h ω).Connected := by
  intro u v
  obtain ⟨u', rfl⟩ := (vertexCode h).surjective u
  obtain ⟨v', rfl⟩ := (vertexCode h).surjective v
  exact (hardGraph_reaches_top ω u').trans
    (Relation.ReflTransGen.symmetric (hardGraph h ω).adjacent_symmetric
      (hardGraph_reaches_top ω v'))

#print axioms contains_topBlock
#print axioms hardGraph_adjacent_member
#print axioms hardGraph_reaches_top
#print axioms hardGraph_connected

end Hard
end Model3MaxSAT
