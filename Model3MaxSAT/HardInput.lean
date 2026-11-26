import Model3MaxSAT.Simulation
import Model3MaxSAT.HardOrder
import Model3MaxSAT.Switching
import Model3MaxSAT.Targets

/-!
# The actual finite hard inputs and their full-observation policy bridge

Vertex names use the fixed level-first enumeration. Edge names use the
fixed level/element enumeration. Neither depends on hidden labels or colors.
Thus the identity arrival permutation presents all blocks level by level,
followed by all elements, and the only sampled input data are edge colors.
-/

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT.Hard

abbrev edgeCount (h : ℕ) := (h + 1) * 4 ^ h

def edgeCode (h : ℕ) : Edge h ≃ Fin (edgeCount h) :=
  (edgeEquiv h).trans finProdFinEquiv

def hardGraph (h : ℕ) (ω : Sample h) : CCGraph (vertexCount h) (edgeCount h) where
  left := fun e => vertexCode h (.inl ((edgeCode h).symm e).val.1)
  right := fun e => vertexCode h (.inr ((edgeCode h).symm e).val.2)
  endpoints_ne := by
    intro e heq
    exact Sum.noConfusion ((vertexCode h).injective heq)
  color := fun e => color ω ((edgeCode h).symm e)
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one

def hardInput (h : ℕ) (ω : Sample h) : CCInput (vertexCount h) (edgeCount h) where
  graph := hardGraph h ω
  order := Equiv.refl _

theorem hardGraph_unweighted (h : ℕ) (ω : Sample h) : (hardGraph h ω).Unweighted :=
  fun _ => rfl

theorem hardGraph_totalWeight (h : ℕ) (ω : Sample h) :
    (hardGraph h ω).totalWeight = (edgeCount h : ℝ) := by
  simp [CCGraph.totalWeight, hardGraph]

theorem hardGraph_satisfiable (h : ℕ) (ω : Sample h) :
    (hardGraph h ω).Satisfiable := by
  refine ⟨fun v => ω ((vertexCode h).symm v), ?_⟩
  intro e
  simpa [hardGraph] using planted_edge_satisfied ω ((edgeCode h).symm e)

theorem hardGraph_optimum (h : ℕ) (ω : Sample h) :
    (hardGraph h ω).optimum = (edgeCount h : ℝ) := by
  rw [(hardGraph h ω).optimum_eq_totalWeight_of_satisfiable (hardGraph_satisfiable h ω),
    hardGraph_totalWeight]

theorem coded_pair_injective (h : ℕ) :
    Function.Injective (fun p : Block h × Element h =>
      ({vertexCode h (.inl p.1), vertexCode h (.inr p.2)} : Finset (Fin (vertexCount h)))) := by
  intro p q hpq
  dsimp only at hpq
  apply Prod.ext
  · have hm : vertexCode h (.inl p.1) ∈
        ({vertexCode h (.inl q.1), vertexCode h (.inr q.2)} : Finset (Fin (vertexCount h))) := by
      rw [← hpq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq
    · exact Sum.inl.inj ((vertexCode h).injective heq)
    · exact Sum.noConfusion ((vertexCode h).injective heq)
  · have hm : vertexCode h (.inr p.2) ∈
        ({vertexCode h (.inl q.1), vertexCode h (.inr q.2)} : Finset (Fin (vertexCount h))) := by
      rw [← hpq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq
    · exact Sum.noConfusion ((vertexCode h).injective heq)
    · exact Sum.inr.inj ((vertexCode h).injective heq)

theorem hardGraph_simple (h : ℕ) (ω : Sample h) : (hardGraph h ω).Simple := by
  intro e f hef
  apply (edgeCode h).symm.injective
  apply Subtype.ext
  exact coded_pair_injective h hef

/-- A concrete two-coloring of the uncolored graph's vertex classes. -/
theorem hardGraph_bipartite (h : ℕ) (ω : Sample h) :
    ∃ side : Fin (vertexCount h) → Bool,
      ∀ e, side ((hardGraph h ω).left e) ≠ side ((hardGraph h ω).right e) := by
  refine ⟨fun v => match (vertexCode h).symm v with
    | .inl _ => true
    | .inr _ => false, ?_⟩
  intro e
  simp [hardGraph]

def hardSAT (h : ℕ) (ω : Sample h) : Input (vertexCount h) (edgeCount h * 2) :=
  (hardInput h ω).toSAT

theorem hardSAT_restricted (h : ℕ) (ω : Sample h) : RestrictedInput (hardSAT h ω) := by
  refine ⟨(hardGraph h ω).toFormula_unweighted (hardGraph_unweighted h ω),
    (hardGraph h ω).toFormula_exactTwo,
    (hardGraph h ω).toFormula_noRepeatedClauses (hardGraph_simple h ω),
    (hardGraph h ω).toFormula_satisfiable (hardGraph_satisfiable h ω)⟩

theorem hardSAT_optimum (h : ℕ) (ω : Sample h) :
    (hardSAT h ω).formula.optimum = 2 * (edgeCount h : ℝ) := by
  change (hardGraph h ω).toFormula.optimum = _
  rw [(hardGraph h ω).toFormula_optimum, hardGraph_totalWeight, hardGraph_optimum]
  ring

theorem hardSAT_totalWeight (h : ℕ) (ω : Sample h) :
    (hardSAT h ω).formula.totalWeight = 2 * (edgeCount h : ℝ) := by
  change (hardGraph h ω).toFormula.totalWeight = _
  rw [(hardGraph h ω).toFormula_totalWeight, hardGraph_totalWeight]
  ring

/-- All named original graph-edge observations at a block agree whenever
the entire typed incidence row agrees. Endpoint names and weights are fixed.
The row includes colors at all named future element vertices. -/
theorem hardInput_item_block_eq {h : ℕ} (ω ω' : Sample h) (D : Block h)
    (hrow : blockItem ω D = blockItem ω' D) :
    (hardInput h ω).item (vertexCode h (.inl D)) =
      (hardInput h ω').item (vertexCode h (.inl D)) := by
  apply congrArg (fun f => CCObservation.mk (vertexCode h (.inl D)) f)
  funext q
  let e : Edge h := (edgeCode h).symm q
  have hright : vertexCode h (.inl D) ≠ vertexCode h (.inr e.val.2) := by
    intro hx
    exact Sum.noConfusion ((vertexCode h).injective hx)
  by_cases hD : D = e.val.1
  · have hi : Contains D e.val.2 := hD.symm ▸ e.property
    have hc := congrFun hrow e.val.2
    simp only [blockItem, if_pos hi, Option.some.injEq] at hc
    have hcolor : color ω e = color ω' e := by
      simpa only [color, labelColor, hD] using hc
    change (if vertexCode h (.inl D) = vertexCode h (.inl e.val.1) ∨
        vertexCode h (.inl D) = vertexCode h (.inr e.val.2) then _ else _) =
      (if vertexCode h (.inl D) = vertexCode h (.inl e.val.1) ∨
        vertexCode h (.inl D) = vertexCode h (.inr e.val.2) then _ else _)
    simp only [hD, true_or, ↓reduceIte]
    exact congrArg some (congrArg (CCEdgeData.mk _ _ 1) hcolor)
  · have hleft : vertexCode h (.inl D) ≠ vertexCode h (.inl e.val.1) := by
      intro hx
      exact hD (Sum.inl.inj ((vertexCode h).injective hx))
    change (if vertexCode h (.inl D) = vertexCode h (.inl e.val.1) ∨
        vertexCode h (.inl D) = vertexCode h (.inr e.val.2) then _ else _) =
      (if vertexCode h (.inl D) = vertexCode h (.inl e.val.1) ∨
        vertexCode h (.inl D) = vertexCode h (.inr e.val.2) then _ else _)
    rw [if_neg (not_or.mpr ⟨hleft, hright⟩), if_neg (not_or.mpr ⟨hleft, hright⟩)]

/-- Restriction of an arbitrary causal full-incidence strategy to the block
phase. Its causality follows from the actual full-input prefix, not from an
assumed invariance of its decisions. -/
def _root_.Model3MaxSAT.CCDeterministicStrategy.toBlockPolicy {h : ℕ}
    (A : Model3MaxSAT.CCDeterministicStrategy (vertexCount h) (edgeCount h)) : BlockPolicy h where
  decision := fun ω D => A.decision (hardInput h ω) (vertexCode h (.inl D))
  causal := by
    intro ω ω' D hprefix
    apply A.causal
    intro s hs
    obtain ⟨v, rfl⟩ := (vertexCode h).surjective s
    cases v with
    | inl E =>
      exact hardInput_item_block_eq ω ω' E (hprefix E ((code_blocks_le_iff E D).mp hs))
    | inr i =>
      exact False.elim ((code_element_not_le_block i D) hs)

theorem blockPolicy_decision_eq_assignment {h : ℕ}
    (A : Model3MaxSAT.CCDeterministicStrategy (vertexCount h) (edgeCount h))
    (ω : Sample h) (D : Block h) :
    A.toBlockPolicy.decision ω D =
      A.assignment (hardInput h ω) (vertexCode h (.inl D)) := rfl

def elementDecision {h : ℕ}
    (A : Model3MaxSAT.CCDeterministicStrategy (vertexCount h) (edgeCount h))
    (ω : Sample h) (i : Element h) : Bool :=
  A.assignment (hardInput h ω) (vertexCode h (.inr i))

#print axioms hardGraph_satisfiable
#print axioms hardGraph_simple
#print axioms hardGraph_optimum
#print axioms hardGraph_bipartite
#print axioms hardSAT_restricted
#print axioms hardSAT_optimum
#print axioms hardInput_item_block_eq
#print axioms Model3MaxSAT.CCDeterministicStrategy.toBlockPolicy
#print axioms blockPolicy_decision_eq_assignment

end Model3MaxSAT.Hard
