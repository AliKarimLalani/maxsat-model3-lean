import Model3MaxSAT.CCModel
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT

def leftSign (s : Fin 2) : Bool := s == 0

def rightSign (c : EdgeColor) (s : Fin 2) : Bool :=
  match c with
  | .blue => !(leftSign s)
  | .red => leftSign s

/-- A syntactic clause of the two-clause encoding, independent of all
other edges and their colors. Slot 0 is the first clause, slot 1 the second. -/
def edgeClause {n : ℕ} (u v : Fin n) (_hne : u ≠ v)
    (c : EdgeColor) (s : Fin 2) : Clause n where
  literal := fun z => if z = u then some (leftSign s)
    else if z = v then some (rightSign c s) else none
  nonempty := ⟨u, by simp⟩

namespace CCGraph

def pairClause {n m : ℕ} (G : CCGraph n m) (e : Fin m) (s : Fin 2) : Clause n :=
  edgeClause (G.left e) (G.right e) (G.endpoints_ne e) (G.color e) s

/-- Edge-slot enumeration is independent of all colors and weights. -/
def toFormula {n m : ℕ} (G : CCGraph n m) : Formula n (m * 2) where
  clause := fun j => G.pairClause (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  weight := fun j => G.weight (finProdFinEquiv.symm j).1
  weight_nonneg := fun _ => G.weight_nonneg _

end CCGraph

@[simp] theorem edgeClause_isSome {n : ℕ} (u v : Fin n) (hne : u ≠ v)
    (c : EdgeColor) (s : Fin 2) (z : Fin n) :
    ((edgeClause u v hne c s).literal z).isSome = true ↔ z = u ∨ z = v := by
  by_cases hu : z = u <;> by_cases hv : z = v <;>
    simp [edgeClause, hu, hv, Ne.symm hne]

@[simp] theorem edgeClause_satisfied {n : ℕ} (u v : Fin n) (hne : u ≠ v)
    (c : EdgeColor) (s : Fin 2) (b : Assignment n) :
    (edgeClause u v hne c s).Satisfied b ↔ b u = leftSign s ∨ b v = rightSign c s := by
  constructor
  · rintro ⟨z,hz⟩
    by_cases hu : z = u
    · subst z
      left
      simpa [edgeClause] using hz.symm
    · by_cases hv : z = v
      · subst z
        right
        simpa [edgeClause, Ne.symm hne] using hz.symm
      · simp [edgeClause, hu, hv] at hz
  · rintro (hu | hv)
    · exact ⟨u, by simp [edgeClause, hu]⟩
    · exact ⟨v, by simp [edgeClause, Ne.symm hne, hv]⟩

theorem edgeClause_variables {n : ℕ} (u v : Fin n) (hne : u ≠ v)
    (c : EdgeColor) (s : Fin 2) :
    (edgeClause u v hne c s).variables = {u,v} := by
  ext z
  simp [Clause.variables]

theorem edgeClause_exactTwo {n : ℕ} (u v : Fin n) (hne : u ≠ v)
    (c : EdgeColor) (s : Fin 2) :
    (edgeClause u v hne c s).variables.card = 2 := by
  rw [edgeClause_variables]
  simp [hne]

theorem edgeClause_first_eval {n : ℕ} (u v : Fin n) (hne : u ≠ v)
    (c : EdgeColor) (b : Assignment n) :
    (edgeClause u v hne c 0).Satisfied b ↔ firstClause c (b u) (b v) = true := by
  rw [edgeClause_satisfied]
  cases c <;> cases b u <;> cases b v <;> decide

theorem edgeClause_second_eval {n : ℕ} (u v : Fin n) (hne : u ≠ v)
    (c : EdgeColor) (b : Assignment n) :
    (edgeClause u v hne c 1).Satisfied b ↔ secondClause c (b u) (b v) = true := by
  rw [edgeClause_satisfied]
  cases c <;> cases b u <;> cases b v <;> decide

theorem leftSign_injective : Function.Injective leftSign := by
  intro s t h
  fin_cases s <;> fin_cases t <;> simp_all [leftSign]

namespace CCGraph

theorem toFormula_exactTwo {n m : ℕ} (G : CCGraph n m) : G.toFormula.ExactTwo := by
  intro j
  exact edgeClause_exactTwo _ _ (G.endpoints_ne _) _ _

theorem toFormula_unweighted {n m : ℕ} (G : CCGraph n m) (h : G.Unweighted) :
    G.toFormula.Unweighted := by
  intro j
  exact h _

theorem toFormula_payoff {n m : ℕ} (G : CCGraph n m) (b : Assignment n) :
    G.toFormula.payoff b = G.totalWeight + G.payoff b := by
  classical
  unfold Formula.payoff
  rw [← (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).sum_comp]
  simp only [toFormula, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp only [pairClause, edgeClause_first_eval, edgeClause_second_eval]
  have hbool (x : Bool) : (if x = true then (1 : ℝ) else 0) = (bval x : ℝ) := by
    cases x <;> simp [bval]
  simp only [hbool]
  exact sum_two_clauses_per_edge G.weight G.color (fun e => b (G.left e)) (fun e => b (G.right e))

theorem toFormula_totalWeight {n m : ℕ} (G : CCGraph n m) :
    G.toFormula.totalWeight = G.totalWeight + G.totalWeight := by
  unfold Formula.totalWeight
  rw [← (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).sum_comp]
  simp only [toFormula, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  exact Finset.sum_add_distrib

/-- Equality of the actual finite optima, not just an assignment-level
identity. This holds for arbitrary nonnegative edge weights. -/
theorem toFormula_optimum {n m : ℕ} (G : CCGraph n m) :
    G.toFormula.optimum = G.totalWeight + G.optimum := by
  apply le_antisymm
  · apply ciSup_le
    intro b
    rw [G.toFormula_payoff]
    exact add_le_add_left (G.payoff_le_optimum b) _
  · have h : G.optimum ≤ G.toFormula.optimum - G.totalWeight := by
      apply ciSup_le
      intro b
      apply (le_sub_iff_add_le').mpr
      rw [← G.toFormula_payoff]
      exact G.toFormula.payoff_le_optimum b
    exact (le_sub_iff_add_le').mp h

theorem toFormula_satisfiable {n m : ℕ} (G : CCGraph n m) (h : G.Satisfiable) :
    G.toFormula.Satisfiable := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b, fun j => ?_⟩
  change (G.pairClause (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).Satisfied b
  generalize he : (finProdFinEquiv.symm j).1 = e
  generalize hs : (finProdFinEquiv.symm j).2 = s
  have hg := (both_clauses_iff_edge (G.color e) (b (G.left e)) (b (G.right e))).mpr (hb e)
  fin_cases s
  · exact (edgeClause_first_eval _ _ _ _ _).mpr hg.1
  · exact (edgeClause_second_eval _ _ _ _ _).mpr hg.2

theorem toFormula_noRepeatedClauses {n m : ℕ} (G : CCGraph n m) (hG : G.Simple) :
    G.toFormula.NoRepeatedClauses := by
  intro j k hjk
  let es : Fin m × Fin 2 := finProdFinEquiv.symm j
  let ft : Fin m × Fin 2 := finProdFinEquiv.symm k
  change (G.pairClause es.1 es.2).literal = (G.pairClause ft.1 ft.2).literal at hjk
  have hv : (G.pairClause es.1 es.2).variables = (G.pairClause ft.1 ft.2).variables := by
    unfold Clause.variables
    rw [hjk]
  have he : es.1 = ft.1 := hG (by
    simpa only [pairClause, edgeClause_variables] using hv)
  have hs : leftSign es.2 = leftSign ft.2 := by
    have hh := congrFun hjk (G.left es.1)
    simpa [pairClause, edgeClause, he] using hh
  apply (finProdFinEquiv.symm : Fin (m * 2) ≃ Fin m × Fin 2).injective
  exact Prod.ext he (leftSign_injective hs)

theorem toFormula_optimum_of_satisfiable {n m : ℕ} (G : CCGraph n m)
    (hG : G.Satisfiable) : G.toFormula.optimum = G.totalWeight + G.totalWeight := by
  rw [G.toFormula_optimum, G.optimum_eq_totalWeight_of_satisfiable hG]

/-- A satisfiable loopless graph gives exactly the promised kind of formula.
The simplicity hypothesis is used only for the no-repeated-clause property. -/
theorem toFormula_restrictions {n m : ℕ} (G : CCGraph n m)
    (hu : G.Unweighted) (hs : G.Simple) (hp : G.Satisfiable) :
    G.toFormula.Unweighted ∧ G.toFormula.ExactTwo ∧
      G.toFormula.NoRepeatedClauses ∧ G.toFormula.Satisfiable :=
  ⟨G.toFormula_unweighted hu, G.toFormula_exactTwo,
    G.toFormula_noRepeatedClauses hs, G.toFormula_satisfiable hp⟩

#print axioms toFormula_payoff
#print axioms toFormula_optimum
#print axioms toFormula_exactTwo
#print axioms toFormula_noRepeatedClauses
#print axioms toFormula_satisfiable
#print axioms toFormula_optimum_of_satisfiable
#print axioms toFormula_restrictions

end CCGraph
end Model3MaxSAT
