import Model3MaxSAT.Gadget
import Model3MaxSAT.Payoff

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT

/-- A finite weighted loopless colored graph with stable edge names.
Parallel endpoint pairs are allowed by this representation. The later
`Simple` predicate rules them out when proving the manuscript's restrictions. -/
structure CCGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  endpoints_ne : ∀ e, left e ≠ right e
  color : Fin m → EdgeColor
  weight : Fin m → ℝ
  weight_nonneg : ∀ e, 0 ≤ weight e

namespace CCGraph

def totalWeight {n m : ℕ} (G : CCGraph n m) : ℝ := ∑ e, G.weight e

def payoff {n m : ℕ} (G : CCGraph n m) (b : Assignment n) : ℝ :=
  ∑ e, G.weight e * (bval (edgeSatisfied (G.color e) (b (G.left e)) (b (G.right e))) : ℝ)

def optimum {n m : ℕ} (G : CCGraph n m) : ℝ := ⨆ b : Assignment n, G.payoff b

def Satisfiable {n m : ℕ} (G : CCGraph n m) : Prop :=
  ∃ b : Assignment n, ∀ e, edgeSatisfied (G.color e) (b (G.left e)) (b (G.right e)) = true

def Unweighted {n m : ℕ} (G : CCGraph n m) : Prop := ∀ e, G.weight e = 1

def Simple {n m : ℕ} (G : CCGraph n m) : Prop :=
  Function.Injective (fun e => ({G.left e, G.right e} : Finset (Fin n)))

theorem totalWeight_nonneg {n m : ℕ} (G : CCGraph n m) : 0 ≤ G.totalWeight :=
  Finset.sum_nonneg fun e _ => G.weight_nonneg e

theorem payoff_nonneg {n m : ℕ} (G : CCGraph n m) (b : Assignment n) :
    0 ≤ G.payoff b := by
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (G.weight_nonneg e) (Nat.cast_nonneg _)

theorem payoff_le_totalWeight {n m : ℕ} (G : CCGraph n m) (b : Assignment n) :
    G.payoff b ≤ G.totalWeight := by
  apply Finset.sum_le_sum
  intro e _
  cases h : edgeSatisfied (G.color e) (b (G.left e)) (b (G.right e)) <;>
    simp [bval, G.weight_nonneg e]

theorem payoff_le_optimum {n m : ℕ} (G : CCGraph n m) (b : Assignment n) :
    G.payoff b ≤ G.optimum := by
  apply le_ciSup
  refine ⟨G.totalWeight, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact G.payoff_le_totalWeight a

theorem optimum_le_totalWeight {n m : ℕ} (G : CCGraph n m) :
    G.optimum ≤ G.totalWeight :=
  ciSup_le fun b => G.payoff_le_totalWeight b

theorem payoff_eq_totalWeight_of_satisfies {n m : ℕ} (G : CCGraph n m)
    (b : Assignment n)
    (h : ∀ e, edgeSatisfied (G.color e) (b (G.left e)) (b (G.right e)) = true) :
    G.payoff b = G.totalWeight := by
  apply Finset.sum_congr rfl
  intro e _
  simp [h e, bval]

theorem optimum_eq_totalWeight_of_satisfiable {n m : ℕ}
    (G : CCGraph n m) (h : G.Satisfiable) : G.optimum = G.totalWeight := by
  obtain ⟨b,hb⟩ := h
  apply le_antisymm G.optimum_le_totalWeight
  rw [← G.payoff_eq_totalWeight_of_satisfies b hb]
  exact G.payoff_le_optimum b

end CCGraph
end Model3MaxSAT
