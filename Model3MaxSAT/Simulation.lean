import Model3MaxSAT.Reduction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Full-incidence online simulation of the two-clause reduction

The graph item contains every original named incident edge, including edges
to future vertices. The reduced SAT item is computed from this item alone.
No satisfied edge or clause is removed. The two slot names are fixed before
any colors or private random choices are sampled.
-/

noncomputable section

open MeasureTheory

namespace Model3MaxSAT

structure CCInput (n m : ℕ) where
  graph : CCGraph n m
  order : Equiv.Perm (Fin n)

structure CCEdgeData (n : ℕ) where
  left : Fin n
  right : Fin n
  weight : ℝ
  color : EdgeColor

structure CCObservation (n m : ℕ) where
  current : Fin n
  incident : Fin m → Option (CCEdgeData n)

def CCInput.item {n m : ℕ} (I : CCInput n m) (t : Fin n) : CCObservation n m where
  current := I.order t
  incident := fun e =>
    if I.order t = I.graph.left e ∨ I.order t = I.graph.right e then
      some ⟨I.graph.left e, I.graph.right e, I.graph.weight e, I.graph.color e⟩
    else none

def CCInput.SamePrefix {n m : ℕ} (I J : CCInput n m) (t : Fin n) : Prop :=
  ∀ s : Fin n, s ≤ t → I.item s = J.item s

structure CCDeterministicStrategy (n m : ℕ) where
  decision : CCInput n m → Fin n → Bool
  causal : ∀ (I J : CCInput n m) (t : Fin n),
    I.SamePrefix J t → decision I t = decision J t

def CCDeterministicStrategy.assignment {n m : ℕ}
    (A : CCDeterministicStrategy n m) (I : CCInput n m) : Assignment n :=
  fun v => A.decision I (I.order.symm v)

def CCInput.toSAT {n m : ℕ} (I : CCInput n m) : Input n (m * 2) where
  formula := I.graph.toFormula
  order := I.order

/-- Each edge slot determines a full clause using only this edge's data. -/
def CCEdgeData.clauseData {n : ℕ} (D : CCEdgeData n) (s : Fin 2) : ClauseData n where
  literal := fun v => if v = D.left then some (leftSign s)
    else if v = D.right then some (rightSign D.color s) else none
  weight := D.weight

/-- The simulator expands every named incident edge into its two named
clauses. Edge-slot names are independent of colors and assignments. -/
def CCObservation.toSAT {n m : ℕ} (O : CCObservation n m) : Observation n (m * 2) where
  current := O.current
  incident := fun j =>
    (O.incident (finProdFinEquiv.symm j).1).map fun D =>
      D.clauseData (finProdFinEquiv.symm j).2

/-- Equality of the entire original incidence item, not merely the already
revealed subgraph. The map includes both literal signs at future neighbors. -/
theorem CCInput.toSAT_item {n m : ℕ} (I : CCInput n m) (t : Fin n) :
    I.toSAT.item t = (I.item t).toSAT := by
  apply congrArg (fun f => Observation.mk (I.order t) f)
  funext j
  simp only [CCInput.toSAT, CCGraph.toFormula, CCGraph.pairClause,
    CCInput.item, edgeClause_isSome]
  simp [CCEdgeData.clauseData, edgeClause]

theorem CCInput.toSAT_samePrefix {n m : ℕ} (I J : CCInput n m) (t : Fin n)
    (h : I.SamePrefix J t) : I.toSAT.SamePrefix J.toSAT t := by
  intro s hs
  rw [I.toSAT_item s, J.toSAT_item s, h s hs]

/-- Every causal Model 3 MAXSAT algorithm induces a causal full-incidence
MaxCC algorithm. This is the information-preservation part of Lemma 4. -/
def DeterministicStrategy.simulate {n m : ℕ}
    (A : DeterministicStrategy n (m * 2)) : CCDeterministicStrategy n m where
  decision := fun I t => A.decision I.toSAT t
  causal := by
    intro I J t h
    exact A.causal I.toSAT J.toSAT t (I.toSAT_samePrefix J t h)

theorem DeterministicStrategy.simulate_assignment {n m : ℕ}
    (A : DeterministicStrategy n (m * 2)) (I : CCInput n m) :
    A.simulate.assignment I = A.assignment I.toSAT := rfl

structure CCRandomizedStrategy (Ξ : Type*) [MeasurableSpace Ξ] (n m : ℕ) where
  law : Measure Ξ
  probability : IsProbabilityMeasure law
  policy : Ξ → CCDeterministicStrategy n m
  measurable_payoff : ∀ I : CCInput n m,
    Measurable (fun ξ => I.graph.payoff ((policy ξ).assignment I))

def CCRandomizedStrategy.expectedPayoff {Ξ : Type*} [MeasurableSpace Ξ]
    {n m : ℕ} (A : CCRandomizedStrategy Ξ n m) (I : CCInput n m) : ℝ :=
  ∫ ξ, I.graph.payoff ((A.policy ξ).assignment I) ∂A.law

theorem CCRandomizedStrategy.integrable_payoff
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : CCRandomizedStrategy Ξ n m) (I : CCInput n m) :
    Integrable (fun ξ => I.graph.payoff ((A.policy ξ).assignment I)) A.law := by
  letI : IsProbabilityMeasure A.law := A.probability
  apply (integrable_const I.graph.totalWeight).mono'
    (A.measurable_payoff I).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (I.graph.payoff_nonneg _)]
  exact I.graph.payoff_le_totalWeight _

theorem DeterministicStrategy.simulate_payoff {n m : ℕ}
    (A : DeterministicStrategy n (m * 2)) (I : CCInput n m) :
    I.toSAT.formula.payoff (A.assignment I.toSAT) =
      I.graph.totalWeight + I.graph.payoff (A.simulate.assignment I) := by
  exact I.graph.toFormula_payoff (A.assignment I.toSAT)

/-- The simulator uses exactly the original private law and private tape.
Its measurability follows from the affine pointwise payoff identity. -/
def RandomizedStrategy.simulate {Ξ : Type*} [MeasurableSpace Ξ]
    {n m : ℕ} (A : RandomizedStrategy Ξ n (m * 2)) :
    CCRandomizedStrategy Ξ n m where
  law := A.law
  probability := A.probability
  policy := fun ξ => (A.policy ξ).simulate
  measurable_payoff := by
    intro I
    have hfun : (fun ξ => I.graph.payoff ((A.policy ξ).simulate.assignment I)) =
        (fun ξ => I.toSAT.formula.payoff ((A.policy ξ).assignment I.toSAT) -
          I.graph.totalWeight) := by
      funext ξ
      rw [(A.policy ξ).simulate_payoff I]
      simp
    rw [hfun]
    exact (A.measurable_payoff I.toSAT).sub measurable_const

theorem RandomizedStrategy.simulate_assignment
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n (m * 2)) (I : CCInput n m) (ξ : Ξ) :
    (A.simulate.policy ξ).assignment I = (A.policy ξ).assignment I.toSAT := rfl

theorem RandomizedStrategy.simulate_law
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n (m * 2)) : A.simulate.law = A.law := rfl

/-- The affine payoff relation survives expectation over arbitrary private
randomness; this is not limited to finite tapes. -/
theorem RandomizedStrategy.simulate_expectedPayoff
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n (m * 2)) (I : CCInput n m) :
    A.expectedPayoff I.toSAT = I.graph.totalWeight + A.simulate.expectedPayoff I := by
  letI : IsProbabilityMeasure A.law := A.probability
  change (∫ ξ, I.toSAT.formula.payoff ((A.policy ξ).assignment I.toSAT) ∂A.law) = _
  calc
    _ = ∫ ξ, (I.graph.totalWeight +
        I.graph.payoff ((A.policy ξ).simulate.assignment I)) ∂A.law := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => (A.policy ξ).simulate_payoff I
    _ = I.graph.totalWeight + A.simulate.expectedPayoff I := by
      have hcc : Integrable
          (fun ξ => I.graph.payoff ((A.policy ξ).simulate.assignment I)) A.law :=
        A.simulate.integrable_payoff I
      rw [integral_add (integrable_const I.graph.totalWeight) hcc]
      simp [CCRandomizedStrategy.expectedPayoff, RandomizedStrategy.simulate]

/-- On the perfectly satisfiable family the reduction transforms ratios
by `r ↦ 1/2 + r/2`, exactly as in equation (5) of the manuscript. -/
theorem RandomizedStrategy.simulate_ratio
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n (m * 2)) (I : CCInput n m)
    (hsat : I.graph.Satisfiable) (hpos : 0 < I.graph.totalWeight) :
    A.expectedPayoff I.toSAT / I.toSAT.formula.optimum =
      (1 : ℝ) / 2 + (1 / 2) *
        (A.simulate.expectedPayoff I / I.graph.optimum) := by
  change A.expectedPayoff I.toSAT / I.graph.toFormula.optimum = _
  rw [A.simulate_expectedPayoff I, I.graph.toFormula_optimum,
    I.graph.optimum_eq_totalWeight_of_satisfiable hsat]
  have hn : I.graph.totalWeight ≠ 0 := ne_of_gt hpos
  have hn2 : I.graph.totalWeight + I.graph.totalWeight ≠ 0 := by linarith
  field_simp
  ring

/-- Transfer an upper payoff estimate from the simulated MaxCC algorithm.
The hypothesis is an arbitrary explicit estimate, not an assumed hard bound. -/
theorem RandomizedStrategy.payoff_le_of_simulated_bound
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n (m * 2)) (I : CCInput n m)
    (hsat : I.graph.Satisfiable) (r : ℝ)
    (h : A.simulate.expectedPayoff I ≤ r * I.graph.optimum) :
    A.expectedPayoff I.toSAT ≤ ((1 : ℝ) / 2 + r / 2) * I.toSAT.formula.optimum := by
  change A.expectedPayoff I.toSAT ≤ _ * I.graph.toFormula.optimum
  rw [A.simulate_expectedPayoff I, I.graph.toFormula_optimum,
    I.graph.optimum_eq_totalWeight_of_satisfiable hsat]
  rw [I.graph.optimum_eq_totalWeight_of_satisfiable hsat] at h
  nlinarith

/-- A proposed SAT guarantee, including its fixed additive loss, transfers
to the same fixed graph and the same private law. -/
theorem RandomizedStrategy.simulated_guarantee_of_guarantee
    {Ξ : Type*} [MeasurableSpace Ξ] {n m : ℕ}
    (A : RandomizedStrategy Ξ n (m * 2)) (I : CCInput n m)
    (hsat : I.graph.Satisfiable) (r C : ℝ)
    (h : r * I.toSAT.formula.optimum - C ≤ A.expectedPayoff I.toSAT) :
    (2 * r - 1) * I.graph.optimum - C ≤ A.simulate.expectedPayoff I := by
  change r * I.graph.toFormula.optimum - C ≤ A.expectedPayoff I.toSAT at h
  rw [I.graph.toFormula_optimum, A.simulate_expectedPayoff I,
    I.graph.optimum_eq_totalWeight_of_satisfiable hsat] at h
  rw [I.graph.optimum_eq_totalWeight_of_satisfiable hsat]
  nlinarith

#print axioms CCInput.toSAT_item
#print axioms CCInput.toSAT_samePrefix
#print axioms DeterministicStrategy.simulate_assignment
#print axioms CCRandomizedStrategy.integrable_payoff
#print axioms DeterministicStrategy.simulate_payoff
#print axioms RandomizedStrategy.simulate_assignment
#print axioms RandomizedStrategy.simulate_law
#print axioms RandomizedStrategy.simulate_expectedPayoff
#print axioms RandomizedStrategy.simulate_ratio
#print axioms RandomizedStrategy.payoff_le_of_simulated_bound
#print axioms RandomizedStrategy.simulated_guarantee_of_guarantee

end Model3MaxSAT
