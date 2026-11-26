import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fintype.Perm

/-!
# MAXSAT inputs and causal randomized strategies

The upper bound is proved in `Main.lean` using these definitions. Variable and clause
names are finite labels. In particular, the total numbers of variables and
clauses are available as parameters to a strategy. Giving these counts in
advance is harmless for the planned hard family, where both are fixed.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Model3MaxSAT

abbrev Assignment (n : ℕ) := Fin n → Bool

/-- `some true` is a positive occurrence, `some false` a negative one,
and `none` means that the variable does not occur. -/
structure Clause (n : ℕ) where
  literal : Fin n → Option Bool
  nonempty : ∃ v, (literal v).isSome = true

def Clause.Satisfied {n : ℕ} (C : Clause n) (b : Assignment n) : Prop :=
  ∃ v, C.literal v = some (b v)

def Clause.variables {n : ℕ} (C : Clause n) : Finset (Fin n) :=
  Finset.univ.filter fun v => (C.literal v).isSome

/-- The index in `Fin m` is the stable name of a clause. Equal clause
contents can have different names and are then counted separately. -/
structure Formula (n m : ℕ) where
  clause : Fin m → Clause n
  weight : Fin m → ℝ
  weight_nonneg : ∀ c, 0 ≤ weight c

def Formula.payoff {n m : ℕ} (F : Formula n m) (b : Assignment n) : ℝ := by
  classical
  exact ∑ c, F.weight c * (if (F.clause c).Satisfied b then 1 else 0)

def Formula.totalWeight {n m : ℕ} (F : Formula n m) : ℝ :=
  ∑ c, F.weight c

/-- This is a supremum over a finite nonempty assignment type.
Attainment is a future lemma. Elementary bounds and the satisfiable case
are proved in `Payoff.lean`. -/
def Formula.optimum {n m : ℕ} (F : Formula n m) : ℝ :=
  ⨆ b : Assignment n, F.payoff b

def Formula.Satisfiable {n m : ℕ} (F : Formula n m) : Prop :=
  ∃ b : Assignment n, ∀ c, (F.clause c).Satisfied b

def Formula.Unweighted {n m : ℕ} (F : Formula n m) : Prop :=
  ∀ c, F.weight c = 1

def Formula.ExactTwo {n m : ℕ} (F : Formula n m) : Prop :=
  ∀ c, (F.clause c).variables.card = 2

def Formula.NoRepeatedClauses {n m : ℕ} (F : Formula n m) : Prop :=
  Function.Injective (fun c => (F.clause c).literal)

structure Input (n m : ℕ) where
  formula : Formula n m
  order : Equiv.Perm (Fin n)

/-- A full original clause with its weight. Its name is the index of its
entry in `Observation.incident`, not part of the contents. -/
structure ClauseData (n : ℕ) where
  literal : Fin n → Option Bool
  weight : ℝ

structure Observation (n m : ℕ) where
  current : Fin n
  incident : Fin m → Option (ClauseData n)

/-- This item depends only on the fixed input and time. Satisfied clauses
are still disclosed, with the same names, contents, and weights. -/
def Input.item {n m : ℕ} (I : Input n m) (t : Fin n) : Observation n m where
  current := I.order t
  incident := fun c =>
    if ((I.formula.clause c).literal (I.order t)).isSome then
      some ⟨(I.formula.clause c).literal, I.formula.weight c⟩
    else none

def Input.SamePrefix {n m : ℕ} (I J : Input n m) (t : Fin n) : Prop :=
  ∀ s : Fin n, s ≤ t → I.item s = J.item s

/-- An extensional deterministic online algorithm. `decision I t` is the
irrevocable decision at time t. The causality field is the information
restriction: identical observed prefixes must produce identical decisions.
There is no locality, memory, or computational efficiency restriction. -/
structure DeterministicStrategy (n m : ℕ) where
  decision : Input n m → Fin n → Bool
  causal : ∀ (I J : Input n m) (t : Fin n),
    I.SamePrefix J t → decision I t = decision J t

def DeterministicStrategy.assignment {n m : ℕ}
    (A : DeterministicStrategy n m) (I : Input n m) : Assignment n :=
  fun v => A.decision I (I.order.symm v)

theorem decision_eq_of_same_prefix {n m : ℕ}
    (A : DeterministicStrategy n m) (I J : Input n m) (t : Fin n)
    (h : I.SamePrefix J t) : A.decision I t = A.decision J t :=
  A.causal I J t h

/-- An example showing that the deterministic interface is inhabited. -/
def constantStrategy (n m : ℕ) (b : Bool) : DeterministicStrategy n m where
  decision := fun _ _ => b
  causal := by intros; rfl

/-- Private randomness may live on an arbitrary probability space, including
an infinite tape. The law is independent of the input. Fixing a tape gives
a causal deterministic strategy. Measurability is imposed on real payoffs,
which is exactly what the later expectation argument needs. -/
structure RandomizedStrategy (Ξ : Type*) [MeasurableSpace Ξ] (n m : ℕ) where
  law : Measure Ξ
  probability : IsProbabilityMeasure law
  policy : Ξ → DeterministicStrategy n m
  measurable_payoff : ∀ I : Input n m,
    Measurable (fun ξ => I.formula.payoff ((policy ξ).assignment I))

def RandomizedStrategy.expectedPayoff {Ξ : Type*} [MeasurableSpace Ξ]
    {n m : ℕ} (A : RandomizedStrategy Ξ n m) (I : Input n m) : ℝ :=
  ∫ ξ, I.formula.payoff ((A.policy ξ).assignment I) ∂A.law

/-- A strategy for each finite input size. A common tape space is allowed
to be arbitrary, so this does not restrict randomness to finite coins. -/
abbrev RandomizedAlgorithm (Ξ : Type*) [MeasurableSpace Ξ] :=
  (n m : ℕ) → RandomizedStrategy Ξ n m

/-- The pure multiplicative guarantee used in the manuscript. -/
def HasGuarantee {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) (r : ℝ) : Prop :=
  ∀ (n m : ℕ) (I : Input n m), 0 < I.formula.optimum →
    r * I.formula.optimum ≤ (A n m).expectedPayoff I

/-- The same guarantee with an input-independent additive loss. -/
def HasAdditiveGuarantee {Ξ : Type*} [MeasurableSpace Ξ]
    (A : RandomizedAlgorithm Ξ) (r C : ℝ) : Prop :=
  ∀ (n m : ℕ) (I : Input n m), 0 < I.formula.optimum →
    r * I.formula.optimum - C ≤ (A n m).expectedPayoff I

#print axioms decision_eq_of_same_prefix

end Model3MaxSAT
