import Model3MaxSAT.HardInput
import Model3MaxSAT.HardEnergy

noncomputable section
open scoped BigOperators

namespace Model3MaxSAT.Hard

open FiniteProbability

/-- The analyzed finite edge sum is exactly the payoff of the actual
full-incidence algorithm on the actual named hard input. -/
theorem hardGraph_payoff_eq_hardPayoff {h : ℕ}
    (A : CCDeterministicStrategy (vertexCount h) (edgeCount h)) (ω : Sample h) :
    (hardGraph h ω).payoff (A.assignment (hardInput h ω)) =
      hardPayoff A.toBlockPolicy (elementDecision A) ω := by
  unfold CCGraph.payoff hardPayoff
  rw [← (edgeCode h).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  simp only [hardGraph, Equiv.symm_apply_apply, one_mul]
  rfl

/-- Proposition 10 for an arbitrary actual causal MaxCC strategy. All
switching, moment and energy bounds have been discharged in its dependencies. -/
theorem hardGraph_expected_le {h : ℕ}
    (A : CCDeterministicStrategy (vertexCount h) (edgeCount h)) :
    uniformMean h (fun ω => (hardGraph h ω).payoff (A.assignment (hardInput h ω))) ≤
      (((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
        (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2 := by
  calc
    _ = uniformMean h (hardPayoff A.toBlockPolicy (elementDecision A)) :=
      mean_congr (hardGraph_payoff_eq_hardPayoff A)
    _ ≤ _ := hardPayoff_expected_le A.toBlockPolicy (elementDecision A)

/-- The deterministic hard-distribution MAXSAT payoff estimate, now for
the actual syntactic formulas and full Model 3 strategies. -/
theorem hardSAT_deterministic_mean_le {h : ℕ}
    (A : DeterministicStrategy (vertexCount h) (edgeCount h * 2)) :
    uniformMean h (fun ω => (hardSAT h ω).formula.payoff (A.assignment (hardSAT h ω))) ≤
      (3 * ((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
        (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2 := by
  have hcc := hardGraph_expected_le A.simulate
  change mean _ ≤ _
  calc
    _ = mean (fun ω => (edgeCount h : ℝ) +
        (hardGraph h ω).payoff (A.simulate.assignment (hardInput h ω))) := by
      apply mean_congr
      intro ω
      change (hardInput h ω).toSAT.formula.payoff
        (A.assignment (hardInput h ω).toSAT) = _
      rw [A.simulate_payoff (hardInput h ω)]
      exact congrArg (fun w => w + _) (hardGraph_totalWeight h ω)
    _ = (edgeCount h : ℝ) + mean (fun ω =>
        (hardGraph h ω).payoff (A.simulate.assignment (hardInput h ω))) := by
      rw [mean_add, mean_const]
    _ ≤ (edgeCount h : ℝ) +
      (((h + 1 : ℕ) : ℝ) * (4 ^ h : ℝ) +
        (4 ^ h : ℝ) * Real.sqrt (3 * ((h + 1 : ℕ) : ℝ))) / 2 :=
      add_le_add_left hcc _
    _ = _ := by
      simp only [edgeCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

#print axioms hardGraph_payoff_eq_hardPayoff
#print axioms hardGraph_expected_le
#print axioms hardSAT_deterministic_mean_le

end Model3MaxSAT.Hard
