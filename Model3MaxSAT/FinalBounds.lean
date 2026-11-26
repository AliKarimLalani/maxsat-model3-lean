import Model3MaxSAT.Energy

namespace Model3MaxSAT

/-- The affine reduction turns the MaxCC numerator into exactly the
manuscript's quantitative MAXSAT ratio. -/
theorem sat_bound_normalization (L N : ℝ) (hL : 0 < L) :
    (3 * L * N + N * Real.sqrt (3 * L)) / 2 =
      ((3 : ℝ) / 4 + Real.sqrt 3 / (4 * Real.sqrt L)) * (2 * L * N) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hs : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  field_simp
  nlinarith [congrArg (fun x : ℝ => N * Real.sqrt 3 * x) hsq]

#print axioms sat_bound_normalization

end Model3MaxSAT
