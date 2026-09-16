import Submission.ZagierHoffmanProof.CarlitzAT

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Carlitz module chapter

Concrete instantiations at `F = ZMod 2` and `F = ZMod 3` of the results of
`Submission.ZagierHoffmanProof.Carlitz`.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

section Two

/-- Over `F₂`, `D_1 = [1] = X ^ 2 - X`. -/
example : carlitzFact (ZMod 2) 1 = X ^ 2 - X := by
  rw [carlitzFact_succ, carlitzFact_zero, carlitzBracket]
  norm_num

/-- Over `F₂`, the degree of `D_k` is `k * 2 ^ k`. -/
example : (carlitzFact (ZMod 2) 5).natDegree = 5 * 2 ^ 5 := by
  rw [natDegree_carlitzFact]
  norm_num

/-- Over `F₂`, `L_1 = X - X ^ 2`. -/
example : carlitzL (ZMod 2) 1 = X - X ^ 2 := by
  rw [carlitzL_succ, carlitzL_zero, one_mul]
  norm_num

/-- Over `F₂` the Carlitz exponential has no constant term, and coefficient `1` at `z`. -/
example : (PowerSeries.coeff 0) (carlitzExp (ZMod 2)) = 0 := by
  rw [carlitzExp, PowerSeries.coeff_mk]
  exact carlitzECoeff_eq_zero (ZMod 2) (fun i hi => by
    have h2 : Nat.card (ZMod 2) = 2 := by simp
    have hpos : 0 < Nat.card (ZMod 2) ^ i := pow_pos (by omega) i
    omega)

example : (PowerSeries.coeff 1) (carlitzExp (ZMod 2)) = 1 := by
  rw [carlitzExp, PowerSeries.coeff_mk]
  rw [show (1 : ℕ) = Nat.card (ZMod 2) ^ 0 from by simp, carlitzECoeff_pow]
  rw [carlitzFact_zero,
    show (((1 : (ZMod 2)[X]) : RatFunc (ZMod 2))) = 1 from map_one _, inv_one]

/-- **The Carlitz functional equation over `F₂`.** -/
example : PowerSeries.rescale (carlitzTheta (ZMod 2)) (carlitzExp (ZMod 2))
    = PowerSeries.C (carlitzTheta (ZMod 2)) * carlitzExp (ZMod 2)
      + (carlitzExp (ZMod 2)) ^ 2 := by
  have := carlitzExp_functional (ZMod 2)
  simpa using this

end Two

section Three

/-- Over `F₃`, `D_1 = [1] = X ^ 3 - X`. -/
example : carlitzFact (ZMod 3) 1 = X ^ 3 - X := by
  rw [carlitzFact_succ, carlitzFact_zero, carlitzBracket]
  norm_num

/-- Over `F₃`, `L_2 = (X - X ^ 3) * (X - X ^ 9)`. -/
example : carlitzL (ZMod 3) 2 = (X - X ^ 3) * (X - X ^ 9) := by
  rw [carlitzL_succ, carlitzL_succ, carlitzL_zero, one_mul]
  norm_num

/-- Over `F₃`, `L_d = (-1) ^ d * ∏_{j<d} [j + 1]`. -/
example : carlitzL (ZMod 3) 2 = (-1) ^ 2 * (carlitzBracket (ZMod 3) 1 * carlitzBracket (ZMod 3) 2) := by
  rw [carlitzL_eq_neg_pow_mul]
  norm_num [Finset.prod_range_succ, Finset.prod_range_one]

/-- Over `F₃`, the third coefficient of the Carlitz exponential is `1 / D_1`. -/
example : (PowerSeries.coeff (Nat.card (ZMod 3) ^ 1)) (carlitzExp (ZMod 3))
    = (((carlitzFact (ZMod 3) 1 : (ZMod 3)[X]) : RatFunc (ZMod 3)))⁻¹ := by
  rw [carlitzExp, PowerSeries.coeff_mk, carlitzECoeff_pow]

/-- **The Carlitz functional equation over `F₃`.** -/
example : PowerSeries.rescale (carlitzTheta (ZMod 3)) (carlitzExp (ZMod 3))
    = PowerSeries.C (carlitzTheta (ZMod 3)) * carlitzExp (ZMod 3)
      + (carlitzExp (ZMod 3)) ^ 3 := by
  have := carlitzExp_functional (ZMod 3)
  simpa using this

end Three

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

section ActionRegression

attribute [local instance 100] Classical.decEq

/-- Over `F₂`, the `n = 1` case of the intertwining theorem is exactly the functional equation. -/
example : carlitzAction (ZMod 2) 1 (carlitzExp (ZMod 2))
    = PowerSeries.rescale (carlitzTheta (ZMod 2)) (carlitzExp (ZMod 2)) := by
  have := carlitzAction_exp (ZMod 2) 1
  simpa using this

/-- Over `F₂`, the intertwining theorem in the two-sided form. -/
example : carlitzAction (ZMod 2) 3 (carlitzExp (ZMod 2))
    = PowerSeries.rescale ((carlitzTheta (ZMod 2)) ^ 3) (carlitzExp (ZMod 2)) :=
  carlitzAction_exp (ZMod 2) 3

/-- Over `F₃`, the same for `n = 2`. -/
example : PowerSeries.rescale ((carlitzTheta (ZMod 3)) ^ 2) (carlitzExp (ZMod 3))
    = carlitzAction (ZMod 3) 2 (carlitzExp (ZMod 3)) :=
  carlitzExp_theta_pow (ZMod 3) 2

end ActionRegression

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

section ATRegression

/-- Over `F₂`, `α_1 = 1` and `α_2 = 1` (the easy range `n ≤ q`). -/
example : atAlpha (ZMod 2) 1 = 1 := atAlpha_eq_one_of_le (ZMod 2) le_rfl (by simp)

example : atAlpha (ZMod 2) 2 = 1 := atAlpha_eq_one_of_le (ZMod 2) (by norm_num) (by simp)

/-- Over `F₃`, `α_3 = 1`. -/
example : atAlpha (ZMod 3) 3 = 1 := atAlpha_eq_one_of_le (ZMod 3) (by norm_num) (by simp)

end ATRegression

end ZagierHoffmanPositiveChar
