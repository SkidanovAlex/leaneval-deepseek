import Mathlib.Algebra.Field.ZMod
import Submission.ZagierHoffmanProof.LSeries
import Submission.ZagierHoffmanProof.OmegaRegression
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: the depth-one `L`-series

Concrete instantiations of the results of `LSeries.lean` over `F = ZMod 2` and `F = ZMod 3`, with
`K = F(t)_∞`, `θ = X` and the small period-like series `omegaSmall q θ = θ⁻¹ · Ω̃`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq
attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

/-- `θ⁻¹Ω̃` is a "small" series over `F₂`. -/
example : IsSmall (omegaSmall 2 (thetaOf (ZMod 2))) :=
  isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `θ⁻¹Ω̃` is a "small" series over `F₃`. -/
example : IsSmall (omegaSmall 3 (thetaOf (ZMod 3))) :=
  isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)

/-- The defining family of the depth-one `L`-series is coefficientwise summable, over `F₂`. -/
example (s n : ℕ) : Summable fun i : ℕ =>
    PowerSeries.coeff n (frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) i
      (omegaSmall 2 (thetaOf (ZMod 2)) ^ s * omegaSmall 2 (thetaOf (ZMod 2)))) :=
  summable_coeff_atL1_term 2 (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) s n

/-- The coefficient formula for the depth-one `L`-series, over `F₂`. -/
example (n : ℕ) : PowerSeries.coeff n (atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1
      (omegaSmall 2 (thetaOf (ZMod 2))))
    = ∑' i : ℕ, PowerSeries.coeff n
        (frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) i
          (omegaSmall 2 (thetaOf (ZMod 2)) ^ 1 * omegaSmall 2 (thetaOf (ZMod 2)))) :=
  coeff_atL1 2 _ 1 _ n

/-- **The `L`-series recursion** `L = ω^sQ + L^{(1)}`, over `F₂`. -/
example : atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1 (omegaSmall 2 (thetaOf (ZMod 2)))
    = omegaSmall 2 (thetaOf (ZMod 2)) ^ 1 * omegaSmall 2 (thetaOf (ZMod 2))
      + frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) 1
          (atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1 (omegaSmall 2 (thetaOf (ZMod 2)))) :=
  atL1_eq_mul_add_frobTwist 2 (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) 1

/-- The `L`-series recursion over `F₃`. -/
example : atL1 3 (omegaSmall 3 (thetaOf (ZMod 3))) 2 (omegaSmall 3 (thetaOf (ZMod 3)))
    = omegaSmall 3 (thetaOf (ZMod 3)) ^ 2 * omegaSmall 3 (thetaOf (ZMod 3))
      + frobTwist (R := RatFunc.CompletionAtInfty (ZMod 3)) (p := 3) 1
          (atL1 3 (omegaSmall 3 (thetaOf (ZMod 3))) 2 (omegaSmall 3 (thetaOf (ZMod 3)))) :=
  atL1_eq_mul_add_frobTwist 3 (by norm_num)
    (isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num))
    (isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)) 2

/-- The twisted functional equation of the small series `θ⁻¹Ω̃`, over `F₂`. -/
example : (1 - PowerSeries.C (omX 2 (thetaOf (ZMod 2)) 1) * PowerSeries.X)
      * frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) 1
        (omegaSmall 2 (thetaOf (ZMod 2)))
    = PowerSeries.C ((thetaOf (ZMod 2) ^ (2 - 1))⁻¹) * omegaSmall 2 (thetaOf (ZMod 2)) :=
  omegaSmall_twist 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

end

end ZagierHoffmanPositiveChar
