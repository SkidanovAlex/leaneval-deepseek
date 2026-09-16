import Submission.ZagierHoffmanProof.MZProperty
import Submission.ZagierHoffmanProof.LSeriesRegression
import Submission.ZagierHoffmanProof.OmegaRegression
import Submission.ZagierHoffmanProof.SuperLSeriesRegression
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: the MZ property of the `L`-series

Concrete instantiations over `K = F(t)_∞`, `θ = X`, `F = ZMod 2` (`q = 2`) of
`evalSeries_atOmega_frobenius_orbit`, `evalSeries_C_mul_atOmega_frobenius_orbit`,
`evalSeries_atL1_frobenius_pow` and `evalSeries_atLrPaper_period_pow`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq
attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

/-- `v (θ⁻¹) = exp (-1)`. -/
lemma v_inv_thetaOf (F : Type*) [Field F] [DecidableEq (RatFunc F)] :
    Valued.v ((thetaOf F)⁻¹) = WithZero.exp (-1) := by
  rw [Valuation.map_inv, v_thetaOf, WithZero.exp_neg]

/-- **`Ω(θ^q) = 0`** over `F₂`: the period function vanishes at its Frobenius orbit. -/
example : evalSeries (atOmega 2 (thetaOf (ZMod 2))) ((thetaOf (ZMod 2)) ^ (2 ^ 1)) = 0 :=
  evalSeries_atOmega_frobenius_orbit 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
    (by norm_num) (by norm_num)

/-- **`Ω(θ^{q²}) = 0`** over `F₂`. -/
example : evalSeries (atOmega 2 (thetaOf (ZMod 2))) ((thetaOf (ZMod 2)) ^ (2 ^ 2)) = 0 :=
  evalSeries_atOmega_frobenius_orbit 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
    (by norm_num) (by norm_num)

/-- **`(θ⁻¹Ω̃)(θ^q) = 0`**: the normalised period function also vanishes. -/
example : evalSeries (omegaSmall 2 (thetaOf (ZMod 2))) ((thetaOf (ZMod 2)) ^ (2 ^ 1)) = 0 :=
  evalSeries_C_mul_atOmega_frobenius_orbit 2 (thetaOf (ZMod 2)) 1 (by norm_num)
    (v_thetaOf (ZMod 2)) (by norm_num) ((thetaOf (ZMod 2))⁻¹) (by norm_num)

/-- **Chang's MZ property, depth one, over `F₂`**:
`𝓛(1;θ⁻¹)(θ²) = (𝓛(1;θ⁻¹)(θ))²`. -/
example : evalSeries (atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1
      (PowerSeries.C ((thetaOf (ZMod 2))⁻¹)))
      ((thetaOf (ZMod 2)) ^ (2 ^ 1))
    = (evalSeries (atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1
        (PowerSeries.C ((thetaOf (ZMod 2))⁻¹))) (thetaOf (ZMod 2))) ^ (2 ^ 1) :=
  evalSeries_atL1_frobenius_pow 2 (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    ((SuperEntire.C ((thetaOf (ZMod 2))⁻¹)).mul
      (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
        (by norm_num))) 1 (by norm_num)
    (isSmall_C (le_of_eq (v_inv_thetaOf (ZMod 2))))
    (SuperEntire.C _)
    (fun _ hk => evalSeries_C_mul_atOmega_frobenius_orbit 2 (thetaOf (ZMod 2)) 1 (by norm_num)
      (v_thetaOf (ZMod 2)) (by norm_num) ((thetaOf (ZMod 2))⁻¹) hk) 1

/-- **Chang's MZ property, depth two, over `F₂`** for the period datum `Ω = θ⁻¹Ω̃`:
`𝓛((1,θ⁻¹),(1,θ⁻¹))(θ^{q²}) = (𝓛(θ))^{q²}`. -/
example : evalSeries (atLrPaper 2 (PowerSeries.C ((thetaOf (ZMod 2))⁻¹) * atOmega 2 (thetaOf (ZMod 2)))
      [(1, PowerSeries.C ((thetaOf (ZMod 2))⁻¹)), (1, PowerSeries.C ((thetaOf (ZMod 2))⁻¹))])
      ((thetaOf (ZMod 2)) ^ (2 ^ 2))
    = (evalSeries (atLrPaper 2
        (PowerSeries.C ((thetaOf (ZMod 2))⁻¹) * atOmega 2 (thetaOf (ZMod 2)))
        [(1, PowerSeries.C ((thetaOf (ZMod 2))⁻¹)), (1, PowerSeries.C ((thetaOf (ZMod 2))⁻¹))])
        (thetaOf (ZMod 2))) ^ (2 ^ 2) :=
  evalSeries_atLrPaper_period_pow 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
    (by norm_num) (le_of_eq (v_inv_thetaOf (ZMod 2)))
    ([(1, PowerSeries.C ((thetaOf (ZMod 2))⁻¹))] : List (ℕ × PowerSeries _))
    (by intro x hx; simp only [List.mem_singleton] at hx; rw [hx]
        exact isSmall_C (le_of_eq (v_inv_thetaOf (ZMod 2))))
    (by intro x hx; simp only [List.mem_singleton] at hx; rw [hx]; exact SuperEntire.C _)
    1 (by norm_num)
    (isSmall_C (le_of_eq (v_inv_thetaOf (ZMod 2))))
    (SuperEntire.C _) 2

end

end ZagierHoffmanPositiveChar
