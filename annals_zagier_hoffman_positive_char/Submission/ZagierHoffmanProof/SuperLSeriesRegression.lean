import Submission.ZagierHoffmanProof.SuperLSeries
import Submission.ZagierHoffmanProof.SuperOmegaRegression
import Submission.ZagierHoffmanProof.LSeries
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: the `L`-series lies in `ε`

Concrete instantiations over `K = F(t)_∞`, `θ = X`, `F = ZMod 2`, with the small series
`ω = θ⁻¹Ω̃` of `LSeries.lean`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

/-- `Ω̃ ∈ ε` over `F₂` (already a regression test of `SuperOmega`). -/
example : SuperEntire (atOmega 2 (thetaOf (ZMod 2))) :=
  superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `θ⁻¹Ω̃` is small, hence eligible for the `L`-series. -/
example : IsSmall (omegaSmall 2 (thetaOf (ZMod 2))) :=
  isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)

/-- `θ⁻¹ Ω̃ ∈ ε`. -/
example : SuperEntire (omegaSmall 2 (thetaOf (ZMod 2))) :=
  (SuperEntire.C ((thetaOf (ZMod 2))⁻¹)).mul
    (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2)) (by norm_num))

/-- **The depth-one `L`-series `∑_{i≥0}(ω^2Q)^{(2^i)}` lies in `ε`** over `F₂`. -/
example : SuperEntire (atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 2
    (PowerSeries.C ((thetaOf (ZMod 2))⁻¹))) :=
  superEntire_atL1Fold 2 (by norm_num) (isSmall_omegaSmall 2 (thetaOf (ZMod 2))
      (v_thetaOf (ZMod 2)) (by norm_num))
    ((SuperEntire.C ((thetaOf (ZMod 2))⁻¹)).mul
      (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
        (by norm_num)))
    (isSmall_C (by rw [Valuation.map_inv, v_thetaOf (ZMod 2), WithZero.exp_neg]))
    (SuperEntire.C _) 2

/-- **The depth-two cutoff `L`-series lies in `ε`** over `F₂`. -/
example : SuperEntire (atLrcut 2 (omegaSmall 2 (thetaOf (ZMod 2)))
    [(1, PowerSeries.C ((thetaOf (ZMod 2))⁻¹))] 0) := by
  refine superEntire_atLrcut 2 (by norm_num) (isSmall_omegaSmall 2 (thetaOf (ZMod 2))
      (v_thetaOf (ZMod 2)) (by norm_num))
    ((SuperEntire.C ((thetaOf (ZMod 2))⁻¹)).mul
      (superEntire_atOmega 2 (thetaOf (ZMod 2)) 1 (by norm_num) (v_thetaOf (ZMod 2))
        (by norm_num))) ?_ ?_ 0
  · intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact isSmall_C (by rw [Valuation.map_inv, v_thetaOf (ZMod 2), WithZero.exp_neg])
  · intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]
    exact SuperEntire.C _

end

end ZagierHoffmanPositiveChar
