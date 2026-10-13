/-
# `Work.CoreResiduals.TimeHolderDeriv` — residual **R4** at the model data, proved

The residual R4 (`TimeHolderDeriv P`) is the time-Hölder regularity of `∂ₜω` on the strips
(finding H of the delivered `NOTES.md`); it is *equivalent* to a strip bound on `∂ₜ²ω`
(`Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData`, a **theorem**).

For the model data (`g = 0`, `T = 2`, `λ̄(t) = 1 - t/2`) the second-order data is explicit:

* the profile is `F_*(z,θ) = p(Γ(θ)/c)·2z/(1+z)²` on the angular branch, whose second
  `z`-derivative is `4(z-2)/(1+z)⁴`, so `|z²∂_z²F| ≤ 80`
  (`Work.ConstructionInstance.zsq_pz_pz_profile_zeroPert_abs_le`);
* the modulation is affine, so `λ̄'' = 0` and `K₂ = 0` works.

Hence R4 holds at the model data:
`timeHolderDeriv_model : TimeHolderDerivModel α` (for `0 < α ≤ 1/3`), and more generally for any
inhabitant of `ProfileData` with the recorded model data. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.Model
import Submission.Work.ConstructionInstance.selfSimTimeHolderDeriv_profileData_inhabited
import Submission.Work.CoreResiduals.solVort_timeDeriv_lipschitz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-- **R4 at any element of the model-data class.**  The proof is the second-order computation of
`Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData` with the *explicit* profile
`F_*` (`g = 0`) and the affine modulation `λ̄(t) = 1 - t/2`. -/
theorem timeHolderDeriv_of_inhabitant {α : NNReal} (I : Inhabitant α) :
    TimeHolderDeriv I.P := by
  have hα : 0 < (α : ℝ) := I.P.hα
  have hα13 : (α : ℝ) ≤ 1 / 3 := I.P.hα13
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith
  refine Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData I.P ?_
    (Cg'' := 80) (K₂ := 0) ?_ ?_ ?_
  · intro z θ hz
    rw [I.hg]
    exact Work.ConstructionInstance.hasDerivAt_pz_profile_zeroPert
      (p := Work.ConstructionInstance.profExp α) hz
  · intro z θ hz hθ
    rw [I.hg]
    exact Work.ConstructionInstance.zsq_pz_pz_profile_zeroPert_abs_le hp hp1 z θ hz hθ
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    exact hasDerivAt_const t (-(1 / 2))
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    norm_num

/-- **The second-order time condition at the model data** (`TimeDerivLocallyLipschitz`), from the
*same* second-order data that proves R4: the explicit second time derivative of the cut
self-similar vorticity (`Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort`) is bounded near
every time of the half-window, so `∂ₜω` is locally Lipschitz in `t`. -/
theorem timeDerivLocallyLipschitz_of_inhabitant {α : NNReal} (I : Inhabitant α) :
    TimeDerivLocallyLipschitz (solVort I.P) I.P.T := by
  have hα : 0 < (α : ℝ) := I.P.hα
  have hα13 : (α : ℝ) ≤ 1 / 3 := I.P.hα13
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith
  refine solVort_timeDeriv_lipschitz I.P ?_ (Cg'' := 80) (K₂ := 0) ?_ ?_ ?_
  · intro z θ hz
    rw [I.hg]
    exact Work.ConstructionInstance.hasDerivAt_pz_profile_zeroPert
      (p := Work.ConstructionInstance.profExp α) hz
  · intro z θ hz hθ
    rw [I.hg]
    exact Work.ConstructionInstance.zsq_pz_pz_profile_zeroPert_abs_le hp hp1 z θ hz hθ
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    exact hasDerivAt_const t (-(1 / 2))
  · intro t _
    have hderiv : deriv I.P.lam = fun _ : ℝ => -(1 / 2) := funext fun s => model_deriv_lam I s
    rw [hderiv, deriv_const]
    norm_num

/-- **R4 at the model data.** -/
theorem timeHolderDeriv_model {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    TimeHolderDerivModel α := by
  obtain ⟨I⟩ := inhabitant_exists hα hα13
  exact ⟨I.P, inhabitant_isModelData I, timeHolderDeriv_of_inhabitant I⟩

end Work.CoreResiduals
