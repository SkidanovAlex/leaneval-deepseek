import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-!
# `Work.StabilityFar.Decay.hasDerivAt_bsK` — the time derivative of the Biot–Savart kernel

`bsK ω x a = (‖x - a‖³)⁻¹ • (ω a × (x - a))` (`Work.LWP.BiotSavart.bsK`) depends on the
vorticity `ω` *only through its value at the fixed point `a`*, and there only linearly: for fixed
`x, a` the map

  `v ↦ bsK (fun _ => v) x a = (‖x - a‖³)⁻¹ • (v × (x - a))`

is a fixed continuous linear map `bsKCLM x a`.  Consequently, if the field slice
`s ↦ ω a s` is differentiable at `t` with derivative `∂ₜω(a,t)`, then so is
`s ↦ bsK (ω · s) x a`, with derivative `bsK (· , t) x a` (the kernel of the `t`-derivative
slice), which is exactly the pointwise statement needed to differentiate the Biot–Savart
integral under the integral sign.
-/

/-- The pointwise Biot–Savart kernel `v ↦ (‖x - a‖³)⁻¹ • (v × (x - a))` as a continuous linear
map in `v`.  It is the fixed linear factor through which `bsK (ω · s) x a` depends on `ω a s`. -/
noncomputable def bsKCLM (x a : Work.StabilityFar.R3) :
    Work.StabilityFar.R3 →L[ℝ] Work.StabilityFar.R3 :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.comp
      (((‖x - a‖ ^ (3 : ℕ))⁻¹ • (LinearMap.flip crossProduct)
          ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) (x - a))).comp
        ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap)))

/-- The defining property of `bsKCLM`: `bsKCLM x a v = bsK (fun _ => v) x a`. -/
theorem bsKCLM_apply (x a v : Work.StabilityFar.R3) :
    bsKCLM x a v = Work.LWP.BiotSavart.bsK (fun _ => v) x a := by
  rw [Work.LWP.BiotSavart.bsK.eq_def]
  simp only [bsKCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.flip_apply, LinearEquiv.coe_toLinearMap,
    WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv, WithLp.ofLp_sub]

/-- `bsK ω x a` depends on the vorticity only through its value `ω a` at `a`. -/
theorem bsK_fun_congr {ω ω' : Work.StabilityFar.R3 → Work.StabilityFar.R3}
    {x a : Work.StabilityFar.R3} (h : ω a = ω' a) :
    Work.LWP.BiotSavart.bsK ω x a = Work.LWP.BiotSavart.bsK ω' x a := by
  rw [Work.LWP.BiotSavart.bsK.eq_def, Work.LWP.BiotSavart.bsK.eq_def, h]

/-- **The time-derivative of the Biot–Savart kernel.**  If the slice `s ↦ ω a s` has derivative
`∂ₜω(a,t)` at `t`, then `s ↦ bsK (ω · s) x a` is differentiable at `t` with derivative
`bsK (fun y => ∂ₜω(y,t)) x a`, since the kernel is the fixed linear map `bsKCLM x a` applied to
`s ↦ ω a s`. -/
theorem hasDerivAt_bsK {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {x a : Work.StabilityFar.R3} {t : ℝ}
    (h : HasDerivAt (fun s' => ω a s') (FiniteTimeSingularity.timeDeriv ω a t) t) :
    HasDerivAt (fun s => Work.LWP.BiotSavart.bsK (ω · s) x a)
      (Work.LWP.BiotSavart.bsK (fun y => FiniteTimeSingularity.timeDeriv ω y t) x a) t := by
  have hcomp : HasDerivAt (fun s => bsKCLM x a (ω a s))
      (bsKCLM x a (FiniteTimeSingularity.timeDeriv ω a t)) t :=
    (bsKCLM x a).hasFDerivAt.comp_hasDerivAt t h
  convert hcomp using 1
  · funext s
    rw [bsKCLM_apply]
    exact bsK_fun_congr rfl
  · rw [bsKCLM_apply]
    exact bsK_fun_congr rfl

end Work.StabilityFar.Decay
