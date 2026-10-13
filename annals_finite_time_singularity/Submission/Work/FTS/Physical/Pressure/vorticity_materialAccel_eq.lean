/-
# `Work.FTS.Physical.Pressure.vorticity_materialAccel_eq`

**The classical product rule for the curl**: for a `C²`, divergence-free velocity field `u`,

  `∇×((u·∇)u) = (u·∇)(∇×u) - ((∇×u)·∇)u`.

This is the identity that makes the *vorticity formulation* of Euler equivalent to the curl of the
Euler equation, and hence is what turns `curl(∂ₜu + (u·∇)u) = 0` into the vorticity equation
`∂ₜω + (u·∇)ω = (ω·∇)u`.  Together with `vorticity_timeDeriv_eq` (Clairaut: `∇×` commutes with
`∂ₜ`) and `Work.LWP.CurlFree.curlFree_isGradient` (the Poincaré lemma on `ℝ³`) it produces the
pressure of the reconstructed solution.

## The proof

Write `f = u(·,t)`, `A = Df(x)`, `A' = D(Df)(x)`.

* The material acceleration is `G = fderiv ℝ f · (f ·)`, i.e. the evaluation of the (continuous
  linear) derivative of `f` on the field itself; by the product rule `HasFDerivAt.clm_apply`,
  `DG(x) = A ∘ A + A'.flip (f x)`.
* The curl is a *linear* function `curlCLM` of the derivative, so
  `∇×G(x) = curlOf (A ∘ A) + curlOf (A' (f x))` (`curlCLM_eq_curlOf`, `curlOf_comp`).
* `∇×(∇×u)(x)·(u x) - Du(x)(ω x) = curlOf (A' (f x)) - A (curlOf A)`, because `curlCLM` is linear
  and because the second derivative is symmetric (`IsSymmSndFDerivAt`), which identifies `A'.flip v`
  with `A' v`.
* The remaining identity `curlOf (A ∘ A) = (tr A) • curlOf A - A (curlOf A)` is the
  linear-algebra computation `Work.FTS.Physical.Pressure.curlCompSelf`, and `tr A = div u = 0` by
  hypothesis.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Pressure.CurlCLM
import Submission.Work.FTS.Physical.Pressure.curlCompSelf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

/-- **The curl of the material acceleration.**  For `f : ℝ³ → ℝ³` of class `C²` at `x` with
`div f = 0`,

  `∇×((f·∇)f) = (f·∇)(∇×f) - ((∇×f)·∇)f`,

i.e. in the notation of this file,
`vorticity (fun y => Df(y) (f y)) x = D(∇×f)(x) (f x) - Df(x) (∇×f(x))`. -/
theorem vorticity_materialAccel_eq_aux {f : Work.FTS.Physical.R3 → Work.FTS.Physical.R3}
    (x : Work.FTS.Physical.R3) (hdiv : FiniteTimeSingularity.div f = 0)
    (hsm : ContDiffAt ℝ 2 f x) :
    FiniteTimeSingularity.vorticity (fun y => fderiv ℝ f y (f y)) x
      = fderiv ℝ (fun y => FiniteTimeSingularity.vorticity f y) x (f x)
        - fderiv ℝ f x (FiniteTimeSingularity.vorticity f x) := by
  -- `div f = 0` is `tr Df(x) = 0`
  have htr : (fderiv ℝ f x).trace ℝ Work.FTS.Physical.R3 = 0 := by
    have h := congr_fun hdiv x
    simpa [FiniteTimeSingularity.div] using h
  -- the derivative of `f`, and the derivative of `Df`
  have hd1 : HasFDerivAt f (fderiv ℝ f x) x :=
    (hsm.differentiableAt (by norm_num)).hasFDerivAt
  have hd2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hsm.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  -- the product rule for the material acceleration `G y = Df(y) (f y)`
  have hG : HasFDerivAt (fun y => fderiv ℝ f y (f y))
      ((fderiv ℝ f x).comp (fderiv ℝ f x) + (fderiv ℝ (fderiv ℝ f) x).flip (f x)) x :=
    hd2.clm_apply hd1
  -- the chain rule for the vorticity, using that `curlCLM` is linear
  have hω : HasFDerivAt (fun y => FiniteTimeSingularity.vorticity f y)
      (curlCLM.comp (fderiv ℝ (fderiv ℝ f) x)) x := by
    have h := (ContinuousLinearMap.hasFDerivAt curlCLM).comp x hd2
    simpa only [Function.comp_def, vorticity_eq_curlCLM] using h
  -- symmetry of the second derivative
  have hsym : (fderiv ℝ (fderiv ℝ f) x).flip (f x) = fderiv ℝ (fderiv ℝ f) x (f x) := by
    apply ContinuousLinearMap.ext
    intro h
    rw [ContinuousLinearMap.flip_apply]
    exact (hsm.isSymmSndFDerivAt (by simp)).eq h (f x)
  rw [vorticity_eq_curlCLM (fun y => fderiv ℝ f y (f y)) x, hG.fderiv, map_add]
  rw [hω.fderiv, ContinuousLinearMap.comp_apply, hsym, vorticity_eq_curlCLM f x]
  simp only [curlCLM_eq_curlOf]
  rw [curlOf_comp (fderiv ℝ f x) (fderiv ℝ f x)]
  simp only [curlOf_eq_symm, FiniteTimeSingularity.e]
  rw [curlCompSelf (fderiv ℝ f x), htr]
  simp only [zero_smul, zero_sub]
  abel

theorem vorticity_materialAccel_eq {u : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3} {t : ℝ} (x : Work.FTS.Physical.R3) (hdiv : FiniteTimeSingularity.div (fun y => u y t) = 0) (hsm : ContDiffAt ℝ 2 (fun y => u y t) x) : FiniteTimeSingularity.vorticity (fun y => fderiv ℝ (fun z => u z t) y (u y t)) x = fderiv ℝ (fun y => FiniteTimeSingularity.vorticity (fun z => u z t) y) x (u x t) - fderiv ℝ (fun z => u z t) x (FiniteTimeSingularity.vorticity (fun z => u z t) x) := by
  exact vorticity_materialAccel_eq_aux (f := fun z => u z t) x hdiv hsm

end Work.FTS.Physical.Pressure
