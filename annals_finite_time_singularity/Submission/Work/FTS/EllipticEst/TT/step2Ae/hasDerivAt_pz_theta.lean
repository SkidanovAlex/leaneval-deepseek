import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.EllipticEst.TT.step2Ae

/-- **Clairaut for the slice `θ ↦ ∂_z f (z,·)`.**
If `f` is `C²` at the point `(z,θ)` then the slice `θ' ↦ ∂_z f (z,θ')` is differentiable at `θ`
with derivative `∂_z ∂_θ f (z,θ) = ∂_z(∂_θ f)(z,θ)`.

The proof identifies the slice with `θ' ↦ (fderiv ℝ (uncurry f) (z,θ')) (1,0)`, which is the
composition of the linear map `L ↦ L (1,0)` with the (differentiable, since `f` is `C²`)
function `fderiv ℝ (uncurry f)`, and then converts the value of the derivative with
`Work.Spaces.deriv_deriv_snd_fst` and `Work.Spaces.pz_pth_comm`. -/
theorem hasDerivAt_pz_theta {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    HasDerivAt (fun θ' => Work.Spaces.pz f z θ') (Work.Spaces.pz (Work.Spaces.pth f) z θ) θ := by
  change HasDerivAt (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z)
    (deriv (fun z' => deriv (fun θ' => Function.uncurry f (z', θ')) θ) z) θ
  -- `fderiv ℝ (uncurry f)` is differentiable at `(z,θ)` because `f` is `C²` there.
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    (ContDiffAt.fderiv_right h (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by norm_num)
  -- `uncurry f` is differentiable near `(z,θ)`, hence along the vertical slice through `z`.
  have hnd : ∀ᶠ y in 𝓝 (z, θ), DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffAt.eventually h (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hslice : ∀ᶠ θ' in 𝓝 θ, DifferentiableAt ℝ (Function.uncurry f) (z, θ') :=
    (Continuous.prodMk_right z).continuousAt.eventually hnd
  -- the `(1,0)`-evaluation of the derivative of `uncurry f`
  let Φ : ℝ × ℝ → ℝ := fun y => fderiv ℝ (Function.uncurry f) y (1, 0)
  -- the slice agrees with `Φ` along `{z} × ℝ`
  have hcongr : (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z) =ᶠ[𝓝 θ]
      (fun t => Φ (z, t)) := by
    filter_upwards [hslice] with θ' hθ'
    have h3 : deriv (fun z' => Function.uncurry f (z', θ')) z
        = (fderiv ℝ (Function.uncurry f) (z, θ')) (1, 0) :=
      Work.Spaces.deriv_slice_fst (Function.uncurry f) z θ' hθ'
    simpa only [Φ] using h3
  -- `Φ` is the composition of a continuous linear map with `fderiv ℝ (uncurry f)`
  have hΦ : Φ = (ContinuousLinearMap.apply ℝ ℝ (1, 0)) ∘ (fderiv ℝ (Function.uncurry f)) := by
    funext y; simp only [Φ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hΦdiff : DifferentiableAt ℝ Φ (z, θ) := by
    rw [hΦ]
    exact (ContinuousLinearMap.differentiableAt _).comp _ hfd_diff
  -- the derivative of the slice of `Φ`
  have hstep : HasDerivAt (fun t => Φ (z, t)) ((fderiv ℝ Φ (z, θ)) (0, 1)) θ := by
    have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
      hasFDerivAt_prodMk_right z θ
    have h3 : HasDerivAt (fun t : ℝ => Φ (z, t))
        ((fderiv ℝ Φ (z, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ := by
      convert (hΦdiff.hasFDerivAt.comp θ h2).hasDerivAt using 1
      · ext t; rfl
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    simpa only [ContinuousLinearMap.inr_apply] using h3
  have hmain : HasDerivAt (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z)
      ((fderiv ℝ Φ (z, θ)) (0, 1)) θ := hcongr.hasDerivAt_iff.mpr hstep
  -- identify the value of the derivative
  have hΦderiv : fderiv ℝ Φ (z, θ) =
      (ContinuousLinearMap.apply ℝ ℝ (1, 0)) ∘SL
        fderiv ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) := by
    conv_lhs => rw [hΦ]
    rw [fderiv_comp (z, θ) (ContinuousLinearMap.differentiableAt _) hfd_diff]
    rw [ContinuousLinearMap.fderiv]
  have hval1 : (fderiv ℝ Φ (z, θ)) (0, 1)
      = deriv (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z) θ := by
    rw [hΦderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact (Work.Spaces.deriv_deriv_snd_fst (Function.uncurry f) z θ h).symm
  -- Clairaut: the two orders of the mixed partial derivative agree
  have hval2 : deriv (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z) θ
      = deriv (fun z' => deriv (fun θ' => Function.uncurry f (z', θ')) θ) z := by
    have hp := Work.Spaces.pz_pth_comm (f := f) h
    simpa only [Work.Spaces.pz, Work.Spaces.pth, Function.uncurry] using hp.symm
  exact (hmain.congr_deriv hval1).congr_deriv hval2

end Work.FTS.EllipticEst.TT.step2Ae
