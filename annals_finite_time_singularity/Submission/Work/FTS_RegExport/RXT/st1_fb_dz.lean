/-
# `Work.FTS_RegExport.RXT.st1_fb_dz` — fallback proof of the `D_z²`-expansion

`DzIter 2 f z θ = z ∂_z f + z² ∂_z² f` at a point where the uncurried `f` is `C²`.  (The delivered
`Work.Spaces.DzIter_two_pt` only covers analytic `z`-slices, hence is not applicable.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

theorem dziter_two_fb {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.DzIter 2 f z θ = z * Work.Spaces.pz f z θ
      + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  -- `∂_zf(·,θ)` is (eventually near `z`) the `(1,0)`-evaluation of `fderiv (uncurry f)`
  set Φ : ℝ × ℝ → ℝ := fun p => (fderiv ℝ (Function.uncurry f) p) (1, 0) with hΦ
  have hΦeq : Φ = (ContinuousLinearMap.apply ℝ ℝ (1, 0))
      ∘ (fderiv ℝ (Function.uncurry f)) := by
    funext p
    simp only [hΦ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    (h.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hΦdiff : DifferentiableAt ℝ Φ (z, θ) := by
    rw [hΦeq]
    exact (ContinuousLinearMap.apply ℝ ℝ (1, 0)).differentiableAt.comp (z, θ) hfd_diff
  have hnd : ∀ᶠ y in 𝓝 (z, θ), DifferentiableAt ℝ (Function.uncurry f) y :=
    (h.eventually (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hθ : ∀ᶠ t in 𝓝 z, DifferentiableAt ℝ (Function.uncurry f) (t, θ) :=
    (Continuous.prodMk_left θ).continuousAt.eventually hnd
  have hslice : (fun t : ℝ => Work.Spaces.pz f t θ) =ᶠ[𝓝 z] (fun t => Φ (t, θ)) := by
    filter_upwards [hθ] with t ht
    exact Work.Spaces.deriv_slice_fst (Function.uncurry f) t θ ht
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Φ (t, θ)) z := by
    show DifferentiableAt ℝ (Φ ∘ fun t : ℝ => (t, θ)) z
    exact hΦdiff.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz f t θ) z :=
    hd1.congr_of_eventuallyEq hslice
  have hderiv : deriv (fun t : ℝ => t * Work.Spaces.pz f t θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
    have h3 := (hasDerivAt_id z).mul hdiff.hasDerivAt
    have h4 : HasDerivAt ((fun t : ℝ => t) * (fun t : ℝ => Work.Spaces.pz f t θ))
        (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) z :=
      h3.congr_deriv (by rw [one_mul, id_eq]; rfl)
    exact h4.deriv
  show z * deriv (fun t : ℝ => t * Work.Spaces.pz f t θ) z = _
  rw [hderiv]; ring

end Work.FTS_RegExport.RXT
