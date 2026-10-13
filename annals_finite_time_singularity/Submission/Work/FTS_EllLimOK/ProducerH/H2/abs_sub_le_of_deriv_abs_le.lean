import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

theorem abs_sub_le_of_deriv_abs_le {f : ℝ → ℝ} {L C : ℝ}
    (hC : ContDiffOn ℝ 1 f (Set.Ioo 0 L))
    (h : ∀ t ∈ Set.Ioo 0 L, |deriv f t| ≤ C) :
    ∀ s ∈ Set.Ioo 0 L, ∀ t ∈ Set.Ioo 0 L, |f s - f t| ≤ C * |s - t| := by
  intro s hs t ht
  -- `f` is differentiable on the open interval, with derivative `deriv f`.
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) L, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hC.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hbound : ∀ x ∈ Set.Ioo (0 : ℝ) L, ‖deriv f x‖ ≤ C := by
    intro x hx
    simpa [Real.norm_eq_abs] using h x hx
  -- Mean value inequality on the convex set `Ioo 0 L`.
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ioo 0 L) ht hs
  simpa [Real.norm_eq_abs] using this

end Work.FTS_EllLimOK.ProducerH.H2
