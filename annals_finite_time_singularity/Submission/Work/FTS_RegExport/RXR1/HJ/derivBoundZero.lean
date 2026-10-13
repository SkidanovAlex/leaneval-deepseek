import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1.HJ

theorem derivBoundZero {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ x : ℝ, 0 < x → ∃ d : ℝ, HasDerivAt f d x ∧ |d| ≤ C)
    (htend : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z : ℝ, 0 < z → |f z| ≤ C * z := by
  intro z hz
  -- Mean value inequality: for every `y > 0`, `|f z - f y| ≤ C * |z - y|`.
  have hdiff : ∀ y ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f y :=
    fun y hy => (hderiv y hy).choose_spec.1.differentiableAt
  have hderivb : ∀ y ∈ Set.Ioi (0 : ℝ), ‖deriv f y‖ ≤ C := by
    intro y hy
    rw [Real.norm_eq_abs, (hderiv y hy).choose_spec.1.deriv]
    exact (hderiv y hy).choose_spec.2
  have hmvt : ∀ y ∈ Set.Ioi (0 : ℝ), |f z - f y| ≤ C * |z - y| := by
    intro y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderivb (convex_Ioi 0) hz hy
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  -- Pass to the limit `y → 0⁺`, where `f y → 0`.
  have hlim : Filter.Tendsto (fun y : ℝ => |f z - f y|) (nhdsWithin 0 (Set.Ioi 0))
      (nhds |f z|) := by
    have hsub : Filter.Tendsto (fun y : ℝ => f z - f y) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (f z - 0)) := tendsto_const_nhds.sub htend
    have h2 : Filter.Tendsto (fun y : ℝ => ‖f z - f y‖) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ‖f z - 0‖) := hsub.norm
    simpa [Real.norm_eq_abs] using h2
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio z from hz))] with y hy hyz
  have hy0 : 0 < y := hy
  have hyz' : y < z := hyz
  have h1 := hmvt y hy0
  have h2 : |z - y| ≤ z := by
    rw [abs_of_pos (show (0 : ℝ) < z - y by linarith)]
    linarith
  calc |f z - f y| ≤ C * |z - y| := h1
    _ ≤ C * z := by nlinarith [hC]

end Work.FTS_RegExport.RXR1.HJ
