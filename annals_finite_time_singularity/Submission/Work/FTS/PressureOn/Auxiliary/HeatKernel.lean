import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Green.laplaceTrace_exp_neg_mul_normSq
import Submission.Work.FTS.PressureOn.Green.integral_exp_neg_normSq_R3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel on `ℝ³`

`heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` is the heat kernel on `ℝ³` (the fundamental
solution of the heat equation `∂_t u = Δu`).

This file collects the definition and the elementary pointwise facts; the analytic facts
(`∫ γ_t = 1`, the heat equation `∂_t γ_t = Δ γ_t`, the `L¹` modulus of continuity, the tail decay
at `t → 0` and the integration-by-parts identity against a harmonic function) are proved in the
sibling files, and are used to prove Liouville's theorem for bounded harmonic functions
(`Work.FTS.PressureOn.Auxiliary.bounded_harmonic_const`).
-/

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **The heat kernel on `ℝ³`**: `heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))`.  It solves the
heat equation `∂_t γ = Δγ`, integrates to `1` and is an approximate identity as `t → 0⁺`. -/
def heatKernel (t : ℝ) (z : R3) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))

@[simp] lemma heatKernel_apply (t : ℝ) (z : R3) :
    heatKernel t z = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) := rfl

lemma heatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (z : R3) : 0 ≤ heatKernel t z := by
  have h1 : (0 : ℝ) ≤ 4 * Real.pi * t := by positivity
  exact mul_nonneg (Real.rpow_nonneg h1 _) (Real.exp_nonneg _)

lemma heatKernel_pos {t : ℝ} (ht : 0 < t) (z : R3) : 0 < heatKernel t z := by
  have h1 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  unfold heatKernel
  exact mul_pos (Real.rpow_pos_of_pos h1 _) (Real.exp_pos _)

lemma heatKernel_even (t : ℝ) (z : R3) : heatKernel t (-z) = heatKernel t z := by
  simp [heatKernel, norm_neg]

/-- The kernel is symmetric in the difference: `γ_t (x - y) = γ_t (y - x)`. -/
lemma heatKernel_sub_comm (t : ℝ) (x y : R3) : heatKernel t (x - y) = heatKernel t (y - x) := by
  rw [← neg_sub y x, heatKernel_even]

/-- The kernel written as a constant times a Gaussian, with the exponent parameter `c = 1/(4t)`. -/
lemma heatKernel_eq_const_mul_exp {t : ℝ} (ht : 0 < t) (z : R3) :
    heatKernel t z = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2)) := by
  have h : ‖z‖ ^ 2 / (4 * t) = (4 * t)⁻¹ * ‖z‖ ^ 2 := by rw [div_eq_inv_mul]
  rw [heatKernel_apply, h]

end

end Work.FTS.PressureOn.Auxiliary
