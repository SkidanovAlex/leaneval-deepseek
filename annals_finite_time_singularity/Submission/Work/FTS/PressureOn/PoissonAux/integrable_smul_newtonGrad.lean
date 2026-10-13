/-
# Integrability of `ψ • newtonGrad (· - y)` for a compactly supported continuous `ψ`

The Newtonian gradient kernel `newtonGrad z = -((4π)⁻¹‖z‖⁻³) • z` blows up like `‖z‖⁻²` at the
origin, and in dimension `3` the function `z ↦ ‖z‖⁻²` is locally integrable (the angular measure
supplies `r² dr`).  Hence for a continuous, compactly supported scalar profile `ψ` the vector field
`x ↦ ψ x • newtonGrad (x - y)` is integrable: the compact support cuts the integral down to a
bounded region, on which `‖x - y‖⁻²` has an integrable singularity.

The proof is a translation to the case `y = 0` — the singularity then sits at the origin, where the
available one-dimensional radial statement
`Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall` applies — together with the two
elementary pointwise facts supplied below: `‖newtonGrad z‖ = (4π)⁻¹‖z‖⁻²`, and the fact that `ψ`
vanishes off the closed ball containing its (compact) topological support.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux

/-- The pointwise size of the Newtonian gradient kernel: `‖∇N z‖ = (4π)⁻¹‖z‖⁻²`, valid also at
`z = 0` (where both sides vanish, using the convention `0⁻¹ = 0`). -/
private lemma newtonGrad_norm_eq (z : Work.FTS.PressureOn.R3) :
    ‖Work.FTS.PressureOn.newtonGrad z‖ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  rw [Work.FTS.PressureOn.norm_newtonGrad]
  have hcore : (‖z‖ ^ 3)⁻¹ * ‖z‖ = (‖z‖ ^ 2)⁻¹ := by
    rcases eq_or_ne (‖z‖ : ℝ) 0 with h | h
    · rw [h]; norm_num
    · rw [show ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ by ring, mul_inv, mul_assoc, inv_mul_cancel₀ h, mul_one]
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ 3)⁻¹ * ‖z‖) := by ring
    _ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by rw [hcore]

theorem integrable_smul_newtonGrad {ψ : Work.FTS.PressureOn.R3 → ℝ} (hψ : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (y : Work.FTS.PressureOn.R3) :
    MeasureTheory.Integrable (fun x : Work.FTS.PressureOn.R3 =>
      ψ x • Work.FTS.PressureOn.newtonGrad (x - y)) := by
  -- `ψ` is bounded and supported in a closed ball.
  obtain ⟨R, _hRpos, hR⟩ := hψcs.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψ
  have hCnn : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hC 0)
  have hK : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  -- The elementary majorant is `‖x - y‖⁻²` on the ball of radius `R + ‖y‖` about `y`.
  have hbase : MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (‖z‖ ^ 2)⁻¹ * (closedBall (0 : Work.FTS.PressureOn.R3) (R + ‖y‖)).indicator
        (fun _ => (1 : ℝ)) z) :=
    Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall (R + ‖y‖)
  have hmp : MeasureTheory.MeasurePreserving (fun x : Work.FTS.PressureOn.R3 => x + (-y))
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-y)
  have htrans := hmp.integrable_comp_of_integrable hbase
  have hmaj : MeasureTheory.Integrable (fun x : Work.FTS.PressureOn.R3 =>
      (4 * Real.pi)⁻¹ * C * ((‖x - y‖ ^ 2)⁻¹ *
        (closedBall (0 : Work.FTS.PressureOn.R3) (R + ‖y‖)).indicator
          (fun _ => (1 : ℝ)) (x - y))) := by
    have h := htrans.const_mul ((4 * Real.pi)⁻¹ * C)
    simpa only [Function.comp_apply, sub_eq_add_neg] using h
  refine hmaj.mono' ?_ ?_
  · -- measurability: `newtonGrad` is Borel (a rescaling of `z ↦ z` by `‖z‖⁻³`)
    have hng : Measurable (Work.FTS.PressureOn.newtonGrad :
        Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3) := by
      change Measurable (fun z : Work.FTS.PressureOn.R3 =>
        -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z)
      measurability
    exact (hψ.measurable.smul (hng.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  · -- the pointwise comparison with the majorant
    filter_upwards with x
    by_cases hx : x ∈ closedBall (0 : Work.FTS.PressureOn.R3) R
    · have hxS : x - y ∈ closedBall (0 : Work.FTS.PressureOn.R3) (R + ‖y‖) := by
        rw [mem_closedBall, dist_zero_right] at hx ⊢
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ ≤ R + ‖y‖ := by linarith
      rw [Set.indicator_of_mem hxS, mul_one, norm_smul]
      calc ‖ψ x‖ * ‖Work.FTS.PressureOn.newtonGrad (x - y)‖
          ≤ C * ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹) :=
            mul_le_mul (hC x) (le_of_eq (newtonGrad_norm_eq _)) (norm_nonneg _) hCnn
        _ = (4 * Real.pi)⁻¹ * C * (‖x - y‖ ^ 2)⁻¹ := by ring
    · -- off the supporting ball `ψ` vanishes identically, and the majorant is nonnegative
      have hxts : x ∉ tsupport ψ := fun hmem => hx (by
        rw [mem_closedBall, dist_zero_right]
        exact hR x hmem)
      have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxts
      rw [hψx, zero_smul, norm_zero]
      exact mul_nonneg (mul_nonneg hK hCnn) (mul_nonneg (by positivity)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _))

end Work.FTS.PressureOn.PoissonAux
