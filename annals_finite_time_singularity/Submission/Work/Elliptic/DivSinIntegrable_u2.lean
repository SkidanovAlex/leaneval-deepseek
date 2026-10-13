import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.SliceBddBounds
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.DivSinIdentitySetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

theorem DivSinIntegrable_u2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hh : Work.Elliptic.SmoothSlice h) (hb : Work.Elliptic.SliceBdd h) :
    MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
          * (deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2)
        Work.Spaces.Iθ MeasureTheory.volume := by
  have hαpos : 0 < α := hα
  -- `h` is `C²` on the closed interval `[0, π/2]`.
  have hf2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) :=
    (hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)).of_le le_top
  -- Continuity of the second derivative of the quotient on `(0, π/2)`.
  have hCv : ContinuousOn (fun θ => deriv (deriv (Work.Elliptic.SinQ h)) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.Elliptic.htU_interior_facts h hf2).2.2.2.2.2.2.2.1
  -- The almost-everywhere bound `|sin(2θ) · u''(θ)| ≤ C`.
  obtain ⟨C, hC0, hae⟩ := Work.Elliptic.SliceBdd_ae_bounds h hh hb
  -- Exponent bounds coming from `1 < gam α ≤ 11/10`.
  have hgam_le : Work.Spaces.gam α ≤ 11 / 10 := by
    unfold Work.Spaces.gam; linarith
  have hp2 : 0 ≤ 2 - Work.Spaces.gam α := by linarith
  have hp4 : 0 ≤ 4 - Work.Spaces.gam α := by linarith
  -- Measurability of the two factors.
  have hcont_s : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) :=
    (Real.continuous_rpow_const hp4).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hmeas_s : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) := hcont_s.measurable.aestronglyMeasurable
  have hμ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))
  have hmeas_v : AEStronglyMeasurable
      (fun θ : ℝ => deriv (deriv (Work.Elliptic.SinQ h)) θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [← hμ]
    exact hCv.aestronglyMeasurable measurableSet_Ioo
  have hmeas_F : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        * (deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    hmeas_s.mul (hmeas_v.pow 2)
  -- The almost-everywhere pointwise bound.
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖(fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        * (deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2) θ‖ ≤ C ^ 2 := by
    filter_upwards [hae, Work.Elliptic.ae_mem_Ioo_Iθ] with θ hb hθ
    obtain ⟨_, _, _, _, hsv⟩ := hb
    have hs_pos : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
    have hs_nn : 0 ≤ Real.sin (2 * θ) := le_of_lt hs_pos
    have hs_le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hrpow : (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ 2 := by
      rw [show (4 : ℝ) - Work.Spaces.gam α = (2 - Work.Spaces.gam α) + 2 by ring,
        Real.rpow_add hs_pos, Real.rpow_two]
    have hsple1 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one hs_nn hs_le1 hp2
    have hsq : (Real.sin (2 * θ) * deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2 ≤ C ^ 2 :=
      sq_le_sq' (abs_le.mp hsv).1 (abs_le.mp hsv).2
    have hkey : (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
          * (deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Real.sin (2 * θ) * deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2 := by
      rw [hrpow]; ring
    rw [hkey]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs_nn _) (sq_nonneg _))]
    calc (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * (Real.sin (2 * θ) * deriv (deriv (Work.Elliptic.SinQ h)) θ) ^ 2
        ≤ 1 * C ^ 2 := mul_le_mul hsple1 hsq (sq_nonneg _) (by norm_num)
      _ = C ^ 2 := by ring
  -- `Iθ` has finite volume, so a bounded almost-everywhere-measurable function is integrable.
  have hfin : volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  exact MeasureTheory.IntegrableOn.of_bound hfin hmeas_F (C ^ 2) hbound

end Work.Elliptic
