import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-`0` `ℋ⁰`-bound for the `cos θ`-weighted angular mass

The `ℋ⁰`-norm of a datum `F` on the open quadrant `Q0 = (0,∞) × (0,π/2)` is

    `∫⁻ p in Q0, ENNReal.ofReal (F p.1 p.2 ^ 2)`

and the *angular mass* of the slice at radius `z` is `∫ θ in Iθ, F z θ ^ 2 * cos θ`.  This file
proves that the `lintegral` over `z > 0` of the `ofReal` of the angular mass is bounded by the
`ℋ⁰`-norm: the weight `cos θ ≤ 1` (and `cos θ ≥ 0` on `Iθ`) bounds the `cos θ`-weighted slice
integral by the unweighted one, the two endpoints `θ = 0, π/2` are null for Lebesgue measure,
and Tonelli's theorem for `ℝ≥0∞`-valued functions (`MeasureTheory.setLIntegral_prod`) identifies
the iterated `lintegral` over the two half-lines with the `lintegral` over the product `Q0`.

The statement is `Work.FTS.PhiStar.Honesty.C0_le_lintegral`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

theorem C0_le_lintegral {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ))
      ≤ ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
  classical
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- The angular set `Iθ = [0, π/2]` differs from the open interval only by the two endpoints,
  -- a null set.
  have hIcc : (Work.Spaces.Iθ : Set ℝ) \ Set.Ioo 0 (π / 2) = {0, π / 2} := by
    rw [Work.Spaces.Iθ]
    exact Set.Icc_sdiff_Ioo_same (by positivity)
  have hnull : volume ({0, π / 2} : Set ℝ) = 0 := by
    rw [Set.insert_eq]
    exact measure_union_null Real.volume_singleton Real.volume_singleton
  have hae : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [hIcc]; exact hnull
    · rw [Work.Spaces.Iθ]
      rw [show Set.Ioo (0 : ℝ) (π / 2) \ Set.Icc 0 (π / 2) = ∅ from
        Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self]
      exact measure_empty
  -- The slice integral is honest: `F z · ² * cos ·` is nonnegative on `Iθ`, so `ofReal` of the
  -- Bochner integral agrees with the `lintegral` of the `ofReal`.
  have hstep1 : (fun z : ℝ => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ))
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2 * Real.cos θ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint z hz)]
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg (sq_nonneg _) hcos
  calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) :=
        MeasureTheory.lintegral_congr_ae hstep1
    -- `cos θ ≤ 1` on all of `ℝ`, so the `cos θ`-weight can be dropped.
    _ ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (F z θ ^ 2) := by
        refine MeasureTheory.lintegral_mono fun z => ?_
        calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2 * Real.cos θ))
            ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2) := by
              refine MeasureTheory.lintegral_mono fun θ => ?_
              exact ENNReal.ofReal_le_ofReal
                (mul_le_of_le_one_right (sq_nonneg _) (Real.cos_le_one θ))
          _ = ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (F z θ ^ 2) := by
              rw [MeasureTheory.Measure.restrict_congr_set hae]
    -- Tonelli for `ℝ≥0∞`-valued functions on the product `Q0`.
    _ = ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
        rw [Work.FTS.EllipticEst.Q0]
        refine (MeasureTheory.setLIntegral_prod (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ)) (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
          (fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2 ^ 2)) ?_).symm
        refine ContinuousOn.aemeasurable ?_ (by measurability)
        exact ENNReal.continuous_ofReal.comp_continuousOn (hsm.continuousOn.pow 2)

end Work.FTS.PhiStar.Honesty
