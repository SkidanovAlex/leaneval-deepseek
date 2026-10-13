import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Honesty.aemeasurable_cmode_clamp
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

open MeasureTheory Set Filter
open scoped Real Topology

/-- The radial weight `w` is continuous on the open half-line: needed only for the a.e. strong
measurability of `z ↦ w z`. -/
theorem continuousOn_w_Ioi : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- **The `L²(w²)` bound for a single angular mode.**

For `F` in the honest `ℋ⁰` class (`HkMem α 0 F`) and `C^∞` on the open quadrant, the weighted
square of the `m`-th mode coefficient is integrable on `(0,∞)` and its `eNorm m`-weighted
integral is dominated by `HkSq α 0 F`:

  `∫_0^∞ (cmode m F z · w z)² dz < ∞`,   `eNorm m · ∫_0^∞ (cmode m F z · w z)² dz ≤ HkSq α 0 F`.

This is the *sharp* (Bessel-type) per-mode bound
`eNorm m * (cmode m F z)² ≤ ∫_θ (F z θ)² sin(2θ)^{-η}` (proved in
`eNorm_mul_cmode_sq_le_sliceMass`) integrated against `w²`; at level `k = 0` the `ℋ⁰`-integrand
is `w z² · ∫_θ (F z θ)² sin(2θ)^{-η}`, so the right-hand side is exactly `HkSq α 0 F`. -/
theorem cmode_L2_bound {α : ℝ} {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F) (m : ℕ) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
        (Set.Ioi 0) ∧
      Work.EllipticEst.ModalSolution.eNorm m
          * (∫ z in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
        ≤ Work.Spaces.HkSq α 0 F := by
  -- the per-slice `η`-weighted mass, as an abbreviation
  set M : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hM
  have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  -- the slice is `Iθ`-integrable at every `z > 0` (honesty of the `ℋ⁰` class)
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem hF0 hz
  -- the sharp per-mode slice bound, integrated against the radial weight
  have hbound : ∀ z : ℝ, 0 < z →
      Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * M z := by
    intro z hz
    have h := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
      (m := m) (F := F) (z := z) (hslice z hz)
    rw [hM]
    calc Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
  -- the `z`-slice of `HkIntegrand α 0 F` is `w z² · M z`
  have hId : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
      = (Work.Spaces.w z) ^ 2 * M z := by
    intro z
    rw [hM]
    rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
              * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
          rw [Work.FTS.EllipticEst.AngAWeak.HkIntegrand_zero_eq_w α F z hθ,
            Work.FTS.EllipticEst.sEta]
          ring)]
    rw [MeasureTheory.integral_const_mul]
  -- the majorant `w² · M` is integrable: it is the `z`-slice function of `HkIntegrand α 0 F`
  have hmaj : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * M z)
      (Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := by
      intro z hz
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hz
    have h1 : MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        (Set.Ioi (0 : ℝ)) := hF0.2.mono_set hsub
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro z _
    exact hId z
  -- hence the target function is integrable as well
  have hT : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * ((Work.Spaces.w z) ^ 2 * M z)) (Set.Ioi (0 : ℝ)) := hmaj.const_mul _
    refine hdom.mono' ?_ ?_
    · have hcm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        Work.EllipticEst.ModalSolution.aesm_cmode hsm m
      have hw : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Work.Spaces.w z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (continuousOn_w_Ioi.aemeasurable measurableSet_Ioi).aestronglyMeasurable
      exact (hcm.mul hw).pow 2
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      have hcm2 : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          ≤ (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z := by
        have h := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
          (m := m) (F := F) (z := z) (hslice z hz)
        rw [hM]
        rw [← div_eq_inv_mul, le_div_iff₀ hEpos]
        calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
              * Work.EllipticEst.ModalSolution.eNorm m
            = Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by ring
          _ ≤ ∫ θ in Work.Spaces.Iθ,
                (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := h
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2
          = (Work.Spaces.w z) ^ 2 * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * ((Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z) :=
              mul_le_mul_of_nonneg_left hcm2 (sq_nonneg _)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * ((Work.Spaces.w z) ^ 2 * M z) := by ring
  -- the integral of the majorant is `HkSq α 0 F`
  have hmaj_eq : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * M z)
      = Work.Spaces.HkSq α 0 F := by
    have h1 : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * M z)
        = ∫ z in Set.Ioi (0 : ℝ),
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => (hId z).symm)
    have h2 : (∫ z in Set.Ioi (0 : ℝ),
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        = Work.Spaces.HkSq α 0 F := by
      rw [Work.Spaces.HkSq, show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := MeasureTheory.volume)
        (x := (0 : ℝ))).symm
    rw [h1, h2]
  refine ⟨hT, ?_⟩
  rw [← MeasureTheory.integral_const_mul]
  calc (∫ z in Set.Ioi (0 : ℝ), Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * M z :=
        MeasureTheory.setIntegral_mono_on (hT.const_mul _) hmaj measurableSet_Ioi
          (fun z hz => hbound z hz)
    _ = Work.Spaces.HkSq α 0 F := hmaj_eq

end Work.FTS.ClassCHon.Hcoef
