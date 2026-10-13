/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HR2.Prep` — preparatory material for the honest energy inequality

* `hr2_restrict_Iz_eq_restrict_Ioi` : the restrictions of `volume` to `Iz = [0,∞)` and `(0,∞)`
  agree;
* `hr2_continuousOn_Icc_of_limits` : continuity on the closed angular interval from the open
  smoothnes plus the two endpoint limits;
* `hr2_cutGap` : the constrained slice gap `Gap9Open` integrated against `cut n · w²`.

-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.HonSliceAeYc
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.HR2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.HR2

theorem restrict_Iz_eq_restrict_Ioi :
    (volume.restrict Work.Spaces.Iz) = (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm

/-- A `C²` function on `(0,b)` with vanishing endpoint limits is continuous on `[0,b]`. -/
theorem continuousOn_Icc_of_limits {u : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 b))
    (h0 : u 0 = 0) (hbb : u b = 0)
    (hl0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlb : Filter.Tendsto u (nhdsWithin b (Set.Iio b)) (nhds 0)) :
    ContinuousOn u (Set.Icc 0 b) := by
  have hcio : ContinuousWithinAt u (Set.Iio b) b := by
    show Filter.Tendsto u (nhdsWithin b (Set.Iio b)) (nhds (u b))
    rw [hbb]; exact hlb
  have hrigo : ContinuousWithinAt u (Set.Ioi 0) 0 := by
    show Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (u 0))
    rw [h0]; exact hl0
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | hx0
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · have hmem : Set.Ioo 0 b ∈ nhds x := isOpen_Ioo.mem_nhds ⟨hx0, hxb⟩
      have hca : ContinuousAt u x :=
        (continuousWithinAt_iff_continuousAt hmem).mp
          (hsm.continuousOn.continuousWithinAt ⟨hx0, hxb⟩)
      exact hca.continuousWithinAt
    · subst hxb
      show Filter.Tendsto u (nhdsWithin x (Set.Icc 0 x)) (nhds (u x))
      rw [nhdsWithin_Icc_eq_nhdsLE hb]
      exact continuousWithinAt_Iio_iff_Iic.mp hcio
  · subst hx0
    show Filter.Tendsto u (nhdsWithin 0 (Set.Icc 0 b)) (nhds (u 0))
    rw [nhdsWithin_Icc_eq_nhdsGE hb]
    exact continuousWithinAt_Ioi_iff_Ici.mp hrigo

/-- **The constrained slice gap integrated against `cut n · w²`.** -/
theorem hr2_cutGap {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) (n : ℕ) :
    (9 : ℝ≥0∞) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2)))
      ≤ (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))) := by
  have hsl : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun θ : ℝ => Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
        IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => Ψ z t) θ) ^ 2) Work.Spaces.Iθ := by
    rw [restrict_Iz_eq_restrict_Ioi]
    exact HonSliceAeYc α F Ψ h
  have hzpos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [restrict_Iz_eq_restrict_Ioi]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have key : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))
        ≤ (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
    filter_upwards [hsl, hzpos] with z hz hzpos
    obtain ⟨hl0, hlπ, hint⟩ := hz
    have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      hon_slice_contDiffOn h hzpos 2
    have hcont : ContinuousOn (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
      continuousOn_Icc_of_limits (by positivity : (0 : ℝ) < Real.pi / 2) hcd (h.d0 z) (h.dπ z)
        hl0 hlπ
    have hgap := Gap9Open (fun θ : ℝ => Ψ z θ) hcd hcont (h.d0 z) (h.dπ z) hint (h.orthΨ z)
    have hLI : IntegrableOn (fun θ : ℝ => ((fun θ : ℝ => Ψ z θ) θ) ^ 2) Work.Spaces.Iθ :=
      (hcont.pow 2).integrableOn_compact isCompact_Icc
    have hL : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (((fun θ : ℝ => Ψ z θ) θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, ((fun θ : ℝ => Ψ z θ) θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLI
        (Filter.Eventually.of_forall (fun θ => sq_nonneg _))).symm
    have hR : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Ψ z θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun θ => sq_nonneg _))).symm
    rw [hL, hR]
    calc 9 * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, ((fun θ : ℝ => Ψ z θ) θ) ^ 2)
        = ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, ((fun θ : ℝ => Ψ z θ) θ) ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
          rw [show ENNReal.ofReal (9 : ℝ) = (9 : ℝ≥0∞) from by norm_num]
      _ ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Ψ z θ) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simpa only [Work.Spaces.pth] using hgap
  have hmain : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2) *
          (9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))))
      ≤ (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))) :=
    MeasureTheory.lintegral_mono_ae
      (key.mono (fun z hz => mul_le_mul_of_nonneg_left hz bot_le))
  calc (9 : ℝ≥0∞) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2)))
      = ∫⁻ z in Work.Spaces.Iz, 9 * (ENNReal.ofReal (Work.FTS.EllipticEst.cut n z
          * (Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))) :=
        (MeasureTheory.lintegral_const_mul' 9 _ (by norm_num)).symm
    _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (Work.FTS.EllipticEst.cut n z
          * (Work.Spaces.w z) ^ 2) *
          (9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))) := by
        refine MeasureTheory.lintegral_congr_ae
          (Filter.Eventually.of_forall (fun z => ?_))
        ac_rfl
    _ ≤ _ := hmain

end Work.FTS.EllipticEst.Honest.HR2
