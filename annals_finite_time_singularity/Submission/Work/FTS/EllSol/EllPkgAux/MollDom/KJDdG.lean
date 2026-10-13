import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.KernelAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_abs_le
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.integrable_sKer_slice
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz)
open Work.EllipticEst.Core

local notation "Iθ" => Work.Spaces.Iθ
local notation "thEta" => Work.FTS.EllipticEst.thEta

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- The log-kernel `t ↦ sKer δ (log z - t)` is integrable (compact support). -/
theorem sKer_sub_integrable {δ z : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hz : 0 < z) :
    Integrable (fun t : ℝ => sKer δ (Real.log z - t)) volume := by
  have hcont : Continuous (fun t : ℝ => sKer δ (Real.log z - t)) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous.comp
      (continuous_const.sub continuous_id)
  have hzero : ∀ t ∉ Set.Icc (Real.log z - 1) (Real.log z + 1),
      sKer δ (Real.log z - t) = 0 := by
    intro t ht
    refine sKer_eq_zero_of_le_abs hδ ?_
    rw [Set.mem_Icc, not_and_or] at ht
    rcases ht with h | h
    · have h1 : t < Real.log z - 1 := not_le.mp h
      rw [abs_of_pos (by linarith)]
      linarith
    · have h1 : Real.log z + 1 < t := not_le.mp h
      rw [abs_of_neg (by linarith)]
      linarith
  have h1 : Integrable (Set.indicator (Set.Icc (Real.log z - 1) (Real.log z + 1))
      (fun t : ℝ => sKer δ (Real.log z - t))) volume :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Set.Icc (Real.log z - 1) (Real.log z + 1)
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    exact (hzero t ht).symm

/-- The `σ_η`-weighted angular slice of `D_z²G` is integrable. -/
theorem ddG_slice_integrable {G : ℝ → ℝ → ℝ} (hT : TraceClass G) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun s : ℝ => (Dz (Dz G) u s) ^ 2 * thEta s) Iθ := by
  have hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G := hT.2.2.2.2.2.2.2
  have h2 : IntegrableOn (fun s : ℝ => (Dz (Dz G) u s) ^ 2 * (Work.Spaces.w u) ^ 2
      * thEta s) Iθ := hhon.2.1 u hu
  refine MeasureTheory.Integrable.mono' h2 ?_ ?_
  · have ha : AEStronglyMeasurable (fun s : ℝ => Dz (Dz G) u s) (volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (Function.uncurry (fun u s : ℝ => Dz (Dz G) u s)) (hT.1.Dz.Dz).continuousOn hu
    have hσ : AEStronglyMeasurable (fun s : ℝ => thEta s) (volume.restrict Iθ) :=
      Work.FTS.EllipticEst.integrableOn_thEta.1.aestronglyMeasurable
    exact (ha.pow 2).mul hσ
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with s hs
    have hσ0 : 0 ≤ thEta s := Work.FTS.EllipticEst.thEta_nonneg hs
    have hw1 : (1 : ℝ) ≤ (Work.Spaces.w u) ^ 2 := one_le_w_sq hu
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσ0)]
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (sq_nonneg _) hw1) hσ0

/-- The pointwise `KJ`-slice bound for the second radial derivative. -/
theorem ddG_KJ_bound {G : ℝ → ℝ → ℝ} (hT : TraceClass G) {ε θ t : ℝ} (hε : 0 < ε) :
    (∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)
      ≤ (3 * (ε * sMass)⁻¹ / 2) * ((∫ s in Iθ,
          (Dz (Dz G) (Real.exp t) s) ^ 2 * thEta s) + Real.pi / 2) :=
  slice_abs_le (Real.exp_pos t) hε (ddG_slice_integrable hT (Real.exp_pos t))
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (Function.uncurry (fun u s : ℝ => Dz (Dz G) u s)) (hT.1.Dz.Dz).continuousOn
      (Real.exp_pos t))

/-- A.e. strong measurability in `t` of the `KJ`-slice of `D_z²G`. -/
theorem ddG_KJ_aesm {G : ℝ → ℝ → ℝ} (hT : TraceClass G) (ε θ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => ∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)
      volume := by
  have hXsm : ContinuousOn (Function.uncurry (fun u s : ℝ => Dz (Dz G) u s))
      Work.FTS.EllipticEst.Q0 := (hT.1.Dz.Dz).continuousOn
  exact MmPsi_aesm (aeStronglyMeasurable_exp hXsm).aemeasurable ε θ

/-- **The angular `KJ`-slice of the second radial derivative of a trace-class datum, tested
against the logarithmic mollification kernel, is integrable in the logarithmic radial
variable.** -/
theorem KJ_ddG_integrable_mine {G : ℝ → ℝ → ℝ} (hT : TraceClass G) (hF : FourInts G)
    {δ ε θ z : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hz : 0 < z) :
    Integrable (fun t : ℝ => sKer δ (Real.log z - t)
      * (∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)) volume := by
  have hdd : IntegrableOn (fun u : ℝ => (Work.Spaces.w u) ^ 2
      * (∫ s in Iθ, (Dz (Dz G) u s) ^ 2 * thEta s)) Work.Spaces.Iz := by
    simpa only [Work.EllipticEst.Core.ddIntS] using hF.2.1
  have hkerint : Integrable (fun t : ℝ => sKer δ (Real.log z - t)
      * (∫ s in Iθ, (Dz (Dz G) (Real.exp t) s) ^ 2 * thEta s)) volume :=
    integrable_sKer_slice (hT.1.Dz.Dz).continuousOn hδ hz hdd
  have hsKerint : Integrable (fun t : ℝ => sKer δ (Real.log z - t)) volume :=
    sKer_sub_integrable hδ hδ1 hz
  have hg : Integrable (fun t : ℝ => sKer δ (Real.log z - t)
      * ((3 * (ε * sMass)⁻¹ / 2) * ((∫ s in Iθ,
          (Dz (Dz G) (Real.exp t) s) ^ 2 * thEta s) + Real.pi / 2))) volume := by
    refine ((hkerint.const_mul (3 * (ε * sMass)⁻¹ / 2)).add
      (hsKerint.const_mul (3 * (ε * sMass)⁻¹ / 2 * (Real.pi / 2)))).congr
      (Filter.Eventually.of_forall fun t => by
        simp only [Pi.add_apply]
        ring)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t)
      * (∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)) volume := by
    have hsK : Continuous (fun t : ℝ => sKer δ (Real.log z - t)) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous.comp
        (continuous_const.sub continuous_id)
    refine (hsK.aestronglyMeasurable.mul (ddG_KJ_aesm hT ε θ)).congr
      (Filter.Eventually.of_forall fun t => rfl)
  refine MeasureTheory.Integrable.mono' hg hmeas ?_
  filter_upwards with t
  have hnn : (0 : ℝ) ≤ ∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s| :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun s _ => mul_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε θ s) (abs_nonneg _))
  rw [Real.norm_of_nonneg (mul_nonneg (sKer_nonneg hδ _) hnn)]
  exact mul_le_mul_of_nonneg_left (ddG_KJ_bound hT hε) (sKer_nonneg hδ _)

end Work.FTS.EllSol.EllPkgAux.MollDom
