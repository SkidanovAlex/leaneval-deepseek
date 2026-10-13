/-
# `ZmollTTAux1` — integral conversions, joint measurability and differentiation of a folded
angular integral.
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.thMollSliceL2
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.mollHdom
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c (sKer Qext)

/-! ## Elementary integral conversions -/

theorem intervalIntegral_Iθ_eq (f : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..(Real.pi / 2), f s) = ∫ s in Iθ, f s := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm

theorem integrableOn_uIoc_of_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntegrableOn f (Set.Icc a b)) : IntegrableOn f (Set.uIoc a b) := by
  rw [Set.uIoc_of_le hab]
  exact h.congr_set_ae MeasureTheory.Ioc_ae_eq_Icc

theorem integrableOn_Icc_of_uIoc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntegrableOn f (Set.uIoc a b)) : IntegrableOn f (Set.Icc a b) := by
  rw [Set.uIoc_of_le hab] at h
  exact h.congr_set_ae MeasureTheory.Ioc_ae_eq_Icc.symm

/-- A kernel supported in `(-δ, δ)` reduces the whole-line integral to `[a,b]`. -/
theorem full_eq_interval_zmoll (K : ℝ → ℝ) (R : ℝ → ℝ) {δ σ a b : ℝ} (hδ0 : 0 ≤ δ)
    (hvan : ∀ x : ℝ, δ < |x| → K x = 0) (ha : a ≤ σ - δ) (hb : σ + δ ≤ b) :
    (∫ t : ℝ, K (σ - t) * R t) = ∫ t in a..b, K (σ - t) * R t := by
  have hab : a ≤ b := le_trans ha (by linarith)
  have hzero' : ∀ t : ℝ, t ∉ Set.Icc a b → K (σ - t) * R t = 0 := by
    intro t ht
    rw [Set.mem_Icc, not_and_or] at ht
    have h : δ < |σ - t| := by
      rcases ht with h | h
      · rw [not_le] at h
        rw [abs_of_pos (by linarith)]
        linarith
      · rw [not_le] at h
        rw [abs_of_neg (by linarith)]
        linarith
    rw [hvan _ h, zero_mul]
  have h1 : (∫ t : ℝ, K (σ - t) * R t) = ∫ t in Set.Icc a b, K (σ - t) * R t := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun t : ℝ => K (σ - t) * R t) (s := Set.Icc a b)]
    exact fun t ht => hzero' t ht
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- A function continuous on the open angular quadrant is jointly measurable, so its angular
integral is a.e. strongly measurable in the radial variable. -/
theorem aesm_param_Iθ (Y : ℝ × ℝ → ℝ)
    (hY : ContinuousOn Y (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable (fun t : ℝ => ∫ s in Iθ, Y (t, s)) volume := by
  have h1 : AEStronglyMeasurable Y
      ((volume : Measure ℝ).prod (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
    have h2 : AEStronglyMeasurable Y
        (((volume : Measure ℝ).prod volume).restrict
          (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hY.aestronglyMeasurable (μ := volume) (MeasurableSet.univ.prod measurableSet_Ioo)
    rw [← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ] at h2
    exact h2
  have h3 := h1.integral_prod_right'
  refine h3.congr ?_
  filter_upwards with t
  exact (MeasureTheory.setIntegral_congr_set (f := fun s => Y (t, s))
    (μ := volume) MeasureTheory.Ioo_ae_eq_Icc)

/-- A product of something tending to `0` with something eventually bounded tends to `0`. -/
theorem tendsto_mul_zero {f g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ}
    (hf : Tendsto f l (𝓝 0)) (hg : ∀ᶠ s in l, |g s| ≤ c) :
    Tendsto (fun s => f s * g s) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  refine squeeze_zero' (g := fun s => ‖f s‖ * max c 0)
    (Filter.Eventually.of_forall fun s => norm_nonneg _) ?_ ?_
  · filter_upwards [hg] with s hs
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans hs (le_max_left _ _)) (abs_nonneg _)
  · have h := hf.mul_const (max c 0)
    simpa using h

/-! ## Differentiating the folded angular integral in `θ` -/

theorem inner_hasDerivAt {K K' : ℝ → ℝ → ℝ} {C : ℝ} {G : ℝ → ℝ → ℝ} {w θ : ℝ}
    (hKc : ∀ x : ℝ, Continuous (fun s : ℝ => K x s))
    (hK'c : ∀ x : ℝ, Continuous (fun s : ℝ => K' x s))
    (hbound : ∀ x s : ℝ, |K' x s| ≤ C)
    (hKdiff : ∀ x s : ℝ, HasDerivAt (fun y : ℝ => K y s) (K' x s) x)
    (hGc : ContinuousOn (fun s : ℝ => G w s) Iθ) :
    HasDerivAt (fun x : ℝ => ∫ s in Iθ, K x s * G w s)
      (∫ s in Iθ, K' θ s * G w s) θ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hGcIcc : ContinuousOn (fun s : ℝ => G w s) (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    rw [Set.uIcc_of_le hle]; exact hGc
  have hGaesm : AEStronglyMeasurable (fun s : ℝ => G w s)
      (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) := by
    rw [Set.uIoc_of_le hle]
    exact (hGc.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hGabs : ContinuousOn (fun s : ℝ => |G w s|) (Set.uIcc (0 : ℝ) (Real.pi / 2)) := hGcIcc.abs
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable (fun s : ℝ => K x s * G w s)
      (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) :=
    Filter.Eventually.of_forall fun x => (hKc x).aestronglyMeasurable.restrict.mul hGaesm
  have hF_int : IntervalIntegrable (fun s : ℝ => K θ s * G w s) volume 0 (Real.pi / 2) :=
    ((hKc θ).continuousOn.mul hGcIcc).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (fun s : ℝ => K' θ s * G w s)
      (volume.restrict (Set.uIoc (0 : ℝ) (Real.pi / 2))) :=
    (hK'c θ).aestronglyMeasurable.restrict.mul hGaesm
  have hbound_ae : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
      ∀ x ∈ (Set.univ : Set ℝ), ‖K' x s * G w s‖ ≤ C * |G w s| := by
    refine Filter.Eventually.of_forall fun s _ x _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x s) (abs_nonneg _)
  have hbound_int : IntervalIntegrable (fun s : ℝ => C * |G w s|) volume 0 (Real.pi / 2) :=
    (hGabs.const_mul C).intervalIntegrable
  have hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
      ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => K y s * G w s) (K' x s * G w s) x := by
    refine Filter.Eventually.of_forall fun s _ x _ => ?_
    exact (hKdiff x s).mul_const _
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := Real.pi / 2) (bound := fun s : ℝ => C * |G w s|)
    (F := fun x s : ℝ => K x s * G w s) (F' := fun x s : ℝ => K' x s * G w s)
    (x₀ := θ) (s := Set.univ) Filter.univ_mem hF_meas hF_int hF'_meas hbound_ae hbound_int hdiff
  have hfun : (fun x : ℝ => ∫ s in (0 : ℝ)..(Real.pi / 2), K x s * G w s)
      = fun x : ℝ => ∫ s in Iθ, K x s * G w s :=
    funext fun x => intervalIntegral_Iθ_eq _
  have hval : (∫ s in (0 : ℝ)..(Real.pi / 2), K' θ s * G w s) = ∫ s in Iθ, K' θ s * G w s :=
    intervalIntegral_Iθ_eq _
  rw [hfun, hval] at hmain
  exact hmain

end Work.FTS.EllSol.EllPkgAux.MollDom
