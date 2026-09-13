/-
The analytic core of Proposition 3.1 of Shankar--Yuan: the paper's Lemma `lem:o(r^2)` of the
appendix.  This module contains the whole *infrastructure* of the proof of
`Submission.TaylorCoreInput`:

* the standard sequence of bump functions `bseq m` (outer radius `1/(m+1)`) and the mollification
  `moll u m`,
* `ContDiff` of the mollification,
* the pointwise convergence `moll u m y → u y` at points of the open set where `u` is continuous,
* the convergence of the derivative at a Lebesgue point of the weak gradient,
* the kernel bounds used to control the second derivatives of the mollification,
* the coordinate algebra `bilin_eq_sum`, `hess_sub_eq_sum`, `two_smul_quadM_apply`.

The analytic core is `Submission.taylorCore`; `Submission.taylor_bound_aux` is its main
intermediate step (the uniform Taylor bound for the mollification).
-/
import Mathlib
import Submission.WeakDerivative
import Submission.AlexandrovCore
import Submission.AlexandrovQuad
import Submission.Commons.Measure.Average.setAverage_ball_comp_smul_sub
import Submission.Commons.Measure.Kernel.setAverage_abs_integral_mul_kernel_le2
import Submission.Commons.Measure.Kernel.setAverage_abs_pairing_mollMeasure_le2
import Submission.Commons.Measure.Kernel.setAverage_toReal_measure_closedBall_le
import Submission.Commons.Measure.Kernel.setAverage_integral_closedBall_le
import Submission.Commons.Measure.Kernel.setAverage_abs_integral_mul_kernel_add_pairing_le
import Submission.Commons.Analysis.Calculus.Taylor.setAverage_taylor_two
import Submission.Commons.Measure.Approximation.approx_sign_integral_ball
import Submission.Commons.Analysis.Convolution.fderiv_fderiv_moll_apply
import Submission.Commons.Analysis.Convolution.fderiv_moll_weakGrad
import Submission.Commons.Measure.Approximation.approx_sign_integral

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable def bseq (m : ℕ) : ContDiffBump (0 : ℝ⁴) :=
  Commons.Measure.Approximation.bumpSeq 4 m

lemma bseq_rOut (m : ℕ) : (bseq m).rOut = 1 / ((m : ℝ) + 1) := rfl
lemma bseq_rIn (m : ℕ) : (bseq m).rIn = (1 / ((m : ℝ) + 1)) / 2 := rfl
lemma bseq_rOut_pos (m : ℕ) : 0 < (bseq m).rOut := (bseq m).rOut_pos

lemma bseq_rOut_le_two_rIn (m : ℕ) : (bseq m).rOut ≤ 2 * (bseq m).rIn := by
  rw [bseq_rOut, bseq_rIn]; ring_nf; norm_num

lemma bseq_tendsto_rOut : Tendsto (fun m : ℕ => (bseq m).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) / ((k:ℝ) + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [bseq_rOut] using h

lemma bseq_tsupport (m : ℕ) :
    tsupport ((bseq m).normed volume) = closedBall (0 : ℝ⁴) (bseq m).rOut :=
  ContDiffBump.tsupport_normed_eq (bseq m) (μ := volume)

lemma bseq_normed_nonneg (m : ℕ) (t : ℝ⁴) : 0 ≤ (bseq m).normed volume t :=
  ContDiffBump.nonneg_normed (bseq m) t

lemma bseq_normed_bound (m : ℕ) (t : ℝ⁴) :
    (bseq m).normed volume t ≤ 16 / (volume.real (ball (0 : ℝ⁴) 1) * (bseq m).rOut ^ 4) := by
  have h1 := ContDiffBump.normed_le_div_measure_closedBall_rOut (bseq m) volume 2 (bseq_rOut_le_two_rIn m) t
  rw [Measure.addHaar_real_closedBall volume (0:ℝ⁴) (bseq m).rOut_pos.le] at h1
  have hfin : Module.finrank ℝ ℝ⁴ = 4 := by simp [finrank_euclideanSpace]
  rw [hfin] at h1
  calc (bseq m).normed volume t ≤ 2 ^ 4 / ((bseq m).rOut ^ 4 * volume.real (ball (0:ℝ⁴) 1)) := h1
    _ = 16 / (volume.real (ball (0:ℝ⁴) 1) * (bseq m).rOut ^ 4) := by ring

/- the mollification -/
noncomputable def moll (u : ℝ⁴ → ℝ) (m : ℕ) : ℝ⁴ → ℝ :=
  fun y => ∫ t, u t * (bseq m).normed volume (y - t)

lemma moll_eq_conv (u : ℝ⁴ → ℝ) (m : ℕ) :
    moll u m = fun y => ((bseq m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) y := by
  funext y
  simp only [moll]
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← MeasureTheory.integral_sub_left_eq_self
    (fun x : ℝ⁴ => u x * (bseq m).normed volume (y - x)) volume y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show u (y - t) * (bseq m).normed volume (y - (y - t)) = (bseq m).normed volume t * u (y - t)
  rw [show y - (y - t) = t by abel, mul_comm]

lemma contDiff_moll (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume) (m : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (moll u m) := by
  rw [moll_eq_conv]
  exact ((bseq m).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((bseq m).contDiff_normed (μ := volume) (n := ⊤)) hu).of_le (WithTop.coe_le_coe.mpr le_top)

lemma contDiff_moll_top (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (moll u m) := by
  rw [moll_eq_conv]
  exact (bseq m).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((bseq m).contDiff_normed (μ := volume) (n := ⊤)) hu

lemma stdE_sum (z : ℝ⁴) : ∑ i : Fin 4, z i • stdE i = z := by
  apply WithLp.ofLp_injective (p := 2)
  rw [WithLp.ofLp_sum]
  funext j
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, stdE, PiLp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma kernel_integral_le_ball {k h : ℝ⁴ → ℝ} {x₀ : ℝ⁴} {ε C : ℝ}
    (hk : ∀ t, 0 ≤ k t) (hC : ∀ t, k t ≤ C) (hC0 : 0 ≤ C) (hε : 0 < ε)
    (hks : ∀ t, k t ≠ 0 → t ∈ closedBall 0 ε)
    (hh : ∀ t, 0 ≤ h t) (hint : IntegrableOn h (ball x₀ (2 * ε)) volume) :
    ∫ t, k (x₀ - t) * h t ≤ C * ∫ t in ball x₀ (2 * ε), h t := by
  have hpt : ∀ t, k (x₀ - t) * h t ≤ (ball x₀ (2 * ε)).indicator (fun t => C * h t) t := by
    intro t
    by_cases ht : t ∈ ball x₀ (2 * ε)
    · rw [Set.indicator_of_mem ht]
      exact mul_le_mul_of_nonneg_right (hC _) (hh t)
    · rw [Set.indicator_of_notMem ht]
      have hk0 : k (x₀ - t) = 0 := by
        by_contra hne
        have hmem := hks (x₀ - t) hne
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
        exact ht (by
          rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
          linarith)
      rw [hk0, zero_mul]
  have hgi : Integrable ((ball x₀ (2 * ε)).indicator (fun t => C * h t)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (hint.const_mul C)
  calc ∫ t, k (x₀ - t) * h t
      ≤ ∫ t, (ball x₀ (2 * ε)).indicator (fun t => C * h t) t :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t => mul_nonneg (hk _) (hh t))) hgi
          (Filter.Eventually.of_forall hpt)
    _ = ∫ t in ball x₀ (2 * ε), C * h t := integral_indicator measurableSet_ball
    _ = C * ∫ t in ball x₀ (2 * ε), h t := integral_const_mul _ _

lemma bseq_normed_integral_sub (m : ℕ) (y : ℝ⁴) :
    ∫ t, (bseq m).normed volume (y - t) = 1 := by
  rw [MeasureTheory.integral_sub_left_eq_self (fun x : ℝ⁴ => (bseq m).normed volume x) volume y]
  exact ContDiffBump.integral_normed (bseq m)

lemma hasCompactSupport_sub_const (m : ℕ) (y : ℝ⁴) :
    HasCompactSupport (fun t : ℝ⁴ => (bseq m).normed volume (y - t)) := by
  have h : tsupport (fun t : ℝ⁴ => (bseq m).normed volume (y - t)) ⊆
      (fun s : ℝ⁴ => y - s) '' tsupport ((bseq m).normed volume) := by
    intro t ht
    have ht' : y - t ∈ tsupport ((bseq m).normed volume) := by
      by_contra hc
      rw [notMem_tsupport_iff_eventuallyEq] at hc
      have h2 : (fun t' : ℝ⁴ => (bseq m).normed volume (y - t')) =ᶠ[𝓝 t] 0 :=
        hc.comp_tendsto (tendsto_const_nhds.sub tendsto_id)
      exact (notMem_tsupport_iff_eventuallyEq.mpr h2) ht
    exact ⟨y - t, ht', by simp⟩
  exact IsCompact.of_isClosed_subset
    ((bseq m).hasCompactSupport_normed.image (continuous_const.sub continuous_id))
    isClosed_closure h

lemma integrable_moll_kernel (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume) (m : ℕ) (y : ℝ⁴) :
    Integrable (fun t => u t * (bseq m).normed volume (y - t)) volume := by
  have hcont : Continuous (fun t : ℝ⁴ => (bseq m).normed volume (y - t)) :=
    (bseq m).continuous_normed.comp (continuous_const.sub continuous_id)
  simpa [smul_eq_mul] using
    hu.integrable_smul_right_of_hasCompactSupport (μ := volume) hcont (hasCompactSupport_sub_const m y)

lemma moll_sub_eq (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume) (m : ℕ) (y : ℝ⁴) :
    moll u m y - u y = ∫ t, (u t - u y) * (bseq m).normed volume (y - t) := by
  have hA : Integrable (fun t => u t * (bseq m).normed volume (y - t)) volume :=
    integrable_moll_kernel u hu m y
  have hK : Integrable (fun t : ℝ⁴ => (bseq m).normed volume (y - t)) volume :=
    ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (hasCompactSupport_sub_const m y)
  have hB : Integrable (fun t => u y * (bseq m).normed volume (y - t)) volume :=
    hK.const_mul (u y)
  have h1 : ∫ t, (bseq m).normed volume (y - t) = 1 := bseq_normed_integral_sub m y
  have h2 : ∫ t, u y * (bseq m).normed volume (y - t) = u y := by
    rw [MeasureTheory.integral_const_mul, h1, mul_one]
  rw [moll]
  rw [show (∫ t, u t * (bseq m).normed volume (y - t)) - u y
      = (∫ t, u t * (bseq m).normed volume (y - t))
        - (∫ t, u y * (bseq m).normed volume (y - t)) by rw [h2]]
  rw [← integral_sub hA hB]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)

lemma setAverage_mono' {f g : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : MeasurableSet s)
    (hf : IntegrableOn f s volume) (hg : IntegrableOn g s volume) (h : ∀ x ∈ s, f x ≤ g x) :
    (⨍ x in s, f x) ≤ ⨍ x in s, g x := by
  rw [setAverage_eq, setAverage_eq, Measure.real_def]
  exact smul_le_smul_of_nonneg_left (setIntegral_mono_on hf hg hs h)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

lemma bseq_two_rOut_tendsto :
    Tendsto (fun m : ℕ => 2 * (bseq m).rOut) atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun m : ℕ => (2:ℝ) * (bseq m).rOut) atTop (𝓝 ((2:ℝ) * 0)) :=
      bseq_tendsto_rOut.const_mul 2
    simpa using h
  · filter_upwards with m
    have h := bseq_rOut_pos m
    exact show (0:ℝ) < 2 * (bseq m).rOut by linarith

/-- The average of `|u · - u y|` over the ball `B(y,r)` tends to `0` as `r → 0⁺` when `u` is
continuous at `y`. -/
lemma tendsto_setAverage_abs_sub_of_contOn {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hcont : ContinuousOn u s) {y : ℝ⁴} (hy : y ∈ s) :
    Tendsto (fun r : ℝ => ⨍ w in ball y r, |u w - u y|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcy : ContinuousAt u y := hcont.continuousAt (hs.mem_nhds hy)
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hy)
  rw [Metric.tendsto_nhds]
  intro η hη
  rw [Metric.continuousAt_iff] at hcy
  obtain ⟨δ, hδpos, hδ⟩ := hcy (η/2) (by linarith)
  refine (nhdsGT_basis (0:ℝ)).eventually_iff.mpr ⟨min δ (δ₀/2), lt_min hδpos (by linarith), ?_⟩
  intro r hr
  obtain ⟨hrpos, hrδ⟩ := hr
  have hrδ' : r < δ := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hrδ₀ : r < δ₀ := lt_of_lt_of_le hrδ (le_trans (min_le_right _ _) (by linarith))
  have hle : ∀ w ∈ ball y r, |u w - u y| ≤ η/2 := by
    intro w hw
    have hwd : dist w y < δ := lt_of_lt_of_le (by rwa [mem_ball] at hw) hrδ'.le
    have h := hδ hwd
    rw [Real.dist_eq] at h
    exact le_of_lt h
  have hFcont : ContinuousOn (fun w : ℝ⁴ => |u w - u y|) (closedBall y r) := by
    have h1 : ContinuousOn u (closedBall y r) :=
      hcont.mono (fun w hw => hδ₀sub (by
        rw [mem_ball]
        exact lt_of_le_of_lt (mem_closedBall.mp hw) hrδ₀))
    exact (h1.sub continuousOn_const).abs
  have hFint : IntegrableOn (fun w : ℝ⁴ => |u w - u y|) (closedBall y r) volume :=
    hFcont.integrableOn_compact (isCompact_closedBall y r)
  have hFint' : IntegrableOn (fun w : ℝ⁴ => |u w - u y|) (ball y r) volume :=
    hFint.mono_set ball_subset_closedBall
  have hCint : IntegrableOn (fun _ : ℝ⁴ => (η/2 : ℝ)) (ball y r) volume :=
    integrableOn_const (measure_ball_lt_top.ne)
  have hvolpos : (0:ℝ) < (volume (ball y r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume y hrpos).ne' measure_ball_lt_top.ne
  have hmono : (⨍ w in ball y r, |u w - u y|) ≤ (η/2 : ℝ) :=
    le_of_le_of_eq (setAverage_mono' measurableSet_ball hFint' hCint hle)
      (setAverage_const (measure_ball_pos volume y hrpos).ne' measure_ball_lt_top.ne (η/2))
  have hnn : 0 ≤ (⨍ w in ball y r, |u w - u y|) := by
    rw [setAverage_eq, Measure.real_def, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg (fun w => abs_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith


lemma volume_real_ball_four (x : ℝ⁴) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball x r)).toReal = r ^ 4 * (volume (ball (0 : ℝ⁴) 1)).toReal := by
  rw [← MeasureTheory.measureReal_def]
  rw [← MeasureTheory.Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x r]
  rw [MeasureTheory.Measure.addHaar_real_closedBall volume x hr, finrank_euclideanSpace,
    Fintype.card_fin]
  rw [measureReal_def]

/-- The localisation of the mollification to a neighbourhood of the base point. -/
lemma eventually_tsupport_moll_subset {s : Set ℝ⁴} (hs : IsOpen s) {y : ℝ⁴} (hy : y ∈ s) :
    ∀ᶠ m in atTop, ∀ z ∈ tsupport ((bseq m).normed volume), (y - z) ∈ s := by
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hy)
  have h : ∀ᶠ m : ℕ in atTop, (bseq m).rOut < δ₀ / 2 :=
    bseq_tendsto_rOut.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [h] with m hm z hz
  have hzt : z ∈ closedBall (0 : ℝ⁴) (bseq m).rOut := by
    rwa [bseq_tsupport m] at hz
  rw [Metric.mem_closedBall, dist_zero_right] at hzt
  refine hδ₀sub (by
    rw [Metric.mem_ball, dist_eq_norm, show (y - z) - y = -z by abel, norm_neg]
    linarith)


/-- The pointwise convergence of the mollification. -/
lemma moll_tendsto_pointwise (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume)
    {s : Set ℝ⁴} (hs : IsOpen s) (hcont : ContinuousOn u s) {y : ℝ⁴} (hy : y ∈ s) :
    Tendsto (fun m => moll u m y) atTop (𝓝 (u y)) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hy)
  have havg : Tendsto (fun r : ℝ => ⨍ w in ball y r, |u w - u y|) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_setAverage_abs_sub_of_contOn hs hcont hy
  have hcomp : Tendsto (fun m : ℕ => ⨍ w in ball y (2 * (bseq m).rOut), |u w - u y|)
      atTop (𝓝 0) := havg.comp bseq_two_rOut_tendsto
  have hsm : ∀ᶠ m : ℕ in atTop, 2 * (bseq m).rOut < δ₀ := by
    have h2 : Tendsto (fun m : ℕ => 2 * (bseq m).rOut) atTop (𝓝 0) := by
      have h := bseq_tendsto_rOut.const_mul 2
      simpa using h
    exact h2.eventually (eventually_lt_nhds hδ₀pos)
  have hb : ∀ᶠ m : ℕ in atTop,
      |moll u m y - u y| ≤ 256 * (⨍ w in ball y (2 * (bseq m).rOut), |u w - u y|) := by
    filter_upwards [hsm] with m hm
    have hεpos : 0 < (bseq m).rOut := bseq_rOut_pos m
    have hωpos : 0 < (volume (ball (0:ℝ⁴) 1)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
    have hvol : volume.real (ball y (2 * (bseq m).rOut))
        = (2 * (bseq m).rOut) ^ 4 * (volume (ball (0:ℝ⁴) 1)).toReal := by
      rw [Measure.real_def, volume_real_ball_four y (by positivity)]
    have hvolne : (2 * (bseq m).rOut) ^ 4 * (volume (ball (0:ℝ⁴) 1)).toReal ≠ 0 := by
      positivity
    have hcont2 : ContinuousOn u (closedBall y (2 * (bseq m).rOut)) :=
      hcont.mono (fun w hw => hδ₀sub (by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt (mem_closedBall.mp hw) hm))
    have hFcont : ContinuousOn (fun w : ℝ⁴ => |u w - u y|) (closedBall y (2 * (bseq m).rOut)) :=
      (hcont2.sub continuousOn_const).abs
    have hint : IntegrableOn (fun w : ℝ⁴ => |u w - u y|) (ball y (2 * (bseq m).rOut)) volume :=
      (hFcont.integrableOn_compact (isCompact_closedBall y _)).mono_set ball_subset_closedBall
    have hks : ∀ t, (bseq m).normed volume t ≠ 0 → t ∈ closedBall 0 (bseq m).rOut := by
      intro t ht
      rw [← bseq_tsupport m]
      exact subset_closure (Function.mem_support.mpr ht)
    have hC := kernel_integral_le_ball (k := (bseq m).normed volume)
      (h := fun t : ℝ⁴ => |u t - u y|) (x₀ := y) (ε := (bseq m).rOut)
      (C := 16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4))
      (bseq_normed_nonneg m) (fun t => bseq_normed_bound m t) (by positivity) hεpos hks
      (fun t => abs_nonneg _) hint
    have step1 : |∫ t, (u t - u y) * (bseq m).normed volume (y - t)|
        ≤ ∫ t, (bseq m).normed volume (y - t) * |u t - u y| := by
      refine (abs_integral_le_integral_abs).trans_eq ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show |(u t - u y) * (bseq m).normed volume (y - t)|
        = (bseq m).normed volume (y - t) * |u t - u y|
      rw [abs_mul, abs_of_nonneg (bseq_normed_nonneg m _), mul_comm]
    have step2 : (16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4))
        * (∫ t in ball y (2 * (bseq m).rOut), |u t - u y|)
        = 256 * (⨍ w in ball y (2 * (bseq m).rOut), |u w - u y|) := by
      have havg2 := setAverage_eq (μ := volume) (f := fun w : ℝ⁴ => |u w - u y|)
        (s := ball y (2 * (bseq m).rOut))
      rw [hvol, smul_eq_mul] at havg2
      have heq : ∫ w in ball y (2 * (bseq m).rOut), |u w - u y|
          = ((2 * (bseq m).rOut) ^ 4 * (volume (ball (0:ℝ⁴) 1)).toReal)
            * (⨍ w in ball y (2 * (bseq m).rOut), |u w - u y|) := by
        rw [havg2, ← mul_assoc, mul_inv_cancel₀ hvolne, one_mul]
      rw [heq, ← mul_assoc]
      congr 1
      rw [Measure.real_def]
      field_simp
      ring
    rw [moll_sub_eq u hu m y]
    exact step1.trans (hC.trans (le_of_eq step2))
  have hlim0 : Tendsto (fun m : ℕ => 256 * (⨍ w in ball y (2 * (bseq m).rOut), |u w - u y|))
      atTop (𝓝 0) := by
    have h := hcomp.const_mul (256:ℝ)
    simpa using h
  have hsq : Tendsto (fun m : ℕ => |moll u m y - u y|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun m => abs_nonneg _) hb hlim0
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hsq


/-- The derivative of the mollification at a Lebesgue point of the weak gradient. -/
lemma fderiv_moll_tendsto (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume)
    {s : Set ℝ⁴} (hs : IsOpen s) {G : ℝ⁴ → ℝ⁴} (hGli : LocallyIntegrable G volume)
    (hwg : HasWeakGradient u s G) {x₀ : ℝ⁴} (hx₀ : x₀ ∈ s)
    (hleb : IsLebesguePointVec G x₀) (v : ℝ⁴) :
    Tendsto (fun m => (fderiv ℝ (moll u m) x₀) v) atTop (𝓝 (⟪G x₀, v⟫)) := by
  have hsupp : ∀ᶠ m in atTop, ∀ z ∈ tsupport ((bseq m).normed volume), (x₀ - z) ∈ s :=
    eventually_tsupport_moll_subset hs hx₀
  have hder : ∀ᶠ m : ℕ in atTop,
      (fderiv ℝ (moll u m) x₀) v
        = ∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫ := by
    filter_upwards [hsupp] with m hm
    have h := Commons.Analysis.Convolution.fderiv_moll_weakGrad ((bseq m).normed volume) u G s x₀
      ((bseq m).contDiff_normed (μ := volume) (n := ⊤)) ((bseq m).hasCompactSupport_normed)
      hu hGli hm hwg v
    rw [show moll u m = (fun y : ℝ⁴ => ∫ t, u t * (bseq m).normed volume (y - t)) from rfl]
    exact h
  have hcomp : Tendsto (fun m : ℕ => ⨍ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖)
      atTop (𝓝 0) := hleb.comp bseq_two_rOut_tendsto
  have hb : ∀ᶠ m : ℕ in atTop,
      |(fderiv ℝ (moll u m) x₀) v - ⟪G x₀, v⟫|
        ≤ ‖v‖ * (256 * (⨍ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖)) := by
    filter_upwards [hder] with m hm
    rw [hm]
    have hεpos : 0 < (bseq m).rOut := bseq_rOut_pos m
    have hωpos : 0 < (volume (ball (0:ℝ⁴) 1)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
    have hvol : volume.real (ball x₀ (2 * (bseq m).rOut))
        = (2 * (bseq m).rOut) ^ 4 * (volume (ball (0:ℝ⁴) 1)).toReal := by
      rw [Measure.real_def, volume_real_ball_four x₀ (by positivity)]
    have hvolne : (2 * (bseq m).rOut) ^ 4 * (volume (ball (0:ℝ⁴) 1)).toReal ≠ 0 := by
      positivity
    have hks : ∀ t, (bseq m).normed volume t ≠ 0 → t ∈ closedBall 0 (bseq m).rOut := by
      intro t ht
      rw [← bseq_tsupport m]
      exact subset_closure (Function.mem_support.mpr ht)
    have hint : IntegrableOn (fun t : ℝ⁴ => ‖G t - G x₀‖) (ball x₀ (2 * (bseq m).rOut)) volume := by
      have h1 : IntegrableOn (fun t : ℝ⁴ => G t - G x₀) (closedBall x₀ (2 * (bseq m).rOut))
          volume :=
        (hGli.integrableOn_isCompact (isCompact_closedBall x₀ _)).sub
          (integrableOn_const measure_closedBall_lt_top.ne)
      exact IntegrableOn.mono_set h1.norm ball_subset_closedBall
    have hC := kernel_integral_le_ball (k := (bseq m).normed volume)
      (h := fun t : ℝ⁴ => ‖G t - G x₀‖) (x₀ := x₀) (ε := (bseq m).rOut)
      (C := 16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4))
      (bseq_normed_nonneg m) (fun t => bseq_normed_bound m t) (by positivity) hεpos hks
      (fun t => norm_nonneg _) hint
    have hsub : (∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫) - ⟪G x₀, v⟫
        = ∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t - G x₀, v⟫ := by
      have hInner : LocallyIntegrable (fun t : ℝ⁴ => ⟪G t, v⟫) volume := by
        have h1 : LocallyIntegrable (fun t : ℝ⁴ => ‖v‖ • G t) volume := hGli.smul ‖v‖
        refine h1.mono (hGli.aestronglyMeasurable.inner aestronglyMeasurable_const) ?_
        filter_upwards with t
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        exact (norm_inner_le_norm (G t) v).trans_eq (mul_comm _ _)
      have hK : Integrable (fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t)) volume :=
        ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
          (hasCompactSupport_sub_const m x₀)
      have hA : Integrable (fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫) volume := by
        have h2 := hInner.integrable_smul_right_of_hasCompactSupport
          (μ := volume) (f := fun t : ℝ⁴ => ⟪G t, v⟫)
          (g := fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t))
          ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id))
          (hasCompactSupport_sub_const m x₀)
        simpa [smul_eq_mul, mul_comm] using h2
      have hB : Integrable (fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t) * ⟪G x₀, v⟫) volume :=
        hK.mul_const _
      have h1 : ∫ t, (bseq m).normed volume (x₀ - t) = 1 := bseq_normed_integral_sub m x₀
      have h2 : (∫ t, (bseq m).normed volume (x₀ - t) * ⟪G x₀, v⟫) = ⟪G x₀, v⟫ := by
        rw [MeasureTheory.integral_mul_const, h1, one_mul]
      calc (∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫) - ⟪G x₀, v⟫
          = (∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫)
            - (∫ t, (bseq m).normed volume (x₀ - t) * ⟪G x₀, v⟫) := by rw [h2]
        _ = ∫ t, ((bseq m).normed volume (x₀ - t) * ⟪G t, v⟫
              - (bseq m).normed volume (x₀ - t) * ⟪G x₀, v⟫) := (integral_sub hA hB).symm
        _ = ∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t - G x₀, v⟫ := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
              show (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫
                    - (bseq m).normed volume (x₀ - t) * ⟪G x₀, v⟫
                  = (bseq m).normed volume (x₀ - t) * ⟪G t - G x₀, v⟫
              rw [inner_sub_left]
              ring
    rw [hsub]
    have step1 : |∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t - G x₀, v⟫|
        ≤ ∫ t, (bseq m).normed volume (x₀ - t) * (‖v‖ * ‖G t - G x₀‖) := by
      refine (abs_integral_le_integral_abs).trans ?_
      have hnorm : LocallyIntegrable (fun t : ℝ⁴ => ‖G t - G x₀‖) volume := by
        have hGl : LocallyIntegrable (fun t : ℝ⁴ => G t - G x₀) volume :=
          hGli.sub (locallyIntegrable_const (G x₀))
        exact hGl.mono hGl.aestronglyMeasurable.norm
          (Filter.Eventually.of_forall fun t => by simp)
      have hgi : Integrable
          (fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t) * (‖v‖ * ‖G t - G x₀‖)) volume := by
        have h2 := (hnorm.smul ‖v‖).integrable_smul_right_of_hasCompactSupport
          (μ := volume) (f := fun t : ℝ⁴ => ‖v‖ * ‖G t - G x₀‖)
          (g := fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t))
          ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id))
          (hasCompactSupport_sub_const m x₀)
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h2
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _) hgi
        (Filter.Eventually.of_forall fun t => ?_)
      show |(bseq m).normed volume (x₀ - t) * ⟪G t - G x₀, v⟫| ≤ _
      rw [abs_mul, abs_of_nonneg (bseq_normed_nonneg m _), ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((norm_inner_le_norm (G t - G x₀) v).trans_eq (mul_comm _ _)) (bseq_normed_nonneg m _)
    have hsplit : ∫ t, (bseq m).normed volume (x₀ - t) * (‖v‖ * ‖G t - G x₀‖)
        = ‖v‖ * ∫ t, (bseq m).normed volume (x₀ - t) * ‖G t - G x₀‖ := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    have step2 : (16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4))
        * (∫ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖)
        = 256 * (⨍ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖) := by
      have havg2 := setAverage_eq (μ := volume) (f := fun w : ℝ⁴ => ‖G w - G x₀‖)
        (s := ball x₀ (2 * (bseq m).rOut))
      rw [hvol, smul_eq_mul] at havg2
      have heq : ∫ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖
          = ((2 * (bseq m).rOut) ^ 4 * (volume (ball (0:ℝ⁴) 1)).toReal)
            * (⨍ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖) := by
        rw [havg2, ← mul_assoc, mul_inv_cancel₀ hvolne, one_mul]
      rw [heq, ← mul_assoc]
      congr 1
      rw [Measure.real_def]
      field_simp
      ring
    calc |∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t - G x₀, v⟫|
        ≤ ∫ t, (bseq m).normed volume (x₀ - t) * (‖v‖ * ‖G t - G x₀‖) := step1
      _ = ‖v‖ * ∫ t, (bseq m).normed volume (x₀ - t) * ‖G t - G x₀‖ := hsplit
      _ ≤ ‖v‖ * ((16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4))
            * (∫ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖)) :=
          mul_le_mul_of_nonneg_left hC (norm_nonneg v)
      _ = ‖v‖ * (256 * (⨍ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖)) := by
          rw [step2]
  have hlim0 : Tendsto (fun m : ℕ => ‖v‖ * (256 * (⨍ w in ball x₀ (2 * (bseq m).rOut), ‖G w - G x₀‖)))
      atTop (𝓝 0) := by
    have h := hcomp.const_mul (256:ℝ)
    have h2 := h.const_mul (‖v‖)
    simpa [mul_assoc] using h2
  have hsq : Tendsto (fun m : ℕ => |(fderiv ℝ (moll u m) x₀) v - ⟪G x₀, v⟫|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun m => abs_nonneg _) hb hlim0
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hsq


/-- A continuous bilinear form evaluated on the diagonal is the sum of its matrix coefficients. -/
lemma bilin_eq_sum (B : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ) (z : ℝ⁴) :
    B z z = ∑ i, ∑ j, (z i * z j) * B (stdE i) (stdE j) := by
  conv_lhs => rw [← stdE_sum z]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `(B - M₀) z z` in coordinates, where `M₀ = 2 • quadM M x₀` is twice the quadratic form of
the matrix `M x₀`. -/
lemma hess_sub_eq_sum (B : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ)
    (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (x₀ z : ℝ⁴) :
    (B - (2:ℝ) • quadM M x₀) z z
      = ∑ i, ∑ j, (z i * z j) * (B (stdE i) (stdE j) - M i j x₀) := by
  have hB := bilin_eq_sum B z
  have hQ := quadM_apply M x₀ z z
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [hB, hQ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `2 • quadM M x₀` evaluated on the diagonal equals `∑ M i j x₀ z_i z_j`. -/
lemma two_smul_quadM_apply (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (x₀ z : ℝ⁴) :
    ((2:ℝ) • quadM M x₀) z z = ∑ i, ∑ j, M i j x₀ * (z i) * (z j) := by
  have hQ := quadM_apply M x₀ z z
  simp only [smul_apply, smul_eq_mul]
  rw [hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring



lemma setAverage_mul_eq {f : ℝ⁴ → ℝ} {t : Set ℝ⁴} (h : volume.real t ≠ 0) :
    (⨍ x in t, f x) * volume.real t = ∫ x in t, f x := by
  rw [setAverage_eq, smul_eq_mul]
  rw [mul_comm (((volume.real t)⁻¹) * ∫ x in t, f x) (volume.real t), ← mul_assoc,
    mul_inv_cancel₀ h, one_mul]

lemma volume_real_ball_pos (x : ℝ⁴) {r : ℝ} (hr : 0 < r) : 0 < volume.real (ball x r) :=
  ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

lemma two_mul_tendsto_nhdsGT (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℝ => a * r) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun r : ℝ => a * r) (𝓝 (0:ℝ)) (𝓝 (a * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos ha hr


lemma setAverage_sum_four {s : Set ℝ⁴} {f : Fin 4 → Fin 4 → ℝ⁴ → ℝ}
    (hf : ∀ i j, IntegrableOn (f i j) s volume) :
    (⨍ x in s, ∑ i, ∑ j, f i j x) = ∑ i, ∑ j, ⨍ x in s, f i j x := by
  have h1 : (∫ x in s, ∑ i, ∑ j, f i j x) = ∑ i, ∑ j, ∫ x in s, f i j x := by
    have hfi : ∀ i, Integrable (fun x => ∑ j, f i j x) (volume.restrict s) :=
      fun i => integrable_finsetSum Finset.univ (fun j _ => hf i j)
    rw [integral_finsetSum Finset.univ (fun i _ => hfi i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ (fun j _ => hf i j)]
  have h2 : (⨍ x in s, ∑ i, ∑ j, f i j x)
      = (volume.real s)⁻¹ * (∫ x in s, ∑ i, ∑ j, f i j x) := by
    rw [setAverage_eq, smul_eq_mul]
  have h3 : ∀ i j, (⨍ x in s, f i j x) = (volume.real s)⁻¹ * (∫ x in s, f i j x) := fun i j => by
    rw [setAverage_eq, smul_eq_mul]
  rw [h2, h1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3]

lemma setAverage_abs_le_of_le {s : Set ℝ⁴} {f g : ℝ⁴ → ℝ} (hs : MeasurableSet s)
    (hf : IntegrableOn f s volume) (hg : IntegrableOn g s volume) (h : ∀ x ∈ s, ‖f x‖ ≤ g x) :
    (⨍ x in s, ‖f x‖) ≤ ⨍ x in s, g x :=
  setAverage_mono' hs hf.norm hg h


lemma setAverage_const_mul' {s : Set ℝ⁴} (c : ℝ) {f : ℝ⁴ → ℝ} :
    (⨍ x in s, c * f x) = c * ⨍ x in s, f x := by
  rw [setAverage_eq, setAverage_eq, integral_const_mul]
  ring

lemma setAverage_abs_add {s : Set ℝ⁴} {f g : ℝ⁴ → ℝ}
    (hf : IntegrableOn f s volume) (hg : IntegrableOn g s volume) :
    (⨍ x in s, (‖f x‖ + ‖g x‖)) = (⨍ x in s, ‖f x‖) + ⨍ x in s, ‖g x‖ := by
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_add hf.norm hg.norm]
  ring

lemma norm_moll_le (u : ℝ⁴ → ℝ) (hu : LocallyIntegrable u volume) {C : ℝ} (hC : 0 ≤ C)
    {y : ℝ⁴} (m : ℕ) (h1 : ∀ t ∈ closedBall y (bseq m).rOut, ‖u t‖ ≤ C) :
    ‖moll u m y‖ ≤ C := by
  have hK : Integrable (fun t : ℝ⁴ => (bseq m).normed volume (y - t)) volume :=
    ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id)
      |>.integrable_of_hasCompactSupport (hasCompactSupport_sub_const m y))
  have hmeq : moll u m y = ∫ t, u t * (bseq m).normed volume (y - t) := rfl
  rw [hmeq]
  calc ‖∫ t, u t * (bseq m).normed volume (y - t)‖
      ≤ ∫ t, C * (bseq m).normed volume (y - t) := by
        refine norm_integral_le_of_norm_le (hK.const_mul C) ?_
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bseq_normed_nonneg m _)]
        by_cases ht : (bseq m).normed volume (y - t) = 0
        · rw [ht, mul_zero, mul_zero]
        · refine mul_le_mul_of_nonneg_right (h1 t ?_) (bseq_normed_nonneg m _)
          rw [Metric.mem_closedBall, dist_eq_norm]
          have ht' : y - t ∈ tsupport ((bseq m).normed volume) :=
            subset_closure (Function.mem_support.mpr ht)
          rw [bseq_tsupport m, Metric.mem_closedBall, dist_zero_right] at ht'
          rwa [show y - t = -(t - y) by abel, norm_neg] at ht'
    _ = C := by rw [MeasureTheory.integral_const_mul, bseq_normed_integral_sub, mul_one]

lemma integrable_kernel_mul (G : ℝ⁴ → ℝ⁴) (hGli : LocallyIntegrable G volume) (m : ℕ)
    (x₀ : ℝ⁴) :
    Integrable (fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t) * ‖G t‖) volume := by
  have h1 : LocallyIntegrable (fun t : ℝ⁴ => ‖G t‖) volume :=
    hGli.mono hGli.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun t => by simp)
  have h2 := h1.integrable_smul_right_of_hasCompactSupport (μ := volume)
    (f := fun t : ℝ⁴ => ‖G t‖) (g := fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t))
    ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id))
    (hasCompactSupport_sub_const m x₀)
  simpa [smul_eq_mul, mul_comm] using h2


/-- If `|f x| ≤ |g x|` pointwise and `g` is integrable on `s`, then the average of `f` is bounded
by the average of `|g|`. -/
lemma setAverage_abs_le_setAverage_abs {s : Set ℝ⁴} {f g : ℝ⁴ → ℝ} (hs : MeasurableSet s)
    (hg : IntegrableOn g s volume) (h : ∀ x, |f x| ≤ |g x|) :
    |⨍ x in s, f x| ≤ ⨍ x in s, |g x| := by
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have hspos : 0 ≤ (volume.real s)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  calc |(volume.real s)⁻¹ * ∫ x in s, f x|
      = (volume.real s)⁻¹ * |∫ x in s, f x| := by rw [abs_mul, abs_of_nonneg hspos]
    _ ≤ (volume.real s)⁻¹ * ∫ x in s, |f x| := by
        refine mul_le_mul_of_nonneg_left ?_ hspos
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm f (μ := volume.restrict s)
    _ ≤ (volume.real s)⁻¹ * ∫ x in s, |g x| := by
        refine mul_le_mul_of_nonneg_left ?_ hspos
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hg.abs
          (Filter.Eventually.of_forall h)

theorem taylor_bound_aux
    (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (x₀ : ℝ⁴) (hs : IsOpen s) (hx₀ : x₀ ∈ s)
    (hcont : ContinuousOn u s) (hu : LocallyIntegrable u volume)
    (G : ℝ⁴ → ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴)
    (hGli : LocallyIntegrable G volume) (hMli : ∀ i j, LocallyIntegrable (M i j) volume)
    (hwg : HasWeakGradient u s G) (hwh : HasWeakHessian u s M σ)
    (hGleb : IsLebesguePointVec G x₀) (hMleb : ∀ i j, IsLebesguePoint (M i j) x₀)
    (hσvan : ∀ i j, IsVanishingPoint (σ i j).totalVariation x₀) :
    ∀ δ > 0, ∃ R > 0, ∀ r ∈ Set.Ioo 0 R, ∀ ψ : ℝ⁴ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.closedBall x₀ r → (∀ y, |ψ y| ≤ 1) →
      |⨍ y in Metric.ball x₀ r, ψ y * taylorRemainder u G M x₀ y| ≤ δ * r ^ 2 := by
  intro δ hδ
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  set ω : ℝ := (volume (ball (0:ℝ⁴) 1)).toReal with hω
  have hωpos : 0 < ω := by
    rw [hω]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set η : ℝ := δ * ω / 4096 with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hMev : ∀ᶠ s' in 𝓝[>] (0:ℝ), ∀ i j,
      (∫ w in ball x₀ s', |M i j w - M i j x₀|) ≤ η * s' ^ 4 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have h1 : ∀ᶠ r in 𝓝[>] (0:ℝ), (⨍ w in ball x₀ r, |M i j w - M i j x₀|) < η / ω :=
      (hMleb i j).eventually (eventually_lt_nhds (div_pos hηpos hωpos))
    filter_upwards [h1, self_mem_nhdsWithin] with r hr hrgt
    have hrp : 0 < r := hrgt
    have hvol : volume.real (ball x₀ r) = r ^ 4 * ω := by
      rw [Measure.real_def, hω, volume_real_ball_four x₀ hrp.le]
    have hvolne : volume.real (ball x₀ r) ≠ 0 := by rw [hvol]; positivity
    rw [← setAverage_mul_eq (f := fun w : ℝ⁴ => |M i j w - M i j x₀|) hvolne, hvol]
    calc (⨍ w in ball x₀ r, |M i j w - M i j x₀|) * (r ^ 4 * ω)
        ≤ (η / ω) * (r ^ 4 * ω) := by
          refine mul_le_mul_of_nonneg_right (le_of_lt hr) (by positivity)
      _ = η * r ^ 4 := by field_simp
  have hσev0 : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i j,
      ((σ i j).totalVariation (ball x₀ r)).toReal / r ^ 4 < η / 16 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact (hσvan i j).eventually (eventually_lt_nhds (div_pos hηpos (by norm_num)))
  have hσev : ∀ᶠ s' in 𝓝[>] (0:ℝ), ∀ i j,
      ((σ i j).totalVariation (closedBall x₀ s')).toReal ≤ η * s' ^ 4 := by
    have hcomp := Filter.Tendsto.eventually (two_mul_tendsto_nhdsGT 2 (by norm_num)) hσev0
    filter_upwards [hcomp, self_mem_nhdsWithin] with r hr hrgt
    intro i j
    have hrp : 0 < r := hrgt
    have hsub : closedBall x₀ r ⊆ ball x₀ (2 * r) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hmono : ((σ i j).totalVariation (closedBall x₀ r)).toReal
        ≤ ((σ i j).totalVariation (ball x₀ (2 * r))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    refine hmono.trans ?_
    have h2 : (2 * r) ^ 4 * (((σ i j).totalVariation (ball x₀ (2 * r))).toReal / (2 * r) ^ 4)
        = ((σ i j).totalVariation (ball x₀ (2 * r))).toReal := by
      field_simp
    rw [← h2]
    calc (2 * r) ^ 4 * (((σ i j).totalVariation (ball x₀ (2 * r))).toReal / (2 * r) ^ 4)
        ≤ (2 * r) ^ 4 * (η / 16) := mul_le_mul_of_nonneg_left (le_of_lt (hr i j)) (by positivity)
      _ = η * r ^ 4 := by ring


  -- boundedness of `u` near `x₀`
  obtain ⟨C₁, hC₁pos, hC₁⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ y ∈ closedBall x₀ (3 * ρ / 4), ‖u y‖ ≤ C₁ := by
    have hK : IsCompact (closedBall x₀ (3 * ρ / 4)) := isCompact_closedBall x₀ _
    have hsub : closedBall x₀ (3 * ρ / 4) ⊆ s := fun y hy =>
      hρsub (by rw [Metric.mem_ball]; exact lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith))
    obtain ⟨C, hC⟩ := isBounded_iff.mp (hK.image_of_continuousOn (hcont.mono hsub)).isBounded
    exact ⟨max C 1 + ‖u x₀‖, by positivity, fun y hy => by
      have h1 := hC (x := u y) ⟨y, hy, rfl⟩ (y := u x₀)
        ⟨x₀, mem_closedBall_self (by linarith), rfl⟩
      rw [dist_eq_norm] at h1
      calc ‖u y‖ = ‖u y - u x₀ + u x₀‖ := by ring_nf
        _ ≤ ‖u y - u x₀‖ + ‖u x₀‖ := norm_add_le _ _
        _ ≤ C + ‖u x₀‖ := by linarith
        _ ≤ max C 1 + ‖u x₀‖ := by linarith [le_max_left C 1]⟩
  have hG1 : ∀ᶠ s' in 𝓝[>] (0:ℝ), (⨍ w in ball x₀ s', ‖G w - G x₀‖) < 1 :=
    hGleb.eventually (eventually_lt_nhds zero_lt_one)
  obtain ⟨RG, hRGpos, hRG⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hG1
  obtain ⟨Ra, hRapos, hRa⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hMev
  obtain ⟨Rb, hRbpos, hRb⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hσev
  set εm : ℝ := min (min (Ra / 4) (min (Rb / 4) (ρ / 2))) (min (RG / 4) (1 / 2)) with hεm
  have hεmRa : εm ≤ Ra / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεmRb : εm ≤ Rb / 4 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεmρ : εm ≤ ρ / 2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεmRG : εm ≤ RG / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεm1 : εm ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hεmpos : 0 < εm := by
    rw [hεm]
    exact lt_min (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
      (lt_min (by linarith) (by norm_num))
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, (bseq m).rOut ≤ εm :=
    (Filter.eventually_atTop.mp (bseq_tendsto_rOut.eventually (eventually_lt_nhds hεmpos))).imp
      (fun m hm => fun k hk => le_of_lt (hm k hk))
  refine ⟨min (min (Ra / 4) (Rb / 4)) (ρ / 4), by
      exact lt_min (lt_min (by linarith) (by linarith)) (by linarith), ?_⟩
  intro r hr ψ hψcd hψsupp hψbd
  rw [Set.mem_Ioo] at hr
  obtain ⟨hrpos, hrR⟩ := hr
  have hrRa : r < Ra / 4 := lt_of_lt_of_le hrR (le_trans (min_le_left _ _) (min_le_left _ _))
  have hrRb : r < Rb / 4 := lt_of_lt_of_le hrR (le_trans (min_le_left _ _) (min_le_right _ _))
  have hrρ : r < ρ / 4 := lt_of_lt_of_le hrR (min_le_right _ _)

  set M₀ : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ := (2:ℝ) • quadM M x₀ with hM₀
  have hhalf : ∀ y : ℝ⁴, (1/2 : ℝ) * M₀ (y - x₀) (y - x₀) = quadM M x₀ (y - x₀) (y - x₀) := by
    intro y
    rw [hM₀]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- ## the pointwise convergence of the integrand
  have hpt : ∀ y ∈ Metric.ball x₀ r,
      Tendsto (fun m => ψ y * (moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
        + quadM M x₀ (y - x₀) (y - x₀)))) atTop
      (𝓝 (ψ y * taylorRemainder u G M x₀ y)) := by
    intro y hy
    have hyρ : y ∈ s := by
      rw [Metric.mem_ball] at hy
      exact hρsub (by rw [Metric.mem_ball]; linarith)
    have h1 := moll_tendsto_pointwise u hu hs hcont hyρ
    have h2 := moll_tendsto_pointwise u hu hs hcont hx₀
    have h3 : Tendsto (fun m => (fderiv ℝ (moll u m) x₀) (y - x₀)) atTop
        (𝓝 ((innerSL ℝ (G x₀)) (y - x₀))) := by
      have h := fderiv_moll_tendsto u hu hs hGli hwg hx₀ hGleb (y - x₀)
      simpa using h
    have h4 : Tendsto (fun m => moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
        + quadM M x₀ (y - x₀) (y - x₀))) atTop
        (𝓝 (u y - (u x₀ + (innerSL ℝ (G x₀)) (y - x₀) + quadM M x₀ (y - x₀) (y - x₀)))) :=
      h1.sub ((h2.add h3).add tendsto_const_nhds)
    have h5goal : ψ y * (u y - (u x₀ + (innerSL ℝ (G x₀)) (y - x₀)
        + quadM M x₀ (y - x₀) (y - x₀))) = ψ y * taylorRemainder u G M x₀ y := by
      rw [taylorRemainder_eq]
      ring
    rw [← h5goal]
    exact h4.const_mul (ψ y)
  -- ## the uniform bound on the kernel average of `‖G‖`
  have hkerG : ∀ m ≥ m₀, ∫ t, (bseq m).normed volume (x₀ - t) * ‖G t‖ ≤ 256 + 256 * ‖G x₀‖ := by
    intro m hm
    have hεle : (bseq m).rOut ≤ εm := hm₀ m hm
    have hεpos : 0 < (bseq m).rOut := bseq_rOut_pos m
    have hnorm : LocallyIntegrable (fun t : ℝ⁴ => ‖G t - G x₀‖) volume := by
      have hGl : LocallyIntegrable (fun t : ℝ⁴ => G t - G x₀) volume :=
        hGli.sub (locallyIntegrable_const (G x₀))
      exact hGl.mono hGl.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun t => by simp)
    have hgLoc : LocallyIntegrable (fun t : ℝ⁴ => ‖G t - G x₀‖ + ‖G x₀‖) volume :=
      hnorm.add (locallyIntegrable_const _)
    have hgi : Integrable
        (fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t) * (‖G t - G x₀‖ + ‖G x₀‖)) volume := by
      have h2 := hgLoc.integrable_smul_right_of_hasCompactSupport (μ := volume)
        (f := fun t : ℝ⁴ => ‖G t - G x₀‖ + ‖G x₀‖)
        (g := fun t : ℝ⁴ => (bseq m).normed volume (x₀ - t))
        ((bseq m).continuous_normed.comp (continuous_const.sub continuous_id))
        (hasCompactSupport_sub_const m x₀)
      simpa [smul_eq_mul, mul_comm] using h2
    have hmono : (∫ t, (bseq m).normed volume (x₀ - t) * ‖G t‖)
        ≤ ∫ t, (bseq m).normed volume (x₀ - t) * (‖G t - G x₀‖ + ‖G x₀‖) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
        mul_nonneg (bseq_normed_nonneg m _) (norm_nonneg _)) hgi
        (Filter.Eventually.of_forall fun t => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (bseq_normed_nonneg m _)
      calc ‖G t‖ = ‖(G t - G x₀) + G x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖G t - G x₀‖ + ‖G x₀‖ := norm_add_le _ _
    refine hmono.trans ?_
    have hint1 : IntegrableOn (fun t : ℝ⁴ => ‖G t - G x₀‖) (ball x₀ (2 * (bseq m).rOut)) volume :=
      (hnorm.integrableOn_isCompact
        (isCompact_closedBall x₀ (2 * (bseq m).rOut))).mono_set ball_subset_closedBall
    have hint : IntegrableOn (fun t : ℝ⁴ => ‖G t - G x₀‖ + ‖G x₀‖)
        (ball x₀ (2 * (bseq m).rOut)) volume :=
      hint1.add (integrableOn_const measure_ball_lt_top.ne)
    have hCb := kernel_integral_le_ball (k := (bseq m).normed volume)
      (h := fun t : ℝ⁴ => ‖G t - G x₀‖ + ‖G x₀‖) (x₀ := x₀) (ε := (bseq m).rOut)
      (C := 16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4))
      (bseq_normed_nonneg m) (fun t => bseq_normed_bound m t) (by positivity) hεpos
      (fun t ht => by rw [← bseq_tsupport m]; exact subset_closure (Function.mem_support.mpr ht))
      (fun t => by positivity) hint
    refine hCb.trans ?_
    have hvol : volume.real (ball x₀ (2 * (bseq m).rOut))
        = (2 * (bseq m).rOut) ^ 4 * ω := by
      rw [Measure.real_def, hω, volume_real_ball_four x₀ (by positivity)]
    have hvolne : volume.real (ball x₀ (2 * (bseq m).rOut)) ≠ 0 := by rw [hvol]; positivity
    have hAvg : (∫ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖)
        = (2 * (bseq m).rOut) ^ 4 * ω * (⨍ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖) := by
      rw [← hvol]
      exact (setAverage_mul_eq (f := fun t : ℝ⁴ => ‖G t - G x₀‖) hvolne).symm.trans (mul_comm _ _)
    have hConstInt : IntegrableOn (fun _ : ℝ⁴ => ‖G x₀‖) (ball x₀ (2 * (bseq m).rOut)) volume :=
      integrableOn_const measure_ball_lt_top.ne
    have hConst : (∫ t in ball x₀ (2 * (bseq m).rOut), ‖G x₀‖)
        = ‖G x₀‖ * ((2 * (bseq m).rOut) ^ 4 * ω) := by
      rw [MeasureTheory.integral_const, smul_eq_mul, Measure.real_def,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, ← hvol, mul_comm,
        Measure.real_def]
    have hAvgLe : (⨍ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖) ≤ 1 := by
      have h2 : 2 * (bseq m).rOut ∈ Set.Ioo (0:ℝ) RG :=
        ⟨by positivity, by linarith [hεmRG, hεle, hRGpos]⟩
      exact le_of_lt (hRG h2)
    have hsplit : (∫ t in ball x₀ (2 * (bseq m).rOut), (‖G t - G x₀‖ + ‖G x₀‖))
        = (2 * (bseq m).rOut) ^ 4 * ω * (⨍ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖)
          + ‖G x₀‖ * ((2 * (bseq m).rOut) ^ 4 * ω) := by
      rw [integral_add (hint1) hConstInt, hAvg, hConst]
    rw [hsplit]
    have hval : 16 / ((volume.real (ball (0:ℝ⁴) 1)) * (bseq m).rOut ^ 4)
        * ((2 * (bseq m).rOut) ^ 4 * ω
            * (⨍ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖)
          + ‖G x₀‖ * ((2 * (bseq m).rOut) ^ 4 * ω))
        = 256 * (⨍ t in ball x₀ (2 * (bseq m).rOut), ‖G t - G x₀‖) + 256 * ‖G x₀‖ := by
      have hvr : volume.real (ball (0:ℝ⁴) 1) = ω := by rw [Measure.real_def, ← hω]
      rw [hvr]
      field_simp
      ring
    rw [hval]
    linarith [hAvgLe]
  have hderm : ∀ m ≥ m₀, ∀ v : ℝ⁴, ‖v‖ ≤ r →
      ‖(fderiv ℝ (moll u m) x₀) v‖ ≤ (256 + 256 * ‖G x₀‖) * r := by
    intro m hm v hv
    have hεle : (bseq m).rOut ≤ εm := hm₀ m hm
    have hερ : (bseq m).rOut < ρ := by linarith [hεmρ, hεle, hrpos]
    have hsupp : ∀ z ∈ tsupport ((bseq m).normed volume), (x₀ - z) ∈ s := by
      intro z hz
      rw [bseq_tsupport m, Metric.mem_closedBall, dist_zero_right] at hz
      refine hρsub (by
        rw [Metric.mem_ball, dist_eq_norm, show x₀ - z - x₀ = -z by abel, norm_neg]
        exact lt_of_le_of_lt hz hερ)
    have hform : (fderiv ℝ (moll u m) x₀) v
        = ∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫ := by
      have h := Commons.Analysis.Convolution.fderiv_moll_weakGrad ((bseq m).normed volume) u G s x₀
        ((bseq m).contDiff_normed (μ := volume) (n := ⊤)) ((bseq m).hasCompactSupport_normed)
        hu hGli hsupp hwg v
      rw [show moll u m = (fun y : ℝ⁴ => ∫ t, u t * (bseq m).normed volume (y - t)) from rfl]
      exact h
    rw [hform]
    calc ‖∫ t, (bseq m).normed volume (x₀ - t) * ⟪G t, v⟫‖
        ≤ ∫ t, (bseq m).normed volume (x₀ - t) * ‖G t‖ * ‖v‖ := by
          refine (abs_integral_le_integral_abs).trans ?_
          refine integral_mono_of_nonneg ?_ ?_ ?_
          · exact Filter.Eventually.of_forall fun t => abs_nonneg _
          · exact (integrable_kernel_mul G hGli m x₀).mul_const _
          · filter_upwards with t
            rw [abs_mul, abs_of_nonneg (bseq_normed_nonneg m _)]
            have h2 : |⟪G t, v⟫| ≤ ‖G t‖ * ‖v‖ := by
              rw [← Real.norm_eq_abs]
              exact norm_inner_le_norm (G t) v
            calc (bseq m).normed volume (x₀ - t) * |⟪G t, v⟫|
                ≤ (bseq m).normed volume (x₀ - t) * (‖G t‖ * ‖v‖) :=
                  mul_le_mul_of_nonneg_left h2 (bseq_normed_nonneg m _)
              _ = (bseq m).normed volume (x₀ - t) * ‖G t‖ * ‖v‖ := by ring
      _ = (∫ t, (bseq m).normed volume (x₀ - t) * ‖G t‖) * ‖v‖ := by
          rw [MeasureTheory.integral_mul_const]
      _ ≤ (256 + 256 * ‖G x₀‖) * r := by
          have hnn : 0 ≤ ∫ t, (bseq m).normed volume (x₀ - t) * ‖G t‖ := by
            refine integral_nonneg fun t => ?_
            exact mul_nonneg (bseq_normed_nonneg m _) (norm_nonneg _)
          nlinarith [hkerG m hm, hv, hnn]
  -- ## the uniform domination
  have hbdd : ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ r)), ∀ m ≥ m₀,
      ‖ψ y * (moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
        + quadM M x₀ (y - x₀) (y - x₀)))‖
        ≤ 2 * C₁ + (256 + 256 * ‖G x₀‖) * r + ‖quadM M x₀‖ * r ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with y hy
    intro m hm
    have hεle : (bseq m).rOut ≤ εm := hm₀ m hm
    have hyball : ‖y - x₀‖ ≤ r := by
      rw [Metric.mem_ball, dist_eq_norm] at hy; exact le_of_lt hy
    -- bound on `u`
    have huy : ‖u y‖ ≤ C₁ := by
      refine hC₁ y ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith [hεmρ, hεle]
    have hux : ‖u x₀‖ ≤ C₁ := hC₁ x₀ (mem_closedBall_self (by linarith))
    -- bound on the mollification at `y`
    have hmoll : ‖moll u m y‖ ≤ C₁ := by
      refine norm_moll_le u hu hC₁pos.le m ?_
      intro t ht
      refine hC₁ t ?_
      rw [Metric.mem_closedBall, dist_eq_norm] at ht ⊢
      calc ‖t - x₀‖ ≤ ‖t - y‖ + ‖y - x₀‖ := by
            rw [show t - x₀ = (t - y) + (y - x₀) by abel]
            exact norm_add_le _ _
        _ ≤ (bseq m).rOut + r := by linarith [ht, hyball]
        _ ≤ 3 * ρ / 4 := by linarith [hεmρ, hεle, hrρ]
    have hquad : ‖quadM M x₀ (y - x₀) (y - x₀)‖ ≤ ‖quadM M x₀‖ * r ^ 2 := by
      calc ‖quadM M x₀ (y - x₀) (y - x₀)‖ ≤ ‖quadM M x₀ (y - x₀)‖ * ‖y - x₀‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖quadM M x₀‖ * ‖y - x₀‖) * ‖y - x₀‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = ‖quadM M x₀‖ * ‖y - x₀‖ ^ 2 := by ring
        _ ≤ ‖quadM M x₀‖ * r ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (quadM M x₀))
            nlinarith [hyball, norm_nonneg (y - x₀)]
    calc ‖ψ y * (moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
          + quadM M x₀ (y - x₀) (y - x₀)))‖
        = |ψ y| * ‖moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
            + quadM M x₀ (y - x₀) (y - x₀))‖ := by rw [norm_mul, Real.norm_eq_abs]
      _ ≤ ‖moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
            + quadM M x₀ (y - x₀) (y - x₀))‖ := by
          refine mul_le_of_le_one_left (norm_nonneg _) (hψbd y)
      _ ≤ ‖moll u m y‖ + (‖moll u m x₀‖ + ‖(fderiv ℝ (moll u m) x₀) (y - x₀)‖)
            + ‖quadM M x₀ (y - x₀) (y - x₀)‖ := by
          calc ‖moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)
                + quadM M x₀ (y - x₀) (y - x₀))‖
              = ‖(moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)))
                  - quadM M x₀ (y - x₀) (y - x₀)‖ := by congr 1; abel
            _ ≤ ‖moll u m y - (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀))‖
                  + ‖quadM M x₀ (y - x₀) (y - x₀)‖ := norm_sub_le _ _
            _ ≤ (‖moll u m y‖ + ‖moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀)‖)
                  + ‖quadM M x₀ (y - x₀) (y - x₀)‖ :=
                add_le_add (norm_sub_le _ _) (le_refl _)
            _ ≤ (‖moll u m y‖ + (‖moll u m x₀‖ + ‖(fderiv ℝ (moll u m) x₀) (y - x₀)‖))
                  + ‖quadM M x₀ (y - x₀) (y - x₀)‖ :=
                add_le_add (add_le_add (le_refl _) (norm_add_le _ _)) (le_refl _)
            _ = ‖moll u m y‖ + (‖moll u m x₀‖ + ‖(fderiv ℝ (moll u m) x₀) (y - x₀)‖)
                  + ‖quadM M x₀ (y - x₀) (y - x₀)‖ := by ring
      _ ≤ 2 * C₁ + (256 + 256 * ‖G x₀‖) * r + ‖quadM M x₀‖ * r ^ 2 := by
          have hmx : ‖moll u m x₀‖ ≤ C₁ := by
            refine norm_moll_le u hu hC₁pos.le m ?_
            intro t ht
            refine hC₁ t ?_
            rw [Metric.mem_closedBall, dist_eq_norm] at ht ⊢
            calc ‖t - x₀‖ ≤ (bseq m).rOut := ht
              _ ≤ 3 * ρ / 4 := by linarith [hεmρ, hεle, hrρ]
          have hder := hderm m hm (y - x₀) hyball
          have hnnr : 0 ≤ r := le_of_lt hrpos
          linarith [hmoll, hmx, hder, hquad]
  -- ## the convergence of `Ffun`
  have hconv_int : Tendsto (fun m => ∫ y in Metric.ball x₀ r, ψ y * (moll u m y -
      (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀) + quadM M x₀ (y - x₀) (y - x₀)))) atTop
      (𝓝 (∫ y in Metric.ball x₀ r, ψ y * taylorRemainder u G M x₀ y)) := by
    have hbdd' : ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict (Metric.ball x₀ r)),
        ‖ψ y * (moll u (n + m₀) y - (moll u (n + m₀) x₀
          + (fderiv ℝ (moll u (n + m₀)) x₀) (y - x₀)
          + quadM M x₀ (y - x₀) (y - x₀)))‖
          ≤ 2 * C₁ + (256 + 256 * ‖G x₀‖) * r + ‖quadM M x₀‖ * r ^ 2 :=
      fun n => hbdd.mono fun y hy => hy (n + m₀) (Nat.le_add_left m₀ n)
    have hcont_int : ∀ n : ℕ, Continuous (fun y : ℝ⁴ => ψ y * (moll u (n + m₀) y -
        (moll u (n + m₀) x₀ + (fderiv ℝ (moll u (n + m₀)) x₀) (y - x₀)
          + quadM M x₀ (y - x₀) (y - x₀)))) := by
      intro n
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (moll u (n + m₀)) := contDiff_moll_top u hu (n + m₀)
      have hA : Continuous (fun y : ℝ⁴ => moll u (n + m₀) y) := hcd.continuous
      have hB : Continuous (fun _ : ℝ⁴ => moll u (n + m₀) x₀) := continuous_const
      have hC : Continuous (fun y : ℝ⁴ => (fderiv ℝ (moll u (n + m₀)) x₀) (y - x₀)) :=
        (continuous_const : Continuous (fun _ : ℝ⁴ =>
          (fderiv ℝ (moll u (n + m₀)) x₀))).clm_apply (continuous_id.sub continuous_const)
      have hD : Continuous (fun y : ℝ⁴ => quadM M x₀ (y - x₀) (y - x₀)) :=
        ((quadM M x₀).continuous.comp (continuous_id.sub continuous_const)).clm_apply
          (continuous_id.sub continuous_const)
      have hψc : Continuous (fun y : ℝ⁴ => ψ y) := hψcd.continuous
      exact hψc.mul (hA.sub ((hB.add hC).add hD))
    have hlim := tendsto_integral_of_dominated_convergence
      (fun _ : ℝ⁴ => 2 * C₁ + (256 + 256 * ‖G x₀‖) * r + ‖quadM M x₀‖ * r ^ 2)
      (fun n => (hcont_int n).aestronglyMeasurable)
      (integrableOn_const measure_ball_lt_top.ne) hbdd'
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with y hy
        exact (hpt y hy).comp (tendsto_add_atTop_nat m₀))
    exact (Filter.tendsto_add_atTop_iff_nat m₀).mp hlim
  have hconv : Tendsto (fun m => ⨍ y in Metric.ball x₀ r, ψ y * (moll u m y -
      (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀) + quadM M x₀ (y - x₀) (y - x₀)))) atTop
      (𝓝 (⨍ y in Metric.ball x₀ r, ψ y * taylorRemainder u G M x₀ y)) := by
    have h := hconv_int.const_smul ((volume.real (Metric.ball x₀ r))⁻¹)
    simpa only [setAverage_eq] using h
  -- ## the uniform bound on the Taylor identity
  have hbd : ∀ m ≥ m₀, |⨍ y in Metric.ball x₀ r, ψ y * (moll u m y -
      (moll u m x₀ + (fderiv ℝ (moll u m) x₀) (y - x₀) + quadM M x₀ (y - x₀) (y - x₀)))|
      ≤ δ * r ^ 2 := by
    intro m hm
    set U : ℝ⁴ → ℝ := moll u m with hU
    set kk : ℝ⁴ → ℝ := (bseq m).normed volume with hkk
    set ε : ℝ := (bseq m).rOut with hε
    have hUcd : ContDiff ℝ (⊤ : ℕ∞) U := by rw [hU]; exact contDiff_moll_top u hu m
    have hU1c : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ U) := contDiff_infty_iff_fderiv.mp hUcd |>.2
    have hU2c : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ U)) :=
      contDiff_infty_iff_fderiv.mp hU1c |>.2
    have hAccont : Continuous (fun z : ℝ⁴ => fderiv ℝ (fderiv ℝ U) (x₀ + z)) :=
      hU2c.continuous.comp (continuous_const.add continuous_id)
    have hQcont : Continuous (fun z : ℝ⁴ => ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)) :=
      ((hAccont.sub continuous_const).clm_apply continuous_id).clm_apply continuous_id
    have hAzcont : ∀ (i j : Fin 4), Continuous (fun z : ℝ⁴ =>
        (fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀) := by
      intro i j
      exact ((hAccont.clm_apply continuous_const).clm_apply continuous_const).sub
        continuous_const
    have hεpos : 0 < ε := by rw [hε]; exact bseq_rOut_pos m
    have hεle : ε ≤ εm := by rw [hε]; exact hm₀ m hm
    have hεRa4 : ε ≤ Ra / 4 := by linarith [hεle, hεmRa]
    have hεRb4 : ε ≤ Rb / 4 := by linarith [hεle, hεmRb]
    have hkcont : Continuous kk := by rw [hkk]; exact (bseq m).continuous_normed
    have hkcd : ContDiff ℝ (⊤ : ℕ∞) kk := by
      rw [hkk]; exact (bseq m).contDiff_normed (μ := volume) (n := ⊤)
    have hkcs : HasCompactSupport kk := by rw [hkk]; exact (bseq m).hasCompactSupport_normed
    have hknonneg : ∀ t, 0 ≤ kk t := by intro t; rw [hkk]; exact bseq_normed_nonneg m t
    have hkbound : ∀ t, kk t ≤ 16 / (volume.real (ball (0:ℝ⁴) 1) * ε ^ 4) := by
      intro t; rw [hkk, hε]; exact bseq_normed_bound m t
    have hksupp : ∀ t, kk t ≠ 0 → t ∈ closedBall (0:ℝ⁴) ε := by
      intro t ht
      have ht' : (bseq m).normed volume t ≠ 0 := by rw [← hkk]; exact ht
      have h1 : t ∈ tsupport ((bseq m).normed volume) :=
        subset_closure (Function.mem_support.mpr ht')
      rw [bseq_tsupport m] at h1
      rwa [hε]
    have hkscs : ∀ y : ℝ⁴, HasCompactSupport (fun t : ℝ⁴ => kk (y - t)) := by
      intro y; rw [hkk]; exact hasCompactSupport_sub_const m y
    -- ## the pointwise identity for the second derivative of the mollification
    have hidentpt : ∀ (i j : Fin 4) (z : ℝ⁴),
        (∀ τ ∈ tsupport kk, (x₀ + z) - τ ∈ s) →
        (fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀
          = (∫ τ, kk (x₀ + z - τ) * (M i j τ - M i j x₀))
            + (∫ᵛ τ, kk (x₀ + z - τ) ∂•(σ i j)) := by
      intro i j z hsupp
      have h := fderiv_fderiv_moll_eq kk u M σ s (x₀ + z) i j hkcd hkcs hsupp hu hwh
      rw [show (fun y : ℝ⁴ => ∫ s, u s * kk (y - s) ∂volume) = U from by rw [hU, hkk]; rfl] at h
      rw [h]
      have hcont' : Continuous (fun τ : ℝ⁴ => kk (x₀ + z - τ)) :=
        hkcont.comp (continuous_const.sub continuous_id)
      have hAint : Integrable (fun τ : ℝ⁴ => kk (x₀ + z - τ) * M i j τ) volume := by
        simpa only [smul_eq_mul, mul_comm] using
          (hMli i j).integrable_smul_right_of_hasCompactSupport hcont' (hkscs (x₀ + z))
      have hBint : Integrable (fun τ : ℝ⁴ => kk (x₀ + z - τ) * M i j x₀) volume := by
        have hK : Integrable (fun τ : ℝ⁴ => kk (x₀ + z - τ)) volume :=
          hcont'.integrable_of_hasCompactSupport (hkscs (x₀ + z))
        simpa only [mul_comm] using hK.const_mul (M i j x₀)
      have hInt : (∫ τ, kk (x₀ + z - τ) * (M i j τ - M i j x₀))
          = (∫ τ, kk (x₀ + z - τ) * M i j τ) - M i j x₀ := by
        rw [show (∫ τ, kk (x₀ + z - τ) * (M i j τ - M i j x₀))
              = ∫ τ, (kk (x₀ + z - τ) * M i j τ - kk (x₀ + z - τ) * M i j x₀) from
            integral_congr_ae (Filter.Eventually.of_forall fun τ => by ring)]
        rw [integral_sub hAint hBint]
        rw [MeasureTheory.integral_mul_const]
        have h1 : (∫ τ : ℝ⁴, kk (x₀ + z - τ)) = 1 := by
          rw [hkk]; exact bseq_normed_integral_sub m (x₀ + z)
        rw [h1, one_mul]
      rw [hInt]
      ring


    -- ## the average of the coordinate second derivatives
    have hAz : ∀ (i j : Fin 4) {a : ℝ}, 0 < a → a ≤ r → a + ε ≤ min (Ra / 2) (Rb / 2) →
        (⨍ z in Metric.ball (0:ℝ⁴) a,
          |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀|)
          ≤ 512 * η / ω := by
      intro i j a ha har haR
      have hsupp : ∀ z ∈ Metric.ball (0:ℝ⁴) a, ∀ τ ∈ tsupport kk, (x₀ + z) - τ ∈ s := by
        intro z hz τ hτ
        have hz' : ‖z‖ < a := by rwa [Metric.mem_ball, dist_zero_right] at hz
        have hτ' : ‖τ‖ ≤ ε := by
          have h1 : τ ∈ tsupport ((bseq m).normed volume) := by rwa [hkk] at hτ
          rw [bseq_tsupport m, Metric.mem_closedBall, dist_zero_right] at h1
          rw [hε]
          exact h1
        refine hρsub ?_
        rw [Metric.mem_ball, dist_eq_norm]
        rw [show (x₀ + z) - τ - x₀ = z - τ by abel]
        calc ‖z - τ‖ ≤ ‖z‖ + ‖τ‖ := norm_sub_le _ _
          _ < ρ := by linarith [hz', hτ', har, hrρ, hεle, hεmρ]
      have heq : (⨍ z in Metric.ball (0:ℝ⁴) a,
            |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀|)
          = (⨍ z in Metric.ball (0:ℝ⁴) a,
            |(∫ τ, kk (x₀ + z - τ) * (M i j τ - M i j x₀))
              + (∫ᵛ τ, kk (x₀ + z - τ) ∂•(σ i j))|) := by
        apply setAverage_congr_fun measurableSet_ball
        filter_upwards with z hz
        congr 1
        exact hidentpt i j z (hsupp z hz)
      rw [heq]
      refine (Commons.Measure.Kernel.setAverage_abs_integral_mul_kernel_add_pairing_le
        (n := 4) (k := kk) (f := fun τ : ℝ⁴ => M i j τ - M i j x₀) (x₀ := x₀)
        (ε := ε) (C := 16 / (volume.real (ball (0:ℝ⁴) 1) * ε ^ 4))
        (R := min (Ra / 2) (Rb / 2)) (E₀ := η)
        hknonneg hkbound (by positivity) hεpos (by positivity)
        (le_min (by linarith [hεle, hεmRa]) (by linarith [hεle, hεmRb])) hksupp
        ((hMli i j).sub (locallyIntegrable_const (M i j x₀))) (le_of_lt hηpos)
        (fun s' hs' => hRa ⟨hs'.1, lt_of_le_of_lt hs'.2
          (lt_of_le_of_lt (min_le_left _ _) (by linarith [hRapos]))⟩ i j)
        (σ i j)
        (fun s' hs' => hRb ⟨hs'.1, lt_of_le_of_lt hs'.2
          (lt_of_le_of_lt (min_le_right _ _) (by linarith [hRbpos]))⟩ i j)
        ha haR).trans (le_of_eq ?_)
      have hvr : volume.real (ball (0:ℝ⁴) 1) = ω := by rw [Measure.real_def, ← hω]
      rw [hvr]
      field_simp
      ring

    -- ## the Taylor identity
    have hU2 : ContDiff ℝ 2 U := hUcd.of_le (WithTop.coe_le_coe.mpr le_top)
    have hTay := Commons.Analysis.Calculus.Taylor.setAverage_taylor_two (n := 4) (U := U)
      (x₀ := x₀) (M₀ := M₀) (ψ := ψ) (r := r) hrpos hU2 hψcd
    have hFlhs : (⨍ y in Metric.ball x₀ r, ψ y * (U y -
        (U x₀ + (fderiv ℝ U x₀) (y - x₀) + quadM M x₀ (y - x₀) (y - x₀))))
        = (⨍ y in Metric.ball x₀ r, ψ y * (U y - U x₀ - (fderiv ℝ U x₀) (y - x₀)
            - (1/2 : ℝ) * M₀ (y - x₀) (y - x₀))) := by
      apply setAverage_congr_fun measurableSet_ball
      filter_upwards with y hy
      congr 1
      rw [hhalf y]
      ring
    rw [hFlhs, hTay]
    -- ## the pointwise bound on the inner average
    have hGm : ∀ t ∈ Set.Ioc (0:ℝ) 1,
        |⨍ z in Metric.ball (0:ℝ⁴) (t * r), ψ (x₀ + t⁻¹ • z) *
            ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)|
          ≤ (t * r) ^ 2 * (8192 * η / ω) := by
      intro t ht
      obtain ⟨htpos, htle⟩ := ht
      have htr : 0 < t * r := mul_pos htpos hrpos
      have htrr : t * r ≤ r := by
        calc t * r ≤ 1 * r := mul_le_mul_of_nonneg_right htle (le_of_lt hrpos)
          _ = r := one_mul r
      have hAR : t * r + ε ≤ min (Ra / 2) (Rb / 2) :=
        le_min (by linarith [htrr, hrRa, hεRa4]) (by linarith [htrr, hrRb, hεRb4])
      have hAzij : ∀ i j : Fin 4, (⨍ z in Metric.ball (0:ℝ⁴) (t * r),
          |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀|)
          ≤ 512 * η / ω :=
        fun i j => hAz i j htr htrr hAR
      have hAzint : ∀ (i j : Fin 4), IntegrableOn (fun z : ℝ⁴ =>
          |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀|)
          (Metric.ball (0 : ℝ⁴) (t * r)) volume := by
        intro i j
        exact ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
          ((hAzcont i j).abs).continuousOn |>.mono_set Metric.ball_subset_closedBall
      have hQint : IntegrableOn (fun z : ℝ⁴ =>
          ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))
          (Metric.ball (0 : ℝ⁴) (t * r)) volume :=
        ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
          hQcont.continuousOn |>.mono_set Metric.ball_subset_closedBall
      have hQint' : IntegrableOn (fun z : ℝ⁴ =>
          |((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)|)
          (Metric.ball (0 : ℝ⁴) (t * r)) volume :=
        hQint.abs
      have hBigcont : Continuous (fun z : ℝ⁴ => (t * r) ^ 2 * ∑ i, ∑ j,
          |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀|) :=
        continuous_const.mul (continuous_finsetSum _ fun i _ =>
          continuous_finsetSum _ fun j _ => (hAzcont i j).abs)
      have hBigint : IntegrableOn (fun z : ℝ⁴ => (t * r) ^ 2 * ∑ i, ∑ j,
          |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀|)
          (Metric.ball (0 : ℝ⁴) (t * r)) volume :=
        ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
          hBigcont.continuousOn |>.mono_set Metric.ball_subset_closedBall
      have hptb : ∀ z ∈ Metric.ball (0:ℝ⁴) (t * r),
          |((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)|
            ≤ (t * r) ^ 2 * ∑ i, ∑ j,
                |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀| := by
        intro z hz
        have hzn : ‖z‖ ≤ t * r := by
          rw [Metric.mem_ball, dist_zero_right] at hz; exact le_of_lt hz
        have hQ := hess_sub_eq_sum (fderiv ℝ (fderiv ℝ U) (x₀ + z)) M x₀ z
        rw [show M₀ = (2:ℝ) • quadM M x₀ from hM₀, hQ]
        calc |∑ i, ∑ j, (z i * z j) *
              ((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀)|
            ≤ ∑ i, |∑ j, (z i * z j) *
                ((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, |(z i * z j) *
                ((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀)| := by
              refine Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ‖z‖ ^ 2 * |((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i)
                (stdE j) - M i j x₀)| := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul, abs_mul]
              have h1 : |z i| ≤ ‖z‖ := by
                rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le z i
              have h2 : |z j| ≤ ‖z‖ := by
                rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le z j
              calc |z i| * |z j| * |((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i)
                    (stdE j) - M i j x₀)|
                  ≤ (‖z‖ * ‖z‖) * |((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i)
                    (stdE j) - M i j x₀)| := by
                    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
                    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
                _ = ‖z‖ ^ 2 * |((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i)
                    (stdE j) - M i j x₀)| := by ring
          _ = ‖z‖ ^ 2 * ∑ i, ∑ j, |((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i)
                (stdE j) - M i j x₀)| := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
          _ ≤ (t * r) ^ 2 * ∑ i, ∑ j, |((fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i)
                (stdE j) - M i j x₀)| :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzn 2)
                (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      calc |⨍ z in Metric.ball (0:ℝ⁴) (t*r), ψ (x₀ + t⁻¹•z) *
            ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)|
          ≤ ⨍ z in Metric.ball (0:ℝ⁴) (t*r),
              |((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)| := by
            apply setAverage_abs_le_setAverage_abs measurableSet_ball hQint
            intro z
            rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) (hψbd _)
        _ ≤ ⨍ z in Metric.ball (0:ℝ⁴) (t*r), (t*r)^2 * ∑ i, ∑ j,
              |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀| :=
            setAverage_mono' measurableSet_ball hQint' hBigint hptb
        _ = (t*r)^2 * ⨍ z in Metric.ball (0:ℝ⁴) (t*r), ∑ i, ∑ j,
              |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀| :=
            setAverage_const_mul' _ 
        _ = (t*r)^2 * ∑ i, ∑ j, ⨍ z in Metric.ball (0:ℝ⁴) (t*r),
              |(fderiv ℝ (fderiv ℝ U) (x₀ + z)) (stdE i) (stdE j) - M i j x₀| := by
            rw [setAverage_sum_four hAzint]
        _ ≤ (t*r)^2 * ∑ i, ∑ j, (512 * η / ω) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hAzij i j
        _ = (t*r)^2 * (8192 * η / ω) := by
            congr 1
            rw [Finset.sum_const, Finset.sum_const]
            simp
            ring
    -- ## the conclusion
    have hptI : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0:ℝ) 1 →
        ‖(1 - t) / t ^ 2 * (⨍ z in Metric.ball (0:ℝ⁴) (t * r), ψ (x₀ + t⁻¹ • z) *
          ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))‖
        ≤ (r ^ 2 * (8192 * η / ω)) * (1 - t) := by
      filter_upwards with t ht
      have htpos : 0 < t := ht.1
      have h1 : 0 ≤ (1 - t) / t ^ 2 := div_nonneg (by linarith [ht.2]) (by positivity)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
      calc (1 - t) / t ^ 2 * |⨍ z in Metric.ball (0:ℝ⁴) (t * r), ψ (x₀ + t⁻¹ • z) *
            ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z)|
          ≤ (1 - t) / t ^ 2 * ((t * r) ^ 2 * (8192 * η / ω)) :=
            mul_le_mul_of_nonneg_left (hGm t ht) h1
        _ = (r ^ 2 * (8192 * η / ω)) * (1 - t) := by field_simp
    have hIntI : IntervalIntegrable (fun t : ℝ => (r ^ 2 * (8192 * η / ω)) * (1 - t)) volume 0 1 :=
      (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1
    have hstep1 : ‖∫ t in (0:ℝ)..1, (1 - t) / t ^ 2 *
        (⨍ z in Metric.ball (0:ℝ⁴) (t * r), ψ (x₀ + t⁻¹ • z) *
          ((fderiv ℝ (fderiv ℝ U) (x₀ + z) - M₀) z z))‖
        ≤ ∫ t in (0:ℝ)..1, (r ^ 2 * (8192 * η / ω)) * (1 - t) :=
      intervalIntegral.norm_integral_le_of_norm_le (show (0:ℝ) ≤ 1 by norm_num) hptI hIntI
    rw [Real.norm_eq_abs] at hstep1
    have hcalc : (∫ t in (0:ℝ)..1, (r ^ 2 * (8192 * η / ω)) * (1 - t)) = δ * r ^ 2 := by
      calc ∫ t in (0:ℝ)..1, (r ^ 2 * (8192 * η / ω)) * (1 - t)
          = (r ^ 2 * (8192 * η / ω)) * ∫ t in (0:ℝ)..1, (1 - t) :=
            intervalIntegral.integral_const_mul _ _
        _ = (r ^ 2 * (8192 * η / ω)) * (1/2) := by
            congr 1
            rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t)
              (continuous_const.intervalIntegrable 0 1) (continuous_id.intervalIntegrable 0 1)]
            simp only [intervalIntegral.integral_const, integral_id, sub_zero, one_smul]
            norm_num
        _ = δ * r ^ 2 := by
            rw [hη]
            field_simp
            ring
    exact hstep1.trans hcalc.le

  -- ## conclusion
  refine le_of_tendsto (hconv.abs) (Filter.eventually_atTop.mpr ⟨m₀, fun m hm => hbd m hm⟩)


theorem taylorCore : ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (x₀ : ℝ⁴), IsOpen s → x₀ ∈ s →
    ContinuousOn u s → LocallyIntegrable u volume →
    ∀ (G : ℝ⁴ → ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴),
    LocallyIntegrable G volume → (∀ i j, LocallyIntegrable (M i j) volume) →
    HasWeakGradient u s G → HasWeakHessian u s M σ →
    IsLebesguePointVec G x₀ → (∀ i j, IsLebesguePoint (M i j) x₀) →
    (∀ i j, IsVanishingPoint (σ i j).totalVariation x₀) →
    ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0:ℝ),
      (∫ y in Metric.ball x₀ r, |taylorRemainder u G M x₀ y|) / (volume (Metric.ball x₀ r)).toReal
        ≤ ε * r ^ 2 := by
  intro u s x₀ hs hx₀ hcont hu G M σ hGli hMli hwg hwh hGleb hMleb hσvan ε hε
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  obtain ⟨R, hRpos, hR⟩ := taylor_bound_aux u s x₀ hs hx₀ hcont hu G M σ hGli hMli hwg hwh
    hGleb hMleb hσvan (ε / 2) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hRpos hρpos)] with r hr
  obtain ⟨hrpos, hrlt⟩ := hr
  have hrR : r < R := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrρ : r < ρ := lt_of_lt_of_le hrlt (min_le_right _ _)
  have hsub : Metric.closedBall x₀ r ⊆ s := fun y hy =>
    hρsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) hrρ))
  have hcontH : ContinuousOn (taylorRemainder u G M x₀) (Metric.closedBall x₀ r) := by
    have h1 : ContinuousOn (fun y : ℝ⁴ => u y) (Metric.closedBall x₀ r) := hcont.mono hsub
    have h2 : ContinuousOn (fun y : ℝ⁴ => u x₀) (Metric.closedBall x₀ r) := continuousOn_const
    have h3 : Continuous (fun y : ℝ⁴ => ⟪G x₀, y - x₀⟫) := by fun_prop
    have h4 : Continuous (fun y : ℝ⁴ =>
        (1 / 2) * ∑ i, ∑ j, M i j x₀ * ((y - x₀) i) * ((y - x₀) j)) := by fun_prop
    exact ((h1.sub h2).sub h3.continuousOn).sub h4.continuousOn
  have hint : IntegrableOn (taylorRemainder u G M x₀) (Metric.ball x₀ r) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall x₀ r) hcontH).mono_set
      Metric.ball_subset_closedBall
  have hgint : Integrable ((Metric.ball x₀ r).indicator (taylorRemainder u G M x₀)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hint
  obtain ⟨φ, hφcd, hφsupp, hφbd, hφlim⟩ :=
    Commons.Measure.Approximation.approx_sign_integral_ball x₀ hgint hrpos
  have hbdeq : ∀ k : ℕ, (⨍ y in Metric.ball x₀ r,
        φ k y * taylorRemainder u G M x₀ y)
      = ⨍ y in Metric.ball x₀ r,
        φ k y * ((Metric.ball x₀ r).indicator (taylorRemainder u G M x₀)) y := by
    intro k
    apply setAverage_congr_fun measurableSet_ball
    filter_upwards with y hy
    rw [Set.indicator_of_mem hy]
  have hbd : ∀ k : ℕ, |⨍ y in Metric.ball x₀ r, φ k y * taylorRemainder u G M x₀ y|
      ≤ (ε / 2) * r ^ 2 := fun k =>
    hR r ⟨hrpos, hrR⟩ (φ k) (hφcd k) (hφsupp k) (hφbd k)
  have hconv2 : Tendsto (fun k => ⨍ y in Metric.ball x₀ r,
        φ k y * ((Metric.ball x₀ r).indicator (taylorRemainder u G M x₀)) y) atTop
      (𝓝 (⨍ y in Metric.ball x₀ r, |taylorRemainder u G M x₀ y|)) := by
    have h := hφlim.const_smul ((volume.real (Metric.ball x₀ r))⁻¹)
    have h2 : (∫ y in Metric.ball x₀ r,
          |((Metric.ball x₀ r).indicator (taylorRemainder u G M x₀)) y|)
        = ∫ y in Metric.ball x₀ r, |taylorRemainder u G M x₀ y| := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      rw [Set.indicator_of_mem hy]
    rw [h2] at h
    simpa only [setAverage_eq] using h
  have hlimLe : (⨍ y in Metric.ball x₀ r, |taylorRemainder u G M x₀ y|)
      ≤ (ε / 2) * r ^ 2 := by
    refine le_of_tendsto hconv2 ?_
    filter_upwards with k
    rw [← hbdeq k]
    exact (le_abs_self _).trans (hbd k)
  have hgoal : (∫ y in Metric.ball x₀ r, |taylorRemainder u G M x₀ y|)
        / (volume (Metric.ball x₀ r)).toReal
      = ⨍ y in Metric.ball x₀ r, |taylorRemainder u G M x₀ y| := by
    rw [setAverage_eq, Measure.real_def, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hgoal]
  refine hlimLe.trans ?_
  nlinarith [hε, sq_nonneg r]

end Submission
