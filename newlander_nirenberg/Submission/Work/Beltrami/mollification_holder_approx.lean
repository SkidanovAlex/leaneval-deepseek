/-
# Smooth approximation of a bounded Hölder function by convolution

This file proves `Work.Beltrami.mollification_holder_approx`: a continuous complex valued
function `f` on `ℂ` which is bounded by `M`, Hölder with exponent `α` and constant `K`, and
supported in the closed ball of radius `R`, can be approximated pointwise by a sequence of
functions `u n` which are

* smooth (`ContDiff ℝ ∞`) with compact support,
* bounded by the same `M` and Hölder with the same constant `K`,
* supported in the closed ball of radius `R + 1`,
* bounded in `L²` by `f` itself: `eLpNorm (u n) 2 volume ≤ eLpNorm f 2 volume`,
* converging pointwise, for every `z`, to `f z`.

The construction is the classical mollification
`u n = ρ n ⋆ f`, where `ρ n` is a smooth nonnegative bump function with integral `1` and
support shrinking to `0` (outer radius `(n+2)⁻¹`).
-/
import Mathlib
import Submission.Work.Beltrami.convolution_holder_le
import Submission.Work.Beltrami.eLpNorm_convolution_compactSupport

namespace Work.Beltrami

open MeasureTheory Function Filter
open ContinuousLinearMap
open scoped ContDiff Convolution Topology Pointwise

noncomputable section

/-- A sequence of smooth bump functions on `ℂ` whose outer radius `(n+2)⁻¹` tends to `0`. -/
def mollBump (n : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨((n : ℝ) + 2)⁻¹ / 2, ((n : ℝ) + 2)⁻¹, by positivity, by
    have h : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := inv_pos.mpr (by positivity)
    linarith⟩

@[simp] theorem mollBump_rIn (n : ℕ) : (mollBump n).rIn = ((n : ℝ) + 2)⁻¹ / 2 := rfl

@[simp] theorem mollBump_rOut (n : ℕ) : (mollBump n).rOut = ((n : ℝ) + 2)⁻¹ := rfl

theorem mollBump_rOut_le_one (n : ℕ) : (mollBump n).rOut ≤ 1 := by
  rw [mollBump_rOut]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h3 : ((n : ℝ) + 2)⁻¹ * ((n : ℝ) + 2) = 1 := inv_mul_cancel₀ h2.ne'
  have h4 : 0 < ((n : ℝ) + 2)⁻¹ := inv_pos.mpr h2
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem tendsto_mollBump_rOut : Tendsto (fun n : ℕ => (mollBump n).rOut) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 := h1.comp (tendsto_add_atTop_nat 1)
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply, mollBump_rOut, Nat.cast_add, Nat.cast_one]
  ring

/-- The normalized bump `ρ n`: a smooth nonnegative function with support
`ball 0 (n+2)⁻¹` and integral `1`. -/
def mollKernel (n : ℕ) : ℂ → ℝ := (mollBump n).normed volume

theorem mollKernel_nonneg (n : ℕ) (z : ℂ) : 0 ≤ mollKernel n z :=
  (mollBump n).nonneg_normed z

theorem mollKernel_integral (n : ℕ) : ∫ z, mollKernel n z ∂volume = 1 :=
  (mollBump n).integral_normed

theorem mollKernel_support (n : ℕ) :
    Function.support (mollKernel n) = Metric.ball (0 : ℂ) ((mollBump n).rOut) :=
  (mollBump n).support_normed_eq

theorem contDiff_mollKernel (n : ℕ) : ContDiff ℝ ∞ (mollKernel n) :=
  (mollBump n).contDiff_normed

theorem continuous_mollKernel (n : ℕ) : Continuous (mollKernel n) :=
  (contDiff_mollKernel n).continuous

theorem hasCompactSupport_mollKernel (n : ℕ) : HasCompactSupport (mollKernel n) :=
  (mollBump n).hasCompactSupport_normed

theorem integrable_mollKernel (n : ℕ) : Integrable (mollKernel n) volume :=
  (continuous_mollKernel n).integrable_of_hasCompactSupport (hasCompactSupport_mollKernel n)

/-- The mollification of `f` by `ρ n`. -/
def mollify (f : ℂ → ℂ) (n : ℕ) : ℂ → ℂ := mollKernel n ⋆[lsmul ℝ ℝ, volume] f

/-- A function vanishing outside the closed ball of radius `R` has compact support. -/
theorem hasCompactSupport_of_bound {R : ℝ} {f : ℂ → ℂ} (h : ∀ z, R < ‖z‖ → f z = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 R)
    (isCompact_closedBall 0 R) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  rw [not_le] at hlt
  exact hz (h z hlt)

theorem contDiff_mollify {f : ℂ → ℂ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ ∞ (mollify f n) :=
  (hasCompactSupport_mollKernel n).contDiff_convolution_left (lsmul ℝ ℝ) (contDiff_mollKernel n)
    (hf.locallyIntegrable (μ := volume))

theorem hasCompactSupport_mollify {f : ℂ → ℂ} (hcs : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (mollify f n) :=
  (hasCompactSupport_mollKernel n).convolution (lsmul ℝ ℝ) hcs

theorem norm_mollify_le {f : ℂ → ℂ} {M : ℝ} (hfm : AEStronglyMeasurable f volume)
    (hM : ∀ z, ‖f z‖ ≤ M)
    (hM0 : 0 ≤ M) (n : ℕ) (z : ℂ) : ‖mollify f n z‖ ≤ M := by
  have h := MeasureTheory.dist_convolution_le (μ := volume) (f := mollKernel n) (g := f)
    (x₀ := z) (R := (mollBump n).rOut) (ε := M) (z₀ := (0 : ℂ)) hM0
    (by rw [mollKernel_support])
    (mollKernel_nonneg n)
    (mollKernel_integral n)
    hfm
    (fun x _ => by rw [dist_zero_right]; exact hM x)
  simpa only [mollify, dist_zero_right] using h

theorem tendsto_mollify {f : ℂ → ℂ} (hf : Continuous f) (z : ℂ) :
    Tendsto (fun n : ℕ => mollify f n z) atTop (𝓝 (f z)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) tendsto_mollBump_rOut hf z

theorem support_mollify {f : ℂ → ℂ} {R : ℝ} (h : ∀ z, R < ‖z‖ → f z = 0) (n : ℕ) (z : ℂ)
    (hz : R + 1 < ‖z‖) : mollify f n z = 0 := by
  by_contra hne
  have hmem : z ∈ Function.support (mollify f n) := hne
  have hz' : z ∈ Function.support (mollKernel n) + Function.support f :=
    support_convolution_subset (lsmul ℝ ℝ) hmem
  rw [Set.mem_add] at hz'
  obtain ⟨a, ha, b, hb, hab⟩ := hz'
  rw [mollKernel_support, Metric.mem_ball, dist_zero_right] at ha
  have hbR : ‖b‖ ≤ R := by
    by_contra hlt
    rw [not_le] at hlt
    exact hb (h b hlt)
  have h2 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h3 : ‖a + b‖ < (mollBump n).rOut + R :=
    lt_of_le_of_lt h2 (add_lt_add_of_lt_of_le ha hbR)
  have h4 : (mollBump n).rOut ≤ 1 := mollBump_rOut_le_one n
  rw [← hab] at hz
  linarith

theorem eLpNorm_mollify_le {f : ℂ → ℂ} {M : ℝ} (hf : Continuous f) (hM : ∀ z, ‖f z‖ ≤ M)
    (hcs : HasCompactSupport f) (n : ℕ) :
    eLpNorm (mollify f n) 2 volume ≤ eLpNorm f 2 volume :=
  eLpNorm_convolution_compactSupport (mollKernel_nonneg n) (continuous_mollKernel n)
    (hasCompactSupport_mollKernel n) (mollKernel_integral n) hf hM hcs

theorem holder_mollify {f : ℂ → ℂ} {M K α : ℝ} (hK : 0 ≤ K)
    (hfm : AEStronglyMeasurable f volume) (hM : ∀ z, ‖f z‖ ≤ M)
    (hholder : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) (n : ℕ) (x y : ℂ) :
    ‖mollify f n x - mollify f n y‖ ≤ K * ‖x - y‖ ^ α :=
  convolution_holder_le hK (mollKernel_nonneg n) (mollKernel_integral n) (integrable_mollKernel n)
    hfm hM hholder x y


theorem mollification_holder_approx {α M K R : ℝ} {f : ℂ → ℂ} (hf : Continuous f)
    (hMb : ∀ z, ‖f z‖ ≤ M) (hKb : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) (hfL2 : MemLp f 2 volume) :
    ∃ (u : ℕ → (ℂ → ℂ)),
      (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, eLpNorm (u n) 2 volume ≤ eLpNorm f 2 volume) ∧
      (∀ z, Filter.Tendsto (fun n => u n z) Filter.atTop (nhds (f z))) ∧
      (∀ n z, ‖u n z‖ ≤ M) ∧ (∀ (n : ℕ) (x y : ℂ), ‖u n x - u n y‖ ≤ K * ‖x - y‖ ^ α) ∧
      (∀ n z, R + 1 < ‖z‖ → u n z = 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hMb 0)
  have hK0 : 0 ≤ K := by
    have h := hKb 0 1
    have h1 : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [h1, Real.one_rpow, mul_one] at h
    exact (norm_nonneg (f 0 - f 1)).trans h
  have hcs : HasCompactSupport f := hasCompactSupport_of_bound hsupp
  exact ⟨mollify f,
    fun n => contDiff_mollify hf n,
    fun n => hasCompactSupport_mollify hcs n,
    fun n => eLpNorm_mollify_le hf hMb hcs n,
    fun z => tendsto_mollify hf z,
    fun n z => norm_mollify_le hfL2.aestronglyMeasurable hMb hM0 n z,
    fun n x y => holder_mollify hK0 hfL2.aestronglyMeasurable hMb hKb n x y,
    fun n z hz => support_mollify hsupp n z hz⟩

end

end Work.Beltrami
