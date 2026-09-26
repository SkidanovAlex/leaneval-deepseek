import Mathlib
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.sweepFam_contDiff_periodic

namespace Work.Drive

open MeasureTheory

/-!
# Smoothness of the double blur of a locally integrable function

This file proves `Work.Drive.contDiff_doubleBlur_scalar`: for a locally integrable
`f : ℝ × ℝ → ℝ`, the doubly blurred function

`t ↦ ∫ v in -1..1, sweepBump v * (∫ u in -1..1, sweepBump u * f (s - δ₂ v, t - δ₁ u))`

is `C^∞`.  The route is the standard one: after the substitutions `x = s - δ₂ v` and
`y = t - δ₁ u` the double interval integral is the convolution of `f` with the smooth
compactly supported kernel `sweepKernel δ₁ δ₂`, and convolution with such a kernel maps
locally integrable functions to `C^∞` functions (`HasCompactSupport.contDiff_convolution_right`).

The bridge between the interval integral and the convolution is proved here in the generality of
an arbitrary normed `ℝ`-vector space of values (the version in
`Submission/Work/Drive/sweepFam_contDiff_periodic.lean` is the special case of
`LeanEval.KnotTheory.Quadrisecant.Space`).
-/

/-- **The double interval integral with the bump is the convolution with `sweepKernel`.**

For a locally integrable `f` with values in an arbitrary normed `ℝ`-vector space, substituting
`x = s - δ₂ v` in the outer and `y = t - δ₁ u` in the inner interval integral turns the double
interval integral into the convolution of `f` with the smooth compactly supported kernel
`sweepKernel δ₁ δ₂`. -/
theorem sweepKernel_convolution_eq_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (hf : LocallyIntegrable f volume)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (s t : ℝ) :
    (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) • f y)
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u • f (s - δ₂ * v, t - δ₁ * u)) := by
  have hK : Continuous (sweepKernel δ₁ δ₂) := by
    unfold sweepKernel
    exact ((continuous_sweepBump.comp (continuous_fst.div_const δ₂)).div_const |δ₂|).mul
      ((continuous_sweepBump.comp (continuous_snd.div_const δ₁)).div_const |δ₁|)
  have hcont : Continuous (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y)) :=
    hK.comp (continuous_const.sub continuous_id)
  have hsupp : Function.support (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y)) ⊆
      Set.Icc (s - |δ₂|) (s + |δ₂|) ×ˢ Set.Icc (t - |δ₁|) (t + |δ₁|) := by
    intro y hy
    rw [Function.mem_support] at hy
    have hb1 : sweepBump ((s - y.1) / δ₂) ≠ 0 := by
      intro h0
      exact hy (by rw [sweepKernel_sub, h0, zero_div, zero_mul])
    have hb2 : sweepBump ((t - y.2) / δ₁) ≠ 0 := by
      intro h0
      exact hy (by rw [sweepKernel_sub, h0, zero_div, mul_zero])
    have hle1 : |y.1 - s| ≤ |δ₂| := by
      have h1 : |(s - y.1) / δ₂| < 1 := lt_of_not_ge fun h => hb1 (sweepBump_eq_zero_of_one_le_abs h)
      rw [abs_div, div_lt_one (abs_pos.mpr hδ₂)] at h1
      rw [abs_sub_comm]; exact h1.le
    have hle2 : |y.2 - t| ≤ |δ₁| := by
      have h1 : |(t - y.2) / δ₁| < 1 := lt_of_not_ge fun h => hb2 (sweepBump_eq_zero_of_one_le_abs h)
      rw [abs_div, div_lt_one (abs_pos.mpr hδ₁)] at h1
      rw [abs_sub_comm]; exact h1.le
    rw [Set.mem_prod]
    exact ⟨mem_Icc_of_abs_le hle1, mem_Icc_of_abs_le hle2⟩
  have hcs : HasCompactSupport (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsupp
  have hint : Integrable (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y) • f y) volume :=
    hf.integrable_smul_left_of_hasCompactSupport hcont hcs
  change (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) • f y ∂(volume.prod volume)) = _
  rw [integral_prod (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y) • f y) hint]
  simp only [sweepKernel_sub]
  have hinner : ∀ y₁ : ℝ,
      (∫ y₂ : ℝ, ((sweepBump ((s - y₁) / δ₂) / |δ₂|) *
          (sweepBump ((t - y₂) / δ₁) / |δ₁|)) • f (y₁, y₂))
        = (sweepBump ((s - y₁) / δ₂) / |δ₂|) •
            (∫ u in (-1 : ℝ)..1, sweepBump u • f (y₁, t - δ₁ * u)) := by
    intro y₁
    simp_rw [mul_smul]
    rw [MeasureTheory.integral_smul]
    congr 1
    rw [integral_eq_integral_interval_of_support (δ := δ₁)
      (fun y₂ => (sweepBump ((t - y₂) / δ₁) / |δ₁|) • f (y₁, y₂)) t ?_]
    · rw [integral_Icc_eq_abs_mul_integral
        (fun y₂ => (sweepBump ((t - y₂) / δ₁) / |δ₁|) • f (y₁, y₂)) hδ₁ t]
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [smul_smul, show t - (t - δ₁ * u) = δ₁ * u by ring, bump_self_div hδ₁,
        abs_mul_div_abs_self hδ₁]
    · intro y₂ hy₂
      have hb : sweepBump ((t - y₂) / δ₁) = 0 := by
        apply sweepBump_eq_zero_of_one_le_abs
        by_contra hcon
        have h1 : |(t - y₂) / δ₁| < 1 := lt_of_not_ge hcon
        rw [abs_div, div_lt_one (abs_pos.mpr hδ₁)] at h1
        exact hy₂ (mem_Icc_of_abs_le (by rw [abs_sub_comm]; exact h1.le))
      rw [hb, zero_div, zero_smul]
  simp_rw [hinner]
  rw [integral_eq_integral_interval_of_support (δ := δ₂)
    (fun y₁ => (sweepBump ((s - y₁) / δ₂) / |δ₂|) •
      (∫ u in (-1 : ℝ)..1, sweepBump u • f (y₁, t - δ₁ * u))) s ?_]
  · rw [integral_Icc_eq_abs_mul_integral
      (fun y₁ => (sweepBump ((s - y₁) / δ₂) / |δ₂|) •
        (∫ u in (-1 : ℝ)..1, sweepBump u • f (y₁, t - δ₁ * u))) hδ₂ s]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [smul_smul, show s - (s - δ₂ * v) = δ₂ * v by ring, bump_self_div hδ₂,
      abs_mul_div_abs_self hδ₂]
  · intro y₁ hy₁
    have hb : sweepBump ((s - y₁) / δ₂) = 0 := by
      apply sweepBump_eq_zero_of_one_le_abs
      by_contra hcon
      have h1 : |(s - y₁) / δ₂| < 1 := lt_of_not_ge hcon
      rw [abs_div, div_lt_one (abs_pos.mpr hδ₂)] at h1
      exact hy₁ (mem_Icc_of_abs_le (by rw [abs_sub_comm]; exact h1.le))
    rw [hb, zero_div, zero_smul]

theorem contDiff_doubleBlur_scalar {f : ℝ × ℝ → ℝ} (hf : MeasureTheory.LocallyIntegrable f volume)
    {δ₁ δ₂ s : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ =>
      ∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v *
        (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u * f (s - δ₂ * v, t - δ₁ * u))) := by
  -- The double interval integral is the convolution of `f` with the smooth kernel `sweepKernel`.
  have hEq : (fun t : ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) • f y)
      = fun t : ℝ => ∫ v in (-1 : ℝ)..1, sweepBump v *
          (∫ u in (-1 : ℝ)..1, sweepBump u * f (s - δ₂ * v, t - δ₁ * u)) := by
    funext t
    rw [sweepKernel_convolution_eq_gen f hf hδ₁ hδ₂ s t]
    simp only [smul_eq_mul]
  -- Convolution with a smooth compactly supported kernel is `C^∞`.
  have hmain : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) • f y) := by
    have h := (hasCompactSupport_sweepKernel hδ₁ hδ₂).contDiff_convolution_right
      (n := (⊤ : ℕ∞)) (μ := volume)
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) hf
      (contDiff_sweepKernel δ₁ δ₂)
    have hfun : MeasureTheory.convolution f (sweepKernel δ₁ δ₂)
          ((ContinuousLinearMap.lsmul ℝ ℝ).flip : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) MeasureTheory.volume
        = (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) • f y) := by
      funext p
      rw [MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rwa [hfun] at h
  rw [← hEq]
  exact hmain.comp (contDiff_prodMk_right s)

end Work.Drive
