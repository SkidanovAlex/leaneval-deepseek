import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.PotCubicSmoothWeight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uvSmear_continuous_decay`

The smoothed weight `uvSmear fu Λ f = uvKernel fu Λ ⋆ f` (`PotCubicSmoothWeight.lean`) is the
convolution of the UV-smoothing kernel `uvKernel fu Λ` with `f`.  The kernel is the inverse
(`p`-convention) Fourier transform of the compactly supported smooth symbol `uvSymbol fu Λ`, hence
— by `uvKernel_cast_eq_fourierInv` — the real part of the inverse Fourier transform of a Schwartz
function: so it is **smooth, bounded and rapidly decreasing**.

This file shows that the convolution inherits those properties as soon as `f` is only `L¹`: with
`f` integrable (and, for the decay, compactly supported, so that the convolution parameter `x` is
uniformly far from `supp f`)

* `uvSmear fu Λ f` is `Continuous` (dominated convergence: the kernel is bounded and continuous,
  and its translates are dominated by `‖uvKernel‖_∞ |f|`);
* `uvSmear fu Λ f` **decays faster than any polynomial**:
  `|uvSmear fu Λ f x| ≤ C (1 + ‖x‖)^{-n}` for every `n`.

Both facts are stated for the raw convolution, so they also cover the auxiliary `L¹`-estimates of
the UV-truncation chapter (`uvSmear_L1_tendsto`).

## Route

* `uvKernelSchwartz` — the Schwartz model of the kernel: the inverse Fourier transform of the
  compactly supported smooth symbol `uvSymbol fu Λ`; `uvKernelSchwartz_coe` identifies its values
  with `uvKernel fu Λ` (through `uvKernel_cast_eq_fourierInv`).
* `uvKernel_continuous`, `uvKernel_rapidDecay` — continuity and the rapid decay
  `‖uvKernel fu Λ z‖ ≤ C (1+‖z‖)^{-n}` of the kernel, read off from `SchwartzMap.decay`
  (`0`-order decay gives boundedness, `n`-order decay gives `‖z‖^n ‖K z‖ ≤ C`) through the
  elementary interpolation `two_bound_arith` of `lowCut_invFT_scaled`.
* `uvSmear_continuous` — the dominated-convergence argument.
* `uvSmear_rapidDecay` — for `y ∈ tsupport f` and `x` large the *shifted* decay factor satisfies
  `(1+‖x-y‖)^{-n} ≤ (1+R)^n (1+‖x‖)^{-n}` (because `1+‖x‖ ≤ (1+‖x-y‖)(1+R)` when `‖y‖ ≤ R`),
  which converts the kernel decay into the stated decay of the convolution; away from
  `tsupport f` the integrand vanishes identically.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The kernel as a Schwartz function -/

/-- The UV-smoothing kernel, realised as an inverse Fourier transform of the compactly supported
smooth symbol `uvSymbol fu Λ` — hence a Schwartz function. -/
noncomputable def uvKernelSchwartz (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    SchwartzMap E3 ℂ :=
  FourierTransform.fourierInv
    (((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap (uvSymbol_contDiff fu hΛ) :
      SchwartzMap E3 ℂ))

/-- The Schwartz model of the kernel takes the values of `uvKernel fu Λ`. -/
lemma uvKernelSchwartz_coe (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) (z : E3) :
    (uvKernelSchwartz fu hΛ z : ℂ) = ((uvKernel fu Λ z : ℝ) : ℂ) := by
  have hcoe : (((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap (uvSymbol_contDiff fu hΛ) :
      SchwartzMap E3 ℂ) : E3 → ℂ) = uvSymbol fu Λ :=
    funext fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x
  rw [uvKernelSchwartz, SchwartzMap.fourierInv_coe, hcoe, ← uvKernel_cast_eq_fourierInv]

/-- **The UV-smoothing kernel is continuous.** -/
lemma uvKernel_continuous (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    Continuous (uvKernel fu Λ) := by
  have h2 : Continuous (fun z : E3 => (uvKernelSchwartz fu hΛ z).re) :=
    Complex.continuous_re.comp (uvKernelSchwartz fu hΛ).continuous
  refine h2.congr (fun z => ?_)
  rw [uvKernelSchwartz_coe fu hΛ z, Complex.ofReal_re]

/-- **The UV-smoothing kernel decays faster than any polynomial**: for every `N` there is a
constant with `‖uvKernel fu Λ z‖ ≤ C (1 + ‖z‖)^{-N}`. -/
lemma uvKernel_rapidDecay (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3,
      ‖uvKernel fu Λ z‖ ≤ C * (1 + ‖z‖) ^ (-(N : ℤ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := (uvKernelSchwartz fu hΛ).decay 0 0
  obtain ⟨CN, _hCNpos, hCN⟩ := (uvKernelSchwartz fu hΛ).decay N 0
  have hnorm : ∀ z : E3, ‖uvKernelSchwartz fu hΛ z‖ = ‖uvKernel fu Λ z‖ := by
    intro z
    rw [uvKernelSchwartz_coe fu hΛ z]
    simp
  refine ⟨2 ^ N * max C₀ CN, by positivity, fun z => ?_⟩
  have hA : 0 ≤ max C₀ CN := le_trans hC₀pos.le (le_max_left _ _)
  have h1 : ‖uvKernel fu Λ z‖ ≤ max C₀ CN := by
    have h := hC₀ z
    rw [norm_iteratedFDeriv_zero, hnorm z] at h
    simpa using h.trans (le_max_left _ _)
  have h2 : ‖z‖ ^ N * ‖uvKernel fu Λ z‖ ≤ max C₀ CN := by
    have h := hCN z
    rw [norm_iteratedFDeriv_zero, hnorm z] at h
    exact h.trans (le_max_right _ _)
  have h3 := two_bound_arith N hA (norm_nonneg z) h1 h2
  have h4 : 2 ^ N * max C₀ CN / (1 + ‖z‖) ^ N
      = (2 ^ N * max C₀ CN) * (1 + ‖z‖) ^ (-(N : ℤ)) := by
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  exact h3.trans h4.le

/-! ## 2. Continuity of the smoothed weight -/

/-- **The smoothed weight of an `L¹` function is continuous** (dominated convergence, with the
kernel's sup-norm as the dominating constant). -/
lemma uvSmear_continuous (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) {f : E3 → ℝ}
    (hf : MeasureTheory.Integrable f) : Continuous (uvSmear fu Λ f) := by
  obtain ⟨M, _hMnn, hM⟩ := uvKernel_rapidDecay fu hΛ 0
  have hM' : ∀ z : E3, |uvKernel fu Λ z| ≤ M := by
    intro z
    rw [← Real.norm_eq_abs]
    simpa using hM z
  have hKcont := uvKernel_continuous fu hΛ
  change Continuous (fun x : E3 => ∫ y : E3, uvKernel fu Λ (x - y) * f y)
  refine continuous_of_dominated
    (F := fun x y => uvKernel fu Λ (x - y) * f y) (bound := fun y => M * ‖f y‖) ?_ ?_ ?_ ?_
  · intro x
    exact (((hKcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable)
  · intro x
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM' (x - y)) (abs_nonneg _)
  · exact hf.norm.const_mul M
  · filter_upwards with y
    exact (hKcont.comp (continuous_id.sub continuous_const)).mul continuous_const

/-! ## 3. Rapid decay of the smoothed weight -/

/-- **The smoothed weight of a compactly supported `L¹` function decays faster than any
polynomial.** -/
lemma uvSmear_rapidDecay (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) {f : E3 → ℝ}
    (hf : MeasureTheory.Integrable f) (hfs : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, |uvSmear fu Λ f x| ≤ C * (1 + ‖x‖) ^ (-(n : ℤ)) := by
  obtain ⟨Ck, hCknn, hCk⟩ := uvKernel_rapidDecay fu hΛ n
  obtain ⟨r, hr⟩ : ∃ r : ℝ, tsupport f ⊆ Metric.closedBall (0 : E3) r :=
    (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hfs.isCompact.isBounded
  set R : ℝ := max r 0 with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hrR : r ≤ R := by rw [hRdef]; exact le_max_left _ _
  have hsub : tsupport f ⊆ Metric.closedBall (0 : E3) R := by
    intro z hz
    have h1 := hr hz
    rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
    exact h1.trans hrR
  have hmem : ∀ y : E3, y ∈ tsupport f → ‖y‖ ≤ R := by
    intro y hy
    have h1 := hsub hy
    rwa [Metric.mem_closedBall, dist_zero_right] at h1
  set If : ℝ := ∫ y : E3, |f y| with hIfdef
  have hIfnn : 0 ≤ If := by rw [hIfdef]; exact integral_nonneg fun y => abs_nonneg _
  refine ⟨Ck * (1 + R) ^ n * If, ?_, fun x => ?_⟩
  · exact mul_nonneg (mul_nonneg hCknn (pow_nonneg (by linarith) n)) hIfnn
  · have hfint : Integrable (fun y : E3 => |f y|) := by simpa using hf.norm
    have hstep1 : |uvSmear fu Λ f x| ≤ ∫ y : E3, |uvKernel fu Λ (x - y)| * |f y| := by
      rw [uvSmear]
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with y
      rw [abs_mul]
    -- the shift of the decay factor: `‖y‖ ≤ R` gives `1 + ‖x‖ ≤ (1 + ‖x-y‖)(1 + R)`
    have hfac : ∀ y : E3, ‖y‖ ≤ R →
        (1 + ‖x - y‖) ^ (-(n : ℤ)) ≤ (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ)) := by
      intro y hyR
      have hux : 1 + ‖x‖ ≤ (1 + ‖x - y‖) * (1 + R) := by
        have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
          have h := norm_add_le (x - y) y
          rwa [sub_add_cancel] at h
        nlinarith [h1, hyR, hRnn, norm_nonneg (x - y)]
      have hpow : (1 + ‖x‖) ^ n ≤ (1 + R) ^ n * (1 + ‖x - y‖) ^ n := by
        calc (1 + ‖x‖) ^ n ≤ ((1 + ‖x - y‖) * (1 + R)) ^ n :=
              pow_le_pow_left₀ (by positivity) hux n
          _ = (1 + R) ^ n * (1 + ‖x - y‖) ^ n := by rw [mul_pow]; ring
      have hv : 0 < (1 + ‖x - y‖) ^ n := pow_pos (by positivity) n
      have hu : 0 < (1 + ‖x‖) ^ n := pow_pos (by positivity) n
      have h1 : ((1 + ‖x - y‖) ^ n)⁻¹ ≤ (1 + R) ^ n * ((1 + ‖x‖) ^ n)⁻¹ := by
        rw [← div_eq_mul_inv]
        rw [show ((1 + ‖x - y‖) ^ n)⁻¹ = 1 / (1 + ‖x - y‖) ^ n from (one_div _).symm]
        rw [div_le_div_iff₀ hv hu]
        simpa using hpow
      simpa only [zpow_neg, zpow_natCast] using h1
    have hpt : ∀ y : E3, |uvKernel fu Λ (x - y)| * |f y|
        ≤ (Ck * (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ))) * |f y| := by
      intro y
      by_cases hy : y ∈ tsupport f
      · have hyR := hmem y hy
        have hdec := hCk (x - y)
        rw [Real.norm_eq_abs] at hdec
        have hfacy := hfac y hyR
        calc |uvKernel fu Λ (x - y)| * |f y|
            ≤ (Ck * (1 + ‖x - y‖) ^ (-(n : ℤ))) * |f y| :=
              mul_le_mul_of_nonneg_right hdec (abs_nonneg _)
          _ ≤ (Ck * ((1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ)))) * |f y| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfacy hCknn) (abs_nonneg _)
          _ = (Ck * (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ))) * |f y| := by ring
      · have hfy : f y = 0 := by
          by_contra h
          exact hy (subset_tsupport f (Function.mem_support.mpr h))
        rw [hfy, abs_zero, mul_zero, mul_zero]
    have hInt_le : (∫ y : E3, |uvKernel fu Λ (x - y)| * |f y|)
        ≤ ∫ y : E3, (Ck * (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ))) * |f y| := by
      refine integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards with y
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      · exact hfint.const_mul _
      · filter_upwards with y
        exact hpt y
    have hInt_eq : (∫ y : E3, (Ck * (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ))) * |f y|)
        = Ck * (1 + R) ^ n * If * (1 + ‖x‖) ^ (-(n : ℤ)) := by
      rw [integral_const_mul, ← hIfdef]
      ring
    calc |uvSmear fu Λ f x|
        ≤ ∫ y : E3, |uvKernel fu Λ (x - y)| * |f y| := hstep1
      _ ≤ ∫ y : E3, (Ck * (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ))) * |f y| := hInt_le
      _ = Ck * (1 + R) ^ n * If * (1 + ‖x‖) ^ (-(n : ℤ)) := hInt_eq
      _ = (Ck * (1 + R) ^ n * If) * (1 + ‖x‖) ^ (-(n : ℤ)) := by ring

/-! ## 4. The target -/

theorem uvSmear_continuous_decay (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (hfs : HasCompactSupport f) :
    Continuous (Work.BoseBoxFock.uvSmear fu Λ f) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin 3),
        |Work.BoseBoxFock.uvSmear fu Λ f x| ≤ C * (1 + ‖x‖) ^ (-(n : ℤ)) :=
  ⟨uvSmear_continuous fu hΛ hf, fun n => uvSmear_rapidDecay fu hΛ hf hfs n⟩

end Work.BoseBoxFock
