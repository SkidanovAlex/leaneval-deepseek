import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
import Submission.Work.SmallBoxD1Newtonian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-283 — the D1 `A₁`-bound (M2)

FS `lm:appbogolubov` adds `A₁ = (2π)⁻³K_s a ∫(b_p†b_p + b†_{−p}b_{−p})dp` and estimates it by
`A₁ ≤ K_s a (n₀+1)|B|⁻¹ n₊` (eq:A1estimate).  In the corpus the corresponding obligation is

  `2 K_s a s⁻³ · (2π)⁻³ ∫_q P(q) dq ≤ C a (M/s³) cnPlus`,

where `P(q) = modeP s (qModeRe s q) Φ + modeP s (qModeIm s q) Φ` and
`cnPlus s Φ = Σ_i ∫_{Λ(s)^M}(aQ s i Φ)²` is the number of excited particles.  The KEY estimate is

  **(2π)⁻³ ∫_q P(q) dq ≤ M · chiSup² · cnPlus**

(the `s³` from `∫_x(aQ_iΦ)(x_{i↦z})²dx = s³∫(aQ_iΦ)²` CANCELS the `(s³)⁻¹` inside `modeP`).

Route:
* `boxOp s 1 g Φ x = Σ_i ∫_{Λ(s)}g(z)Φ(x_{i↦z})dz`;  since `∫_{Λ(s)}g = 0` for `g = qMode_`,
  and the fibre mean `∫_{Λ(s)}(aQ s i Φ)(x_{i↦z})dz = 0`, the slot integral equals the
  χ-COSINE (resp. χ-SINE) overlap against the EXCITED part `aQ s i Φ`;
* `∫_{Λ(s)}χ_s(z)cos⟨q,z⟩h(z)dz = (𝓕(χ_s·h)((2π)⁻¹•q)).re` (`cosCoeff_eq_re_fourier`) and the
  sine companion;  Plancherel (`integral_norm_sq_fourier_l1l2`) + the scaling
  `q ↦ q/(2π)` give `(2π)⁻³∫_q (overlap)² ≤ ∫(χ_s h)² ≤ chiSup²∫_{Λ(s)}h²`;
* Cauchy–Schwarz over the slots + the peel `∫_{Λ(s)^M}∫_{Λ(s)}(aQ_iΦ)(x_{i↦z})² = s³∫(aQ_iΦ)²`.

## Contents

* `integral_chiMul_sq`, `memLp_chiMul`, `integrable_chiMul`;
* **`cos_overlap_sq_integral_le`**, **`sin_overlap_sq_integral_le`**;
* `overlap_mean_zero` (the `qMode` slot-integral reduction);
* `boxOp_qModeIm_eq`;
* the per-slot and summed `modeP` bounds.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the complexified windowed function `χ_s·h` is integrable when `h` is continuous. -/
lemma integrable_chiMul {s : ℝ} (hs : 0 < s) {h : ℝ³ → ℝ} (hh : Continuous h) :
    Integrable (fun z : ℝ³ => ((chiScale s z * h z : ℝ) : ℂ)) := by
  have hcont : Continuous (fun z : ℝ³ => ((chiScale s z * h z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((chiScale_continuous s).mul hh)
  have hsupp : HasCompactSupport (fun z : ℝ³ => ((chiScale s z * h z : ℝ) : ℂ)) := by
    refine HasCompactSupport.intro (K := acube s) (acube_compact hs) ?_
    intro z hz
    have hχ : chiScale s z = 0 := not_ne_iff.mp (fun hh' => hz (chiScale_mem_acube hs hh'))
    rw [show chiScale s z * h z = 0 from by rw [hχ, zero_mul], Complex.ofReal_zero]
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- `χ_s·h` is square-integrable when `h` is continuous. -/
lemma memLp_chiMul {s : ℝ} (hs : 0 < s) {h : ℝ³ → ℝ} (hh : Continuous h) :
    MemLp (fun z : ℝ³ => ((chiScale s z * h z : ℝ) : ℂ)) 2 volume := by
  obtain ⟨B, hB⟩ := (acube_compact hs).exists_bound_of_continuousOn hh.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (h 0))
    (hB 0 (mem_acube_of_norm_le hs.le (by simp only [norm_zero]; positivity)))
  have hcont : Continuous (fun z : ℝ³ => ((chiScale s z * h z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((chiScale_continuous s).mul hh)
  have hbdd : ∀ z : ℝ³, ‖((chiScale s z * h z : ℝ) : ℂ)‖ ≤ B * |chiScale s z| := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    by_cases hz : z ∈ acube s
    · have hBz : |h z| ≤ B := by simpa using hB z hz
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hBz (abs_nonneg _)
    · have hχ : chiScale s z = 0 := not_ne_iff.mp (fun hh' => hz (chiScale_mem_acube hs hh'))
      rw [hχ]
      simp
  have hχ2 : HasCompactSupport (fun z : ℝ³ => (B * |chiScale s z|) ^ 2) := by
    refine HasCompactSupport.intro (K := acube s) (acube_compact hs) ?_
    intro z hz
    have hχ : chiScale s z = 0 := not_ne_iff.mp (fun hh' => hz (chiScale_mem_acube hs hh'))
    rw [hχ]
    simp
  have hχ2cont : Continuous (fun z : ℝ³ => (B * |chiScale s z|) ^ 2) :=
    ((continuous_const.mul (chiScale_continuous s).abs).pow 2)
  have hdom : Integrable (fun z : ℝ³ => (B * |chiScale s z|) ^ 2) :=
    hχ2cont.integrable_of_hasCompactSupport hχ2
  have hsq : Integrable (fun z : ℝ³ => ‖((chiScale s z * h z : ℝ) : ℂ)‖ ^ 2) := by
    refine Integrable.mono' hdom ((hcont.norm.pow 2).aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbdd z) 2
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hsq

/-! ## 2 The overlap bound: the χ-cosine/sine overlaps are `L²` in the frequency -/

/-- `(Re z)² ≤ ‖z‖²`. -/
lemma re_sq_le_normSq_c (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  have h : z.re ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  rwa [Complex.normSq_eq_norm_sq] at h

/-- `(Im z)² ≤ ‖z‖²`. -/
lemma im_sq_le_normSq_c (z : ℂ) : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
  have h : z.im ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re]
  rwa [Complex.normSq_eq_norm_sq] at h

/-- the elementary identity `-2π⟪z,(2π)⁻¹q⟫ = -⟪q,z⟫`. -/
lemma neg_two_pi_inner_inv_two_pi (q z : ℝ³) :
    -2 * Real.pi * inner ℝ z (((2 * Real.pi : ℝ)⁻¹) • q) = -inner ℝ q z := by
  rw [real_inner_smul_right, real_inner_comm]
  field_simp

/-- the cosine of the shifted argument: `cos⟨q,z⟩ = cos(-2π⟨z,(2π)⁻¹q⟩)`. -/
lemma cos_inner_eq (q z : ℝ³) :
    Real.cos (inner ℝ q z)
      = Real.cos (-2 * Real.pi * inner ℝ z (((2 * Real.pi : ℝ)⁻¹) • q)) := by
  rw [neg_two_pi_inner_inv_two_pi, Real.cos_neg]

/-- **The χ-COSINE overlap bound.**  For SMOOTH `h`,
`(2π)⁻³∫_q (∫_{Λ(s)}χ_s(z)cos⟨q,z⟩h(z)dz)²dq ≤ ∫(χ_s h)²`.

The smoothness is used only to make `χ_s·h` a Schwartz function, so that Plancherel
(`SchwartzMap.integral_norm_sq_fourier`) applies and the frequency-side integrand is
manifestly integrable. -/
theorem cos_overlap_sq_integral_le {s : ℝ} (hs : 0 < s) {h : ℝ³ → ℝ}
    (hh : ContDiff ℝ ∞ h) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z) ^ 2
      ≤ ∫ z : ℝ³, (chiScale s z * h z) ^ 2 := by
  set W : ℝ³ → ℝ := fun z => chiScale s z * h z with hW
  have hWcd : ContDiff ℝ ∞ W := by
    rw [hW]
    exact (chiScale_contDiff (ne_of_gt hs)).mul hh
  have hWsupp : HasCompactSupport W := by
    rw [hW]
    exact (chiScale_hasCompactSupport (ℓ := s) (ne_of_gt hs)).mul_right
  have hFcsupp : HasCompactSupport (fun z : ℝ³ => (W z : ℂ)) :=
    hWsupp.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hFccd : ContDiff ℝ ∞ (fun z : ℝ³ => (W z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hWcd
  obtain ⟨Fs, hFs⟩ : ∃ Fs : SchwartzMap ℝ³ ℂ, (Fs : ℝ³ → ℂ) = fun z => (W z : ℂ) :=
    ⟨hFcsupp.toSchwartzMap hFccd, rfl⟩
  set G : ℝ³ → ℂ := fun p => (𝓕 Fs) p with hGdef
  have hGmem : MemLp G 2 volume := (𝓕 Fs).memLp 2
  have hplan : (∫ p : ℝ³, ‖G p‖ ^ 2) = ∫ z : ℝ³, ‖(Fs : ℝ³ → ℂ) z‖ ^ 2 :=
    SchwartzMap.integral_norm_sq_fourier Fs
  -- `𝓕 Fs` is again Schwartz, so its squared modulus is integrable
  have hIntF : Integrable (fun p : ℝ³ => ‖G p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hGmem.aestronglyMeasurable).mp hGmem
  have hGint : Integrable (fun q : ℝ³ => ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2) :=
    hIntF.comp_smul (R := (2 * π : ℝ)⁻¹) (by positivity)
  -- the pointwise bound
  have hpt : ∀ q : ℝ³,
      (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z) ^ 2
        ≤ ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 := by
    intro q
    have hcos : (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z)
        = (G (((2 * π : ℝ)⁻¹) • q)).re := by
      rw [show (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z)
          = ∫ z in acube s, chiScale s z
              * Real.cos (-2 * Real.pi * inner ℝ z (((2 * π : ℝ)⁻¹) • q)) * h z from by
        refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
        rw [cos_inner_eq]]
      rw [cosCoeff_eq_re_fourier hs (((2 * π : ℝ)⁻¹) • q) hh.continuous]
      congr 1
      rw [hGdef]
      simp only []
      rw [show (fun z : ℝ³ => (↑(chiScale s z * h z) : ℂ)) = (Fs : ℝ³ → ℂ) from by
        rw [hFs, hW]]
      rfl
    rw [hcos]
    exact re_sq_le_normSq_c _
  have hmeas1 : AEStronglyMeasurable
      (fun q : ℝ³ => (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z) ^ 2) := by
    have hcont : Continuous fun q : ℝ³ => ∫ z in acube s,
        chiScale s z * Real.cos (inner ℝ q z) * h z := by
      refine continuous_parametric_integral_of_continuous (f := fun q z =>
        chiScale s z * Real.cos (inner ℝ q z) * h z) ?_ (acube_compact hs)
      exact Continuous.mul (Continuous.mul
        ((chiScale_continuous s).comp continuous_snd)
        (Real.continuous_cos.comp (continuous_fst.inner continuous_snd)))
        (hh.continuous.comp continuous_snd)
    exact (hcont.pow 2).aestronglyMeasurable
  have hmono : (∫ q, (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z) ^ 2)
      ≤ ∫ q, ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => sq_nonneg _) hGint
      (Filter.Eventually.of_forall fun q => hpt q)
  -- the scaling
  have hscale : (∫ q : ℝ³, ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2)
      = (2 * π : ℝ) ^ 3 * ∫ p : ℝ³, ‖G p‖ ^ 2 := by
    have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
      (fun p : ℝ³ => ‖G p‖ ^ 2) (((2 * π : ℝ))⁻¹)
      (hR := inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2 * π))
    rw [finrank_euclideanSpace, Fintype.card_fin] at h
    rw [h, inv_pow, inv_inv, smul_eq_mul]
  -- the RHS identification
  have hrhs : (∫ z : ℝ³, (chiScale s z * h z) ^ 2) = ∫ z : ℝ³, ‖(Fs : ℝ³ → ℂ) z‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFs, hW, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hplan' : (∫ p : ℝ³, ‖G p‖ ^ 2) = ∫ z : ℝ³, (chiScale s z * h z) ^ 2 := by
    rw [hrhs]
    exact hplan
  have h2πpos : (0 : ℝ) < (2 * π) ^ 3 := by positivity
  calc ((2 * π) ^ 3)⁻¹ * ∫ q, (∫ z in acube s, chiScale s z * Real.cos (inner ℝ q z) * h z) ^ 2
      ≤ ((2 * π) ^ 3)⁻¹ * ∫ q, ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((2 * π) ^ 3)⁻¹ * ((2 * π : ℝ) ^ 3 * ∫ p : ℝ³, ‖G p‖ ^ 2) := by
        rw [hscale]
    _ = ∫ p : ℝ³, ‖G p‖ ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2πpos), one_mul]
    _ = ∫ z : ℝ³, (chiScale s z * h z) ^ 2 := hplan'

/-- the sine of the shifted argument: `sin⟨q,z⟩ = -sin(-2π⟨z,(2π)⁻¹q⟩)`. -/
lemma sin_inner_eq (q z : ℝ³) :
    Real.sin (inner ℝ q z)
      = -Real.sin (-2 * Real.pi * inner ℝ z (((2 * Real.pi : ℝ)⁻¹) • q)) := by
  rw [neg_two_pi_inner_inv_two_pi, Real.sin_neg, neg_neg]

/-- **The χ-SINE overlap bound** (the companion of `cos_overlap_sq_integral_le`). -/
theorem sin_overlap_sq_integral_le {s : ℝ} (hs : 0 < s) {h : ℝ³ → ℝ}
    (hh : ContDiff ℝ ∞ h) :
    ((2 * π) ^ 3)⁻¹ * ∫ q, (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z) ^ 2
      ≤ ∫ z : ℝ³, (chiScale s z * h z) ^ 2 := by
  set W : ℝ³ → ℝ := fun z => chiScale s z * h z with hW
  have hWcd : ContDiff ℝ ∞ W := by
    rw [hW]
    exact (chiScale_contDiff (ne_of_gt hs)).mul hh
  have hWsupp : HasCompactSupport W := by
    rw [hW]
    exact (chiScale_hasCompactSupport (ℓ := s) (ne_of_gt hs)).mul_right
  have hFcsupp : HasCompactSupport (fun z : ℝ³ => (W z : ℂ)) :=
    hWsupp.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hFccd : ContDiff ℝ ∞ (fun z : ℝ³ => (W z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hWcd
  obtain ⟨Fs, hFs⟩ : ∃ Fs : SchwartzMap ℝ³ ℂ, (Fs : ℝ³ → ℂ) = fun z => (W z : ℂ) :=
    ⟨hFcsupp.toSchwartzMap hFccd, rfl⟩
  set G : ℝ³ → ℂ := fun p => (𝓕 Fs) p with hGdef
  have hGmem : MemLp G 2 volume := (𝓕 Fs).memLp 2
  have hplan : (∫ p : ℝ³, ‖G p‖ ^ 2) = ∫ z : ℝ³, ‖(Fs : ℝ³ → ℂ) z‖ ^ 2 :=
    SchwartzMap.integral_norm_sq_fourier Fs
  have hIntF : Integrable (fun p : ℝ³ => ‖G p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hGmem.aestronglyMeasurable).mp hGmem
  have hGint : Integrable (fun q : ℝ³ => ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2) :=
    hIntF.comp_smul (R := (2 * π : ℝ)⁻¹) (by positivity)
  have hpt : ∀ q : ℝ³,
      (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z) ^ 2
        ≤ ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 := by
    intro q
    have hsin : (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z)
        = -((G (((2 * π : ℝ)⁻¹) • q)).im) := by
      rw [show (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z)
          = ∫ z in acube s, -(chiScale s z
              * Real.sin (-2 * Real.pi * inner ℝ z (((2 * π : ℝ)⁻¹) • q)) * h z) from by
        refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
        rw [sin_inner_eq]; ring]
      rw [MeasureTheory.integral_neg,
        sinCoeff_eq_im_fourier hs (((2 * π : ℝ)⁻¹) • q) hh.continuous]
      congr 2
      rw [hGdef]
      simp only []
      rw [show (fun z : ℝ³ => (↑(chiScale s z * h z) : ℂ)) = (Fs : ℝ³ → ℂ) from by
        rw [hFs, hW]]
      rw [SchwartzMap.fourier_coe]
    rw [hsin]
    have := im_sq_le_normSq_c (G (((2 * π : ℝ)⁻¹) • q))
    simpa using this
  have hmeas1 : AEStronglyMeasurable
      (fun q : ℝ³ => (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z) ^ 2) := by
    have hcont : Continuous fun q : ℝ³ => ∫ z in acube s,
        chiScale s z * Real.sin (inner ℝ q z) * h z := by
      refine continuous_parametric_integral_of_continuous (f := fun q z =>
        chiScale s z * Real.sin (inner ℝ q z) * h z) ?_ (acube_compact hs)
      exact Continuous.mul (Continuous.mul
        ((chiScale_continuous s).comp continuous_snd)
        (Real.continuous_sin.comp (continuous_fst.inner continuous_snd)))
        (hh.continuous.comp continuous_snd)
    exact (hcont.pow 2).aestronglyMeasurable
  have hmono : (∫ q, (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z) ^ 2)
      ≤ ∫ q, ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => sq_nonneg _) hGint
      (Filter.Eventually.of_forall fun q => hpt q)
  have hscale : (∫ q : ℝ³, ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2)
      = (2 * π : ℝ) ^ 3 * ∫ p : ℝ³, ‖G p‖ ^ 2 := by
    have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
      (fun p : ℝ³ => ‖G p‖ ^ 2) (((2 * π : ℝ))⁻¹)
      (hR := inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2 * π))
    rw [finrank_euclideanSpace, Fintype.card_fin] at h
    rw [h, inv_pow, inv_inv, smul_eq_mul]
  have hrhs : (∫ z : ℝ³, (chiScale s z * h z) ^ 2) = ∫ z : ℝ³, ‖(Fs : ℝ³ → ℂ) z‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFs, hW, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hplan' : (∫ p : ℝ³, ‖G p‖ ^ 2) = ∫ z : ℝ³, (chiScale s z * h z) ^ 2 := by
    rw [hrhs]
    exact hplan
  have h2πpos : (0 : ℝ) < (2 * π) ^ 3 := by positivity
  calc ((2 * π) ^ 3)⁻¹ * ∫ q, (∫ z in acube s, chiScale s z * Real.sin (inner ℝ q z) * h z) ^ 2
      ≤ ((2 * π) ^ 3)⁻¹ * ∫ q, ‖G (((2 * π : ℝ)⁻¹) • q)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((2 * π) ^ 3)⁻¹ * ((2 * π : ℝ) ^ 3 * ∫ p : ℝ³, ‖G p‖ ^ 2) := by
        rw [hscale]
    _ = ∫ p : ℝ³, ‖G p‖ ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2πpos), one_mul]
    _ = ∫ z : ℝ³, (chiScale s z * h z) ^ 2 := hplan'

/-! ## 3 The mean-zero reductions (the `qMode` slots see only the excited part) -/

/-- the `χ`-cosine/sine slot integral only sees the fibre-mean-free part. -/
lemma slot_eq_excited {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    (hg0 : (∫ z in acube s, g z) = 0) {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (i : Fin (n + 1)) (x : X (n + 1)) :
    (∫ z in acube s, g z * Φ (Function.update x i z))
      = ∫ z in acube s, g z * (aQ s i Φ) (Function.update x i z) := by
  have hpt : ∀ z : ℝ³, g z * Φ (Function.update x i z)
      = g z * (aQ s i Φ) (Function.update x i z) + g z * (aP s i Φ x) := by
    intro z
    have h1 : (aQ s i Φ) (Function.update x i z) = Φ (Function.update x i z) - aP s i Φ x := by
      unfold aQ
      rw [aP_const_in_coord hs i hΦ.continuous x z]
    rw [h1]; ring
  have hcont1 : Continuous fun z : ℝ³ => g z * (aQ s i Φ) (Function.update x i z) :=
    hg.mul ((contDiff_aQ hs i hΦ).continuous.comp
      (continuous_const.update i continuous_id))
  have hcont2 : Continuous fun z : ℝ³ => g z * (aP s i Φ x) := hg.mul continuous_const
  calc (∫ z in acube s, g z * Φ (Function.update x i z))
      = ∫ z in acube s, (g z * (aQ s i Φ) (Function.update x i z) + g z * (aP s i Φ x)) :=
        setIntegral_congr_fun (acube_measurable s) (fun z _ => hpt z)
    _ = (∫ z in acube s, g z * (aQ s i Φ) (Function.update x i z))
          + ∫ z in acube s, g z * (aP s i Φ x) :=
        MeasureTheory.integral_add
          (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
          (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)
    _ = (∫ z in acube s, g z * (aQ s i Φ) (Function.update x i z))
          + (∫ z in acube s, g z) * (aP s i Φ x) := by
        rw [MeasureTheory.integral_mul_const]
    _ = ∫ z in acube s, g z * (aQ s i Φ) (Function.update x i z) := by
        rw [hg0, zero_mul, add_zero]

/-- the fibre mean of `aQ s i Φ` along the `i`-th slot vanishes. -/
lemma aQ_fibre_mean_zero {s : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) (i : Fin (n + 1)) (x : X (n + 1)) :
    (∫ z in acube s, (aQ s i Φ) (Function.update x i z)) = 0 := by
  have hpt : ∀ z : ℝ³, (aQ s i Φ) (Function.update x i z)
      = Φ (Function.update x i z) - aP s i Φ x := by
    intro z
    unfold aQ
    rw [aP_const_in_coord hs i hΦ x z]
  have hcont1 : Continuous fun z : ℝ³ => Φ (Function.update x i z) :=
    hΦ.comp (continuous_const.update i continuous_id)
  have hcont2 : Continuous fun z : ℝ³ => aP s i Φ x := continuous_const
  rw [setIntegral_congr_fun (acube_measurable s) (fun z _ => hpt z)]
  rw [MeasureTheory.integral_sub
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)]
  rw [MeasureTheory.setIntegral_const, Measure.real_def, acube_volume s hs.le,
    ENNReal.toReal_ofReal (by positivity)]
  unfold aP
  rw [smul_eq_mul]
  have hs3 : s ^ 3 ≠ 0 := by positivity
  field_simp
  ring

/-- **`qModeRe` slot reduction**: the slot integral of `qModeRe s p` is the bare χ-cosine
overlap against the excited part `aQ s i Φ`. -/
lemma qModeRe_slot_eq_cos {s : ℝ} (hs : 0 < s) {n : ℕ} (p : ℝ³)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) (x : X (n + 1)) :
    (∫ z in acube s, qModeRe s p z * Φ (Function.update x i z))
      = ∫ z in acube s, chiScale s z * Real.cos (inner ℝ p z)
          * (aQ s i Φ) (Function.update x i z) := by
  rw [slot_eq_excited hs (continuous_qModeRe p) (integral_qModeRe_eq_zero hs p) hΦ i x]
  have hpt : ∀ z : ℝ³, qModeRe s p z * (aQ s i Φ) (Function.update x i z)
      = chiScale s z * Real.cos (inner ℝ p z) * (aQ s i Φ) (Function.update x i z)
        + (-((s ^ 3)⁻¹ * (modeChat s p).re)) * (aQ s i Φ) (Function.update x i z) := by
    intro z
    rw [qModeRe_eq]; ring
  have hH : Continuous fun z : ℝ³ => (aQ s i Φ) (Function.update x i z) :=
    (contDiff_aQ hs i hΦ).continuous.comp (continuous_const.update i continuous_id)
  have hcont1 : Continuous fun z : ℝ³ => chiScale s z * Real.cos (inner ℝ p z)
      * (aQ s i Φ) (Function.update x i z) :=
    (((chiScale_continuous s).mul
      (Real.continuous_cos.comp (continuous_const.inner continuous_id)))).mul hH
  have hcont2 : Continuous fun z : ℝ³ =>
      (-((s ^ 3)⁻¹ * (modeChat s p).re)) * (aQ s i Φ) (Function.update x i z) :=
    continuous_const.mul hH
  calc (∫ z in acube s, qModeRe s p z * (aQ s i Φ) (Function.update x i z))
      = ∫ z in acube s, (chiScale s z * Real.cos (inner ℝ p z)
            * (aQ s i Φ) (Function.update x i z)
          + (-((s ^ 3)⁻¹ * (modeChat s p).re)) * (aQ s i Φ) (Function.update x i z)) :=
        setIntegral_congr_fun (acube_measurable s) (fun z _ => hpt z)
    _ = (∫ z in acube s, chiScale s z * Real.cos (inner ℝ p z)
            * (aQ s i Φ) (Function.update x i z))
          + ∫ z in acube s, (-((s ^ 3)⁻¹ * (modeChat s p).re))
              * (aQ s i Φ) (Function.update x i z) :=
        MeasureTheory.integral_add
          (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
          (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)
    _ = (∫ z in acube s, chiScale s z * Real.cos (inner ℝ p z)
            * (aQ s i Φ) (Function.update x i z))
          + (-((s ^ 3)⁻¹ * (modeChat s p).re))
              * (∫ z in acube s, (aQ s i Φ) (Function.update x i z)) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ z in acube s, chiScale s z * Real.cos (inner ℝ p z)
          * (aQ s i Φ) (Function.update x i z) := by
        rw [aQ_fibre_mean_zero hs hΦ.continuous i x, mul_zero, add_zero]

end BoseGases
end Submission
