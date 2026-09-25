import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.BourgainPlan.Maximal.mstHat_decay_of_contDiff
import Submission.Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- The trigonometric-polynomial factor `x ↦ Σ_{n ∈ T} F n · e^{2πi n x}` of the wide-bump
amplitude is `C²` (indeed entire). -/
private theorem contDiff_two_mstWideExt_trig (F : ℤ → ℂ) (T : Finset ℤ) :
    ContDiff ℝ 2
      (fun x : ℝ => ∑ n ∈ T, F n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (x : ℂ)))) := by
  apply ContDiff.sum
  intro n hn
  apply ContDiff.mul contDiff_const
  exact (Complex.contDiff_exp (𝕜 := ℝ) (n := 2)).comp (by
    have : (fun x : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (x : ℂ)))
        = (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (x : ℂ)) := by
      funext x; ring
    rw [this]
    exact contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- The wide-bump amplitude `mstWideExt` is `C²`: it is the product of the rescaled bump
`x ↦ η (c_s x)` (`C²` since `η` is and `c_s ≥ 1`) with a trigonometric polynomial. -/
private theorem contDiff_two_mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (F : ℤ → ℂ) (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) :
    ContDiff ℝ 2 (mstWideExt P χ η s F T) := by
  unfold mstWideExt
  exact (hηc.comp (contDiff_const.mul contDiff_id)).mul (contDiff_two_mstWideExt_trig F T)

/-- The rescaled bump `x ↦ η (c_s x)` has compact support: `η` vanishes off `[-1/2, 1/2]` and
`c_s ≥ 1 > 0`, so the support is contained in the compact interval `[-1/(2 c_s), 1/(2 c_s)]`. -/
private theorem hasCompactSupport_rescaled_bump (P : Polynomial ℤ) (η : ℝ → ℂ) (s : ℕ)
    (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    HasCompactSupport (fun x : ℝ => η (mstWideC P s * x)) := by
  have hc : 0 < mstWideC P s := lt_of_lt_of_le zero_lt_one (one_le_mstWideC P s)
  refine HasCompactSupport.intro
    (K := Set.Icc (-(1 / (2 * mstWideC P s))) (1 / (2 * mstWideC P s))) isCompact_Icc ?_
  intro x hx
  apply hηsup
  have hxabs : 1 / (2 * mstWideC P s) < |x| := by
    rw [lt_abs]
    by_contra h
    push Not at h
    exact hx (by rw [Set.mem_Icc]; exact ⟨by linarith [h.2], h.1⟩)
  rw [abs_mul, abs_of_nonneg hc.le]
  have hthis : mstWideC P s * (1 / (2 * mstWideC P s)) = 1 / 2 := by field_simp
  rw [← hthis]
  exact mul_lt_mul_of_pos_left hxabs hc

/-- The wide-bump amplitude `mstWideExt` has compact support (contained in the support of the
rescaled bump factor). -/
private theorem hasCompactSupport_mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (F : ℤ → ℂ) (T : Finset ℤ) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    HasCompactSupport (mstWideExt P χ η s F T) := by
  have hmul := hasCompactSupport_rescaled_bump P η s hηsup
  unfold mstWideExt
  exact hmul.mul_right

/-- **Integrability of the band-limited interpolant of the wide-bump multiplier.**
The amplitude `mstWideExt` is `C²` and compactly supported, so its inverse Fourier transform
`mstWideLat = 𝓕⁻ (mstWideExt)` is integrable on `ℝ`
(`Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport`). -/
theorem mstWideLat_integrable (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    MeasureTheory.Integrable (Work.Maximal.mstWideLat P χ η s F T) := by
  exact Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport
    (contDiff_two_mstWideExt P χ η s F T hηc) (hasCompactSupport_mstWideExt P χ η s F T hηsup)

end

end Work.Maximal
