import Mathlib
import Submission.Work.TMComp.RedC8.EllBound.Defs

/-!
# Harmonicity and nonnegativity of the harmonic-measure barrier `harc`

With `w(z) = (R + (z - E₀)) / (R - (z - E₀))` and `harc E₀ R M z = (2M/π) · Im (log w(z))`,
we show that on the upper half disk `{0 < Im z, ‖z - E₀‖ < R}`:
* `harc` is harmonic there (`Complex.log` is analytic on the slit plane, `w` takes values in the
  upper half plane, and `Im` of an analytic function is harmonic);
* `harc` is nonnegative there (`harc z = (2M/π) · arg (w z)` and `arg (w z) ≥ 0` because
  `Im (w z) > 0`).

For `R ≤ 0` the region is empty and both assertions are trivial.
-/

noncomputable section

open Complex

namespace Work.TMComp.RedC8

/-- Explicit formula for the imaginary part of the Möbius transform
`w = (R + u)/(R - u)` with `u = z - E₀`. -/
private lemma div_im_formula (E₀ R : ℝ) (z : ℂ) :
    ((R + (z - (E₀ : ℂ))) / (R - (z - (E₀ : ℂ)))).im
      = 2 * R * (z - (E₀ : ℂ)).im / Complex.normSq (R - (z - (E₀ : ℂ))) := by
  rw [Complex.div_im]
  simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.sub_im, Complex.sub_re]
  ring

/-- The Möbius transform `w = (R + (z - E₀))/(R - (z - E₀))` maps the upper half plane into
itself: `Im w > 0` whenever `Im z > 0` and `R > 0`. -/
private lemma div_im_pos (E₀ R : ℝ) (hR : 0 < R) {z : ℂ} (hz : 0 < z.im) :
    0 < ((R + (z - (E₀ : ℂ))) / (R - (z - (E₀ : ℂ)))).im := by
  rw [div_im_formula]
  have hden : 0 < Complex.normSq (R - (z - (E₀ : ℂ))) := by
    rw [Complex.normSq_pos]
    intro h
    have h0 : (R - (z - (E₀ : ℂ))).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at h0
    linarith
  have hnum : 0 < 2 * R * (z - (E₀ : ℂ)).im := by
    have h : (z - (E₀ : ℂ)).im = z.im := by simp
    rw [h]
    positivity
  exact div_pos hnum hden

/-- `harc` is nonnegative in the upper half plane. -/
private lemma harc_nonneg (E₀ R M : ℝ) (hM : 0 ≤ M) (hR : 0 < R) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ harc E₀ R M z := by
  unfold harc
  apply mul_nonneg
  · positivity
  · rw [Complex.log_im]
    exact Complex.arg_nonneg_iff.mpr (le_of_lt (div_im_pos E₀ R hR hz))

/-- `harc` is harmonic in the upper half plane. -/
private lemma harmonicAt_harc (E₀ R M : ℝ) (hR : 0 < R) {z : ℂ} (hz : 0 < z.im) :
    InnerProductSpace.HarmonicAt (harc E₀ R M) z := by
  have hden : R - (z - (E₀ : ℂ)) ≠ 0 := by
    intro h
    have h0 : (R - (z - (E₀ : ℂ))).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at h0
    linarith
  have han : AnalyticAt ℂ (fun w => (R + (w - (E₀ : ℂ))) / (R - (w - (E₀ : ℂ)))) z :=
    (analyticAt_const.add (analyticAt_id.sub analyticAt_const)).div
      (analyticAt_const.sub (analyticAt_id.sub analyticAt_const)) hden
  have hslit : ((R + (z - (E₀ : ℂ))) / (R - (z - (E₀ : ℂ)))) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt (div_im_pos E₀ R hR hz)))
  have hlog : AnalyticAt ℂ
      (fun w => Complex.log ((R + (w - (E₀ : ℂ))) / (R - (w - (E₀ : ℂ))))) z :=
    han.clog hslit
  have him : InnerProductSpace.HarmonicAt
      (fun w => (Complex.log ((R + (w - (E₀ : ℂ))) / (R - (w - (E₀ : ℂ))))).im) z :=
    hlog.harmonicAt_im
  have hsmul : InnerProductSpace.HarmonicAt
      ((2 * M / Real.pi) •
        fun w => (Complex.log ((R + (w - (E₀ : ℂ))) / (R - (w - (E₀ : ℂ))))).im) z :=
    InnerProductSpace.HarmonicAt.const_smul (c := 2 * M / Real.pi) him
  have hfun : ((2 * M / Real.pi) •
        fun w => (Complex.log ((R + (w - (E₀ : ℂ))) / (R - (w - (E₀ : ℂ))))).im)
      = harc E₀ R M := by
    funext w
    simp [harc, Pi.smul_apply, smul_eq_mul]
  rwa [hfun] at hsmul

theorem harc_harmonic_and_nonneg (E₀ R M : ℝ) (hM : 0 ≤ M) :
    InnerProductSpace.HarmonicOnNhd (Work.TMComp.RedC8.harc E₀ R M)
        {z : ℂ | 0 < z.im ∧ ‖z - (E₀ : ℂ)‖ < R} ∧
      (∀ z : ℂ, 0 < z.im → ‖z - (E₀ : ℂ)‖ < R →
        0 ≤ Work.TMComp.RedC8.harc E₀ R M z) := by
  by_cases hR : 0 < R
  · exact ⟨fun z hz => harmonicAt_harc E₀ R M hR hz.1,
      fun z hz _ => harc_nonneg E₀ R M hM hR hz⟩
  · have hs : {z : ℂ | 0 < z.im ∧ ‖z - (E₀ : ℂ)‖ < R} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      have := norm_nonneg (z - (E₀ : ℂ))
      linarith
    refine ⟨?_, ?_⟩
    · rw [hs]
      intro x hx
      exact absurd hx (Set.notMem_empty x)
    · intro z _ hzn
      have := norm_nonneg (z - (E₀ : ℂ))
      linarith

end Work.TMComp.RedC8
