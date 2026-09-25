import Mathlib

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped FourierTransform

/-- The Fourier transform of an integrable function on `ℝ` is continuous. -/
private lemma continuous_fourier_of_integrable {h : ℝ → ℂ} (hh : Integrable h) :
    Continuous (𝓕 h) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hh
  convert hc using 1
  all_goals (funext w; rw [Real.fourier_eq]; simp only [VectorFourier.fourierIntegral]; congr 1)

/-- **Two-fold integration-by-parts decay.**  If `f : ℝ → ℂ` is `C²` with compact support, then
`‖𝓕 f ξ‖ ≤ C / |ξ| ^ 2` for every `ξ ≠ 0`.  This is
`Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` at `j = 2`, but with the correct
(weaker) regularity hypothesis `ContDiff ℝ 2`. -/
private lemma fourier_decay_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hcs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 f ξ‖ ≤ C / |ξ| ^ 2 := by
  have hf' : ContDiff ℝ ((2:ℕ∞) : WithTop ℕ∞) f := by
    convert hf using 2 <;> rfl
  -- Every iterated derivative of order `≤ 2` is continuous with compact support, hence integrable.
  have hint : ∀ n : ℕ, (n:ℕ∞) ≤ (2:ℕ∞) → Integrable (iteratedDeriv n f) := by
    intro n hn
    have hsupp : HasCompactSupport (iteratedDeriv n f) := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact (hcs.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)
    exact (hf'.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport hsupp
  -- Differentiation becomes multiplication by `(2πi·)^2` under the Fourier transform.
  have hfour := Real.fourier_iteratedDeriv (f := f) (N := (2:ℕ∞)) (n := 2) hf' hint le_rfl
  have hfour' : ∀ x : ℝ, 𝓕 (iteratedDeriv 2 f) x
        = (2 * Real.pi * Complex.I * (x : ℂ)) ^ 2 • (𝓕 f x) := fun x => congrFun hfour x
  set A : ℝ := ∫ y, ‖iteratedDeriv 2 f y‖ with hAdef
  have hAbound (ξ : ℝ) : ‖𝓕 (iteratedDeriv 2 f) ξ‖ ≤ A := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq hAdef.symm
  have hAnonneg : 0 ≤ A := by
    rw [hAdef]; exact integral_nonneg (fun y => norm_nonneg _)
  have h2pi : ∀ ξ : ℝ, ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 2‖ = (2 * Real.pi * |ξ|) ^ 2 := by
    intro ξ
    rw [norm_pow]
    congr 1
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
    rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
    simp
  have hkey (ξ : ℝ) : ‖𝓕 f ξ‖ * (2 * Real.pi * |ξ|) ^ 2 ≤ A := by
    have hb : (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 f ξ‖ ≤ A := by
      have h := hAbound ξ
      rwa [hfour' ξ, norm_smul, h2pi ξ] at h
    calc ‖𝓕 f ξ‖ * (2 * Real.pi * |ξ|) ^ 2
        = (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 f ξ‖ := by ring
      _ ≤ A := hb
  refine ⟨A / (2 * Real.pi) ^ 2, div_nonneg hAnonneg (by positivity), ?_⟩
  intro ξ hξ
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  have hDpos : 0 < (2 * Real.pi * |ξ|) ^ 2 := pow_pos (by positivity) 2
  have h1 : ‖𝓕 f ξ‖ ≤ A / (2 * Real.pi * |ξ|) ^ 2 := (le_div_iff₀ hDpos).mpr (hkey ξ)
  rw [mul_pow] at h1
  have h2 : A / ((2 * Real.pi) ^ 2 * |ξ| ^ 2) = (A / (2 * Real.pi) ^ 2) / |ξ| ^ 2 := by
    rw [div_div]
  rwa [h2] at h1

/-- **A `C²` compactly supported symbol has an integrable inverse Fourier transform.**  For a function `φ : ℝ → ℂ` of class `C²` with compact support, the inverse Fourier transform `𝓕⁻φ` is integrable on `ℝ`.

Suggested route (all ingredients are in Mathlib or in the workspace's `Submission/Commons/Analysis/`):
* `‖𝓕⁻φ x‖ = ‖𝓕φ (-x)‖` (`Real.fourierInv_eq_fourier_neg`) and `‖𝓕φ ξ‖ ≤ ∫‖φ‖` everywhere;
* for `x ≠ 0`, integration by parts twice gives `‖𝓕φ x‖ ≤ ‖φ''‖₁ / (2π|x|)²`: this is exactly the statement of `Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` at `j = 2` (see `Submission/Commons/Analysis/Fourier/fourierTransform_iteratedDeriv_decay.lean`), whose proof only uses `Integrable (iteratedDeriv n φ)` for `n ≤ j` together with `Real.fourier_iteratedDeriv` — for `j = 2` that is `ContDiff ℝ 2` + `HasCompactSupport` (its statement however asks for the stronger `ContDiff ℝ ⊤`);
* combine the two bounds into `‖𝓕⁻φ x‖ ≤ B / (1 + x ^ 2)` for a suitable `B` and conclude by `Integrable.mono'` from `integrable_inv_one_add_sq`; the a.e. strong measurability needed there follows from continuity of `𝓕⁻φ` for integrable `φ` (Mathlib's `VectorFourier.fourierIntegral_continuous`, or `Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable` in `Submission/Commons/Analysis/CalderonZygmund/cz_shift.lean`).

**Import trap**: do NOT import `Submission.Work.Analysis.Fourier.dyadic_mikhlin` or `Submission.Commons.Analysis.Fourier.mean_zero_remainder_dilation_variation_ls` — each of them re-defines `Commons.Analysis.Fourier.intSplitEquiv`, which clashes with `Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp`, and the consumer of this lemma (the Mikhlin multiplier theorem) must import the latter. `Submission.Commons.Analysis.CalderonZygmund.cz_shift` and `Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` are safe to import. -/
theorem integrable_fourierInv_of_contDiff_two_hasCompactSupport {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    MeasureTheory.Integrable (FourierTransformInv.fourierInv φ) MeasureTheory.volume := by
  have hint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hcontF : Continuous (𝓕 φ) := continuous_fourier_of_integrable hint
  have hcontInv : Continuous (FourierTransformInv.fourierInv φ) := by
    rw [show FourierTransformInv.fourierInv φ = (𝓕 φ) ∘ Neg.neg from by
      funext w; rw [Real.fourierInv_eq_fourier_neg]; rfl]
    exact hcontF.comp continuous_neg
  obtain ⟨C, hCnn, hC⟩ := fourier_decay_two hφ hφc
  set I : ℝ := ∫ y, ‖φ y‖ with hIdef
  have hI0 : 0 ≤ I := by rw [hIdef]; exact integral_nonneg (fun y => norm_nonneg _)
  have hIbound (ξ : ℝ) : ‖𝓕 φ ξ‖ ≤ I := by
    rw [hIdef, Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq rfl
  set B : ℝ := max (2 * I) (2 * C) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]; exact le_trans (by linarith) (le_max_left _ _)
  -- The two bounds combine into `‖𝓕⁻φ x‖ ≤ B / (1 + x ^ 2)`.
  have hbound : ∀ x : ℝ, ‖FourierTransformInv.fourierInv φ x‖ ≤ B * (1 + x^2)⁻¹ := by
    intro x
    rw [Real.fourierInv_eq_fourier_neg]
    by_cases hx1 : |x| ≤ 1
    · -- small `|x|`: use the trivial sup bound.
      have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
      have hIx : I * (1 + x^2) ≤ B := by
        have h2 : (1:ℝ) + x^2 ≤ 2 := by linarith
        calc I * (1 + x^2) ≤ I * 2 := by nlinarith
          _ = 2 * I := by ring
          _ ≤ B := by rw [hBdef]; exact le_max_left _ _
      have hden : (0:ℝ) < 1 + x^2 := by positivity
      have hstep : I ≤ B * (1 + x^2)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (le_div_iff₀ hden).mpr hIx
      linarith [hIbound (-x), hstep]
    · -- large `|x|`: use the integration-by-parts decay.
      push Not at hx1
      have hxne : -x ≠ 0 := by
        have : x ≠ 0 := abs_pos.mp (lt_trans zero_lt_one hx1)
        simpa using this
      have h2 : ‖𝓕 φ (-x)‖ ≤ C / |(-x)| ^ 2 := hC (-x) hxne
      rw [abs_neg] at h2
      have hx2 : 1 < x^2 := by nlinarith [sq_abs x, abs_nonneg x]
      have hCx : C * (1 + x^2) ≤ B * x^2 := by
        have h2' : (1:ℝ) + x^2 ≤ 2 * x^2 := by linarith
        calc C * (1 + x^2) ≤ C * (2 * x^2) := by nlinarith
          _ = (2 * C) * x^2 := by ring
          _ ≤ B * x^2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              rw [hBdef]; exact le_max_right _ _
      have hden : (0:ℝ) < 1 + x^2 := by positivity
      have hden2 : (0:ℝ) < |x|^2 := by positivity
      have hstep : C / |x|^2 ≤ B * (1 + x^2)⁻¹ := by
        rw [← div_eq_mul_inv]
        rw [div_le_div_iff₀ hden2 hden]
        rw [sq_abs]
        exact hCx
      linarith [h2, hstep]
  have hnormg : ∀ x : ℝ, ‖B * (1 + x^2)⁻¹‖ = B * (1 + x^2)⁻¹ := by
    intro x
    rw [norm_mul, Real.norm_of_nonneg hB0, Real.norm_of_nonneg (by positivity)]
  refine Integrable.mono (integrable_inv_one_add_sq.const_mul B) hcontInv.aestronglyMeasurable ?_
  filter_upwards with x
  rw [hnormg]
  exact hbound x

end Work.BourgainPlan.Maximal
