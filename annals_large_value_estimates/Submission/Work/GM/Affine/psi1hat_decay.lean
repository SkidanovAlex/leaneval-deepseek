import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay

/-!
# Decay of the Fourier transform `\hat\psi_1`

GM §9 uses the Fourier transform of the smooth bump `ψ₁ = psi1 K`, which is `C^∞` and
compactly supported (its support lies in `[-(K+1), K+1]`).  Consequently `hat ψ₁` decays faster
than any polynomial: for every `N` there is `C > 0` with

`‖psi1hat K y‖ ≤ C / (1 + |y|)^N`  for all `y`.

The decay for `|y| ≥ 1` is `Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay`
(applied to the `N`-th derivative); on the remaining compact range `|y| ≤ 1` the trivial bound
`‖𝓕 f y‖ ≤ ∫ ‖f‖` is used.
-/

namespace Work.GM.Affine

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

noncomputable section

/-- **Faster than polynomial decay of the Fourier transform of a `C^∞` compactly supported
function.**  For every `N : ℕ` there is `C > 0` with `‖𝓕 f y‖ ≤ C / (1 + |y|)^N`. -/
theorem fourier_decay_one_add (N : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcs : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖𝓕 f y‖ ≤ C / (1 + |y|) ^ N := by
  obtain ⟨C₀, hC₀, hb⟩ :=
    Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay N hf hcs
  -- The trivial (`L¹`) bound, used on the compact range `|y| ≤ 1`.
  set B : ℝ := ∫ t, ‖f t‖ with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact integral_nonneg (fun t => norm_nonneg _)
  have hB : ∀ y : ℝ, ‖𝓕 f y‖ ≤ B := by
    intro y
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [hBdef]
    refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)))
    simp
  have h2N : (0 : ℝ) ≤ 2 ^ N := pow_nonneg (by norm_num) N
  have hCpos : 0 < (B + C₀) * 2 ^ N + 1 := by
    have : 0 ≤ (B + C₀) * 2 ^ N := mul_nonneg (by linarith) h2N
    linarith
  refine ⟨(B + C₀) * 2 ^ N + 1, hCpos, fun y => ?_⟩
  have hden : 0 < (1 + |y|) ^ N := by positivity
  rw [le_div_iff₀ hden]
  by_cases h : |y| ≤ 1
  · have h2 : (1 + |y|) ^ N ≤ 2 ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have h1 := hB y
    have h1nn : (0 : ℝ) ≤ ‖𝓕 f y‖ := norm_nonneg _
    calc ‖𝓕 f y‖ * (1 + |y|) ^ N ≤ B * 2 ^ N := mul_le_mul h1 h2 (by positivity) hBnn
      _ ≤ (B + C₀) * 2 ^ N + 1 := by
          have : 0 ≤ C₀ * 2 ^ N := mul_nonneg hC₀ h2N
          nlinarith
  · have h1 : 1 < |y| := lt_of_not_ge h
    have hy : y ≠ 0 := by rintro rfl; norm_num at h1
    have h2 : (1 + |y|) ^ N ≤ 2 ^ N * |y| ^ N := by
      calc (1 + |y|) ^ N ≤ (2 * |y|) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * |y| ^ N := mul_pow 2 |y| N
    have hyN : |y| ^ N ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hy)
    have hb' := hb y hy
    have hbnn : (0 : ℝ) ≤ C₀ / |y| ^ N := le_trans (norm_nonneg _) hb'
    calc ‖𝓕 f y‖ * (1 + |y|) ^ N ≤ (C₀ / |y| ^ N) * (2 ^ N * |y| ^ N) :=
          mul_le_mul hb' h2 (by positivity) hbnn
      _ = C₀ * 2 ^ N := by field_simp
      _ ≤ (B + C₀) * 2 ^ N + 1 := by
          have hBn : 0 ≤ B * 2 ^ N := mul_nonneg hBnn h2N
          have hCn : 0 ≤ C₀ * 2 ^ N := mul_nonneg hC₀ h2N
          nlinarith

/-- The bump `ψ₁` is `C^∞` after viewing it as a complex-valued function. -/
theorem psi1_ofReal_contDiff (K : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ((psi1 K t : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (psi1_contDiff K)

/-- The bump `ψ₁` has compact support (contained in `[-(K+1), K+1]`). -/
theorem psi1_ofReal_hasCompactSupport (K : ℝ) :
    HasCompactSupport (fun t : ℝ => ((psi1 K t : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(K + 1)) (K + 1)) isCompact_Icc ?_
  intro x hx
  have hmem : ¬ (-(K + 1) ≤ x ∧ x ≤ K + 1) := by
    simpa [Set.mem_Icc] using hx
  rw [not_and_or] at hmem
  have habs : K + 1 ≤ |x| := by
    rcases hmem with h | h
    · have hx' : K + 1 < -x := by
        have h' : x < -(K + 1) := lt_of_not_ge h
        linarith
      exact le_trans hx'.le (neg_le_abs x)
    · have hx' : K + 1 < x := lt_of_not_ge h
      exact le_trans hx'.le (le_abs_self x)
  rw [psi1_eq_zero habs]
  simp

/-- **Decay of `\hat\psi_1`**: for every `N` there is `C > 0` such that
`‖psi1hat K y‖ ≤ C / (1 + |y|)^N` for all `y`. -/
theorem psi1hat_decay (K : ℝ) (hK : 0 < K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖psi1hat K y‖ ≤ C / (1 + |y|) ^ N := by
  obtain ⟨C, hC, hb⟩ := fourier_decay_one_add N (psi1_ofReal_contDiff K)
    (psi1_ofReal_hasCompactSupport K)
  exact ⟨C, hC, fun y => by rw [psi1hat]; exact hb y⟩

end

end Work.GM.Affine
