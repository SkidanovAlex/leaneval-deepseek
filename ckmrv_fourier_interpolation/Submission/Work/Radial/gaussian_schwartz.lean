import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Radial.exp_iteratedFDeriv_bound
import Submission.Work.Radial.quad_iteratedFDeriv_bound
import Submission.Work.Radial.poly_mul_exp_neg_sq_bounded

namespace Work.Radial

open scoped FourierTransform SchwartzMap ContDiff
open LeanEval.Analysis.CKMRVInterpolation

/-- The complex Gaussian `x ↦ exp (π i τ ‖x‖²)` on `R^n`, with `Im τ > 0`, is a Schwartz
function: the factor `exp (-π Im τ ‖x‖²)` provides decay faster than any polynomial while
the whole function is smooth. -/
theorem gaussian_schwartz (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ x, G x = Work.Core.gaussianFun n τ x := by
  set c : ℂ := ↑Real.pi * Complex.I * τ with hc
  set a : ℝ := Real.pi * τ.im with ha
  have hapos : 0 < a := by rw [ha]; exact mul_pos Real.pi_pos hτ
  have hcre : c.re = -a := by
    rw [hc, ha]
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hf : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => c * (↑(‖x‖ ^ 2) : ℂ)) := by
    have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (‖x‖ ^ 2 : ℝ)) :=
      (Function.hasTemperateGrowth_norm_sq (H := EuclideanSpace ℝ (Fin n))).1
    have h3 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => ((‖x‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h2
    exact contDiff_const.mul h3
  refine ⟨⟨(fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (c * (↑(‖x‖ ^ 2) : ℂ))),
    ?_, ?_⟩, ?_⟩
  · exact Complex.contDiff_exp.comp hf
  · intro k m
    obtain ⟨B, hB⟩ := poly_mul_exp_neg_sq_bounded a hapos k m
    refine ⟨(Nat.factorial m : ℝ) * (2 * (‖c‖ + 1) + 1) ^ m * B, fun x => ?_⟩
    have hcomp := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := m) (N := ∞) (g := Complex.exp)
      (f := fun x : EuclideanSpace ℝ (Fin n) => c * (↑(‖x‖ ^ 2) : ℂ))
      Complex.contDiff_exp hf (by
        rw [show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top) x
      (C := Real.exp (-a * ‖x‖ ^ 2)) (D := (2 * (‖c‖ + 1) + 1) * (1 + ‖x‖) ^ 2)
      ?_ ?_
    rw [Function.comp_def] at hcomp
    · calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m
              (fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (c * (↑(‖x‖ ^ 2) : ℂ))) x‖
          ≤ ‖x‖ ^ k * ((Nat.factorial m : ℝ) * Real.exp (-a * ‖x‖ ^ 2)
              * ((2 * (‖c‖ + 1) + 1) * (1 + ‖x‖) ^ 2) ^ m) := by
            gcongr
        _ = (Nat.factorial m : ℝ) * (2 * (‖c‖ + 1) + 1) ^ m
              * (‖x‖ ^ k * (1 + ‖x‖) ^ (2 * m) * Real.exp (-a * ‖x‖ ^ 2)) := by
            rw [mul_pow, pow_mul]; ring
        _ ≤ (Nat.factorial m : ℝ) * (2 * (‖c‖ + 1) + 1) ^ m * B := by
            gcongr
            exact hB ‖x‖ (norm_nonneg x)
    · intro i hi
      have h := exp_iteratedFDeriv_bound i (c * (↑(‖x‖ ^ 2) : ℂ))
      have hxre : (c * (↑(‖x‖ ^ 2) : ℂ)).re = -a * ‖x‖ ^ 2 := by
        rw [Complex.mul_re, hcre, Complex.ofReal_im, Complex.ofReal_re]; ring
      rwa [hxre] at h
    · intro i hi1 him
      have h := quad_iteratedFDeriv_bound c i x
      refine h.trans ?_
      have hK1 : 1 ≤ 2 * (‖c‖ + 1) + 1 := by have := norm_nonneg c; linarith
      have hx1 : 1 ≤ 1 + ‖x‖ := by have := norm_nonneg x; linarith
      have h1 : 2 * (‖c‖ + 1) ≤ (2 * (‖c‖ + 1) + 1) ^ i := by
        calc 2 * (‖c‖ + 1) ≤ 2 * (‖c‖ + 1) + 1 := by linarith
          _ ≤ (2 * (‖c‖ + 1) + 1) ^ i := by
              simpa using pow_le_pow_right₀ hK1 (show 1 ≤ i by omega)
      have h2 : (1 + ‖x‖) ^ 2 ≤ (1 + ‖x‖) ^ (2 * i) :=
        pow_le_pow_right₀ hx1 (by omega)
      calc 2 * (‖c‖ + 1) * (1 + ‖x‖) ^ 2
          ≤ (2 * (‖c‖ + 1) + 1) ^ i * (1 + ‖x‖) ^ (2 * i) := by
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (((2 * (‖c‖ + 1) + 1) * (1 + ‖x‖) ^ 2)) ^ i := by
            rw [mul_pow, pow_mul]
  · intro x; rfl

end Work.Radial
