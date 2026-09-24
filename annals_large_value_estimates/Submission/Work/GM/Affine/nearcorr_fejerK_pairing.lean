import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.autocorr_eq_spectral
import Submission.Work.GM.Affine.integrable_Fhat_sq
import Submission.Work.GM.Affine.fejerK_pairing

/-!
# The Fejér pairing identity for a general test function `g`

For a continuous compactly supported real function `g` and any `M₃ : ℝ`,

  `∫ x, ‖Fhat g x‖ ^ 2 * fejerK M₃ x
     = Σ_{k = -(N-1)}^{N-1} (1 - |k|/N) * ∫ v, g v * g (v + k)`,  `N = fejerN M₃`.

The Fejér kernel is the symmetric trigonometric polynomial
`fejerK M₃ x = Σ_{k=-(N-1)}^{N-1} (1 - |k|/N) cos (2π k x)`
(`fejerK_eq_sum_over_symm_range`).  Exchanging the integral with this finite sum and using
Wiener–Khinchin (`autocorr_eq_spectral`), the `k`-th Fourier coefficient of `‖Fhat g‖²` is the
autocorrelation `∫ v, g v * g (v + k)`.  The result is the pairing identity used in GM §9.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `k`-th Fourier coefficient of `‖Fhat g‖²` is the autocorrelation of `g` at lag `k`:
`∫ x, ‖Fhat g x‖ ^ 2 * cos (2 π k x) = ∫ v, g v * g (v + k)`. -/
lemma integral_Fhat_sq_cos {g : ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
    (k : ℤ) :
    (∫ x : ℝ, ‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = ∫ v : ℝ, g v * g (v + (k : ℝ)) := by
  have h1 : (∫ x : ℝ, ‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = ∫ x : ℝ, ‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * x * (k : ℝ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show ‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)
        = ‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * x * (k : ℝ))
    rw [show 2 * Real.pi * (k : ℝ) * x = 2 * Real.pi * x * (k : ℝ) by ring]
  rw [h1, ← autocorr_eq_spectral hg hcs (k : ℝ)]

theorem nearcorr_fejerK_pairing {g : ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
    (M₃ : ℝ) :
    (∫ x : ℝ, ‖Fhat g x‖ ^ 2 * fejerK M₃ x)
      = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
          (1 - |(k : ℝ)| / (fejerN M₃)) * ∫ v : ℝ, g v * g (v + (k : ℝ)) := by
  have hIntF : Integrable (fun x : ℝ => ‖Fhat g x‖ ^ 2) := integrable_Fhat_sq hg hcs
  set A : ℤ → ℝ := fun k => ∫ v : ℝ, g v * g (v + (k : ℝ)) with hA
  -- each term of the Fejér sum is integrable
  have hIntCos : ∀ k : ℤ,
      Integrable (fun x : ℝ => ‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
    intro k
    refine Integrable.mono' hIntF ?_ ?_
    · exact hIntF.aestronglyMeasurable.mul
        ((Real.continuous_cos.comp (by fun_prop : Continuous
          fun x : ℝ => 2 * Real.pi * (k : ℝ) * x)).aestronglyMeasurable)
    · filter_upwards with x
      calc ‖‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)‖
          = ‖Fhat g x‖ ^ 2 * |Real.cos (2 * Real.pi * (k : ℝ) * x)| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ ‖Fhat g x‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)
        _ = ‖Fhat g x‖ ^ 2 := by ring
  have hIntTerm : ∀ k : ℤ, Integrable (fun x : ℝ =>
      ‖Fhat g x‖ ^ 2 *
        ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))) := by
    intro k
    refine ((hIntCos k).const_mul (1 - |(k : ℝ)| / (fejerN M₃))).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  -- exchange the integral with the finite sum
  have hL2 : (∫ x : ℝ, ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
        ‖Fhat g x‖ ^ 2 *
          ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
      = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
          ∫ x : ℝ, ‖Fhat g x‖ ^ 2 *
            ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) :=
    integral_finsetSum _ (fun k _ => hIntTerm k)
  -- the `k`-th Fourier coefficient of `‖Fhat g‖²` is the autocorrelation of `g`
  have hTerm : ∀ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
      (∫ x : ℝ, ‖Fhat g x‖ ^ 2 *
          ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
        = (1 - |(k : ℝ)| / (fejerN M₃)) * A k := by
    intro k _
    rw [show (∫ x : ℝ, ‖Fhat g x‖ ^ 2 *
            ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
          = ∫ x : ℝ, (1 - |(k : ℝ)| / (fejerN M₃)) *
              (‖Fhat g x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
    rw [integral_const_mul, integral_Fhat_sq_cos hg hcs k]
  have hLHS : (∫ x : ℝ, ‖Fhat g x‖ ^ 2 * fejerK M₃ x)
      = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
          (1 - |(k : ℝ)| / (fejerN M₃)) * A k := by
    rw [show (∫ x : ℝ, ‖Fhat g x‖ ^ 2 * fejerK M₃ x)
          = ∫ x : ℝ, ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
              ‖Fhat g x‖ ^ 2 *
                ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun x => by
          show ‖Fhat g x‖ ^ 2 * fejerK M₃ x
              = ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
                  ‖Fhat g x‖ ^ 2 *
                    ((1 - |(k : ℝ)| / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
          rw [fejerK_eq_sum_over_symm_range M₃ x, Finset.mul_sum]))]
    rw [hL2]
    exact Finset.sum_congr rfl hTerm
  rw [hLHS]

end

end Work.GM.Affine
