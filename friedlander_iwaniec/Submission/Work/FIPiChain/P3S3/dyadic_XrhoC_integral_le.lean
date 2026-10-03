/-
# `Work.FIPiChain.P3S3.dyadic_XrhoC_integral_le`

The `s`-integral of the `ρ`-weighted dyadic window `(z, 2^J z]` is bounded by the sum of the
`s`-integrals of the elementary dyadic windows `(2^j z, 2^{j+1} z]`, `j < J`.

This is the "integrate the §8 dyadic splitting" step of the companion's §8 estimate.  All the
pointwise input (`Work.FIChain.XrhoC_dyadic`) and the integrability of the individual pieces
(`Work.FIChain.measurable_XrhoC`, `Work.FIChain.abs_XrhoC_le`,
`Submission.ASP.intervalIntegrable_div_Ioc`) live in `Submission.Work.FIChain.abs_S3minusC_le`;
here we only assemble them.
-/
import Mathlib
import Submission.Work.FIChain.abs_S3minusC_le
import Submission.Work.FIPiChain.Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIPiChain.P3S3

open Finset MeasureTheory
open scoped Interval BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem dyadic_XrhoC_integral_le (a w : ℕ → ℝ) (N : ℕ) (z C : ℝ) (J : ℕ)
    (hC : 1 ≤ C) (hz : 0 < z) (hw0 : ∀ ℓ : ℕ, 0 ≤ w ℓ) :
    (∫ s in (1 : ℝ)..C,
        (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|) / s)
      ≤ ∑ j ∈ Finset.range J,
          ∫ s in (1 : ℝ)..C,
            (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
              * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s := by
  classical
  -- Integrability of every window integrand, uniformly in the window endpoints.
  have hIntGen : ∀ (t u : ℝ), IntervalIntegrable
      (fun s : ℝ => (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s t u|) / s)
      volume (1 : ℝ) C := by
    intro t u
    have hfun : (fun s : ℝ =>
          (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s t u|) / s)
        = ∑ ℓ ∈ Finset.Icc 1 N,
            fun s : ℝ => w ℓ * (|Work.FITop.XrhoC a N ℓ s t u| / s) := by
      funext s
      rw [Finset.sum_apply, Finset.sum_div]
      exact Finset.sum_congr rfl (fun ℓ _ => by ring)
    rw [hfun]
    exact IntervalIntegrable.sum _ (fun ℓ _ =>
      (Submission.ASP.intervalIntegrable_div_Ioc
        (Work.FIChain.measurable_XrhoC a N ℓ t u).abs one_pos hC
        (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)|)
        (fun s _ => by simpa using Work.FIChain.abs_XrhoC_le a N ℓ s t u)).const_mul (w ℓ))
  -- The pointwise dyadic triangle inequality.
  have hpt : ∀ s ∈ Set.Icc (1 : ℝ) C,
      (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|) / s
        ≤ ∑ j ∈ Finset.range J,
            (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
              * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs.1
    have hdyad : ∀ ℓ : ℕ, |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|
        ≤ ∑ j ∈ Finset.range J,
            |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
      intro ℓ
      rw [Work.FIChain.XrhoC_dyadic a N ℓ s hz J]
      exact Finset.abs_sum_le_sum_abs _ _
    have hnum : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|)
        ≤ ∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ
            * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
      calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|)
          ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * ∑ j ∈ Finset.range J,
              |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
            Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hdyad ℓ) (hw0 ℓ))
        _ = ∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ
              * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
            rw [Finset.sum_congr rfl (fun ℓ _ => Finset.mul_sum _ _ _), Finset.sum_comm]
    calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|) / s
        ≤ (∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ
              * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s :=
          div_le_div_of_nonneg_right hnum hs0.le
      _ = ∑ j ∈ Finset.range J,
            (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
              * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s :=
          Finset.sum_div _ _ _
  have hIntF : IntervalIntegrable
      (fun s : ℝ => (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|) / s)
      volume (1 : ℝ) C := hIntGen z ((2 : ℝ) ^ J * z)
  have hIntG : ∀ j ∈ Finset.range J, IntervalIntegrable
      (fun s : ℝ => (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
          * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s)
      volume (1 : ℝ) C :=
    fun j _ => hIntGen ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)
  have hIntGsum : IntervalIntegrable
      (fun s : ℝ => ∑ j ∈ Finset.range J, (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
          * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s)
      volume (1 : ℝ) C := by
    have hfun : (fun s : ℝ => ∑ j ∈ Finset.range J, (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
          * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s)
        = ∑ j ∈ Finset.range J, fun s : ℝ => (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
          * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s := by
      funext s
      rw [Finset.sum_apply]
    rw [hfun]
    exact IntervalIntegrable.sum _ hIntG
  calc (∫ s in (1 : ℝ)..C,
        (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ s z ((2 : ℝ) ^ J * z)|) / s)
      ≤ ∫ s in (1 : ℝ)..C, ∑ j ∈ Finset.range J, (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
          * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s := by
        refine intervalIntegral.integral_mono_ae_restrict hC hIntF hIntGsum ?_
        change ∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) C)),
            (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * |Work.FITop.XrhoC a N ℓ x z ((2 : ℝ) ^ J * z)|) / x
              ≤ ∑ j ∈ Finset.range J, (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
                  * |Work.FITop.XrhoC a N ℓ x ((2 : ℝ) ^ j * z)
                      ((2 : ℝ) ^ (j + 1) * z)|) / x
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        exact Filter.Eventually.of_forall (fun s hs => hpt s hs)
    _ = ∑ j ∈ Finset.range J, ∫ s in (1 : ℝ)..C, (∑ ℓ ∈ Finset.Icc 1 N, w ℓ
          * |Work.FITop.XrhoC a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|) / s :=
        intervalIntegral.integral_finsetSum hIntG

end

end Work.FIPiChain.P3S3
