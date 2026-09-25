import Mathlib
import Submission.Commons.Analysis.Real.sum_range_mul_le_lintegral_of_antitone

namespace Commons.Analysis.Real

open MeasureTheory
open scoped ENNReal

/-- **Dyadic sum bounded by the integral of the entropy majorant.**

Let `E : ℝ → ℝ≥0∞` be non-increasing on the positive half-line.  For a natural number
`K` and a sequence `M : ℕ → ℕ` whose values are dominated by the dyadic samples `E (2^{-t})`
(in `ℝ≥0∞`), the dyadic sum
`∑_{t ≤ S} 2^{-t} √(min K (M t + 1))`
is at most twice the integral over `(0,1]` of the `ℝ≥0∞`-valued majorant
`min (√K) ((E r + 1)^{1/2})`.

The proof compares the `t`-th term with the integral over the dyadic cell
`(2^{-(t+1)}, 2^{-t}]`, where `E r ≥ E(2^{-t}) ≥ M t`, hence
`√(min K (M t + 1)) ≤ min (√K) ((E r + 1)^{1/2})`. -/
theorem ofReal_sum_dyadic_le_lintegral_entropy_Ioc (E : ℝ → ENNReal)
    (hE : ∀ x y : ℝ, 0 < x → x ≤ y → E y ≤ E x)
    (K : ℕ) (M : ℕ → ℕ) (hM : ∀ t : ℕ, (M t : ENNReal) ≤ E ((1/2 : ℝ) ^ t)) (S : ℕ) :
    ENNReal.ofReal (∑ t ∈ Finset.range (S + 1),
        (1/2 : ℝ) ^ t * Real.sqrt (min (K : ℝ) ((M t : ℝ) + 1)))
      ≤ 2 * MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc (0:ℝ) 1))
          (fun r : ℝ => min (ENNReal.ofReal (Real.sqrt (K : ℝ))) ((E r + 1) ^ (1/2 : ℝ))) := by
  -- The `ℝ≥0∞`-valued majorant appearing on the right-hand side.
  let f : ℝ → ENNReal := fun r => min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r + 1) ^ (1/2:ℝ))
  -- `f` is non-increasing on `(0,∞)`: `E` is, and `x ↦ (x+1)^{1/2}` and `min` preserve this.
  have hf : ∀ x y : ℝ, 0 < x → x ≤ y → f y ≤ f x := by
    intro x y hx hxy
    apply min_le_min le_rfl
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact add_le_add (hE x y hx hxy) le_rfl
  -- Dyadic sum versus integral for the non-increasing function `f`.
  have hmain := sum_range_mul_le_lintegral_of_antitone f hf (S+1)
  -- The `t`-th dyadic sample of `f` dominates `√(min K (M t + 1))`.
  have hbound : ∀ t : ℕ,
      ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t:ℝ)+1))) ≤ f ((1/2:ℝ)^t) := by
    intro t
    apply le_min
    · -- `√(min K (M t+1)) ≤ √K`
      apply ENNReal.ofReal_mono
      apply Real.sqrt_le_sqrt
      exact min_le_left _ _
    · -- `√(min K (M t+1)) ≤ (E(2^{-t}) + 1)^{1/2}`
      have h1 : ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t:ℝ)+1)))
            ≤ ENNReal.ofReal (Real.sqrt ((M t:ℝ)+1)) := by
        apply ENNReal.ofReal_mono
        apply Real.sqrt_le_sqrt
        exact min_le_right _ _
      have h2 : ENNReal.ofReal (Real.sqrt ((M t:ℝ)+1)) = ((M t:ENNReal) + 1) ^ (1/2:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rw [← ENNReal.ofReal_rpow_of_nonneg (x := (M t:ℝ)+1) (p := (1/2:ℝ))
              (by positivity) (by norm_num)]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
      rw [h2] at h1
      refine le_trans h1 ?_
      -- `(M t + 1)^{1/2} ≤ (E(2^{-t}) + 1)^{1/2}`
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact add_le_add (hM t) le_rfl
  -- `ofReal` distributes over the finite sum and each term is bounded by the corresponding one for `f`.
  have hterm : ∀ t ∈ Finset.range (S+1),
      ENNReal.ofReal ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t:ℝ)+1)))
        ≤ (1/2:ENNReal)^t * f ((1/2:ℝ)^t) := by
    intro t ht
    rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num) t)]
    have hpow : ENNReal.ofReal ((1/2:ℝ)^t) = (1/2:ENNReal)^t := by
      rw [show (1/2:ENNReal) = ENNReal.ofReal (1/2:ℝ) by simp,
          ← ENNReal.ofReal_pow (by norm_num)]
    rw [hpow]
    gcongr
    exact hbound t
  have hsum : ENNReal.ofReal (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t:ℝ)+1)))
      ≤ ∑ t ∈ Finset.range (S+1), (1/2:ENNReal)^t * f ((1/2:ℝ)^t) := by
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun t ht => mul_nonneg (pow_nonneg (by norm_num) t) (Real.sqrt_nonneg _))]
    exact Finset.sum_le_sum hterm
  calc ENNReal.ofReal (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t:ℝ)+1)))
      ≤ ∑ t ∈ Finset.range (S+1), (1/2:ENNReal)^t * f ((1/2:ℝ)^t) := hsum
    _ ≤ 2 * ∫⁻ r in Set.Ioc (0:ℝ) 1, f r := hmain

end Commons.Analysis.Real
