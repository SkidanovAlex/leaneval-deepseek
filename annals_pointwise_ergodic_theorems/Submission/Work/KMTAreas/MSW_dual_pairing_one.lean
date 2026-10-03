import Mathlib
import Submission.Port.Aesm

open MeasureTheory
open scoped ENNReal

namespace Work.KMTAreas

/-- The finite partial sum form of the `ℓ¹` duality bound: the hypothesis that every finitely
supported `g` with `‖g‖ ≤ 1` pairs against `X` with value at most `A` forces every finite partial
sum of the `enorm`s of `X` to be at most `A`.

The test function is `g n = X n / ‖X n‖` on a finite set `s` (so that
`X n * conj (g n) = ‖X n‖`), which is finitely supported with `‖g‖ ≤ 1`. -/
theorem sum_enorm_le_of_dual_pairing {X : ℤ → ℂ} {A : NNReal}
    (h : ∀ g : ℤ → ℂ, (Function.support g).Finite → (∀ n, ‖g n‖ ≤ 1) →
      enorm (tsum (fun n : ℤ => X n * starRingEnd ℂ (g n))) ≤ ENNReal.ofReal (A : ℝ))
    (s : Finset ℤ) : ∑ n ∈ s, ‖X n‖ₑ ≤ ENNReal.ofReal (A : ℝ) := by
  -- The pointwise identity `X n * conj (X n / ‖X n‖) = ‖X n‖`.
  have key : ∀ n : ℤ, X n * (starRingEnd ℂ) (X n / ((‖X n‖ : ℝ) : ℂ)) = ((‖X n‖ : ℝ) : ℂ) := by
    intro n
    rw [map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rcases eq_or_ne (X n) 0 with h0 | h0
    · simp [h0]
    · rw [← Complex.ofReal_div]
      congr 1
      rw [pow_two, mul_div_assoc, div_self (norm_ne_zero_iff.mpr h0), mul_one]
  -- The test function, supported in `s`.
  let gs : ℤ → ℂ := fun n => if n ∈ s then X n / ((‖X n‖ : ℝ) : ℂ) else 0
  have hsupp : (Function.support gs).Finite := by
    refine s.finite_toSet.subset ?_
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hns
    exact hn (show (if n ∈ s then X n / ((‖X n‖ : ℝ) : ℂ) else 0) = 0 from if_neg hns)
  have hnorm : ∀ n, ‖gs n‖ ≤ 1 := by
    intro n
    by_cases hns : n ∈ s
    · rw [show gs n = X n / ((‖X n‖ : ℝ) : ℂ) from by simp [gs, hns]]
      rw [norm_div, show ‖(((‖X n‖ : ℝ)) : ℂ)‖ = ‖X n‖ from by
        rw [show ‖(((‖X n‖ : ℝ)) : ℂ)‖ = |(‖X n‖ : ℝ)| from RCLike.norm_ofReal _,
          abs_of_nonneg (norm_nonneg _)]]
      rcases eq_or_ne (X n) 0 with h0 | h0
      · simp [h0]
      · rw [div_self (norm_ne_zero_iff.mpr h0)]
    · rw [show gs n = 0 from by simp [gs, hns]]
      norm_num
  -- The pairing of `gs` with `X` is the real finite sum `∑_{n ∈ s} ‖X n‖`.
  have hsum : tsum (fun n : ℤ => X n * starRingEnd ℂ (gs n)) = ∑ n ∈ s, ((‖X n‖ : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := s)]
    · refine Finset.sum_congr rfl ?_
      intro n hn
      rw [show gs n = X n / ((‖X n‖ : ℝ) : ℂ) from by simp [gs, hn]]
      exact key n
    · intro n hn
      rw [show gs n = 0 from by simp [gs, hn], map_zero, mul_zero]
  have hh := h gs hsupp hnorm
  rw [hsum] at hh
  -- Compute the `enorm` of the (real, nonnegative) sum.
  have hEq : enorm (∑ n ∈ s, ((‖X n‖ : ℝ) : ℂ)) = ∑ n ∈ s, ‖X n‖ₑ := by
    rw [← ofReal_norm]
    have hnorm' : ‖(∑ n ∈ s, ((‖X n‖ : ℝ) : ℂ))‖ = ∑ n ∈ s, ‖X n‖ := by
      rw [← Complex.ofReal_sum,
        show ‖(((∑ n ∈ s, ‖X n‖ : ℝ)) : ℂ)‖ = |∑ n ∈ s, ‖X n‖| from RCLike.norm_ofReal _,
        abs_of_nonneg (Finset.sum_nonneg (fun i hi => norm_nonneg _))]
    rw [hnorm', ENNReal.ofReal_sum_of_nonneg (fun i hi => norm_nonneg _)]
    simp
  rw [hEq] at hh
  exact hh

theorem MSW_dual_pairing_one {X : ℤ → ℂ} {A : NNReal}
    (h : ∀ g : ℤ → ℂ, (Function.support g).Finite → (∀ n, ‖g n‖ ≤ 1) →
      enorm (tsum (fun n : ℤ => X n * starRingEnd ℂ (g n))) ≤ ENNReal.ofReal (A : ℝ)) :
    MeasureTheory.eLpNorm X 1 MeasureTheory.Measure.count ≤ ENNReal.ofReal (A : ℝ) := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count,
    ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  exact sum_enorm_le_of_dual_pairing h s

end Work.KMTAreas
