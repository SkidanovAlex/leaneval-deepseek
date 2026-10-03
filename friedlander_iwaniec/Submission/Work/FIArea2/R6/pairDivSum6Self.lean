import Mathlib
import Submission.Work.FIArea2.R6.pairFibre6Aux

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Monotonicity of a double sum over `Icc 1 ·` in both summation bounds, for a nonnegative
summand.  Used to enlarge the ranges `Icc 1 K₁`, `Icc 1 K₂` to `Icc 1 K`. -/
private lemma double_sum_Icc_mono (f : ℕ → ℕ → ℝ) (hf : ∀ d e, 0 ≤ f d e)
    {K1 K2 K : ℕ} (hK1 : K1 ≤ K) (hK2 : K2 ≤ K) :
    (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2, f d e)
      ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K, f d e := by
  have hsub1 : Finset.Icc 1 K1 ⊆ Finset.Icc 1 K := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hK1⟩
  have hsub2 : Finset.Icc 1 K2 ⊆ Finset.Icc 1 K := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hK2⟩
  calc (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2, f d e)
      ≤ ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K, f d e :=
        Finset.sum_le_sum fun d _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun e _ _ => hf d e
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K, f d e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun d _ _ =>
          Finset.sum_nonneg fun e _ => hf d e

/-- **The three divisor sums of the pair bracket, with box-shaped ranges**: the version of
`Work.FIArea2.R6.pairDivisorSums6` in which the two summation ranges are `Icc 1 K1`, `Icc 1 K2`
with `K1, K2 ≤ K` (the bound stays in terms of `K`).  Immediate from `pairDivisorSums6` by
enlarging both ranges to `Icc 1 K` (all summands are nonnegative):
`Finset.sum_le_sum_of_subset_of_nonneg` (`Icc_subset_Icc_right`). -/
theorem pairDivSum6Self :
    ∃ C : ℝ, 0 < C ∧ ∀ (K1 K2 K : ℕ), 1 ≤ K → K1 ≤ K → K2 ≤ K →
      (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
          (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            / ((d : ℝ) * (e : ℝ)))
        ≤ C * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))
      ∧ (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
          (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            / Real.sqrt (d : ℝ))
        ≤ C * (Real.sqrt (K : ℝ) * (K : ℝ)) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))
      ∧ (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
          (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
        ≤ C * ((K : ℝ) * (K : ℝ)) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
  obtain ⟨C, hCpos, hC⟩ := pairDivisorSums6
  refine ⟨C, hCpos, ?_⟩
  intro K1 K2 K hK hK1 hK2
  obtain ⟨h1, h2, h3⟩ := hC K hK
  have htau17 : ∀ d : ℕ, (0 : ℝ) ≤ (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) :=
    fun d => pow_nonneg (Nat.cast_nonneg _) _
  have htau16 : ∀ e : ℕ, (0 : ℝ) ≤ (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) :=
    fun e => pow_nonneg (Nat.cast_nonneg _) _
  refine ⟨?_, ?_, ?_⟩
  · have hf : ∀ d e : ℕ,
        (0 : ℝ) ≤ (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
          * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) / ((d : ℝ) * (e : ℝ)) :=
      fun d e => div_nonneg (mul_nonneg (htau17 d) (htau16 e))
        (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg e))
    exact le_trans (double_sum_Icc_mono _ hf hK1 hK2) h1
  · have hf : ∀ d e : ℕ,
        (0 : ℝ) ≤ (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
          * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) / Real.sqrt (d : ℝ) :=
      fun d e => div_nonneg (mul_nonneg (htau17 d) (htau16 e)) (Real.sqrt_nonneg _)
    exact le_trans (double_sum_Icc_mono _ hf hK1 hK2) h2
  · have hf : ∀ d e : ℕ,
        (0 : ℝ) ≤ (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
          * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) :=
      fun d e => mul_nonneg (htau17 d) (htau16 e)
    exact le_trans (double_sum_Icc_mono _ hf hK1 hK2) h3

end

end Work.FIArea2.R6
