import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Work.FIArea2.sum_weight_sqcong
import Submission.Work.FIArea2.Count.summable_int_rpow_majorant
import Submission.Work.FIArea2.Count.summable_Wt_tau4
import Submission.Work.FIArea2.Count.dyadic_weight_pointwise
import Submission.Work.FIArea2.Count.dyadic_log_series_bound
import Submission.Work.FIArea2.R6.Lsum_fixedK
import Submission.Work.FIArea2.R6.Swapper6

namespace Work.FIArea2.R6

theorem hL_of_box (C : ℝ) (hC : 0 < C) (K : ℕ)
    (hbox : ∀ (R : ℕ), 1 ≤ R → ∀ (X : ℕ), 1 ≤ X → ∀ (Y : ℕ), 1 ≤ Y →
      (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
      ≤ C * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ K) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (H : ℝ), 1 ≤ H → ∀ (R : ℕ), 1 ≤ R →
        (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
          * (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              (Nat.gcd u1.natAbs u2.natAbs : ℝ)
                * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
        ≤ C' * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2)
            * (Real.log (H + R + 2)) ^ K := by
  obtain ⟨C', hC', hb⟩ := hL_avg_fixedK_of_box C hC K hbox
  refine ⟨C', hC', fun H hH R hR => ?_⟩
  rw [← swap_uh H hH R]
  exact hb H hH R hR

end Work.FIArea2.R6
