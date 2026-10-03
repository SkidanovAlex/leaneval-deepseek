/-
# `Submission.Work.FIArea6Road.DivisorWindowDefs`

Vocabulary for the window estimate `sum_tau_sq_window_le`: the divisor function `τ`, its
summatory function `D2`, the "four-fold divisor function" `d4 = τ * τ` and its summatory `D4`.
-/
import Mathlib
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_asymptotic
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea3.sum_tau_pow_div_sqrt_le

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

noncomputable section

/-- `τ(n) = #(n.divisors)`, viewed as a real number. -/
def tauR (n : ℕ) : ℝ := (n.divisors.card : ℝ)

/-- `D2(x) = ∑_{n ≤ x} τ(n)`. -/
def D2 (x : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 x, tauR n

/-- The four-fold divisor function, as the Dirichlet convolution `d4 = τ * τ`. -/
def d4 (n : ℕ) : ℝ := ∑ a ∈ n.divisors, tauR a * tauR (n / a)

/-- `D4(x) = ∑_{n ≤ x} d4(n)`. -/
def D4 (x : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 x, d4 n

lemma tauR_nonneg (n : ℕ) : 0 ≤ tauR n := by
  unfold tauR; positivity

lemma D2_zero : D2 0 = 0 := by simp [D2]

lemma d4_nonneg (n : ℕ) : 0 ≤ d4 n := by
  unfold d4
  exact Finset.sum_nonneg fun a _ => mul_nonneg (tauR_nonneg a) (tauR_nonneg _)

lemma D4_nonneg (x : ℕ) : 0 ≤ D4 x := by
  unfold D4
  exact Finset.sum_nonneg fun n _ => d4_nonneg n

end

end Work.FIArea6Road
