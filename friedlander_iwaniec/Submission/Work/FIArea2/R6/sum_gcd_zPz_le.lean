import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.Count.sum_gcd_le_mul_card_divisors
import Submission.Work.FIArea2.Count.sum_int_natAbs_le

namespace Work.FIArea2.R6

/-- `Σ_{h ∈ zPz X} gcd(|h|, c) ≤ 2 X τ(c)` for `c ≥ 1`, where `zPz X = ([-X,X] : Finset ℤ) \ {0}`
(from `Submission/Work/FIArea2/R6/BSBoxDefs.lean`). Hint: `gcd(h, c) = Σ_{e ∣ c, e ∣ h} φ(e)`
(`Commons.Data.Nat.gcd_eq_sum_totient_divisors_of_ne_zero`), interchange the sums, and bound the
number of non-zero multiples of `e ≥ 1` in `[-X, X]` by `2X/e` (or use
`Work.FIArea2.Count.sum_gcd_le_mul_card_divisors`, which gives `Σ_{1 ≤ n ≤ X} gcd(n, c) ≤ X τ(c)`,
and note that the map `h ↦ |h|` is two-to-one from `zPz X` onto `{1, …, X}`). Finally
`Σ_{e ∣ c} φ(e)/e ≤ τ(c)` since `φ(e)/e ≤ 1`. -/
theorem sum_gcd_zPz_le (c X : ℕ) (hc : 1 ≤ c) :
    ∑ h ∈ Work.FIArea2.R6.zPz X, (Nat.gcd h.natAbs c : ℝ)
      ≤ 2 * (X : ℝ) * (c.divisors.card : ℝ) := by
  -- The map `h ↦ |h|` from `zPz X` onto `{1, …, X}` is two-to-one, so the box sum is at most
  -- twice the sum over `1 ≤ n ≤ X`.
  have htwo : ∑ h ∈ Work.FIArea2.R6.zPz X, (Nat.gcd h.natAbs c : ℝ)
      ≤ 2 * ∑ n ∈ Finset.Icc 1 X, (Nat.gcd n c : ℝ) :=
    Work.FIArea2.Count.sum_int_natAbs_le X (fun n => (Nat.gcd n c : ℝ)) (fun _ => by positivity)
  -- And `Σ_{1 ≤ n ≤ X} gcd(n,c) ≤ X·τ(c)`.
  have hone : ∑ n ∈ Finset.Icc 1 X, (Nat.gcd n c : ℝ)
      ≤ (X : ℝ) * (c.divisors.card : ℝ) :=
    Work.FIArea2.Count.sum_gcd_le_mul_card_divisors c X hc
  calc ∑ h ∈ Work.FIArea2.R6.zPz X, (Nat.gcd h.natAbs c : ℝ)
      ≤ 2 * ∑ n ∈ Finset.Icc 1 X, (Nat.gcd n c : ℝ) := htwo
    _ ≤ 2 * ((X : ℝ) * (c.divisors.card : ℝ)) := by linarith
    _ = 2 * (X : ℝ) * (c.divisors.card : ℝ) := by ring

end Work.FIArea2.R6
