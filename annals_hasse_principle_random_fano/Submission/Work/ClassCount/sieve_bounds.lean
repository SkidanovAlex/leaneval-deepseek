import Mathlib
import Submission.Work.HP.HP2.moebius_sieve_lower
import Submission.Work.ClassCount.zeta_partial_sum_le
import Submission.Work.ClassCount.sieve_error_le

namespace Work.ClassCount

/-- **Möbius-sieve bounds.**  For `n ≥ 2`, `w ≥ 4`, `K ≥ 1` and a modulus `W` divisible by every
prime at most `w`, with `s := (n : ℝ) + 1`:
* `1 - 1/10 ≤ Σ_{k ≤ ⌊K⌋₊, (k,W)=1} μ(k) k^{-s}` (from
  `Work.HP.HP2.moebius_sieve_lower` with `s, w, K, P := W`, whose error term
  `w^{1-s}/(s-1) + w^{-s} ≤ 4^{-2}/2 + 4^{-3} ≤ 1/10` because `s ≥ 3`, `w ≥ 4`);
* `Σ_{k ≤ ⌊K⌋₊, (k,W)=1} k^{-s} ≤ 13/10`, since all the terms are nonnegative, `s ≥ 3`, and
  `Σ_{k ≥ 1} k^{-3} ≤ 1 + 1/8 + 1/27 + ∫_3^∞ x^{-3} dx = 1 + 1/8 + 1/27 + 1/18 ≤ 13/10`. -/
theorem sieve_bounds (n : ℕ) (hn : 2 ≤ n) (w : ℝ) (hw : 4 ≤ w) (K : ℝ) (hK : 1 ≤ K)
    (W : ℕ) (hW : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ W) :
    (1 - 1 / 10 ≤ ∑ k ∈ (Finset.range (⌊K⌋₊ + 1)).filter (fun k => Nat.Coprime k W),
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-((n : ℝ) + 1)))
    ∧ (∑ k ∈ (Finset.range (⌊K⌋₊ + 1)).filter (fun k => Nat.Coprime k W),
        (k : ℝ) ^ (-((n : ℝ) + 1)) ≤ 13 / 10) := by
  have hs3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs1 : (1 : ℝ) < (n : ℝ) + 1 := by linarith
  have hw1 : (1 : ℝ) ≤ w := by linarith
  constructor
  · -- the Möbius sieve lower bound, with the error term bounded by `1/10`
    have hsieve := Work.HP.HP2.moebius_sieve_lower ((n : ℝ) + 1) w K hs1 hw1 hK W hW
    have herr : w ^ (1 - ((n : ℝ) + 1)) / (((n : ℝ) + 1) - 1) + w ^ (-((n : ℝ) + 1)) ≤ 1 / 10 :=
      sieve_error_le ((n : ℝ) + 1) w hs3 hw
    linarith
  · -- the `k^{-s}`-mass over the coprime integers is at most `13/10`
    have hzeta : ∑ k ∈ Finset.range (⌊K⌋₊ + 1), (k : ℝ) ^ (-((n : ℝ) + 1)) ≤ 13 / 10 :=
      zeta_partial_sum_le ((n : ℝ) + 1) hs3 (⌊K⌋₊ + 1)
    calc ∑ k ∈ (Finset.range (⌊K⌋₊ + 1)).filter (fun k => Nat.Coprime k W),
            (k : ℝ) ^ (-((n : ℝ) + 1))
        ≤ ∑ k ∈ Finset.range (⌊K⌋₊ + 1), (k : ℝ) ^ (-((n : ℝ) + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
      _ ≤ 13 / 10 := hzeta

end Work.ClassCount
