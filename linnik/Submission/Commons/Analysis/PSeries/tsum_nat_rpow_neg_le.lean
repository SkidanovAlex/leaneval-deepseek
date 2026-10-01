import Mathlib

/-!
# An elementary bound for the `p`-series

For `1 < p`, the series `∑' n : ℕ, n ^ (-p)` is bounded by `1 + 1 / (p - 1)`.

The proof compares the tail of the series (starting at `n = 2`) with the integral
`∫_{x > 1} x ^ (-p) dx = 1 / (p - 1)` via the integral test for antitone functions,
and adds the explicit first two terms `0 ^ (-p) = 0` and `1 ^ (-p) = 1`.
-/

open Set MeasureTheory intervalIntegral Filter

namespace Commons.Analysis.PSeries

theorem tsum_nat_rpow_neg_le {p : ℝ} (hp : 1 < p) :
    ∑' n : ℕ, (n : ℝ) ^ (-p) ≤ 1 + (p - 1)⁻¹ := by
  -- `x ↦ x ^ (-p)` is antitone on `[1, ∞)`.
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Ici (1 : ℝ)) := by
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  -- and nonnegative there.
  have hnonneg : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ t ^ (-p) := by
    intro t ht
    simp only [mem_Ioi] at ht
    exact Real.rpow_nonneg (by linarith) _
  -- and integrable on `(1, ∞)`, since `-p < -1`.
  have hint : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  -- its improper integral is `1 / (p - 1)`.
  have hintval : ∫ x in Ioi (1 : ℝ), x ^ (-p) = (p - 1)⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (a := -p) (c := 1) (by linarith) (by norm_num), Real.one_rpow,
      show (-p + 1 : ℝ) = -(p - 1) by ring, neg_div_neg_eq, one_div]
  -- Integral test: the tail `∑_{n ≥ 2} n ^ (-p)` is at most that integral.
  have htail : ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p) ≤ (p - 1)⁻¹ := by
    have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-p)) 1
      (by simpa using hanti) (by simpa using hint) (by simpa using hnonneg)
    simp only [Nat.cast_one] at h
    rw [hintval] at h
    convert h using 2 with n
  -- The full series is summable, so we can split off the first two terms.
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsplit : ∑' n : ℕ, (n : ℝ) ^ (-p)
      = ((0 : ℝ) ^ (-p) + (1 : ℝ) ^ (-p)) + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p) := by
    rw [← Summable.sum_add_tsum_nat_add 2 hsumm]
    simp [Finset.sum_range_succ]
  calc ∑' n : ℕ, (n : ℝ) ^ (-p)
      = ((0 : ℝ) ^ (-p) + (1 : ℝ) ^ (-p)) + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p) := hsplit
    _ = 1 + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p) := by
        rw [Real.zero_rpow (by linarith : (-p : ℝ) ≠ 0), Real.one_rpow]
        ring
    _ ≤ 1 + (p - 1)⁻¹ := by linarith

end Commons.Analysis.PSeries
