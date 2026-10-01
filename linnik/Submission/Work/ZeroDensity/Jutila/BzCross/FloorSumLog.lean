import Mathlib

namespace Work.ZeroDensity.Jutila.BzCross

open Finset

/-- Recurrence for the sum of `log(n/r)`: pulling off the last term `r = n+1`. -/
private lemma sum_log_div_succ (n : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.Icc 1 (n + 1), Real.log (((n : ℝ) + 1) / (r : ℝ)))
      = (∑ r ∈ Finset.Icc 1 n, Real.log ((n : ℝ) / (r : ℝ)))
        + (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
  have h1 : 1 ≤ n + 1 := by omega
  rw [Finset.sum_Icc_succ_top h1]
  have hterm : Real.log (((n : ℝ) + 1) / (((n + 1 : ℕ)) : ℝ)) = 0 := by
    rw [Nat.cast_add, Nat.cast_one]
    have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    rw [div_self hne, Real.log_one]
  rw [hterm, add_zero]
  have hpt : ∀ r ∈ Finset.Icc 1 n,
      Real.log (((n : ℝ) + 1) / (r : ℝ))
        = Real.log ((n : ℝ) / (r : ℝ)) + Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
    have hx : (n : ℝ) / (r : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hy : ((n : ℝ) + 1) / (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have h := Real.log_mul hx hy
    have heq : (n : ℝ) / (r : ℝ) * (((n : ℝ) + 1) / (n : ℝ)) = ((n : ℝ) + 1) / (r : ℝ) := by
      field_simp
    rwa [heq] at h
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]

/-- `∑_{r=1}^{n} log(n/r) ≤ n - 1` for `n ≥ 1` (the telescoping log-sum bound). -/
private lemma sum_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.Icc 1 n, Real.log ((n : ℝ) / (r : ℝ))) ≤ (n : ℝ) - 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [sum_log_div_succ n hn]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ 1 / (n : ℝ) := by
      have hpos : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
      have h := Real.log_le_sub_one_of_pos hpos
      have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
      rwa [heq] at h
    have hmul : (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ 1 := by
      calc (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ))
          ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hlog (le_of_lt hn0)
        _ = 1 := by rw [mul_one_div, div_self hnne]
    calc (∑ r ∈ Finset.Icc 1 n, Real.log ((n : ℝ) / (r : ℝ)))
          + (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ))
        ≤ ((n : ℝ) - 1) + 1 := add_le_add ih hmul
      _ = ((n : ℝ) + 1) - 1 := by ring

/-- Splitting a constant and a `+1` off a finite sum over `Icc 1 n`. -/
private lemma sum_add_const (n : ℕ) (g : ℕ → ℝ) (c : ℝ) :
    (∑ r ∈ Finset.Icc 1 n, (c + g r + 1)) = (n : ℝ) * c + (∑ r ∈ Finset.Icc 1 n, g r) + (n : ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- **Sum of the `log(U/r)+1` weights.** For `U > 0` and `R = ⌊U⌋₊`,
`Σ_{r=1}^{R} (log(U/r) + 1) ≤ 3R`. (`R = 0` gives the empty sum.)
ROUTE: if `R ≥ 1` then `U < R+1 ≤ 2R`, so for `1 ≤ r ≤ R`,
`log(U/r) ≤ log 2 + log(R/r)`; and `Σ_{r=1}^{R} log(R/r) ≤ R − 1` by writing
`log(R/r) = Σ_{j=r}^{R−1} log((j+1)/j)` (`= 0` at `r = R`), swapping the two sums to get
`Σ_{j=1}^{R−1} j·log(1+1/j)`, and using `log(1+1/j) ≤ 1/j`. Adding the `R` terms `+1` and
`R·log 2 ≤ R` gives `≤ R(log 2 + 2) − 1 ≤ 3R`. -/
theorem FloorSumLog (U : ℝ) (hU : 0 < U) :
    ∑ r ∈ Finset.Icc 1 ⌊U⌋₊, (Real.log (U / (r : ℝ)) + 1) ≤ 3 * ((⌊U⌋₊ : ℕ) : ℝ) := by
  by_cases h0 : ⌊U⌋₊ = 0
  · rw [h0]
    simp
  · have hn1 : 1 ≤ ⌊U⌋₊ := by omega
    set n : ℕ := ⌊U⌋₊ with hn
    have hn1' : 1 ≤ n := hn1
    have hR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
    have hUlt : U < (n : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one U
      rw [← hn] at h
      exact h
    have hUle : U ≤ 2 * (n : ℝ) := by linarith
    have hpt : ∀ r ∈ Finset.Icc 1 n,
        Real.log (U / (r : ℝ)) + 1 ≤ Real.log 2 + Real.log ((n : ℝ) / (r : ℝ)) + 1 := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrpos : (0 : ℝ) < (r : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
      have hUrpos : (0 : ℝ) < U / (r : ℝ) := by positivity
      have hle : U / (r : ℝ) ≤ 2 * (n : ℝ) / (r : ℝ) :=
        div_le_div_of_nonneg_right hUle (le_of_lt hrpos)
      have hl := Real.log_le_log hUrpos hle
      have hsplit : Real.log (2 * (n : ℝ) / (r : ℝ))
          = Real.log 2 + Real.log ((n : ℝ) / (r : ℝ)) := by
        rw [mul_div_assoc, Real.log_mul (by norm_num) (ne_of_gt (by positivity))]
      linarith
    have key : (∑ r ∈ Finset.Icc 1 n, (Real.log (U / (r : ℝ)) + 1))
        ≤ (n : ℝ) * Real.log 2 + (∑ r ∈ Finset.Icc 1 n, Real.log ((n : ℝ) / (r : ℝ)))
          + (n : ℝ) := by
      calc (∑ r ∈ Finset.Icc 1 n, (Real.log (U / (r : ℝ)) + 1))
          ≤ ∑ r ∈ Finset.Icc 1 n, (Real.log 2 + Real.log ((n : ℝ) / (r : ℝ)) + 1) :=
            Finset.sum_le_sum hpt
        _ = (n : ℝ) * Real.log 2 + (∑ r ∈ Finset.Icc 1 n, Real.log ((n : ℝ) / (r : ℝ)))
              + (n : ℝ) := by
            rw [sum_add_const]
    have hS := sum_log_div_le n hn1'
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hRlog : (n : ℝ) * Real.log 2 ≤ (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
      simpa using h
    calc (∑ r ∈ Finset.Icc 1 n, (Real.log (U / (r : ℝ)) + 1))
        ≤ (n : ℝ) * Real.log 2 + (∑ r ∈ Finset.Icc 1 n, Real.log ((n : ℝ) / (r : ℝ)))
            + (n : ℝ) := key
      _ ≤ (n : ℝ) * Real.log 2 + ((n : ℝ) - 1) + (n : ℝ) := by linarith
      _ ≤ 3 * (n : ℝ) := by linarith

end Work.ZeroDensity.Jutila.BzCross
