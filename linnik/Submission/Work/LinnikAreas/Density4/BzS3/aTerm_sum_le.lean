import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.sigma_half_sqrt_defs
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Work.LinnikAreas.Density4.rpow_neg_three_halves_sum_le_four

namespace Work.LinnikAreas.Density4.BzS3

open Finset

/-- For `d ∣ n`, `n ≠ 0`, the term `(1/d)·(n/d)^{-1/2}` equals `n^{-1/2}·d^{-1/2}`:
indeed `d·(n/d) = n`, so `√n = √d·√(n/d)` and both sides are `1/(√d·√(n/d))`. -/
private lemma inv_mul_inv_sqrt_div (n d : ℕ) (hdvd : d ∣ n) (hn0 : n ≠ 0) :
    (1 / (d : ℝ)) * (1 / Real.sqrt ((n / d : ℕ) : ℝ))
      = (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (d : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
    exact_mod_cast hpos
  have hnd : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  have hsq : Real.sqrt (n : ℝ) = Real.sqrt (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ) := by
    rw [← hnd, Real.sqrt_mul hd0.le]
  have hsqd : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := by
    rw [← pow_two]; exact Real.sq_sqrt hd0.le
  have hden : Real.sqrt (n : ℝ) * Real.sqrt (d : ℝ)
      = (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ) := by
    calc Real.sqrt (n : ℝ) * Real.sqrt (d : ℝ)
        = Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ)) := by
          rw [hsq]; ring
      _ = (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) * Real.sqrt ((n / d : ℕ) : ℝ) := by ring
      _ = (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ) := by rw [hsqd]
  have hL : (1 / (d : ℝ)) * (1 / Real.sqrt ((n / d : ℕ) : ℝ))
      = 1 / ((d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ)) := by
    rw [one_div, one_div, ← mul_inv, one_div]
  have hR : (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (d : ℝ))
      = 1 / ((d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ)) := by
    rw [one_div, one_div, ← mul_inv, one_div, hden]
  rw [hL, hR]

/-- Divisor-sum identity: `aTerm n = Σ_{d ∣ n} (1/d)·(n/d)^{-1/2}`. -/
private lemma divisors_sum_eq_aTerm (n : ℕ) :
    ∑ d ∈ n.divisors, (1 / (d : ℝ)) * (1 / Real.sqrt ((n / d : ℕ) : ℝ)) = aTerm n := by
  rw [aTerm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
  exact inv_mul_inv_sqrt_div n d hdvd hn0

/-- `1/(d·√d) = d^{-3/2}` for `d ≥ 1`, since `d^{3/2} = d·√d`. -/
private lemma inv_mul_sqrt_eq_rpow (d : ℕ) (hd : 1 ≤ d) :
    (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) = (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h32 : (d : ℝ) ^ (3 / 2 : ℝ) = (d : ℝ) * Real.sqrt (d : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hd0, Real.rpow_one,
      Real.rpow_div_two_eq_sqrt 1 hd0.le, Real.rpow_one]
  rw [Real.rpow_neg hd0.le, h32, inv_eq_one_div]

/-- Arithmetic term bound: for `d ≥ 1` and any `m`,
`(1/d)·2√(m/d) ≤ 2√m·d^{-3/2}`, because `√(⌊m/d⌋) ≤ √(m/d) = √m/√d` and
`2√m/(√d·d) = 2√m·d^{-3/2}`. -/
private lemma one_div_mul_two_sqrt_div_le (m d : ℕ) (hd : 1 ≤ d) :
    (1 / (d : ℝ)) * (2 * Real.sqrt (((m / d : ℕ) : ℝ)))
      ≤ 2 * Real.sqrt (m : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt (((m / d : ℕ) : ℝ)) ≤ Real.sqrt (m : ℝ) / Real.sqrt (d : ℝ) := by
    have hle : (((m / d : ℕ)) : ℝ) ≤ (m : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd0]
      exact_mod_cast Nat.div_mul_le_self m d
    calc Real.sqrt (((m / d : ℕ) : ℝ)) ≤ Real.sqrt ((m : ℝ) / (d : ℝ)) :=
          Real.sqrt_le_sqrt hle
      _ = Real.sqrt (m : ℝ) / Real.sqrt (d : ℝ) :=
          Real.sqrt_div (x := (m : ℝ)) (by positivity) (d : ℝ)
  calc (1 / (d : ℝ)) * (2 * Real.sqrt (((m / d : ℕ) : ℝ)))
      ≤ (1 / (d : ℝ)) * (2 * (Real.sqrt (m : ℝ) / Real.sqrt (d : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hs]
    _ = 2 * Real.sqrt (m : ℝ) * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
        field_simp
    _ = 2 * Real.sqrt (m : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [inv_mul_sqrt_eq_rpow d hd]

/-- **Partial sums of the `σ_{-1/2}`-weight are `O(√m)`.**  With
`aTerm r = r^{-1/2}·Σ_{d ∣ r} d^{-1/2}` (defined in the available
`Submission/Work/LinnikAreas/Density4/BzS3/sigma_half_sqrt_defs.lean`), one has
`Σ_{r ≤ m} aTerm r ≤ 16·√m`.

Route (reviewer-verified): reindex the double sum over pairs `(d, k)` with `r = d·k`
(`Work.LinnikAreas.Density4.sum_Icc_div_reindex`) to get
`Σ_{r≤m}aTerm r = Σ_{d≤m} (1/d)·Σ_{k≤m/d}k^{-1/2}`, bound the inner sum by `2√(m/d)`, and then
`Σ_{d≤m}2/√d ≤ 4√m`; the constant `16` is deliberately generous (the true size is `≈5.22√m`).
Available inputs: `Work.LinnikAreas.Density4.sum_Icc_div_reindex`,
`Work.LinnikAreas.Density4.BzS3.sum_Icc_inv_sqrt_le`,
`Work.LinnikAreas.Density4.rpow_neg_three_halves_sum_le_four`.  This result is the missing
ingredient of the available file `BzS3/sigma_half_sqrt_sum.lean`, which imports this very module,
so it must be placed at exactly this path and name. -/
theorem aTerm_sum_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ r ∈ Finset.Icc 1 m, Work.LinnikAreas.Density4.BzS3.aTerm r ≤ 16 * Real.sqrt (m : ℝ) := by
  -- Reindex the double sum over pairs `(d, k)`, `r = d·k`.
  have hreindex : (∑ r ∈ Finset.Icc 1 m, aTerm r)
      = ∑ d ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 (m / d),
          (1 / (d : ℝ)) * (1 / Real.sqrt (k : ℝ)) := by
    have h1 : (∑ r ∈ Finset.Icc 1 m, aTerm r)
        = ∑ n ∈ Finset.Icc 1 m, ∑ d ∈ n.divisors,
            (1 / (d : ℝ)) * (1 / Real.sqrt ((n / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (divisors_sum_eq_aTerm n).symm
    rw [h1]
    have h2 := Work.LinnikAreas.Density4.sum_Icc_div_reindex m (fun _ => True)
      (fun d k => (1 / (d : ℝ)) * (1 / Real.sqrt (k : ℝ)))
    simpa using h2.symm
  rw [hreindex]
  -- Each inner sum is at most `2√m·d^{-3/2}`.
  have hstep : ∀ d ∈ Finset.Icc 1 m,
      ∑ k ∈ Finset.Icc 1 (m / d), (1 / (d : ℝ)) * (1 / Real.sqrt (k : ℝ))
        ≤ 2 * Real.sqrt (m : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hsum := sum_Icc_inv_sqrt_le (m / d)
    calc ∑ k ∈ Finset.Icc 1 (m / d), (1 / (d : ℝ)) * (1 / Real.sqrt (k : ℝ))
        = (1 / (d : ℝ)) * ∑ k ∈ Finset.Icc 1 (m / d), (1 / Real.sqrt (k : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / (d : ℝ)) * (2 * Real.sqrt (((m / d : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 * Real.sqrt (m : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
          one_div_mul_two_sqrt_div_le m d hd1
  calc ∑ d ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 (m / d),
          (1 / (d : ℝ)) * (1 / Real.sqrt (k : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 m, 2 * Real.sqrt (m : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = 2 * Real.sqrt (m : ℝ) * ∑ d ∈ Finset.Icc 1 m, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt (m : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left (rpow_neg_three_halves_sum_le_four m) (by positivity)
    _ ≤ 16 * Real.sqrt (m : ℝ) := by nlinarith [Real.sqrt_nonneg (m : ℝ)]

end Work.LinnikAreas.Density4.BzS3
