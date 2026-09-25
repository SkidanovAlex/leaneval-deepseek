import Mathlib

namespace Work.RHContract.A.RegionI

open scoped BigOperators

/-- On `[0, 1/2]` the magnitudes `t ^ (n+1) / (n+1)` of the terms of the Taylor series of
`log (1 + t)` are antitone in `n`.  This is what makes the alternating series test apply. -/
lemma altLog_term_antitone {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Antitone (fun n : ℕ => t ^ (n + 1) / ((n : ℝ) + 1)) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show n + 1 + 1 = n + 2 by omega]
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  rw [show t ^ (n + 2) = t ^ (n + 1) * t by rw [pow_succ]]
  have hpow : (0 : ℝ) ≤ t ^ (n + 1) := pow_nonneg h0 _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmain : t / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h1, hn]
  have step : t ^ (n + 1) * (t / ((n : ℝ) + 2)) ≤
      t ^ (n + 1) * (1 / ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hmain hpow
  calc t ^ (n + 1) * t / ((n : ℝ) + 2)
      = t ^ (n + 1) * (t / ((n : ℝ) + 2)) := by ring
    _ ≤ t ^ (n + 1) * (1 / ((n : ℝ) + 1)) := step
    _ = t ^ (n + 1) / ((n : ℝ) + 1) := by ring

/-- The Taylor series `Σ (-1)^n t^(n+1)/(n+1)` of `log (1 + t)` converges to `log (1 + t)`
for `0 ≤ t ≤ 1/2` (indeed for `|t| < 1`). -/
lemma altLog_hasSum {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (t ^ (n + 1) / ((n : ℝ) + 1)))
      (Real.log (1 + t)) := by
  have hx : |(-t)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have hbase := Real.hasSum_pow_div_log_of_abs_lt_one (x := -t) hx
  rw [show (1 : ℝ) - -t = 1 + t by ring] at hbase
  have hterm : ∀ n : ℕ,
      (-1 : ℝ) ^ n * (t ^ (n + 1) / ((n : ℝ) + 1)) = -(((-t) ^ (n + 1)) / ((n : ℝ) + 1)) := by
    intro n
    rw [neg_pow, pow_succ]
    ring
  simpa only [neg_neg] using hbase.neg.congr_fun hterm

/-- The alternating series bounds for `log (1 + t)` on `[0, 1/2]`: partial sums of even
length underestimate, partial sums of odd length overestimate. -/
theorem altLog_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) (N : ℕ) :
    (Even N →
      (∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * t ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) ≤ Real.log (1 + t)) ∧
    (Odd N →
      Real.log (1 + t) ≤ (∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * t ^ (i + 1) / ((i + 1 : ℕ) : ℝ))) := by
  have hanti := altLog_term_antitone h0 h1
  have hfl := (altLog_hasSum h0 h1).tendsto_sum_nat
  constructor
  · intro hN
    obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hN
    have h := hanti.alternating_series_le_tendsto hfl k
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using h
  · intro hN
    obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hN
    have h := hanti.tendsto_le_alternating_series hfl k
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using h

end Work.RHContract.A.RegionI
