import Mathlib
import Submission.Work.HP.MDEstimates.ceil_logb_cube_le
import Submission.Work.HP.MDEstimates.ceil_logb_rpow_le

namespace Work.HP.MDEstimates

/-- Crude `log`-growth bound: for `x ≥ 16` (indeed for any `x ≥ 1`) the ceiling of `logb 2 x`
plus one is controlled, after cubing, by a constant times `x ^ (1/3)`.

Proof: `⌈logb 2 x⌉₊ + 1 < logb 2 x + 2 = log x / log 2 + 2`, and
`log x ≤ 9 · x ^ (1/9)` (`Real.log_le_rpow_div` with `ε = 1/9`), while `2 ≤ 2 · x ^ (1/9)`
since `x ≥ 1`.  Hence `⌈logb 2 x⌉₊ + 1 ≤ (9/log 2 + 2) · x ^ (1/9)`, and cubing gives the claim
because `(x ^ (1/9)) ^ 3 = x ^ (1/3)`. -/
theorem q44_log_bound (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 3
        * (2 : ℝ) ^ (71 * (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) / 3)
      ≤ K * Δ ^ 24 := by
  refine ⟨(9 / Real.log 2 + 2)^3 * 2 ^ ((71:ℝ)/3) * (8 * Kmink)^24 * 2^24, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hKm : 0 < Kmink := lt_of_lt_of_le zero_lt_one hKmink
    positivity
  · intro Δ hΔ
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hKm : 0 < Kmink := lt_of_lt_of_le zero_lt_one hKmink
    set x : ℝ := 8 * Kmink * (Δ + 1) with hxdef
    set n : ℕ := ⌈Real.logb 2 x⌉₊ with hndef
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith [hKmink, hΔ]
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    -- polynomial factor: `(n+1)^3 ≤ C₁ · x^(1/3)`
    have hn1 : ((n:ℝ) + 1)^3 ≤ (9 / Real.log 2 + 2)^3 * x ^ ((1:ℝ)/3) :=
      ceil_logb_cube_le x hx1
    -- exponential factor: `2^(71 n / 3) ≤ 2^(71/3) · x^(71/3)`
    have hn2 : (2:ℝ) ^ (71 * (n:ℝ) / 3) ≤ 2 ^ ((71:ℝ)/3) * x ^ ((71:ℝ)/3) :=
      ceil_logb_rpow_le x hx1
    have hxpow : x ^ ((1:ℝ)/3) * x ^ ((71:ℝ)/3) = x^24 := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hx24 : x^24 ≤ (8*Kmink)^24 * 2^24 * Δ^24 := by
      rw [hxdef, mul_pow]
      have hstep : (Δ+1)^24 ≤ 2^24 * Δ^24 := by
        have h : (Δ+1)^24 ≤ (2*Δ)^24 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 24
        rwa [mul_pow] at h
      calc (8 * Kmink)^24 * (Δ + 1)^24
          ≤ (8 * Kmink)^24 * (2^24 * Δ^24) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (8 * Kmink)^24 * 2^24 * Δ^24 := by ring
    have hcomb : ((n:ℝ)+1)^3 * (2:ℝ)^(71*(n:ℝ)/3)
        ≤ (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * x^24 := by
      calc ((n:ℝ)+1)^3 * (2:ℝ)^(71*(n:ℝ)/3)
          ≤ (((9 / Real.log 2 + 2)^3 * x ^ ((1:ℝ)/3))
              * (2 ^ ((71:ℝ)/3) * x ^ ((71:ℝ)/3))) :=
            mul_le_mul hn1 hn2 (by positivity) (by positivity)
        _ = (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3)
              * (x ^ ((1:ℝ)/3) * x ^ ((71:ℝ)/3)) := by ring
        _ = (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * x^24 := by rw [hxpow]
    have hfinal :
        (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * x^24
          ≤ ((9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * (8 * Kmink)^24 * 2^24) * Δ^24 := by
      have hnonneg : (0:ℝ) ≤ (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) := by positivity
      calc (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * x^24
          = ((9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3)) * x^24 := by ring
        _ ≤ ((9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3)) * ((8*Kmink)^24 * 2^24 * Δ^24) :=
              mul_le_mul_of_nonneg_left hx24 hnonneg
        _ = ((9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * (8 * Kmink)^24 * 2^24) * Δ^24 := by ring
    calc ((n:ℝ)+1)^3 * (2:ℝ)^(71*(n:ℝ)/3)
        ≤ (9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * x^24 := hcomb
      _ ≤ ((9 / Real.log 2 + 2)^3 * 2^((71:ℝ)/3) * (8 * Kmink)^24 * 2^24) * Δ^24 := hfinal

end Work.HP.MDEstimates
