import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- Auxiliary: an integer whose absolute value is `< 1` is `0`. -/
private lemma int_eq_zero_of_abs_lt_one {m : ℤ} (h : |(m : ℝ)| < 1) : m = 0 := by
  have hlt1 : (m : ℝ) < 1 := (abs_lt.mp h).2
  have hgt1 : (-1 : ℝ) < (m : ℝ) := (abs_lt.mp h).1
  have h1 : m < (1 : ℤ) := by exact_mod_cast hlt1
  have h2 : (-1 : ℤ) < m := by exact_mod_cast hgt1
  omega

/--
The key point: `(2B+2)` is a base strictly larger than the maximum size `B` of the
"digits" `n 0, n 1, n 2`.  Hence the mixed-radix expansion
`(n 0)·(2B+2)² + (n 1)·(2B+2) + (n 2)` of an integer vanishes only for `n = 0`.
-/
theorem realQuad_ne_zero {B : ℕ} {n : Fin 3 → ℤ} (hn : n ≠ 0) (hB : ∀ i, |n i| ≤ (B : ℤ)) :
    (n 0 : ℝ) * (2 * (B : ℝ) + 2) ^ 2 + (n 1 : ℝ) * (2 * (B : ℝ) + 2) + (n 2 : ℝ) ≠ 0 := by
  intro h
  set K : ℝ := 2 * (B : ℝ) + 2 with hK
  have hh : (n 0 : ℝ) * K ^ 2 + (n 1 : ℝ) * K + (n 2 : ℝ) = 0 := h
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  have hb : ∀ i, |(n i : ℝ)| ≤ (B : ℝ) := by
    intro i
    have h1 : ((|n i| : ℤ) : ℝ) ≤ ((B : ℤ) : ℝ) := by exact_mod_cast hB i
    simpa [Int.cast_abs] using h1
  -- the "leading digit" is bounded by `B·K + B < K²`
  have hAK : (n 0 : ℝ) * K ^ 2 = -((n 1 : ℝ) * K + (n 2 : ℝ)) := by linarith
  have hstep : |(n 0 : ℝ)| * K ^ 2 ≤ (B : ℝ) * K + (B : ℝ) := by
    have h1 : |(n 0 : ℝ)| * K ^ 2 = |(n 1 : ℝ) * K + (n 2 : ℝ)| := by
      have h2 : |(n 0 : ℝ) * K ^ 2| = |(n 1 : ℝ) * K + (n 2 : ℝ)| := by
        rw [hAK, abs_neg]
      rwa [abs_mul, abs_of_nonneg (sq_nonneg K)] at h2
    calc |(n 0 : ℝ)| * K ^ 2 = |(n 1 : ℝ) * K + (n 2 : ℝ)| := h1
      _ ≤ |(n 1 : ℝ) * K| + |(n 2 : ℝ)| := abs_add_le _ _
      _ = |(n 1 : ℝ)| * K + |(n 2 : ℝ)| := by rw [abs_mul, abs_of_nonneg hKpos.le]
      _ ≤ (B : ℝ) * K + (B : ℝ) := by
          have h2 := mul_le_mul_of_nonneg_right (hb 1) hKpos.le
          have h3 := hb 2
          linarith
  have hBK : (B : ℝ) * K + (B : ℝ) < K ^ 2 := by
    rw [hK]
    have hBnn : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    nlinarith [sq_nonneg ((B : ℝ))]
  -- hence `n 0 = 0`
  have hn0 : n 0 = 0 := by
    refine int_eq_zero_of_abs_lt_one ?_
    have hK2pos : (0 : ℝ) < K ^ 2 := pow_pos hKpos 2
    have hlt : |(n 0 : ℝ)| * K ^ 2 < 1 * K ^ 2 := by nlinarith [hstep, hBK]
    exact (mul_lt_mul_iff_left₀ hK2pos).mp hlt
  -- then `(n 1)·K + n 2 = 0`, and `|n 2| ≤ B < K` forces `n 1 = 0`
  have hn1 : n 1 = 0 := by
    have h1 : (n 1 : ℝ) * K = -((n 2 : ℝ)) := by
      have h' := hh
      rw [hn0] at h'
      simp only [Int.cast_zero, zero_mul, zero_add] at h'
      linarith
    have hstep2 : |(n 1 : ℝ)| * K = |(n 2 : ℝ)| := by
      calc |(n 1 : ℝ)| * K = |(n 1 : ℝ) * K| := by rw [abs_mul, abs_of_nonneg hKpos.le]
        _ = |-(n 2 : ℝ)| := by rw [h1]
        _ = |(n 2 : ℝ)| := abs_neg _
    have hBK2 : (B : ℝ) < K := by
      rw [hK]
      have hBnn : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
      linarith
    refine int_eq_zero_of_abs_lt_one ?_
    have h2 : |(n 1 : ℝ)| * K < K := by
      rw [hstep2]
      have h3 := hb 2
      linarith
    have hlt : |(n 1 : ℝ)| * K < 1 * K := by nlinarith [h2, hKpos]
    exact (mul_lt_mul_iff_left₀ hKpos).mp hlt
  -- and finally `n 2 = 0`
  have hn2 : n 2 = 0 := by
    have h1 : (n 2 : ℝ) = 0 := by
      have h' := hh
      rw [hn0, hn1] at h'
      simp only [Int.cast_zero, zero_mul, zero_add] at h'
      linarith
    exact_mod_cast h1
  exact hn (funext fun i => by fin_cases i <;> assumption)

end Work.BoseBoxFock
