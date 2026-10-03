import Mathlib

namespace Work.A7

/-- Elementary absorption of the lower-order terms of the polynomial averages:
the `N ^ (E-1)` term with coefficient `4 * q` and the `N ^ (E-2)` term with
coefficient `(q^2/8) (1 + S + S^2)` are dominated by
`5 * q^2 * (1 + S^2/N) * N ^ (E-1)`, for `N ≥ 1`, `S ≥ 0` and `q ≥ 1`.

The two powers are brought to a common denominator: writing `A = N ^ (E-1)`,
one has `N ^ (E-2) = A / N`, so after multiplying by `N / A > 0` the claim is the
purely polynomial inequality
`4 q N + (q^2/8)(1+S+S^2) ≤ 5 q^2 N + 5 q^2 S^2`,
which follows from `q ≥ 1`, `N ≥ 1`, `S ≥ 0` (case split on `S ≤ 1`). -/
theorem rpow_absorb {N S : ℝ} (hN : 1 ≤ N) (hS : 0 ≤ S) {q : ℕ} (hq : 1 ≤ q) (E : ℕ) :
    4 * (q : ℝ) * N ^ ((E : ℝ) - 1) + ((q : ℝ) ^ 2 / 8) * N ^ ((E : ℝ) - 2) * (1 + S + S ^ 2)
      ≤ 5 * (q : ℝ) ^ 2 * (1 + S ^ 2 / N) * N ^ ((E : ℝ) - 1) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := hNpos.ne'
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  -- The polynomial core, obtained after multiplying by `N / A > 0`.
  have hcore : 4 * (q : ℝ) * N + (q : ℝ) ^ 2 / 8 * (1 + S + S ^ 2)
      ≤ 5 * (q : ℝ) ^ 2 * N + 5 * (q : ℝ) ^ 2 * S ^ 2 := by
    have haux : (q : ℝ) ^ 2 * (1 + S + S ^ 2)
        ≤ 40 * (q : ℝ) ^ 2 * S ^ 2 + (40 * (q : ℝ) ^ 2 - 32 * (q : ℝ)) := by
      rcases lt_or_ge (1 : ℝ) S with hS1 | hS1
      · have h1 : 1 + S + S ^ 2 ≤ 3 * S ^ 2 := by nlinarith [sq_nonneg S]
        have h2 : 0 ≤ 40 * (q : ℝ) ^ 2 - 32 * (q : ℝ) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (q : ℝ))]
      · have h1 : 1 + S + S ^ 2 ≤ 3 := by nlinarith [sq_nonneg S]
        have h2 : 3 * (q : ℝ) ^ 2 ≤ 40 * (q : ℝ) ^ 2 - 32 * (q : ℝ) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (q : ℝ))]
    have h1 : 4 * (q : ℝ) * N ≤ 5 * (q : ℝ) ^ 2 * N := by
      have hpos : 0 ≤ (q : ℝ) * N * (5 * (q : ℝ) - 4) :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
      nlinarith [hpos]
    have h3 : 5 * (q : ℝ) ^ 2 * N - 4 * (q : ℝ) * N ≥ 5 * (q : ℝ) ^ 2 - 4 * (q : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1)
        (by nlinarith : (0 : ℝ) ≤ 5 * (q : ℝ) ^ 2 - 4 * (q : ℝ))]
    have h2 : (q : ℝ) ^ 2 / 8 * (1 + S + S ^ 2)
        ≤ 5 * (q : ℝ) ^ 2 * S ^ 2 + (5 * (q : ℝ) ^ 2 * N - 4 * (q : ℝ) * N) := by
      nlinarith [haux, h3]
    linarith
  set A : ℝ := N ^ ((E : ℝ) - 1) with hA
  have hApos : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos hNpos _
  have hBN : N ^ ((E : ℝ) - 2) = A / N := by
    rw [hA, eq_div_iff hNne]
    have h1 : N ^ ((E : ℝ) - 2) * N = N ^ ((E : ℝ) - 2) * N ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add hNpos, show (E : ℝ) - 2 + 1 = (E : ℝ) - 1 by ring]
  have hgoal : 4 * (q : ℝ) * A + (q : ℝ) ^ 2 / 8 * (A / N) * (1 + S + S ^ 2)
      ≤ 5 * (q : ℝ) ^ 2 * (1 + S ^ 2 / N) * A := by
    have h := mul_le_mul_of_nonneg_right hcore (le_of_lt (div_pos hApos hNpos))
    have e1 : (4 * (q : ℝ) * N + (q : ℝ) ^ 2 / 8 * (1 + S + S ^ 2)) * (A / N)
        = 4 * (q : ℝ) * A + (q : ℝ) ^ 2 / 8 * (A / N) * (1 + S + S ^ 2) := by
      field_simp
    have e2 : (5 * (q : ℝ) ^ 2 * N + 5 * (q : ℝ) ^ 2 * S ^ 2) * (A / N)
        = 5 * (q : ℝ) ^ 2 * (1 + S ^ 2 / N) * A := by
      field_simp
    rw [e1, e2] at h
    exact h
  rw [hBN]
  exact hgoal

end Work.A7
