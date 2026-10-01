import Mathlib

namespace Work.Sieve

/-- Elementary half-norm tail estimate.

For `t : ℝ` and `N : ℕ` with `1 ≤ N` and `|t| ≤ N`,

`‖((1/2 : ℂ) + t·i)‖ / (1/2) · N ^ (-(1/2)) ≤ 3 · (1 + |t|) ^ (1/2)`.

Indeed the left-hand factor equals `√(1 + 4 t²)` and `N ^ (-(1/2)) = (√N)⁻¹`, so it
suffices to show `√(1 + 4 t²) ≤ 3 · √(1 + |t|) · √N`, which follows from the
squared inequality `1 + 4 t² ≤ 9 (1 + |t|) N`:
when `|t| ≤ 1` both sides satisfy `1 + 4 t² ≤ 5 ≤ 9 ≤ 9 (1 + |t|) N`, and when
`|t| ≥ 1` we have `1 + 4 t² ≤ 5 |t|² ≤ 9 (1 + |t|) |t| ≤ 9 (1 + |t|) N`. -/
theorem half_norm_tail_arith {t : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hNt : |t| ≤ (N : ℝ)) :
    (‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ / (1/2)) * ((N : ℝ) ^ (-(1/2 : ℝ)))
      ≤ 3 * (1 + |t|) ^ (1/2 : ℝ) := by
  -- Rewrite `(1/2 : ℂ)` as the image of `(1/2 : ℝ)` so that the norm squared can be computed.
  have hz : ((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I = (1/2 : ℂ) + (t : ℂ) * Complex.I := by
    norm_num
  -- Step 1: the norm factor equals `√(1 + 4 t²)`.
  have hA : ‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ / (1/2) = Real.sqrt (1 + 4*t^2) := by
    have h1 : ‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = (1/2)^2 + t^2 := by
      rw [← Complex.normSq_eq_norm_sq, ← hz, Complex.normSq_add_mul_I]
    have h2 : ‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ / (1/2)
        = 2 * ‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by ring
    have h3 : Real.sqrt (1 + 4*t^2) = 2 * ‖((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
      nlinarith [h1]
    rw [h2, h3]
  -- Step 2: the `rpow` factor equals `(√N)⁻¹`.
  have hB : ((N : ℝ) ^ (-(1/2 : ℝ))) = (Real.sqrt (N : ℝ))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg N) (1/2), ← Real.sqrt_eq_rpow]
  -- Step 3: the core squared arithmetic inequality.
  have hC : 1 + 4*t^2 ≤ 9*(1+|t|)*(N:ℝ) := by
    have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    rcases lt_or_ge (1:ℝ) |t| with h | h
    · have hstep1 : 1 + 4*t^2 ≤ 5*|t|^2 := by nlinarith [sq_abs t, abs_nonneg t, h]
      have hstep2 : 5*|t|^2 ≤ 9*(1+|t|)*|t| := by nlinarith [abs_nonneg t]
      have hstep3 : 9*(1+|t|)*|t| ≤ 9*(1+|t|)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hNt (by positivity)
      linarith
    · have hstep1 : 1 + 4*t^2 ≤ 5 := by nlinarith [sq_abs t, abs_nonneg t, h]
      have hprod : 1 ≤ (1+|t|)*(N:ℝ) := by
        have := mul_le_mul (show (1:ℝ) ≤ 1+|t| by linarith [abs_nonneg t]) hN1R
          (by norm_num) (by linarith [abs_nonneg t])
        simpa using this
      nlinarith [hstep1, hprod]
  rw [hA, hB, ← Real.sqrt_eq_rpow]
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hsqrtN_pos : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNpos
  -- Take square roots of the core inequality and use `√(9(1+|t|)N) = 3√(1+|t|)√N`.
  have hmain : Real.sqrt (1 + 4*t^2) ≤ 3 * Real.sqrt (1+|t|) * Real.sqrt (N:ℝ) := by
    have h1 : Real.sqrt (1+4*t^2) ≤ Real.sqrt (9*(1+|t|)*(N:ℝ)) := Real.sqrt_le_sqrt hC
    have h2 : Real.sqrt (9*(1+|t|)*(N:ℝ)) = 3 * Real.sqrt (1+|t|) * Real.sqrt (N:ℝ) := by
      rw [Real.sqrt_mul (by positivity) (N:ℝ), Real.sqrt_mul (by norm_num) (1+|t|)]
      rw [show Real.sqrt 9 = 3 from by
        rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    linarith [h1, h2.le]
  calc Real.sqrt (1+4*t^2) * (Real.sqrt (N:ℝ))⁻¹
      ≤ (3 * Real.sqrt (1+|t|) * Real.sqrt (N:ℝ)) * (Real.sqrt (N:ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = 3 * Real.sqrt (1+|t|) := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqrtN_pos), mul_one]

end Work.Sieve
