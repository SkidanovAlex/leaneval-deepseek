import Mathlib

namespace Work.LinnikAreas.Density4

set_option linter.unusedVariables false

/-- Weighted AM-GM core inequality: for `N ≥ 2` (as a real number `n`) and `w, c ≥ 0`,
`n * w * c ≤ w^N + c^2 + (n - 2) * c`.  This is the weighted AM-GM inequality applied to the
`n` nonnegative numbers consisting of `w^N`, `c^2` and `n - 2` copies of `c` (with common
weight `1/n`), whose geometric mean is `w * c`. -/
lemma amgm_core (N : ℕ) (hN : 2 ≤ N) (w c : ℝ) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (N:ℝ) * w * c ≤ w^N + c^2 + ((N:ℝ) - 2) * c := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]; simp; positivity
  · -- `(w^N)^(1/N) = w`
    have h1 : (w^N) ^ ((1:ℝ)/(N:ℝ)) = w := by
      rw [← Real.rpow_natCast w N, ← Real.rpow_mul hw, mul_one_div, div_self hNne, Real.rpow_one]
    -- `(c^2)^(1/N) * c^((N-2)/N) = c`
    have h2 : (c^2) ^ ((1:ℝ)/(N:ℝ)) * c ^ (((N:ℝ)-2)/(N:ℝ)) = c := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc, ← Real.rpow_add hcpos]
      have hx : ((2:ℕ):ℝ) * (1/(N:ℝ)) + ((N:ℝ)-2)/(N:ℝ) = 1 := by
        push_cast; field_simp; ring
      rw [hx, Real.rpow_one]
    -- the geometric mean of the three weighted factors is `w * c`
    have hgm : (w^N) ^ ((1:ℝ)/(N:ℝ)) * (c^2) ^ ((1:ℝ)/(N:ℝ)) * c ^ (((N:ℝ)-2)/(N:ℝ)) = w*c := by
      rw [mul_assoc, h2, h1]
    have hw1 : (0:ℝ) ≤ 1/(N:ℝ) := div_nonneg zero_le_one (le_of_lt hNpos)
    have hw3 : (0:ℝ) ≤ ((N:ℝ)-2)/(N:ℝ) := div_nonneg (by linarith) (le_of_lt hNpos)
    have hsum : 1/(N:ℝ) + 1/(N:ℝ) + ((N:ℝ)-2)/(N:ℝ) = 1 := by field_simp; ring
    have hAM := Real.geom_mean_le_arith_mean3_weighted hw1 hw1 hw3
      (pow_nonneg hw N) (sq_nonneg c) hc hsum
    rw [hgm] at hAM
    -- multiply the weighted AM-GM inequality by `N > 0`
    have hstep := mul_le_mul_of_nonneg_left hAM (le_of_lt hNpos)
    have hsimp : (N:ℝ) * (1/(N:ℝ) * w^N + 1/(N:ℝ) * c^2 + ((N:ℝ)-2)/(N:ℝ) * c)
        = w^N + c^2 + ((N:ℝ)-2)*c := by field_simp
    rw [hsimp] at hstep
    rw [← mul_assoc] at hstep
    exact hstep

lemma amgm_pow_le (N : ℕ) (hN : 2 ≤ N) (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    a*w - b*w^N ≤ a*((N:ℝ)-2)/(N:ℝ) + a^2/((N:ℝ)^2*b) := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  set c : ℝ := a / ((N:ℝ) * b) with hcdef
  have hcnonneg : 0 ≤ c := by
    rw [hcdef]; exact div_nonneg ha (le_of_lt (mul_pos hNpos hb))
  have hcore := amgm_core N hN w c hw0 hcnonneg
  -- rewrite the difference `RHS - LHS` as `b * (w^N + c^2 + (N-2)*c - N*w*c)`
  have hident : a*((N:ℝ)-2)/(N:ℝ) + a^2/((N:ℝ)^2*b) - (a*w - b*w^N)
      = b * (w^N + c^2 + ((N:ℝ)-2)*c - (N:ℝ)*w*c) := by
    rw [hcdef]; field_simp; ring
  have hbracket : 0 ≤ w^N + c^2 + ((N:ℝ)-2)*c - (N:ℝ)*w*c := by linarith
  have hH : 0 ≤ a*((N:ℝ)-2)/(N:ℝ) + a^2/((N:ℝ)^2*b) - (a*w - b*w^N) := by
    rw [hident]; exact mul_nonneg (le_of_lt hb) hbracket
  linarith

end Work.LinnikAreas.Density4
