import Mathlib

namespace Work.KMTAreas.A7rand

theorem good_deriv_zero (η : ℝ → ℂ)
    (hηin : ∀ y : ℝ, |y| < 1 / 2 → deriv η y = 0)
    (hηout : ∀ y : ℝ, 1 ≤ |y| → deriv η y = 0)
    (s : ℕ → ℕ) (hs : Monotone s) (m : ℕ) (ξ : ℝ)
    (hgood : ¬ (s (m + 1) > s m ∧ (2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
      (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|)) :
    (2 : ℝ) ^ (s m) * deriv η ((2 : ℝ) ^ (s m) * ξ)
      - (2 : ℝ) ^ (s (m + 1)) * deriv η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
  -- Monotonicity of `s` gives `s m ≤ s (m+1)`.
  have hmono : s m ≤ s (m + 1) := hs (Nat.le_succ m)
  rcases lt_or_ge (s m) (s (m + 1)) with hlt | hge
  · -- The scales are strictly increasing.  Then the failure of the "bad" condition
    -- forces `2^(s m) * |ξ| > 1` or `2^(s (m+1)) * |ξ| < 1/2`; in either case both
    -- arguments of `deriv η` lie in the region where `deriv η = 0`.
    have hAB : ¬ ((2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
        (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|) := by
      intro hc
      exact hgood ⟨hlt, hc.1, hc.2⟩
    have hp1 : (0 : ℝ) < (2 : ℝ) ^ (s m) := pow_pos (by norm_num) _
    have hp2 : (0 : ℝ) < (2 : ℝ) ^ (s (m + 1)) := pow_pos (by norm_num) _
    have hple : (2 : ℝ) ^ (s m) ≤ (2 : ℝ) ^ (s (m + 1)) :=
      pow_le_pow_right₀ (by norm_num) (le_of_lt hlt)
    rw [not_and_or] at hAB
    rcases hAB with hA | hB
    · -- `2^(s m) * |ξ| > 1`: both scales exceed `1/|ξ|`, so both derivatives vanish.
      have hA' : 1 < (2 : ℝ) ^ (s m) * |ξ| := not_le.mp hA
      have h1 : deriv η ((2 : ℝ) ^ (s m) * ξ) = 0 := by
        refine hηout _ ?_
        rw [abs_mul, abs_of_nonneg (le_of_lt hp1)]
        exact le_of_lt hA'
      have h2 : deriv η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
        refine hηout _ ?_
        rw [abs_mul, abs_of_nonneg (le_of_lt hp2)]
        exact le_of_lt (lt_of_lt_of_le hA'
          (mul_le_mul_of_nonneg_right hple (abs_nonneg ξ)))
      rw [h1, h2]
      ring
    · -- `2^(s (m+1)) * |ξ| < 1/2`: both scales are below `1/2`, so both derivatives vanish.
      have hB' : (2 : ℝ) ^ (s (m + 1)) * |ξ| < 1 / 2 := not_le.mp hB
      have h1 : deriv η ((2 : ℝ) ^ (s m) * ξ) = 0 := by
        refine hηin _ ?_
        rw [abs_mul, abs_of_nonneg (le_of_lt hp1)]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hple (abs_nonneg ξ)) hB'
      have h2 : deriv η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
        refine hηin _ ?_
        rw [abs_mul, abs_of_nonneg (le_of_lt hp2)]
        exact hB'
      rw [h1, h2]
      ring
  · -- The scales are equal (`s` is monotone), so the two terms coincide.
    have heq : s (m + 1) = s m := le_antisymm hge hmono
    rw [heq]
    ring

end Work.KMTAreas.A7rand
