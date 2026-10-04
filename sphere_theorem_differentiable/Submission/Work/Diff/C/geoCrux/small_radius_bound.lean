import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

/-- Elementary sublinear bound for the logarithm: `Real.log x ≤ 2 * Real.sqrt x` for `x > 0`.
This is all that is needed to control the logarithmic factor `(Real.log (2/ρ))^2` below. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div (le_of_lt hx) (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : x ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
    ring
  linarith

theorem small_radius_bound {c ε₁ ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hρ : 0 < ρ) (hρδ : ρ ≤ Real.sqrt (c / 4)) :
    3 * (ε₁ * (1 + (Real.log (2 / ρ)) ^ 2) + ρ ^ 2) * ρ
      ≤ 40 * (Real.sqrt c + ε₁ * Real.pi) := by
  -- `ρ` is bounded by `1/4` and by `√c / 2`.
  have hρ14 : ρ ≤ 1 / 4 := by
    have h1 : Real.sqrt (c / 4) ≤ 1 / 4 := by
      rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
            rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hρ_le : ρ ≤ Real.sqrt c / 2 := by
    have h1 : Real.sqrt (c / 4) = Real.sqrt c / 2 := by
      rw [Real.sqrt_div (le_of_lt hc) 4]; norm_num
    linarith
  -- Bound on the `ε₁`-term: `3 * (1 + log²(2/ρ)) * ρ ≤ 40 * π`.
  have hlog : 3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ ≤ 40 * Real.pi := by
    have hx : 0 < 2 / ρ := by positivity
    have h1 : Real.log (2 / ρ) ≤ 2 * Real.sqrt (2 / ρ) := log_le_two_sqrt hx
    have h1nn : 0 ≤ Real.log (2 / ρ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
    -- squaring the sublinear bound
    have hsq : (Real.log (2 / ρ)) ^ 2 ≤ 4 * (2 / ρ) := by
      calc (Real.log (2 / ρ)) ^ 2 ≤ (2 * Real.sqrt (2 / ρ)) ^ 2 :=
            pow_le_pow_left₀ h1nn h1 2
        _ = 4 * (2 / ρ) := by rw [mul_pow, Real.sq_sqrt (le_of_lt hx)]; ring
    have hlead : 3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ ≤ 3 * (1 + 4 * (2 / ρ)) * ρ := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hρ)
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
      linarith
    have hval : 3 * (1 + 4 * (2 / ρ)) * ρ = 3 * ρ + 24 := by
      field_simp
      ring
    calc 3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ ≤ 3 * (1 + 4 * (2 / ρ)) * ρ := hlead
      _ = 3 * ρ + 24 := hval
      _ ≤ 40 * Real.pi := by linarith [Real.pi_gt_three]
  -- Bound on the `ρ²`-term: `3 * ρ³ ≤ 40 * √c`.
  have hcube : 3 * ρ ^ 3 ≤ 40 * Real.sqrt c := by
    have h3 : ρ ^ 3 ≤ (Real.sqrt c / 2) ^ 3 := pow_le_pow_left₀ (le_of_lt hρ) hρ_le 3
    have h4 : (Real.sqrt c / 2) ^ 3 = c * Real.sqrt c / 8 := by
      rw [div_pow, show (2 : ℝ) ^ 3 = 8 by norm_num,
          show (Real.sqrt c) ^ 3 = (Real.sqrt c) ^ 2 * Real.sqrt c by ring,
          Real.sq_sqrt (le_of_lt hc)]
    rw [h4] at h3
    calc 3 * ρ ^ 3 ≤ 3 * (c * Real.sqrt c / 8) := by linarith
      _ = (3 * c / 8) * Real.sqrt c := by ring
      _ ≤ 40 * Real.sqrt c := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg c)
  -- Assembly.
  have key : ε₁ * (3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ) + 3 * ρ ^ 3
      ≤ 40 * (Real.sqrt c + ε₁ * Real.pi) := by
    have h1 : ε₁ * (3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ) ≤ ε₁ * (40 * Real.pi) :=
      mul_le_mul_of_nonneg_left hlog hε₁
    calc ε₁ * (3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ) + 3 * ρ ^ 3
        ≤ ε₁ * (40 * Real.pi) + 40 * Real.sqrt c := add_le_add h1 hcube
      _ = 40 * (Real.sqrt c + ε₁ * Real.pi) := by ring
  calc 3 * (ε₁ * (1 + (Real.log (2 / ρ)) ^ 2) + ρ ^ 2) * ρ
      = ε₁ * (3 * (1 + (Real.log (2 / ρ)) ^ 2) * ρ) + 3 * ρ ^ 3 := by ring
    _ ≤ 40 * (Real.sqrt c + ε₁ * Real.pi) := key

end Work.Diff.C.geoCrux
