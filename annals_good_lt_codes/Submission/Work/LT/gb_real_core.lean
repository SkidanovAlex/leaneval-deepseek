import Mathlib

namespace Work.LT

/-- The real-analytic core bound: for `γ > 0` with `γ ≤ 2^{c/2}-1` and `(2e/γ)^γ ≤ 2^{c/2}`, we have `(γD²+1)(2e/γ)^{γD²} ≤ 2^{cD²}` for every `D`. -/
theorem gb_real_core (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ)
    (hγδ : γ ≤ 2 ^ (c/2) - 1) (hbase : (2 * Real.exp 1 / γ) ^ γ ≤ (2:ℝ) ^ (c/2)) (D : ℕ) :
    (γ * (D:ℝ)^2 + 1) * (2 * Real.exp 1 / γ) ^ (γ * (D:ℝ)^2)
      ≤ (2:ℝ) ^ (c * (D:ℝ)^2) := by
  have hb_pos : 0 < 2 * Real.exp 1 / γ := by positivity
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · -- D = 0: both factors are `1` and the right side is `1`.
    subst hD0
    norm_num
  · -- D ≥ 1, so `u = D^2 ≥ 1`.
    set u : ℝ := (D:ℝ)^2 with hu_def
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hDpos
    have hu1 : 1 ≤ u := by
      rw [hu_def]; nlinarith [hD1]
    have hu0 : 0 ≤ u := le_trans zero_le_one hu1
    have hA1 : 1 ≤ (2:ℝ) ^ (c/2) := Real.one_le_rpow (by norm_num) (by positivity)
    -- `(2^{c/2})^u = 2^{c u / 2}`
    have hAu_eq : ((2:ℝ) ^ (c/2)) ^ u = (2:ℝ) ^ (c*u/2) := by
      rw [← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num)]
      congr 1
      ring
    -- First factor: `γ u + 1 ≤ 2^{c u / 2}` by Bernoulli's inequality.
    have h1 : γ * u + 1 ≤ (2:ℝ) ^ (c*u/2) := by
      have hx : (-1:ℝ) ≤ (2:ℝ) ^ (c/2) - 1 := by linarith
      have hbern := one_add_mul_self_le_rpow_one_add hx hu1
      have hsimp : (1:ℝ) + ((2:ℝ) ^ (c/2) - 1) = (2:ℝ) ^ (c/2) := by ring
      rw [hsimp] at hbern
      have hle : γ * u ≤ u * ((2:ℝ) ^ (c/2) - 1) := by
        have := mul_le_mul_of_nonneg_right hγδ hu0
        linarith [this]
      calc γ * u + 1 ≤ 1 + u * ((2:ℝ) ^ (c/2) - 1) := by linarith
        _ ≤ ((2:ℝ) ^ (c/2)) ^ u := hbern
        _ = (2:ℝ) ^ (c*u/2) := hAu_eq
    -- Second factor: `(2e/γ)^{γu} ≤ 2^{c u / 2}` from the base hypothesis.
    have h2 : (2 * Real.exp 1 / γ) ^ (γ*u) ≤ (2:ℝ) ^ (c*u/2) := by
      calc (2 * Real.exp 1 / γ) ^ (γ*u)
            = ((2 * Real.exp 1 / γ) ^ γ) ^ u := Real.rpow_mul (le_of_lt hb_pos) γ u
        _ ≤ ((2:ℝ) ^ (c/2)) ^ u :=
              Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hb_pos) γ) hbase hu0
        _ = (2:ℝ) ^ (c*u/2) := hAu_eq
    calc (γ * u + 1) * (2 * Real.exp 1 / γ) ^ (γ*u)
          ≤ (2:ℝ) ^ (c*u/2) * (2:ℝ) ^ (c*u/2) :=
            mul_le_mul h1 h2 (Real.rpow_nonneg (le_of_lt hb_pos) _)
              (Real.rpow_nonneg (by norm_num) _)
        _ = (2:ℝ) ^ (c*u) := by
            rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
            congr 1; ring

end Work.LT
