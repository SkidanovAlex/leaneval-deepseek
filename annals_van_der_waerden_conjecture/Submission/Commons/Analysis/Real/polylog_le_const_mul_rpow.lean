import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- For every `L : ℕ` and `eps > 0` there is a positive constant `C` with
`(log x) ^ L ≤ C * x ^ eps` for all `x ≥ 1`: a fixed power of the logarithm is
dominated by any positive power of `x`. -/
theorem polylog_le_const_mul_rpow (L : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ L ≤ C * x ^ eps := by
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · -- `L = 0`: the left-hand side is `1`, and `1 ≤ x ^ eps`.
    subst hL0
    refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [pow_zero, one_mul]
    exact Real.one_le_rpow hx (le_of_lt heps)
  · -- `L ≥ 1`: use `log x ≤ x ^ (eps / L) / (eps / L)` and raise to the `L`-th power.
    have hLposR : 0 < (L : ℝ) := by exact_mod_cast hLpos
    have hLne : (L : ℝ) ≠ 0 := hLposR.ne'
    refine ⟨((L : ℝ) / eps) ^ L, pow_pos (div_pos hLposR heps) L, fun x hx => ?_⟩
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
    have hx0 : 0 ≤ x := le_of_lt hxpos
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx
    set a : ℝ := eps / (L : ℝ) with ha_def
    have ha : 0 < a := by rw [ha_def]; exact div_pos heps hLposR
    -- `log x ≤ x ^ a / a`
    have hlog : Real.log x ≤ x ^ a / a := by
      rw [le_div_iff₀ ha, Real.rpow_def_of_pos hxpos a]
      have h := Real.add_one_le_exp (Real.log x * a)
      linarith
    -- `x ^ a / a = (L / eps) * x ^ a`
    have hbase : x ^ a / a = ((L : ℝ) / eps) * x ^ a := by
      have hinv : a⁻¹ = (L : ℝ) / eps := by rw [ha_def, inv_div]
      rw [div_eq_mul_inv, hinv, mul_comm]
    calc (Real.log x) ^ L
        ≤ (x ^ a / a) ^ L := pow_le_pow_left₀ hlognn hlog L
      _ = (((L : ℝ) / eps) * x ^ a) ^ L := by rw [hbase]
      _ = ((L : ℝ) / eps) ^ L * (x ^ a) ^ L := by rw [mul_pow]
      _ = ((L : ℝ) / eps) ^ L * x ^ eps := by
            rw [← Real.rpow_natCast (x ^ a) L, ← Real.rpow_mul hx0 a (L : ℝ), ha_def,
              div_mul_cancel₀ eps hLne]

end Commons.Analysis.Real