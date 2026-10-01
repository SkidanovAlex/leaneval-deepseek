import Mathlib

namespace Work.LinnikAreas.Density4

/-- For `μ > 0` and `A ≥ 0`, the quantity `q ^ (-μ) * (log q) ^ A` is at most `1` for all
sufficiently large natural numbers `q`. -/
theorem exp_neg_mul_log_pow_le (μ A : ℝ) (hμ : 0 < μ) (hA : 0 ≤ A) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → (q : ℝ) ^ (-μ) * (Real.log q) ^ A ≤ 1 := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · subst hA0
    refine ⟨1, fun q hq => ?_⟩
    rw [Real.rpow_zero, mul_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq) (by linarith)
  · set r : ℝ := μ / (2 * A) with hrdef
    have hr : 0 < r := by rw [hrdef]; positivity
    set c : ℝ := r ^ (-A) with hcdef
    have hcpos : 0 < c := by rw [hcdef]; exact Real.rpow_pos_of_pos hr _
    obtain ⟨N, hN⟩ := exists_nat_ge (c ^ (2 / μ))
    refine ⟨max 2 N, fun q hq => ?_⟩
    have hq2 : 2 ≤ q := le_trans (le_max_left 2 N) hq
    have hqN : N ≤ q := le_trans (le_max_right 2 N) hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    -- `log q` is bounded by `q ^ r / r`
    have hlog_le : Real.log (q : ℝ) ≤ (q : ℝ) ^ r / r := Real.log_natCast_le_rpow_div q hr
    have hlog_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have step1 : (Real.log (q : ℝ)) ^ A ≤ ((q : ℝ) ^ r / r) ^ A :=
      Real.rpow_le_rpow hlog_nonneg hlog_le hA
    have h2 : ((q : ℝ) ^ r / r) ^ A = (q : ℝ) ^ (r * A) * r ^ (-A) := by
      rw [Real.div_rpow (Real.rpow_nonneg hqpos.le r) hr.le A, div_eq_mul_inv,
        ← Real.rpow_mul hqpos.le, ← Real.rpow_neg hr.le]
    -- eventually `q ^ (μ/2)` dominates the constant `c = r ^ (-A)`
    have hqc : c ^ (2 / μ) ≤ (q : ℝ) := le_trans hN (by exact_mod_cast hqN)
    have hsimp : (c ^ (2 / μ)) ^ (μ / 2) = c := by
      rw [← Real.rpow_mul hcpos.le]
      have : 2 / μ * (μ / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    have hkey : c ≤ (q : ℝ) ^ (μ / 2) := by
      rw [← hsimp]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hcpos.le (2 / μ)) hqc (by positivity)
    have hfinal : (q : ℝ) ^ (-μ / 2) * r ^ (-A) ≤ 1 := by
      have hk : r ^ (-A) ≤ (q : ℝ) ^ (μ / 2) := by simpa [hcdef] using hkey
      calc (q : ℝ) ^ (-μ / 2) * r ^ (-A)
          ≤ (q : ℝ) ^ (-μ / 2) * (q : ℝ) ^ (μ / 2) :=
            mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hqpos.le _)
        _ = 1 := by
            rw [← Real.rpow_add hqpos, show -μ / 2 + μ / 2 = 0 by ring, Real.rpow_zero]
    calc (q : ℝ) ^ (-μ) * (Real.log (q : ℝ)) ^ A
        ≤ (q : ℝ) ^ (-μ) * ((q : ℝ) ^ r / r) ^ A :=
          mul_le_mul_of_nonneg_left step1 (Real.rpow_nonneg hqpos.le _)
      _ = (q : ℝ) ^ (-μ) * ((q : ℝ) ^ (r * A) * r ^ (-A)) := by rw [h2]
      _ = ((q : ℝ) ^ (-μ) * (q : ℝ) ^ (r * A)) * r ^ (-A) := by ring
      _ = (q : ℝ) ^ (-μ + r * A) * r ^ (-A) := by rw [← Real.rpow_add hqpos]
      _ = (q : ℝ) ^ (-μ / 2) * r ^ (-A) := by
          have hnum : -μ + r * A = -μ / 2 := by
            rw [hrdef]
            field_simp
            ring
          rw [hnum]
      _ ≤ 1 := hfinal

end Work.LinnikAreas.Density4
