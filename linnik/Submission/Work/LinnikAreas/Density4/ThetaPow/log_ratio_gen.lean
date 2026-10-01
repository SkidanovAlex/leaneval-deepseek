import Mathlib

namespace Work.LinnikAreas.Density4.ThetaPow

/-- For `d ≤ Q^{1/M}` (with `Q ≥ 1`, `d ≥ 1`, `M ≥ 1`) one has
`(1 - 1/M) * log(2+Q) ≤ log(2 + Q/d)`.  This is the general-exponent version
of `Work.LinnikAreas.Density4.log_ratio`. -/
theorem log_ratio_gen {Q : ℝ} (hQ : 1 ≤ Q) {d : ℕ} (hd : 1 ≤ d)
    {M : ℝ} (hM : 1 ≤ M) (hdQ : (d : ℝ) ≤ Q ^ ((1:ℝ)/M)) :
    (1 - 1/M) * Real.log (2 + Q) ≤ Real.log (2 + Q/(d:ℝ)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  set θ : ℝ := 1 - 1/M with hθdef
  have hθ0 : 0 ≤ θ := by
    have h1M : 1/M ≤ 1 := by rw [div_le_one hM0]; exact hM
    rw [hθdef]; linarith
  have hθ1 : θ ≤ 1 := by
    have h1M : 0 ≤ 1/M := by positivity
    rw [hθdef]; linarith
  have hq : (0:ℝ) < Q ^ θ := Real.rpow_pos_of_pos hQ0 _
  -- `Q^θ ≤ Q/d`
  have hdiv : Q ^ θ ≤ Q/(d:ℝ) := by
    rw [le_div_iff₀ hd0]
    calc Q ^ θ * (d:ℝ) ≤ Q ^ θ * Q ^ ((1:ℝ)/M) :=
          mul_le_mul_of_nonneg_left hdQ hq.le
      _ = Q ^ (θ + (1:ℝ)/M) := by rw [← Real.rpow_add hQ0]
      _ = Q ^ (1:ℝ) := by
            have hsum : θ + (1:ℝ)/M = 1 := by rw [hθdef]; ring
            rw [hsum]
      _ = Q := Real.rpow_one Q
  -- subadditivity of `x ↦ x^θ`
  have hsub : (2 + Q) ^ θ ≤ 2 + Q ^ θ := by
    have h := Real.rpow_add_le_add_rpow (p := θ) (a := 2) (b := Q)
      (by norm_num) hQ0.le hθ0 hθ1
    have h2 : (2:ℝ) ^ θ ≤ 2 := by
      calc (2:ℝ) ^ θ ≤ (2:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
        _ = 2 := Real.rpow_one 2
    linarith
  have hlogeq : θ * Real.log (2+Q) = Real.log ((2+Q) ^ θ) := by
    rw [Real.log_rpow (by linarith)]
  rw [hlogeq]
  calc Real.log ((2+Q) ^ θ) ≤ Real.log (2 + Q ^ θ) :=
        Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hsub
    _ ≤ Real.log (2 + Q/(d:ℝ)) := Real.log_le_log (by linarith) (by linarith)

end Work.LinnikAreas.Density4.ThetaPow
