import Mathlib

namespace Work.CNum

/-- Elementary lower bound for `log ‖1 + z‖`: if `‖z‖ ≤ b < 1` then `log ‖1 + z‖ ≥ -b/(1-b)`.

Chain of inequalities: `‖1+z‖ ≥ 1-‖z‖ ≥ 1-b > 0`, so `log‖1+z‖ ≥ log(1-b)`; and
`log(1-b) ≥ -b/(1-b)` is the standard `log x ≤ x - 1` applied to `x = 1/(1-b)`. -/
private lemma log_norm_one_add_lower {z : ℂ} {b : ℝ} (_hb0 : 0 ≤ b) (hb1 : b < 1)
    (hz : ‖z‖ ≤ b) : -(b / (1 - b)) ≤ Real.log ‖(1 : ℂ) + z‖ := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz hb1
  have hbpos : 0 < 1 - b := by linarith
  have hzpos : 0 < 1 - ‖z‖ := by linarith
  have hlow : -(b / (1 - b)) ≤ Real.log (1 - b) := by
    have hp : (0 : ℝ) < (1 - b)⁻¹ := inv_pos.mpr hbpos
    have h := Real.log_le_sub_one_of_pos hp
    rw [Real.log_inv] at h
    have heq : (1 - b)⁻¹ - 1 = b / (1 - b) := by
      field_simp
      ring
    rw [heq] at h
    linarith
  have hmid : Real.log (1 - b) ≤ Real.log (1 - ‖z‖) :=
    Real.log_le_log hbpos (by linarith)
  have hup : Real.log (1 - ‖z‖) ≤ Real.log ‖(1 : ℂ) + z‖ := by
    apply Real.log_le_log hzpos
    have h := norm_add_le ((1 : ℂ) + z) (-z)
    rw [show (1 : ℂ) + z + -z = 1 by ring, norm_one, norm_neg] at h
    linarith
  linarith

theorem SerDnTail {q : ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) (hq : ‖q‖ ≤ R) (k : ℕ) :
    -(R ^ (k + 1) / ((1 - R) * (1 - R ^ (k + 1)))) ≤
      ∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖ := by
  set a : ℝ := R ^ (k + 1) with ha_def
  have ha0 : 0 ≤ a := by rw [ha_def]; exact pow_nonneg hR0 _
  have hRle1 : R ≤ 1 := le_of_lt hR1
  have ha1 : a < 1 := by
    rw [ha_def]; exact pow_lt_one₀ hR0 hR1 (Nat.succ_ne_zero k)
  have h1a : 0 < 1 - a := by linarith
  have h1R : 0 < 1 - R := by linarith
  have hRnorm : ‖R‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hR0]; exact hR1
  have hqnorm : ‖q‖ < 1 := lt_of_le_of_lt hq hR1
  -- summability of the actual series
  have hf_sum : Summable (fun j : ℕ => Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖) := by
    have hgeoq : Summable (fun n : ℕ => q ^ (n + (k + 1))) :=
      (summable_nat_add_iff (k + 1)).2 (summable_geometric_iff_norm_lt_one.mpr hqnorm)
    have hgn : Summable (fun n : ℕ => ‖q ^ (n + (k + 1))‖) := hgeoq.norm
    have h := hgn.summable_log_norm_one_add
    simpa only [Nat.add_assoc] using h
  -- summability of the comparison series
  have hc_sum : Summable (fun j : ℕ => -(R ^ (j + k + 1) / (1 - a))) := by
    have hgeo : Summable (fun n : ℕ => R ^ (n + (k + 1))) :=
      (summable_nat_add_iff (k + 1)).2 (summable_geometric_iff_norm_lt_one.mpr hRnorm)
    have h1 : Summable (fun n : ℕ => R ^ (n + (k + 1)) / (1 - a)) := hgeo.div_const _
    simpa only [Nat.add_assoc] using h1.neg
  -- the geometric sum
  have hS : ∑' j : ℕ, R ^ (j + k + 1) = a * (1 - R)⁻¹ := by
    have hcongr : (fun j : ℕ => R ^ (j + k + 1)) = (fun j : ℕ => R ^ (k + 1) * R ^ j) := by
      funext j
      rw [show j + k + 1 = (k + 1) + j by omega, pow_add]
    rw [hcongr, tsum_mul_left, tsum_geometric_of_norm_lt_one hRnorm, ha_def]
  have hc_val : ∑' j : ℕ, -(R ^ (j + k + 1) / (1 - a)) = -(a / ((1 - R) * (1 - a))) := by
    rw [tsum_neg, tsum_div_const, hS]
    field_simp [ne_of_gt h1R, ne_of_gt h1a]
  -- pointwise comparison
  have hclf : ∀ j : ℕ, -(R ^ (j + k + 1) / (1 - a)) ≤
      Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖ := by
    intro j
    have hb0 : 0 ≤ R ^ (j + k + 1) := pow_nonneg hR0 _
    have hb_le_a : R ^ (j + k + 1) ≤ a := by
      rw [ha_def]; exact pow_le_pow_of_le_one hR0 hRle1 (by omega)
    have hb1 : R ^ (j + k + 1) < 1 := lt_of_le_of_lt hb_le_a ha1
    have hz : ‖q ^ (j + k + 1)‖ ≤ R ^ (j + k + 1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg q) hq _
    have hstep := log_norm_one_add_lower hb0 hb1 hz
    have hcmp : R ^ (j + k + 1) / (1 - R ^ (j + k + 1)) ≤ R ^ (j + k + 1) / (1 - a) :=
      div_le_div_of_nonneg_left hb0 h1a (by linarith)
    linarith
  have hle := Summable.tsum_le_tsum hclf hc_sum hf_sum
  calc -(a / ((1 - R) * (1 - a)))
      = ∑' j : ℕ, -(R ^ (j + k + 1) / (1 - a)) := hc_val.symm
    _ ≤ ∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + k + 1)‖ := hle

end Work.CNum
