import Mathlib

namespace Work.ZeroFreeTables

/-- Auxiliary: for `q, T > 0` with `log q ≥ 15` and `T ≤ 10 log q`, one has
`log (q * T) ≤ 2 * log q + 9`. -/
private lemma log_mul_le_two_log_add_nine {q T : ℝ} (hq : 0 < q)
    (hlog : 15 ≤ Real.log q) (hT : 1 ≤ T) (hTq : T ≤ 10 * Real.log q) :
    Real.log (q * T) ≤ 2 * Real.log q + 9 := by
  have hLpos : 0 < Real.log q := by linarith
  have hTpos : 0 < T := by linarith
  rw [Real.log_mul (ne_of_gt hq) (ne_of_gt hTpos)]
  have h1 : Real.log T ≤ Real.log (10 * Real.log q) :=
    Real.log_le_log hTpos hTq
  have h2 : Real.log (10 * Real.log q) = Real.log 10 + Real.log (Real.log q) :=
    Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have h3 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10); linarith
  have h4 : Real.log (Real.log q) ≤ Real.log q := by
    have := Real.log_le_sub_one_of_pos hLpos; linarith
  linarith

theorem rpow_three_le_exp {q : ℕ} {Λ T : ℝ} (hlog : 15 ≤ Real.log (q : ℝ))
    (hΛ : Λ ≤ 3) (hT : 1 ≤ T) (hTq : T ≤ 10 * Real.log (q : ℝ)) :
    ((q : ℝ) * T) ^ (3 * (max Λ 0 / Real.log (q : ℝ))) ≤ Real.exp 27 := by
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso
      rw [h] at hlog
      norm_num at hlog
    · exact_mod_cast h
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hTpos : 0 < T := by linarith
  set L := Real.log (q : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hbasepos : 0 < (q:ℝ) * T := mul_pos hqpos hTpos
  have hM : max Λ 0 ≤ 3 := max_le hΛ (by norm_num)
  have hMnn : 0 ≤ max Λ 0 := le_max_right _ _
  -- exponent bound: `3 * max Λ 0 / L ≤ 9 / L`
  have heL : 3 * (max Λ 0 / L) ≤ 9 / L := by
    have h3 : 3 * (max Λ 0 / L) = (3 * max Λ 0) / L := by ring
    rw [h3]
    apply div_le_div_of_nonneg_right _ hLpos.le
    linarith
  have henn : 0 ≤ 3 * (max Λ 0 / L) := by
    have : 0 ≤ max Λ 0 / L := div_nonneg hMnn hLpos.le
    linarith
  -- logarithm bound
  have hlogqT : Real.log ((q:ℝ) * T) ≤ 2 * L + 9 :=
    log_mul_le_two_log_add_nine hqpos (by linarith) hT hTq
  have hlogqTnn : 0 ≤ Real.log ((q:ℝ) * T) := by
    apply Real.log_nonneg
    nlinarith [hq1, hT]
  have hfin : (2 * L + 9) * (9 / L) ≤ 27 := by
    have h : (2 * L + 9) * (9 / L) = (9 * (2 * L + 9)) / L := by ring
    rw [h, div_le_iff₀ hLpos]
    linarith
  have hmain : Real.log ((q:ℝ) * T) * (3 * (max Λ 0 / L)) ≤ 27 := by
    have hb : (0:ℝ) ≤ 2 * L + 9 := by linarith
    exact le_trans (mul_le_mul hlogqT heL henn hb) hfin
  calc ((q:ℝ) * T) ^ (3 * (max Λ 0 / L))
      = Real.exp (Real.log ((q:ℝ) * T) * (3 * (max Λ 0 / L))) :=
        Real.rpow_def_of_pos hbasepos _
    _ ≤ Real.exp 27 := Real.exp_le_exp.mpr hmain

end Work.ZeroFreeTables
