import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Robin

theorem caExp_eq_zero_of_ge_bound (p : ℕ) (ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (h : Nat.ceil (Real.exp (2 / ε)) + 2 ≤ p) :
    Nat.floor (Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)) = 0 := by
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  -- p ≥ exp(2/ε), hence 2/ε ≤ log p
  have hp_ge_exp : Real.exp (2 / ε) ≤ (p : ℝ) := by
    have hc1 : Real.exp (2 / ε) ≤ (Nat.ceil (Real.exp (2 / ε)) : ℝ) := Nat.le_ceil _
    have hc2 : (Nat.ceil (Real.exp (2 / ε)) : ℝ) ≤
        (Nat.ceil (Real.exp (2 / ε)) : ℝ) + 2 := by linarith
    have hc3 : (Nat.ceil (Real.exp (2 / ε)) : ℝ) + 2 ≤ (p : ℝ) := by
      have h' : ((Nat.ceil (Real.exp (2 / ε)) + 2 : ℕ) : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast h
      simpa [Nat.cast_add] using h'
    exact le_trans (le_trans hc1 hc2) hc3
  have hlog_ge : (2 / ε) ≤ Real.log (p : ℝ) := by
    have h1 : Real.log (Real.exp (2 / ε)) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hp_ge_exp
    simpa [Real.log_exp] using h1
  have ht_ge : (2 : ℝ) ≤ ε * Real.log (p : ℝ) := by
    have hmul : ε * (2 / ε) ≤ ε * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlog_ge (le_of_lt hε)
    have htwo : (2 : ℝ) = ε * (2 / ε) := by field_simp [hε.ne']
    linarith
  -- t := ε log p ≥ 2, A := p^{1+ε}
  let t : ℝ := ε * Real.log (p : ℝ)
  let A : ℝ := (p : ℝ) ^ (1 + ε)
  have ht_ge' : (2 : ℝ) ≤ t := by simpa [t] using ht_ge
  have hAeq : A = (p : ℝ) * Real.exp t := by
    dsimp [A, t]
    rw [Real.rpow_add hp0r, Real.rpow_one, Real.rpow_def_of_pos hp0r]
    congr 1
    ring_nf
  -- 1 < p·(exp t − 1)  (stronger than needed: p·t ≥ 4)
  have hexpm1 : t ≤ Real.exp t - 1 := by
    have h1 := Real.add_one_le_exp t
    linarith
  have hpt : (4 : ℝ) ≤ (p : ℝ) * t := by
    have hm := mul_le_mul hp2r ht_ge' (by norm_num) (le_of_lt hp0r)
    norm_num at hm
    exact hm
  have hpt_le : (p : ℝ) * t ≤ (p : ℝ) * (Real.exp t - 1) :=
    mul_le_mul_of_nonneg_left hexpm1 (le_of_lt hp0r)
  have hmain : (1 : ℝ) < (p : ℝ) * (Real.exp t - 1) := by
    have h4 : (4 : ℝ) ≤ (p : ℝ) * (Real.exp t - 1) := le_trans hpt hpt_le
    linarith
  have hBig : (p : ℝ) + 1 < A := by
    rw [hAeq]
    linarith
  -- denominator and numerator of the quotient are positive
  have hdenpos : 0 < A - (p : ℝ) := by linarith
  have hnumpos : 0 < A - 1 := by linarith [hBig, hp2r]
  have hqpos : 0 < (A - 1) / (A - (p : ℝ)) := div_pos hnumpos hdenpos
  -- quotient < p
  have hqlp : (A - 1) / (A - (p : ℝ)) < (p : ℝ) := by
    have hpdiff : 0 < (p : ℝ) - 1 := by linarith
    have hprodpos : 0 < ((p : ℝ) - 1) * (A - (p : ℝ) - 1) := mul_pos hpdiff (by linarith)
    have hnlt : A - 1 < (p : ℝ) * (A - (p : ℝ)) := by nlinarith
    exact (div_lt_iff₀ hdenpos).mpr hnlt
  -- log(q) < log p, so v := log q / log p < 1, hence its Nat.floor is 0
  have hlogqlt : Real.log ((A - 1) / (A - (p : ℝ))) < Real.log (p : ℝ) :=
    Real.log_lt_log hqpos hqlp
  have hvlt : Real.log ((A - 1) / (A - (p : ℝ))) / Real.log (p : ℝ) < 1 :=
    (div_lt_one hlogp_pos).mpr hlogqlt
  rw [Nat.floor_eq_zero]
  simpa [A] using hvlt

end Commons.NumberTheory.Robin