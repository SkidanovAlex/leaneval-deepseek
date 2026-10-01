import Mathlib

namespace Work.Sieve

/-- For `x > 0` and `p > 0` we have `log x ≤ x^p / p`.

This is the elementary fact that the logarithm is dominated by any positive
power; it is obtained from `log t ≤ t - 1` applied to `t = x^p`. -/
lemma log_le_rpow_div (x : ℝ) (hx : 0 < x) (p : ℝ) (hp : 0 < p) :
    Real.log x ≤ x ^ p / p := by
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  have hlog1 : Real.log (x ^ p) ≤ x ^ p - 1 := Real.log_le_sub_one_of_pos hxp
  have hxp_expr : (x ^ p) ^ (1 / p) = x := by
    rw [← Real.rpow_mul hx.le p (1 / p)]
    have hp1 : p * (1 / p) = 1 := by rw [mul_one_div, div_self (ne_of_gt hp)]
    rw [hp1, Real.rpow_one]
  have hlog2 : (1 / p) * Real.log (x ^ p) = Real.log x := by
    rw [← Real.log_rpow hxp (1 / p), hxp_expr]
  rw [← hlog2]
  have h1 : (1 / p) * Real.log (x ^ p) ≤ (1 / p) * (x ^ p - 1) := by
    apply mul_le_mul_of_nonneg_left hlog1; positivity
  have h2 : (1 / p) * (x ^ p - 1) ≤ (1 / p) * x ^ p := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have h3 : (1 / p) * x ^ p = x ^ p / p := by ring
  linarith

theorem LFunction_critical_line_absorb :
    ∃ C : ℝ, 0 < C ∧ ∀ (N T : ℝ), 1 ≤ N →
      N ^ ((1 : ℝ) / 4) * (2 + |T|) ^ ((1 : ℝ) / 4) * (Real.log (N * (2 + |T|)) + 2)
        ≤ C * N ^ ((7 : ℝ) / 24) * Real.log (2 * N + 2) * (1 + |T|) ^ ((1 : ℝ) / 3) := by
  refine ⟨38 * (2 : ℝ) ^ ((1 : ℝ) / 3), mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro N T hN
  set S := 2 + |T| with hSdef
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have hS2 : 2 ≤ S := by rw [hSdef]; have := abs_nonneg T; linarith
  have hSpos : 0 < S := by linarith
  have h24 : Real.log N ≤ 24 * N ^ ((1 : ℝ) / 24) := by
    have h := log_le_rpow_div N hNpos (1 / 24) (by norm_num)
    rw [div_eq_mul_inv, show ((1 : ℝ) / 24)⁻¹ = 24 by norm_num, mul_comm] at h
    exact h
  have h12 : Real.log S ≤ 12 * S ^ ((1 : ℝ) / 12) := by
    have h := log_le_rpow_div S hSpos (1 / 12) (by norm_num)
    rw [div_eq_mul_inv, show ((1 : ℝ) / 12)⁻¹ = 12 by norm_num, mul_comm] at h
    exact h
  have hlog2N1 : 1 ≤ Real.log (2 * N + 2) := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 ≤ 4 by linarith [Real.exp_one_lt_three])
      rwa [Real.log_exp] at h
    have h5 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ 2 * N + 2 by linarith)
    linarith
  have hNp1 : 1 ≤ N ^ ((1 : ℝ) / 24) := Real.one_le_rpow hN (by norm_num)
  have hSp1 : 1 ≤ S ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith : (1 : ℝ) ≤ S) (by norm_num)
  have hNp0 : 0 ≤ N ^ ((1 : ℝ) / 24) := le_trans zero_le_one hNp1
  have hSp0 : 0 ≤ S ^ ((1 : ℝ) / 12) := le_trans zero_le_one hSp1
  have hlogpos : 0 ≤ Real.log (2 * N + 2) := le_trans zero_le_one hlog2N1
  set M := N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 12) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hab : 1 ≤ N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2) := by
    nlinarith [hNp1, hlog2N1, hNp0, hlogpos]
  have hab0 : 0 ≤ N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2) := mul_nonneg hNp0 hlogpos
  have hMn : N ^ ((1 : ℝ) / 24) ≤ M := by
    rw [hMdef]
    have hbc : 1 ≤ Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 12) := by
      nlinarith [hlog2N1, hSp1, hlogpos, hSp0]
    calc N ^ ((1 : ℝ) / 24) = N ^ ((1 : ℝ) / 24) * 1 := by ring
      _ ≤ N ^ ((1 : ℝ) / 24) * (Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 12)) :=
            mul_le_mul_of_nonneg_left hbc hNp0
      _ = N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 12) := by ring
  have hMs : S ^ ((1 : ℝ) / 12) ≤ M := by
    rw [hMdef]
    calc S ^ ((1 : ℝ) / 12) = 1 * S ^ ((1 : ℝ) / 12) := by ring
      _ ≤ (N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2)) * S ^ ((1 : ℝ) / 12) :=
            mul_le_mul_of_nonneg_right hab hSp0
      _ = N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 12) := by ring
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2)) * S ^ ((1 : ℝ) / 12) :=
            mul_le_mul hab hSp1 zero_le_one hab0
      _ = N ^ ((1 : ℝ) / 24) * Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 12) := by ring
  have hlogNS : Real.log (N * S) + 2 ≤ 24 * N ^ ((1 : ℝ) / 24) + 12 * S ^ ((1 : ℝ) / 12) + 2 := by
    rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hSpos)]
    linarith
  have hcore : Real.log (N * S) + 2 ≤ 38 * M := by
    have e1 : 24 * N ^ ((1 : ℝ) / 24) ≤ 24 * M := mul_le_mul_of_nonneg_left hMn (by norm_num)
    have e2 : 12 * S ^ ((1 : ℝ) / 12) ≤ 12 * M := mul_le_mul_of_nonneg_left hMs (by norm_num)
    have e3 : (2 : ℝ) ≤ 2 * M := by linarith
    linarith
  have hNexp : N ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 24) = N ^ ((7 : ℝ) / 24) := by
    rw [← Real.rpow_add hNpos (1 / 4) (1 / 24), show ((1 : ℝ) / 4 + 1 / 24) = 7 / 24 by norm_num]
  have hSexp : S ^ ((1 : ℝ) / 4) * S ^ ((1 : ℝ) / 12) = S ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hSpos (1 / 4) (1 / 12), show ((1 : ℝ) / 4 + 1 / 12) = 1 / 3 by norm_num]
  have hSle : S ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) * (1 + |T|) ^ ((1 : ℝ) / 3) := by
    have hle : S ≤ 2 * (1 + |T|) := by rw [hSdef]; have := abs_nonneg T; linarith
    calc S ^ ((1 : ℝ) / 3) ≤ (2 * (1 + |T|)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hSpos.le hle (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 3) * (1 + |T|) ^ ((1 : ℝ) / 3) :=
          Real.mul_rpow (by norm_num) (by positivity)
  calc N ^ ((1 : ℝ) / 4) * S ^ ((1 : ℝ) / 4) * (Real.log (N * S) + 2)
      ≤ N ^ ((1 : ℝ) / 4) * S ^ ((1 : ℝ) / 4) * (38 * M) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 38 * (N ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 24)) * Real.log (2 * N + 2)
          * (S ^ ((1 : ℝ) / 4) * S ^ ((1 : ℝ) / 12)) := by rw [hMdef]; ring
    _ = 38 * N ^ ((7 : ℝ) / 24) * Real.log (2 * N + 2) * S ^ ((1 : ℝ) / 3) := by rw [hNexp, hSexp]
    _ ≤ 38 * N ^ ((7 : ℝ) / 24) * Real.log (2 * N + 2)
          * ((2 : ℝ) ^ ((1 : ℝ) / 3) * (1 + |T|) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = 38 * (2 : ℝ) ^ ((1 : ℝ) / 3) * N ^ ((7 : ℝ) / 24) * Real.log (2 * N + 2)
          * (1 + |T|) ^ ((1 : ℝ) / 3) := by ring

end Work.Sieve
