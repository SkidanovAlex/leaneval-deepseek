import Mathlib

namespace Work.LinnikAreas.Density4

/-- Uniform bound for the "large divisor" part of the induction step: since
`t ↦ t^{-1/200}(log t)^5` is continuous on `[1,∞)` and tends to `0`, the expression
`Q^{-1/200}·(1000 + log(2+Q^{99/100})(1+log(2+Q^{99/100})))·(log(2+Q))^3` is bounded for `Q ≥ 1`.
(Provable from `Real.log_le_rpow_div`/`Real.log_le_sub_one_of_pos`-type estimates, e.g.
`log y ≤ 200·y^{1/1000}`, or directly by continuity on a compact interval plus a tail bound.) -/
theorem window_log_bound : ∃ Kw : ℝ, 0 < Kw ∧ ∀ Q : ℝ, 1 ≤ Q →
    Q ^ (-(1:ℝ)/200) *
        (1000 + Real.log (2 + Q ^ ((99:ℝ)/100)) * (1 + Real.log (2 + Q ^ ((99:ℝ)/100))))
      * (Real.log (2 + Q)) ^ 3 ≤ Kw := by
  -- The explicit constant `1002 ^ 6` suffices.
  refine ⟨1002^6, by norm_num, ?_⟩
  intro Q hQ
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  set M := Real.log (2 + Q) with hMdef
  set L := Real.log (2 + Q ^ ((99:ℝ)/100)) with hLdef
  -- `L ≤ M`, because `Q^{99/100} ≤ Q`.
  have hLleM : L ≤ M := by
    have hQ991 : (1:ℝ) ≤ Q ^ ((99:ℝ)/100) := Real.one_le_rpow hQ (by norm_num)
    have h1 : Q ^ ((99:ℝ)/100) ≤ Q := by
      have h := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (99:ℝ)/100 ≤ 1)
      simpa using h
    rw [hLdef, hMdef]
    exact Real.log_le_log (by linarith) (by linarith)
  -- `1 ≤ M`, since `2 + Q ≥ 3` and `log 3 ≥ 1`.
  have hMge1 : 1 ≤ M := by
    rw [hMdef]
    have h3 : (3:ℝ) ≤ 2 + Q := by linarith
    have h4 : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) h3
    have h5 : (1:ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three.le
    linarith
  have hMnn : 0 ≤ M := le_trans (by norm_num) hMge1
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    have hQ991 : (1:ℝ) ≤ Q ^ ((99:ℝ)/100) := Real.one_le_rpow hQ (by norm_num)
    linarith
  -- `1000 + L(1+L) ≤ 1002 M²`.
  have hpoly : 1000 + L * (1 + L) ≤ 1002 * M^2 := by
    have h1 : L * (1 + L) ≤ M * (1 + M) :=
      mul_le_mul hLleM (by linarith) (by linarith) hMnn
    have h2 : 1000 + M * (1 + M) ≤ 1002 * M^2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - 1)
        (by linarith : (0:ℝ) ≤ 1001 * M + 1000)]
    linarith
  -- `log Q ≤ 1000 · Q^{1/1000}`.
  have hlogQ : Real.log Q ≤ 1000 * Q ^ ((1:ℝ)/1000) := by
    have h := Real.log_le_rpow_div (le_of_lt hQpos) (by norm_num : (0:ℝ) < 1/1000)
    have h' : Q ^ ((1:ℝ)/1000) / ((1:ℝ)/1000) = 1000 * Q ^ ((1:ℝ)/1000) := by ring
    linarith [h, h'.le]
  -- `M ≤ 1002 · Q^{1/1000}`.
  have hMle : M ≤ 1002 * Q ^ ((1:ℝ)/1000) := by
    rw [hMdef]
    have h3Q : (2 + Q) ≤ 3 * Q := by linarith
    have hlog3Q : Real.log (2 + Q) ≤ Real.log (3 * Q) := Real.log_le_log (by linarith) h3Q
    have hlog3mul : Real.log (3 * Q) = Real.log 3 + Real.log Q :=
      Real.log_mul (by norm_num) (ne_of_gt hQpos)
    have hlog3le2 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
    have hQp : (1:ℝ) ≤ Q ^ ((1:ℝ)/1000) := Real.one_le_rpow hQ (by norm_num)
    calc Real.log (2 + Q) ≤ Real.log (3 * Q) := hlog3Q
      _ = Real.log 3 + Real.log Q := hlog3mul
      _ ≤ 2 + 1000 * Q ^ ((1:ℝ)/1000) := by linarith
      _ ≤ 1002 * Q ^ ((1:ℝ)/1000) := by nlinarith [hQp]
  -- `(Q^{1/1000})^5 = Q^{1/200}`.
  have hpow : (Q ^ ((1:ℝ)/1000)) ^ 5 = Q ^ ((1:ℝ)/200) := by
    calc (Q ^ ((1:ℝ)/1000)) ^ 5
        = (Q ^ ((1:ℝ)/1000)) ^ (5:ℝ) := (Real.rpow_natCast _ 5).symm
      _ = Q ^ (((1:ℝ)/1000) * (5:ℝ)) := (Real.rpow_mul (le_of_lt hQpos) _ _).symm
      _ = Q ^ ((1:ℝ)/200) := by norm_num
  have hQinv : Q ^ (-(1:ℝ)/200) * Q ^ ((1:ℝ)/200) = 1 := by
    rw [← Real.rpow_add hQpos, show (-(1:ℝ)/200) + ((1:ℝ)/200) = 0 by ring, Real.rpow_zero]
  -- `Q^{-1/200} · M^5 ≤ 1002^5`.
  have hcore : Q ^ (-(1:ℝ)/200) * M^5 ≤ 1002^5 := by
    have hM5 : M^5 ≤ 1002^5 * Q ^ ((1:ℝ)/200) := by
      calc M^5 ≤ (1002 * Q ^ ((1:ℝ)/1000))^5 := pow_le_pow_left₀ hMnn hMle 5
        _ = 1002^5 * (Q ^ ((1:ℝ)/1000))^5 := by rw [mul_pow]
        _ = 1002^5 * Q ^ ((1:ℝ)/200) := by rw [hpow]
    calc Q ^ (-(1:ℝ)/200) * M^5
        ≤ Q ^ (-(1:ℝ)/200) * (1002^5 * Q ^ ((1:ℝ)/200)) :=
          mul_le_mul_of_nonneg_left hM5 (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ = 1002^5 * (Q ^ (-(1:ℝ)/200) * Q ^ ((1:ℝ)/200)) := by ring
      _ = 1002^5 := by rw [hQinv, mul_one]
  calc Q ^ (-(1:ℝ)/200) * (1000 + L * (1 + L)) * M^3
      ≤ Q ^ (-(1:ℝ)/200) * (1002 * M^2) * M^3 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (le_of_lt hQpos) _)
        · exact pow_nonneg hMnn 3
    _ = 1002 * (Q ^ (-(1:ℝ)/200) * M^5) := by ring
    _ ≤ 1002 * 1002^5 := mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = 1002^6 := by norm_num

end Work.LinnikAreas.Density4
