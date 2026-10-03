import Mathlib
import Submission.Work.FIArea6Road.CaseAArith

namespace Work.FIArea6Road

/-- Case-A arithmetic inequality with the constant `C_z`-lower-bound stated through an
arbitrary positive parameter `K` (`1 / (K · d · (log N)^6) ≤ C_z`) and with the matching
factor `(K + 1)` on the right-hand side.

It is deduced from `CaseAArith` (which handles the fixed constant `10000` and no `(K+1)`
factor) by rescaling the `d`-parameter: put `d' = max (K·d/10000) 1`.  Then

* `1 / (10000 · d' · L^6) ≤ C_z` follows from the hypothesis `1 / (K · d · L^6) ≤ C_z`,
  because `10000 · d' ≥ K · d`;
* `d' ≤ (K + 1) · d`, so `4 d' ≤ (K + 1) · (4 d)`, which supplies the extra `(K+1)`
  factor on the right-hand side. -/
theorem HeartZcCaseAArith (N θ d K C_W C_z R : ℝ)
    (hN1 : 1 ≤ N) (hlogN : 1000 ≤ Real.log N) (hd : 1 ≤ d) (hK : 0 < K) (hCW : 0 < C_W)
    (hCz : 1 / (K * d * (Real.log N) ^ (6 : ℕ)) ≤ C_z)
    (hθ : 0 ≤ θ) (hcase : θ ≤ R / (256 * (Real.log N) ^ (3 : ℕ)))
    (hR : Real.exp (-(Real.log N / 8)) ≤ R) :
    4 * (C_W * (θ * N + 1) * (Real.log (4 * N)) ^ (3 : ℕ)
          + C_W * (2 * N) ^ ((3 : ℝ) / 4) * (Real.log (4 * N)) ^ (2 : ℕ))
      ≤ ((10 : ℝ) ^ 100 * (C_W + 1) * (K + 1)) * C_z * R * (4 * d) * N
          * (Real.log N) ^ (6 : ℕ) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hLpos : 0 < Real.log N := by linarith
  have hL6pos : 0 < (Real.log N) ^ (6 : ℕ) := pow_pos hLpos 6
  have hKdpos : 0 < K * d := mul_pos hK hdpos
  have hdenpos : 0 < K * d * (Real.log N) ^ (6 : ℕ) := mul_pos hKdpos hL6pos
  -- rescaled parameter `d' = max (K·d/10000) 1`
  set d' : ℝ := max (K * d / 10000) 1 with hd'def
  have hd'1 : 1 ≤ d' := by rw [hd'def]; exact le_max_right _ _
  have hd'ge : K * d / 10000 ≤ d' := by rw [hd'def]; exact le_max_left _ _
  have hKd_le : K * d ≤ 10000 * d' := by
    have h : (10000 : ℝ) * (K * d / 10000) ≤ 10000 * d' :=
      mul_le_mul_of_nonneg_left hd'ge (by norm_num)
    rwa [show (10000 : ℝ) * (K * d / 10000) = K * d by ring] at h
  have hd'le : d' ≤ (K + 1) * d := by
    apply max_le
    · have h1 : K * d / 10000 ≤ K * d := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10000)]
        nlinarith [le_of_lt hKdpos]
      have h2 : K * d ≤ (K + 1) * d := by nlinarith [hdpos]
      linarith
    · have hKdnn : 0 ≤ K * d := le_of_lt hKdpos
      nlinarith [hKdnn, hd]
  -- transfer the `C_z` lower bound to `d'`
  have hCz' : 1 / (10000 * d' * (Real.log N) ^ (6 : ℕ)) ≤ C_z := by
    refine le_trans ?_ hCz
    apply one_div_le_one_div_of_le hdenpos
    exact mul_le_mul_of_nonneg_right hKd_le (le_of_lt hL6pos)
  have hmain :=
    CaseAArith N θ d' C_W C_z R hN1 hlogN hd'1 hCW hCz' hθ hcase hR
  have hCznn : 0 ≤ C_z := le_trans (le_of_lt (one_div_pos.mpr hdenpos)) hCz
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hR
  have hbase : 0 ≤ (10 : ℝ) ^ 100 * (C_W + 1) * C_z * R * N * (Real.log N) ^ (6 : ℕ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hCznn)
      (le_of_lt hRpos)) (le_of_lt hNpos)) (le_of_lt hL6pos)
  have hfac : 4 * d' ≤ (K + 1) * (4 * d) := by
    have h := mul_le_mul_of_nonneg_left hd'le (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith [h]
  calc 4 * (C_W * (θ * N + 1) * (Real.log (4 * N)) ^ (3 : ℕ)
          + C_W * (2 * N) ^ ((3 : ℝ) / 4) * (Real.log (4 * N)) ^ (2 : ℕ))
      ≤ ((10 : ℝ) ^ 100 * (C_W + 1)) * C_z * R * (4 * d') * N * (Real.log N) ^ (6 : ℕ) := hmain
    _ = ((10 : ℝ) ^ 100 * (C_W + 1) * C_z * R * N * (Real.log N) ^ (6 : ℕ)) * (4 * d') := by ring
    _ ≤ ((10 : ℝ) ^ 100 * (C_W + 1) * C_z * R * N * (Real.log N) ^ (6 : ℕ))
          * ((K + 1) * (4 * d)) :=
        mul_le_mul_of_nonneg_left hfac hbase
    _ = ((10 : ℝ) ^ 100 * (C_W + 1) * (K + 1)) * C_z * R * (4 * d) * N
          * (Real.log N) ^ (6 : ℕ) := by ring

end Work.FIArea6Road
