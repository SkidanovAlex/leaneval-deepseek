import Mathlib
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz

namespace Work.TMC7Core.Scale

/-- **S0** of the lead's C7 design (see `Submission/Work/TMC7Core/Scale/S0_GUIDE.md`):
the crude Lipschitz constant `lipK` is bounded by `2·lipL·e^{(log lipM + 2)N}`. -/
theorem lipK_le_exp (lam : ℝ) (N : ℕ) (R : ℝ) (hN : 1 ≤ N) :
    Work.TMC7Core.Scale.lipK lam N R
      ≤ 2 * Work.TMC7Core.Scale.lipL lam
        * Real.exp ((Real.log (Work.TMC7Core.Scale.lipM lam R) + 2) * (N : ℝ)) := by
  have hM1 : 1 ≤ lipM lam R := lipM_ge_one lam R
  have hM0 : 0 < lipM lam R := lt_of_lt_of_le one_pos hM1
  have hL1 : 1 ≤ lipL lam := le_max_left _ _
  have hL0 : 0 ≤ lipL lam := le_trans zero_le_one hL1
  have hMN0 : 0 ≤ (lipM lam R) ^ N := pow_nonneg (le_of_lt hM0) N
  -- The exponential rewrites as `lipM ^ N * exp (2 N)`.
  have hexp : Real.exp ((Real.log (lipM lam R) + 2) * (N : ℝ))
      = (lipM lam R) ^ N * Real.exp (2 * (N : ℝ)) := by
    rw [add_mul, Real.exp_add, mul_comm (Real.log (lipM lam R)) (N : ℝ), Real.exp_nat_mul,
      Real.exp_log hM0]
  rw [hexp, lipK]
  apply max_le
  · -- `1 ≤ 2 * lipL * (lipM ^ N * exp (2N))`
    have he2 : 1 ≤ Real.exp (2 * (N : ℝ)) := Real.one_le_exp (by positivity)
    have hMN : 1 ≤ (lipM lam R) ^ N := one_le_pow₀ hM1
    have ha : 1 ≤ 2 * lipL lam := by linarith
    have hb : 1 ≤ (lipM lam R) ^ N * Real.exp (2 * (N : ℝ)) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (lipM lam R) ^ N * Real.exp (2 * (N : ℝ)) :=
            mul_le_mul hMN he2 (by norm_num) hMN0
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * lipL lam) * ((lipM lam R) ^ N * Real.exp (2 * (N : ℝ))) :=
          mul_le_mul ha hb (by norm_num) (by linarith)
      _ = 2 * lipL lam * ((lipM lam R) ^ N * Real.exp (2 * (N : ℝ))) := by ring
  · -- `lipC ≤ 2 * lipL * (lipM ^ N * exp (2N))`, reducing to `N ^ 2 ≤ 2 * exp (2N)`
    rw [lipC, lipD]
    have hsq : (N : ℝ) ^ 2 ≤ 2 * Real.exp (2 * (N : ℝ)) := by
      have h1 : (N : ℝ) < (2 : ℝ) ^ N := by
        have h := Nat.lt_two_pow_self (n := N)
        calc (N : ℝ) = ((N : ℕ) : ℝ) := by simp
          _ < ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast h
          _ = (2 : ℝ) ^ N := by push_cast; ring
      have h2 : (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ N) ^ 2 := by
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
        have h2N : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
        have := mul_le_mul h1.le h1.le hN0 h2N
        simpa [sq] using this
      have h3 : ((2 : ℝ) ^ N) ^ 2 = (4 : ℝ) ^ N := by
        have e1 : ((2 : ℝ) ^ N) ^ 2 = (2 : ℝ) ^ (N * 2) := by rw [← pow_mul]
        have e2 : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * N) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
        rw [e1, e2]
        congr 1
        ring
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        have h : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
        have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [he]; nlinarith
      have h5 : (4 : ℝ) ^ N ≤ (Real.exp 2) ^ N := pow_le_pow_left₀ (by norm_num) h4 N
      have h6 : (Real.exp 2) ^ N = Real.exp (2 * (N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ N) ^ 2 := h2
        _ = (4 : ℝ) ^ N := h3
        _ ≤ (Real.exp 2) ^ N := h5
        _ = Real.exp (2 * (N : ℝ)) := h6
        _ ≤ 2 * Real.exp (2 * (N : ℝ)) := by
            have := Real.exp_nonneg (2 * (N : ℝ)); linarith
    have hML : 0 ≤ (lipM lam R) ^ N * lipL lam := mul_nonneg hMN0 hL0
    calc (N : ℝ) * (lipM lam R) ^ N * (lipL lam * (N : ℝ))
        = ((N : ℝ) ^ 2) * ((lipM lam R) ^ N * lipL lam) := by ring
      _ ≤ (2 * Real.exp (2 * (N : ℝ))) * ((lipM lam R) ^ N * lipL lam) :=
          mul_le_mul_of_nonneg_right hsq hML
      _ = 2 * lipL lam * ((lipM lam R) ^ N * Real.exp (2 * (N : ℝ))) := by ring

end Work.TMC7Core.Scale
