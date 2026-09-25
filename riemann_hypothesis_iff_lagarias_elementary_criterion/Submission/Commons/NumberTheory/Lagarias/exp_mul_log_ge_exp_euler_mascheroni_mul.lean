import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Submission.Commons.NumberTheory.Harmonic.positive

namespace Commons.NumberTheory.Lagarias

theorem exp_mul_log_ge_exp_euler_mascheroni_mul (n : ℕ) (hn : 3 ≤ n) :
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hγ_lt : Real.eulerMascheroniConstant < (harmonic n : ℝ) - Real.log (n : ℝ) := by
    simpa [Real.eulerMascheroniSeq', hn0] using
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hH_ge_logn_addγ : Real.log (n : ℝ) + Real.eulerMascheroniConstant ≤ (harmonic n : ℝ) := by
    linarith
  have h_exp : Real.exp Real.eulerMascheroniConstant * (n : ℝ) ≤ Real.exp (harmonic n : ℝ) := by
    have htmp : Real.exp (Real.log (n : ℝ) + Real.eulerMascheroniConstant) ≤
        Real.exp (harmonic n : ℝ) := by
      exact Real.exp_le_exp.mpr hH_ge_logn_addγ
    rw [Real.exp_add, Real.exp_log] at htmp
    · rwa [mul_comm] at htmp
    · exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have h_logn_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h_log3_ge_one : 1 ≤ Real.log (3 : ℝ) := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
  have h_log3_le_logn : Real.log (3 : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hn)
  have h_one_le_logn : 1 ≤ Real.log (n : ℝ) := by
    linarith
  have h_loglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Real.log_nonneg h_one_le_logn
  have hH_pos : 0 ≤ Real.exp (harmonic n : ℝ) := by positivity
  have h_logn_le_H : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
    have hlog_n_le_log_succ : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) := by
      exact Real.log_le_log hn_pos_real (by exact_mod_cast Nat.le_succ n)
    calc
      Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) := hlog_n_le_log_succ
      _ ≤ (harmonic n : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n
  have h_log_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (harmonic n : ℝ) := by
    exact Real.log_le_log h_logn_pos h_logn_le_H
  calc
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))
        ≤ Real.exp (harmonic n : ℝ) * Real.log (Real.log (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right h_exp h_loglog_nonneg
    _ ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
          exact mul_le_mul_of_nonneg_left h_log_le hH_pos

end Commons.NumberTheory.Lagarias