import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotics

theorem log_add_one_rpow_le_mul_rpow {A : ℝ} (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x + 1) ^ A ≤ C * x ^ a := by
  set n : ℕ := Nat.ceil A with hn
  have hAn : A ≤ (n : ℝ) := by
    rw [hn]; exact Nat.le_ceil A
  refine ⟨(n.factorial : ℝ) * Real.exp a * (a ^ n)⁻¹, ?_, ?_⟩
  · positivity
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hbase : (1 : ℝ) ≤ Real.log x + 1 := by linarith
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have ha_pow : 0 < a ^ n := by positivity
    have hy : 0 ≤ a * (Real.log x + 1) := by positivity
    have hy_pow :
        (a * (Real.log x + 1)) ^ n ≤ (n.factorial : ℝ) * Real.exp (a * (Real.log x + 1)) := by
      have h := Real.pow_div_factorial_le_exp (a * (Real.log x + 1)) hy n
      rw [div_le_iff₀ hfac] at h
      simpa [mul_comm] using h
    have hexp : Real.exp (a * Real.log x) = x ^ a := by
      rw [mul_comm a (Real.log x), ← Real.rpow_def_of_pos hx0 a]
    have key : a ^ n * (Real.log x + 1) ^ n ≤ (n.factorial : ℝ) * Real.exp a * x ^ a := by
      calc
        a ^ n * (Real.log x + 1) ^ n = (a * (Real.log x + 1)) ^ n := by rw [mul_pow]
        _ ≤ (n.factorial : ℝ) * Real.exp (a * (Real.log x + 1)) := hy_pow
        _ = (n.factorial : ℝ) * (Real.exp (a * Real.log x) * Real.exp a) := by
              rw [mul_add, mul_one, Real.exp_add]
        _ = (n.factorial : ℝ) * (x ^ a * Real.exp a) := by rw [hexp]
        _ = (n.factorial : ℝ) * Real.exp a * x ^ a := by ring
    have step2' : (Real.log x + 1) ^ n ≤
        ((n.factorial : ℝ) * Real.exp a * x ^ a) / a ^ n := by
      rw [le_div_iff₀ ha_pow, mul_comm]
      exact key
    have heq : ((n.factorial : ℝ) * Real.exp a * x ^ a) / a ^ n
        = ((n.factorial : ℝ) * Real.exp a * (a ^ n)⁻¹) * x ^ a := by
      rw [div_eq_mul_inv]; ring
    calc
      (Real.log x + 1) ^ A ≤ (Real.log x + 1) ^ (n : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase hAn
      _ = (Real.log x + 1) ^ n := Real.rpow_natCast _ _
      _ ≤ ((n.factorial : ℝ) * Real.exp a * (a ^ n)⁻¹) * x ^ a := by
            rw [← heq]; exact step2'

end Commons.Analysis.Asymptotics