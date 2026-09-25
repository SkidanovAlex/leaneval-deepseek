import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound

namespace Commons.NumberTheory.Zeta

/-- **Lagarias-type consequence of RH for Chebyshev's first function:**
`|θ(x) − x| = O(√x (log x)^10)` as `x → ∞`.

This follows from the analogous bound for `ψ` (which is a consequence of RH via
the truncated Perron formula) together with Chebyshev's elementary estimate
`ψ(x) − θ(x) = O(√x)`. -/
theorem chebyshevTheta_sub_id_rh_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.theta x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 10 := by
  obtain ⟨Cψ, hCψ0, x₀ψ, hCψ⟩ := chebyshevPsi_sub_id_rh_bound h
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : ℝ := Cψ + max C₀ 1
  have hC0 : 0 < C := by
    dsimp [C]
    have hmaxpos : 0 < max C₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
    linarith
  refine ⟨C, hC0, max x₀ψ (Real.exp 1), ?_⟩
  intro x hx
  have hxψ : x₀ψ ≤ x := le_trans (le_max_left x₀ψ (Real.exp 1)) hx
  have hx₁ : Real.exp 1 ≤ x := le_trans (le_max_right x₀ψ (Real.exp 1)) hx
  have hbpsi := hCψ x hxψ
  -- For `x ≥ e` we have `log x ≥ 1`, hence `(log x)^10 ≥ 1`.
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx₁
    rwa [Real.log_exp] at h
  have hpow : (1 : ℝ) ≤ (Real.log x) ^ 10 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog1 10
    simpa using hp
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- `ψ x − θ x ≥ 0`, since `θ ≤ ψ`.
  have hdiff_nonneg : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
    exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  -- `ψ x − θ x ≤ max C₀ 1 * √x * (log x)^10` for large `x`.
  have hdiff_le : Chebyshev.psi x - Chebyshev.theta x ≤
      max C₀ 1 * Real.sqrt x * (Real.log x) ^ 10 := by
    have hmaxpos : 0 < max C₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
    calc
      Chebyshev.psi x - Chebyshev.theta x ≤ C₀ * Real.sqrt x := hC₀ x
      _ ≤ max C₀ 1 * Real.sqrt x := by
        exact mul_le_mul_of_nonneg_right (le_max_left C₀ 1) hsqrt
      _ ≤ max C₀ 1 * Real.sqrt x * (Real.log x) ^ 10 := by
        exact le_mul_of_one_le_right (mul_nonneg (le_of_lt hmaxpos) hsqrt) hpow
  -- Triangle inequality: `θ − x = (ψ − x) − (ψ − θ)`.
  have htri : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
    calc
      |Chebyshev.theta x - x|
          = |(Chebyshev.psi x - x) + (Chebyshev.theta x - Chebyshev.psi x)| := by
            congr 1
            ring
      _ ≤ |Chebyshev.psi x - x| + |Chebyshev.theta x - Chebyshev.psi x| := abs_add_le _ _
      _ = |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
            congr 1
            rw [abs_sub_comm, abs_of_nonneg hdiff_nonneg]
  calc
    |Chebyshev.theta x - x|
        ≤ |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := htri
    _ ≤ Cψ * Real.sqrt x * (Real.log x) ^ 10 +
          max C₀ 1 * Real.sqrt x * (Real.log x) ^ 10 := add_le_add hbpsi hdiff_le
    _ = (Cψ + max C₀ 1) * Real.sqrt x * (Real.log x) ^ 10 := by ring
    _ = C * Real.sqrt x * (Real.log x) ^ 10 := by rfl

end Commons.NumberTheory.Zeta
