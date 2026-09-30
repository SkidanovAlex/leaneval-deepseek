import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- An explicit, fully uniform upper bound for the prime counting function at `⌊T⌋₊`
in terms of `T / log T`, valid for all `T ≥ 2`.

It is obtained from Mathlib's explicit Chebyshev-type bound
`Chebyshev.pi_le_log4_mul_div` (`π ⌊x⌋₊ ≤ log 4 * x / log √x + √x` for `x > 1`)
together with the elementary inequality `log x ≤ 2 √x`. -/
theorem primeCounting_floor_le_div_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ((⌊T⌋₊).primeCounting : ℝ) ≤ C * T / Real.log T := by
  refine ⟨2 * Real.log 4 + 2,
    by have : 0 < Real.log 4 := Real.log_pos (by norm_num); linarith, ?_⟩
  intro T hT
  have hT1 : 1 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hTpos : 0 < T := by linarith
  -- `log T ≤ 2 √T`, from Mathlib's `log x ≤ x ^ ε / ε` with `ε = 1/2`.
  have hlog_le_sqrt : Real.log T ≤ 2 * Real.sqrt T := by
    have h := Real.log_le_rpow_div (x := T) (ε := (1 : ℝ) / 2) (by linarith) (by norm_num)
    rw [show T ^ ((1 : ℝ) / 2) = Real.sqrt T by rw [Real.sqrt_eq_rpow]] at h
    have h' : Real.sqrt T / (1 / 2) = 2 * Real.sqrt T := by ring
    linarith
  have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt (le_of_lt hTpos)
  -- consequently `√T ≤ 2 T / log T`.
  have hsqrt_le : Real.sqrt T ≤ 2 * T / Real.log T := by
    rw [le_div_iff₀ hlogT]
    nlinarith [hlog_le_sqrt, Real.sqrt_nonneg T, hsq]
  -- Chebyshev's explicit bound, with `log √T = (log T)/2`.
  have hpi := Chebyshev.pi_le_log4_mul_div hT1
  rw [Real.log_sqrt (le_of_lt hTpos)] at hpi
  have hterm : Real.log 4 * T / (Real.log T / 2) = 2 * Real.log 4 * T / Real.log T := by
    field_simp
  rw [hterm] at hpi
  calc ((⌊T⌋₊).primeCounting : ℝ)
      ≤ 2 * Real.log 4 * T / Real.log T + Real.sqrt T := hpi
    _ ≤ 2 * Real.log 4 * T / Real.log T + 2 * T / Real.log T := by linarith
    _ = (2 * Real.log 4 + 2) * T / Real.log T := by ring

end Work.BMF.mr_direct
