import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

/-- Pointwise exponential moment bound.

For `0 ≤ Cw`, `0 ≤ ε ≤ 1` and `0 ≤ u ≤ 2·Cw·ε` one has
`2 (e^u - 1) e^u ≤ 4·Cw·ε·e^{4 Cw}`.

The proof uses the tangent-line bound `e^u - 1 ≤ u e^u` (equivalently
`1 - u ≤ e^{-u}`, i.e. the tangent line of `exp` at `0`), then
`e^u ≤ e^{2 Cw ε} ≤ e^{4 Cw}` (as `ε ≤ 1` and `Cw ≥ 0`). -/
theorem exp_moment_pt {Cw ε u : ℝ} (hCw : 0 ≤ Cw) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : 0 ≤ u) (hu2 : u ≤ 2 * Cw * ε) :
    2 * (Real.exp u - 1) * Real.exp u ≤ 4 * Cw * ε * Real.exp (4 * Cw) := by
  have hCwε : 0 ≤ Cw * ε := mul_nonneg hCw hε0
  have hEpos : 0 < Real.exp u := Real.exp_pos u
  -- Tangent-line bound: `e^u - 1 ≤ u * e^u` for `u ≥ 0`.
  have h3 : Real.exp u - 1 ≤ u * Real.exp u := by
    have hlin : 1 - u ≤ Real.exp (-u) := by
      have h := Real.add_one_le_exp (-u); linarith
    have hmul : (1 - u) * Real.exp u ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hlin hEpos.le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
      exact h
    nlinarith [hmul]
  have h4 : Real.exp u ≤ Real.exp (2 * Cw * ε) := Real.exp_le_exp.2 hu2
  have hsq : Real.exp (2 * Cw * ε) ^ 2 = Real.exp (4 * Cw * ε) := by
    rw [sq, ← Real.exp_add, Real.exp_eq_exp]; ring
  have h5 : Real.exp (4 * Cw * ε) ≤ Real.exp (4 * Cw) := by
    apply Real.exp_le_exp.2
    nlinarith [hCw, hε0, hε1]
  have hA : 2 * (Real.exp u - 1) * Real.exp u ≤ 2 * u * Real.exp u ^ 2 := by
    calc 2 * (Real.exp u - 1) * Real.exp u
        ≤ 2 * (u * Real.exp u) * Real.exp u := by
          have h2 : 2 * (Real.exp u - 1) ≤ 2 * (u * Real.exp u) := by linarith
          exact mul_le_mul_of_nonneg_right h2 hEpos.le
      _ = 2 * u * Real.exp u ^ 2 := by ring
  have hB : 2 * u * Real.exp u ^ 2 ≤
      2 * (2 * Cw * ε) * Real.exp (2 * Cw * ε) ^ 2 := by
    have h1 : 2 * u ≤ 2 * (2 * Cw * ε) := by linarith
    have h2 : Real.exp u ^ 2 ≤ Real.exp (2 * Cw * ε) ^ 2 :=
      pow_le_pow_left₀ hEpos.le h4 2
    exact mul_le_mul h1 h2 (by positivity) (by linarith)
  have hC : 4 * Cw * ε * Real.exp (4 * Cw * ε) ≤ 4 * Cw * ε * Real.exp (4 * Cw) :=
    mul_le_mul_of_nonneg_left h5 (by linarith)
  calc 2 * (Real.exp u - 1) * Real.exp u
      ≤ 2 * u * Real.exp u ^ 2 := hA
    _ ≤ 2 * (2 * Cw * ε) * Real.exp (2 * Cw * ε) ^ 2 := hB
    _ = 4 * Cw * ε * Real.exp (4 * Cw * ε) := by rw [hsq]; ring
    _ ≤ 4 * Cw * ε * Real.exp (4 * Cw) := hC

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
