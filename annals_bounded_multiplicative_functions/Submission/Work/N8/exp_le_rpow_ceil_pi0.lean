import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Quantitative comparison: for `0 < c`, `4 ≤ x ≤ P` one has
`exp (c/2 * x) ≤ (P/2) ^ ⌈c * π₀(P)⌉₊`.

The point is that while the exponential on the left grows in `x`, the power on
the right grows in the *number* of primes up to `P` (roughly `P / log P`), with
base `P / 2 ≥ 2`: since `P ≥ 4` we have `log P ≤ 2 log (P/2)`, i.e.
`log (P/2) ≥ (1/2) log P`, so
`log (P/2) * c * π₀(P) ≥ (1/2) log P * c * P / log P = c P / 2 ≥ c x / 2`. -/
theorem exp_le_rpow_ceil_pi0 (c x P : ℝ) (hc : 0 < c) (hx : 4 ≤ x) (hP : x ≤ P) :
    Real.exp (c / 2 * x) ≤ (P / 2) ^ ⌈c * Work.BMF.pi0 P⌉₊ := by
  have hP4 : (4 : ℝ) ≤ P := le_trans hx hP
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hpi0pos : 0 < Work.BMF.pi0 P := by
    unfold Work.BMF.pi0; exact div_pos hPpos hlogP
  have hbase1 : (1 : ℝ) ≤ P / 2 := by linarith
  have hbasepos : 0 < P / 2 := by linarith
  -- the ceiling is at least the real exponent
  have hexp_le : c * Work.BMF.pi0 P ≤ (⌈c * Work.BMF.pi0 P⌉₊ : ℝ) := Nat.le_ceil _
  have hstep1 : (P / 2) ^ (c * Work.BMF.pi0 P) ≤ (P / 2) ^ ⌈c * Work.BMF.pi0 P⌉₊ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase1 hexp_le
  -- `log (P/2) ≥ (1/2) log P`
  have hsquares : P ≤ (P / 2) ^ 2 := by nlinarith
  have hloghalf : Real.log P ≤ 2 * Real.log (P / 2) := by
    calc Real.log P ≤ Real.log ((P / 2) ^ 2) := Real.log_le_log hPpos hsquares
      _ = 2 * Real.log (P / 2) := by rw [Real.log_pow]; push_cast; ring
  -- the exponent comparison
  have hstepB : c / 2 * P ≤ Real.log (P / 2) * (c * Work.BMF.pi0 P) := by
    have h1 : Real.log P / 2 ≤ Real.log (P / 2) := by linarith
    have h2 : 0 ≤ c * Work.BMF.pi0 P := le_of_lt (mul_pos hc hpi0pos)
    calc c / 2 * P = (Real.log P / 2) * (c * Work.BMF.pi0 P) := by
          unfold Work.BMF.pi0; field_simp [hlogP.ne']
      _ ≤ Real.log (P / 2) * (c * Work.BMF.pi0 P) := mul_le_mul_of_nonneg_right h1 h2
  have hstepA : c / 2 * x ≤ c / 2 * P := mul_le_mul_of_nonneg_left hP (by linarith)
  have hkey : c / 2 * x ≤ Real.log (P / 2) * (c * Work.BMF.pi0 P) := le_trans hstepA hstepB
  calc Real.exp (c / 2 * x) ≤ Real.exp (Real.log (P / 2) * (c * Work.BMF.pi0 P)) :=
        Real.exp_le_exp.mpr hkey
    _ = (P / 2) ^ (c * Work.BMF.pi0 P) := (Real.rpow_def_of_pos hbasepos _).symm
    _ ≤ (P / 2) ^ ⌈c * Work.BMF.pi0 P⌉₊ := hstep1

end Work.N8
