import Mathlib

namespace Work.Pert.pert2v2

/-- Elementary real-analytic bookkeeping.

With `A = Ξ' + 3 Λ + MK + 5 CW + 4` (so `A ≥ 197`), the hypothesis
`hΛlog : 32 CW (2 + log A) ≤ Λ` bounds `CW` in terms of the logarithm of the "small" scale,
while `hm` bounds `m` by the scale `Ξ' + 4Λ + MK + 5CW + 21 ≤ 2A`.  Since `log` is monotone and
`log (2A) = log 2 + log A ≤ 1 + log A`, we get
`1 + log (m+1) ≤ 2 (2 + log A)`, and the claim follows by multiplying by `CW ≥ 0`. -/
theorem log_linear_bound {Ξ' MK CW Λ : ℝ} {m : ℕ}
    (hΞ' : 1 ≤ Ξ') (hMK0 : 0 ≤ MK) (hCW : 0 ≤ CW) (hΛ16 : 64 ≤ Λ)
    (hΛlog : 32 * CW * (2 + Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4)) ≤ Λ)
    (hm : (m : ℝ) < Ξ' + 4 * Λ + MK + 5 * CW + 21) :
    CW * (1 + Real.log ((m : ℝ) + 1)) ≤ Λ / 16 := by
  set A : ℝ := Ξ' + 3 * Λ + MK + 5 * CW + 4 with hAdef
  -- `A` is large: `A ≥ 197`.
  have hA1 : 1 ≤ A := by rw [hAdef]; linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  -- the "large" scale `B` is at most `2 A`
  have hB2A : Ξ' + 4 * Λ + MK + 5 * CW + 22 ≤ 2 * A := by
    rw [hAdef]; linarith
  have hBpos : 0 < Ξ' + 4 * Λ + MK + 5 * CW + 22 := by linarith
  -- `m + 1 < B`
  have hm1 : (m : ℝ) + 1 < Ξ' + 4 * Λ + MK + 5 * CW + 22 := by linarith
  -- monotonicity of `log`
  have hlog1 : Real.log ((m : ℝ) + 1)
      ≤ Real.log (Ξ' + 4 * Λ + MK + 5 * CW + 22) :=
    Real.log_le_log (by positivity) (le_of_lt hm1)
  have hlog2 : Real.log (Ξ' + 4 * Λ + MK + 5 * CW + 22) ≤ Real.log A + 1 := by
    have hle : Real.log (Ξ' + 4 * Λ + MK + 5 * CW + 22) ≤ Real.log (2 * A) :=
      Real.log_le_log hBpos hB2A
    have hmul : Real.log (2 * A) = Real.log 2 + Real.log A :=
      Real.log_mul (by norm_num) (by positivity)
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  -- main elementary inequality
  have hstep : 1 + Real.log ((m : ℝ) + 1) ≤ 2 * (2 + Real.log A) := by linarith
  -- the linear bound coming from `hΛlog`
  have hfin : 2 * (CW * (2 + Real.log A)) ≤ Λ / 16 := by linarith
  calc CW * (1 + Real.log ((m : ℝ) + 1))
      ≤ CW * (2 * (2 + Real.log A)) := mul_le_mul_of_nonneg_left hstep hCW
    _ = 2 * (CW * (2 + Real.log A)) := by ring
    _ ≤ Λ / 16 := hfin

end Work.Pert.pert2v2
