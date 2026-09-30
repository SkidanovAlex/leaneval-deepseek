import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric lower bound for the exponential:
`exp (-0.536) ≥ 0.5847`.

Proof: the truncated exponential series of order `5` at `x = -0.536` equals
`S = ∑_{m<5} x^m/m! = 0.585422015...`, and the standard tail bound
`Real.exp_bound` (valid since `|x| ≤ 1`) gives
`|exp x - S| ≤ |x|^5 * (6/(5! * 5)) = 0.0004424089...`.
Hence `exp x ≥ S - 0.000442409 = 0.58497960... > 0.5847`. -/
theorem exp_neg_536_ge_05847 : (0.5847 : ℝ) ≤ Real.exp (-0.536) := by
  have hx : |(-0.536 : ℝ)| ≤ 1 := by norm_num
  have h := Real.exp_bound (x := (-0.536 : ℝ)) hx (n := 5) (by norm_num)
  rw [abs_sub_le_iff] at h
  have hval : (0.5847 : ℝ) ≤ (∑ m ∈ Finset.range 5, (-0.536:ℝ)^m / m.factorial)
      - |(-0.536:ℝ)|^5 * ((Nat.succ 5 : ℝ) / ((5:ℕ).factorial * 5)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith [h.2]

end Work.BW
