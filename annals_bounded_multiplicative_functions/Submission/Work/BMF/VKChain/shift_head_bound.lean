import Mathlib
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.VKChain.shiftTerm_head_norm_sum
import Submission.Work.BMF.VKChain.head_rpow_sum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The head bound for the shift-difference series

`shift_head_bound` bounds the head `∑_{m < K₀}` of the shift-difference series
`∑_m ((m+a)^{-s} - (m+1)^{-s})` at `s = σ + i t`, uniformly in `t`, by
`a^{-σ} + 2 · (5 e⁴) · (2 + κ)`, under the hypothesis `K₀ ≤ e^κ + 2` together with
`(1 - σ) κ ≤ 1`.

The proof combines two estimates:

* `Work.BMF.VKChain.shiftTerm_head_norm_sum` (triangle inequality, termwise):
  `‖∑_{m < K₀} shiftTerm a m (σ + it)‖ ≤ a^{-σ} + 2 ∑_{1 ≤ m ≤ K₀} m^{-σ}`;
* `Work.BMF.VKChain.head_rpow_sum_bound` (the real-variable bookkeeping): the Riemann-type
  sum `∑_{1 ≤ m ≤ K₀} m^{-σ}` is at most `5 e⁴ (2 + κ)` in the range cut out by the hypothesis
  `K₀ ≤ e^κ + 2`, `(1 - σ) κ ≤ 1`.
-/

namespace Work.BMF.VKChain

theorem shift_head_bound {K₀ : ℕ} {a σ t κ : ℝ} (ha : 0 < a) (hσ0 : 0 < σ) (hσ2 : σ ≤ 2)
    (hκ0 : 0 ≤ κ) (hσκ : (1 - σ) * κ ≤ 1) (hK₀ : (K₀ : ℝ) ≤ Real.exp κ + 2) :
    ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      a ^ (-σ) + 2 * ((Real.exp 4 * 5) * (2 + κ)) := by
  have hred := shiftTerm_head_norm_sum (K₀ := K₀) (a := a) (σ := σ) (t := t) ha hσ0
  have hT := head_rpow_sum_bound (K₀ := K₀) hσ0 hσ2 hκ0 hσκ hK₀
  have h2 : 2 * (∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ))
      ≤ 2 * (5 * Real.exp 4 * (2 + κ)) :=
    mul_le_mul_of_nonneg_left hT (by norm_num)
  calc ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ a ^ (-σ) + 2 * ∑ m ∈ Finset.Icc 1 K₀, (m : ℝ) ^ (-σ) := hred
    _ ≤ a ^ (-σ) + 2 * (5 * Real.exp 4 * (2 + κ)) := by linarith
    _ = a ^ (-σ) + 2 * ((Real.exp 4 * 5) * (2 + κ)) := by ring

end Work.BMF.VKChain
