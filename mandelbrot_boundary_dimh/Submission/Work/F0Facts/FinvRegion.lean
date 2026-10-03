/-
Support material for `Work.F0Facts.finv_iterate_tendsto`.

The backward branch `finv w = (-1 + sqrt (1 + 4w))/2` of `f₀(z) = z + z²` contracts on the
"repelling region" `repelling = {w | 2 ≤ ‖1 + 4w‖ + re (1 + 4w)}` — equivalently the region where
`re (sqrt (1 + 4w)) ≥ 1` — and leaves it invariant.  The backward orbit of `ω = (-1+√3i)/2`
starts in this region, hence converges to `0`.
-/
import Mathlib
import Submission.Work.F0Facts.Basic

namespace Work.F0Facts

open Filter Topology Set Metric
open scoped Topology

noncomputable section

/-- `s w = sqrt (1 + 4w)`, the square root appearing in the inverse branch `finv`. -/
def sqroot (w : ℂ) : ℂ := Complex.sqrt (1 + 4 * w)

/-- The repelling region: the set of `w` with `2 ≤ ‖1 + 4w‖ + (1 + 4w).re`. -/
def repelling : Set ℂ := {w : ℂ | 2 ≤ ‖1 + 4 * w‖ + (1 + 4 * w).re}

lemma re_sqroot (w : ℂ) :
    (sqroot w).re = Real.sqrt ((‖1 + 4 * w‖ + (1 + 4 * w).re) / 2) := by
  rw [sqroot, Complex.sqrt_eq_real_add_ite]
  split_ifs <;>
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma one_le_re_sqroot_of_mem {w : ℂ} (hw : w ∈ repelling) : 1 ≤ (sqroot w).re := by
  have hw' : 2 ≤ ‖1 + 4 * w‖ + (1 + 4 * w).re := hw
  rw [re_sqroot, Real.le_sqrt' (by norm_num : (0:ℝ) < 1)]
  linarith

lemma isClosed_repelling : IsClosed repelling := by
  unfold repelling
  exact isClosed_le continuous_const (by fun_prop)

end

end Work.F0Facts
