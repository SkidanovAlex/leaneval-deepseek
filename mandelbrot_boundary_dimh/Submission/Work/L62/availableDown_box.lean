import Mathlib
import Submission.Work.L62.l62c_end

namespace Work.L62

open Set Filter Topology Complex
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- **The available box `{0 ≤ Re β ≤ 1, |Im β| ≤ b} ∩ AvailableDown` is compact.**  Used in `Work.L62.lowCyl_family` for the joint-continuity argument: the parameter set over which the lower-end cylinder family is required to be jointly continuous is compact.  (`{β | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b}` is closed and bounded in `ℂ`, and `{β | Work.L62.AvailableDown d hd β}` is closed by `Work.L62.isClosed_availableDown`.) -/
theorem availableDown_box {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} :
    IsCompact ({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | Work.L62.AvailableDown d hd β}) := by
  -- the box is closed: it is cut out by three closed conditions on the continuous
  -- coordinate functions `re`, `re` and `|· ∘ im|`
  have hbox : IsClosed ({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b}) := by
    have hA : IsClosed {β : ℂ | (0 : ℝ) ≤ β.re} :=
      isClosed_le continuous_const Complex.continuous_re
    have hB : IsClosed {β : ℂ | β.re ≤ 1} :=
      isClosed_le Complex.continuous_re continuous_const
    have hC : IsClosed {β : ℂ | |β.im| ≤ b} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have hset : ({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b})
        = {β : ℂ | 0 ≤ β.re} ∩ {β : ℂ | β.re ≤ 1} ∩ {β : ℂ | |β.im| ≤ b} := by
      ext β; simp [and_assoc]
    rw [hset]
    exact (hA.inter hB).inter hC
  -- the whole set is closed
  have hclosed : IsClosed ({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | Work.L62.AvailableDown d hd β}) :=
    hbox.inter (isClosed_availableDown d hd)
  -- and it is bounded, being contained in a closed ball
  have hbound : ({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | Work.L62.AvailableDown d hd β}) ⊆ Metric.closedBall 0 (|b| + 1) := by
    rintro β ⟨⟨h0, h1, h2⟩, -⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖β‖ ≤ |β.re| + |β.im| := Complex.norm_le_abs_re_add_abs_im β
    have hre : |β.re| = β.re := abs_of_nonneg h0
    have him : |β.im| ≤ |b| := le_trans h2 (le_abs_self b)
    rw [hre] at hnorm
    linarith
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 (|b| + 1)) hclosed hbound

end

end Work.L62
