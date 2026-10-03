import Submission.Work.L61.Basic

/-! Off the critical values `v + ℤ`, the lifted horn map `E` has nonzero derivative. -/

namespace Work.L61

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

theorem E_deriv_ne_zero {d : ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) (h : ∀ k : ℤ, d.E w ≠ hd.v + k) : deriv d.E w ≠ 0 := by
  intro hc
  obtain ⟨k, hk⟩ := hd.crit w hw hc
  exact h k hk

end

end Work.L61
