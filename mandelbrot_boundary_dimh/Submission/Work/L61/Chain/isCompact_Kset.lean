import Submission.Work.L61.Basic

/-! `Kset` is compact: it is `{0}` together with the critical orbit, which converges to `0`. -/

namespace Work.L61

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

theorem isCompact_Kset {d : ParabData f₀ D₀} (hd : HornData d) : IsCompact (Kset d hd) := by
  have hseq : Tendsto (fun n : ℕ => (g d)^[n] (critVal hd)) atTop (𝓝 (0 : ℂ)) := hd.crit_orbit.2
  have heq : Kset d hd = insert 0 (Set.range fun n : ℕ => (g d)^[n] (critVal hd)) := rfl
  rw [heq]
  exact hseq.isCompact_insert_range

end

end Work.L61
