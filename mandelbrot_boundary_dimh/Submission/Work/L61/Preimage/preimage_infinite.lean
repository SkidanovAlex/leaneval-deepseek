import Submission.Work.L61.Basic

/-! A point outside `gdom` has infinitely many preimages in `gdom` under `g`. -/

namespace Work.L61

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

theorem preimage_infinite {d : ParabData f₀ D₀} (hd : HornData d) {w₀ : ℂ}
    (hw₀ : w₀ ∉ gdom d hd) : {ζ : ℂ | ζ ∈ gdom d hd ∧ g d ζ = w₀}.Infinite := by
  have hw0 : w₀ ≠ 0 := by
    intro h
    exact hw₀ (h ▸ Set.mem_insert_iff.mpr (Or.inl rfl))
  set w : ℂ := Complex.log w₀ / (2 * Real.pi * Complex.I) with hw
  have hπ : piExp w = w₀ := piExp_log_div w₀ hw0
  have hinf := hd.inf_u w
  refine hinf.mono ?_
  rintro ζ ⟨w', ⟨hw'Bu, hw'E⟩, rfl⟩
  have hunion : w' ∈ hd.Bu ∪ hd.Bl := Or.inl hw'Bu
  refine ⟨Set.mem_insert_iff.mpr (Or.inr ⟨w', hunion, rfl⟩), ?_⟩
  rw [g_piExp d hd hunion, hw'E, hπ]

end

end Work.L61
