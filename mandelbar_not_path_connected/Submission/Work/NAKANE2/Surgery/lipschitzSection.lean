import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.Surgery.surgeryData_exists
import Submission.Work.NAKANE2.Surgery.phi_after_surgery

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

/-- Route: `surgeryData_exists` supplies `D : SurgeryData c₀`; take `r = rConst D` and
`K = Kconst D` (`rConst_pos`) and apply `phi_after_surgery`. -/
theorem lipschitzSection {c₀ : ℂ} (hc₀ : c₀ ∉ Work.NAKANE2.Mb) :
    ∃ r K : ℝ, 0 < r ∧ ∀ v : ℂ, ‖v‖ < r → ∃ c : ℂ, c ∉ Work.NAKANE2.Mb ∧
      Work.NAKANE2.Phi c = Work.Bottcher.varphiCrit c₀ (c₀ + v) ∧ ‖c - c₀‖ ≤ K * ‖v‖ := by
  obtain ⟨D⟩ := surgeryData_exists hc₀
  exact ⟨rConst D, Kconst D, rConst_pos D, fun v hv => phi_after_surgery D hv⟩

end Work.NAKANE2.Surgery
