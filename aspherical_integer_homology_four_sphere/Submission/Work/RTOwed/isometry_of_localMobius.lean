import Mathlib
import Submission.Work.HypModel.mobius_isometry
import Submission.Work.RTInstance.Models
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.RTOwed

theorem isometry_of_localMobius {w : Work.Cusp.E4 → Work.Cusp.E4} {T : Set Work.Cusp.E4} {δ : ℝ}
    (hδ : 0 < δ) (hT : ∀ z ∈ T, δ ≤ w z 3) (hT' : ∀ z ∈ T, δ ≤ z 3)
    (h : ∀ z ∈ T, ∃ (V : Set Work.Cusp.E4) (B : Matrix (Fin 5) (Fin 5) ℝ),
      IsOpen V ∧ z ∈ V ∧ Work.HypModel.IsLorentzMat B ∧
      ∀ z' ∈ V, w z' = Work.HypModel.mobius B z') :
    ∀ z ∈ T, ∀ u v : Work.Cusp.E4,
      Work.RTInstance.uhsModel δ (w z) (fderiv ℝ w z u) (fderiv ℝ w z v)
        = Work.RTInstance.uhsModel δ z u v := by
  intro z hz u v
  obtain ⟨V, B, hVopen, hzV, hB, hw⟩ := h z hz
  have hzeq : w =ᶠ[𝓝 z] Work.HypModel.mobius B :=
    Filter.mem_of_superset (hVopen.mem_nhds hzV) (fun x hx => hw x hx)
  have hfd : fderiv ℝ w z = fderiv ℝ (Work.HypModel.mobius B) z := hzeq.fderiv_eq
  have hz3 : 0 < z 3 := lt_of_lt_of_le hδ (hT' z hz)
  have hw3 : δ ≤ Work.HypModel.mobius B z 3 := by rw [← hw z hzV]; exact hT z hz
  rw [hfd, hw z hzV]
  rw [Work.RTInstance.uhsModel_eq_uhsMetric hδ hw3,
      Work.RTInstance.uhsModel_eq_uhsMetric hδ (hT' z hz)]
  exact Work.HypModel.mobius_isometry hB hz3 u v

end Work.RTOwed
