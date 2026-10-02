/-
# `ELAssembly` — the landing points of the three arm pairs are pairwise distinct

`Work.ELTop.tripodArms_disjoint` (T8) says the three arms of a tripod are pairwise disjoint.  The
cut points of the three arm pairs of the nest at `b₂` lie in the three arms
(`CertGeometry.cutA_mem`/`cutB_mem`/`cutC_mem`), so they are pairwise distinct — the
`inj` content of `PolyAdmissible` for the three-pair list, which `D_adm_of` consumes.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELTop.tripodArms_disjoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

/-- **The three cut points are pairwise distinct.** -/
theorem tripod_cut_ne {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (T : Work.EL.Tripod hN) {yA yB yC : ℂ}
    (hA : yA ∈ Work.EL.Tripod.armA T) (hB : yB ∈ Work.EL.Tripod.armB T)
    (hC : yC ∈ Work.EL.Tripod.armC T) :
    yA ≠ yB ∧ yB ≠ yC ∧ yC ≠ yA := by
  have h1 := Work.ELTop.tripodArms_disjoint hN hJ T
  refine ⟨fun h => Set.disjoint_left.mp h1.1 hA (h ▸ hB),
    fun h => Set.disjoint_left.mp h1.2.1 hB (h ▸ hC),
    fun h => Set.disjoint_left.mp h1.2.2 hC (h ▸ hA)⟩

end Work.ELAssembly
