/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Submission.Work.FlowerGlue2.ChartMatch
import Submission.Work.FlowerGlue2.exists_attrCompare_flowerFix3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.AttrNorm` — N1: the attracting normalisation constant and the deepening

`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.3 (N1).  The flower's attracting coordinate
is the reference coordinate of `Work.FlowerGlue2.exists_refCoord_P` shifted by a constant `sa`
(the "phase").

## Main results

* `Work.FlowerGlue2.exists_attrCompare` — the bundle (for the flower of `ELAssembly`/`PARIMPL`);
* `Work.FlowerGlue2.attr_norm` — N1 in the form of the design note.

The companion `box_deep` of the design note is **not** included: as stated it is false for an
abstract `AttrCompare` — see `NOTES_FALSE_box_deep_attr2.md`, and §4 of
`NOTES_FALSE_mandelbar_implosion_N2.md`.
-/

open scoped Topology
open Filter Set Metric

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **N1 (bundle form).**  The attracting comparison datum of the flower `fl`, obtained by
combining the chart matching `Work.FlowerGlue2.exists_refCoord_P` with the Fatou-uniqueness
comparison `Work.FlowerGlue.ecalle_eq_ref_add_const`. -/
theorem exists_attrCompare (P : ParNormal d) (hτ : P.h c₀ 0 = 1)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) :
    Nonempty (AttrCompare P fl.Pa fl.φa) := by
  obtain ⟨Rf, N, K, hN, hK, hmem, hasymp⟩ := exists_refCoord_P P hτ
  exact exists_attrCompare_flowerFix3 P fl ⟨Rf, N, K, hN, hK, hmem, hasymp⟩

/-- **N1.**  There is a phase constant `sa` such that, on the part of the petal which is deeper
than `N` in the chart `w0`, the flower's coordinate differs from
`approxCoord (P.κ c₀) (w0 P ·) + sa` by `O(1/Re w0)`, and the reference petal covers the
half-plane there. -/
theorem attr_norm (P : ParNormal d) (hτ : P.h c₀ 0 = 1)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) :
    ∃ sa : ℂ, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      ∀ z ∈ fl.Pa, z ≠ d.z₁ → N < (w0 P z).re →
        (∃ Rf : Work.FlowerGlue.RefCoord d, z ∈ Rf.P) ∧
        ‖fl.φa z - (Work.FatouCoord.approxCoord (P.κ c₀) (w0 P z) + sa)‖
          ≤ K / (w0 P z).re := by
  obtain ⟨A⟩ := exists_attrCompare P hτ fl
  exact ⟨A.sa, A.N, A.K, A.N_pos, A.K_nonneg, fun z hz hzne hNz =>
    ⟨⟨A.Rf, A.mem_P z hzne hNz⟩, A.asymp z hz hzne hNz⟩⟩

end

end Work.FlowerGlue2
