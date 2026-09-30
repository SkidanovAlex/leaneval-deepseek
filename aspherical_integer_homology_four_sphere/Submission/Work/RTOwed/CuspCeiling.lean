/-
# The ceiling data of the five cusps: the missing inhabitant for `GlueHomeo`

`Work.RTInstance.GlueHomeo` is the `τ_v` homeomorphism `Work.FoldInst.Tset ≃ₜ ∂(⊔_v [-1,1]² × T_v)`
(items 4 of the contract).  Everything *below* it in the area `Cusp` is stated for an inhabitant of
`Work.Cusp.CuspGlueData`, which does not exist yet: the cusp chart `mbarLow : E4 → M̄` of the
hyperbolic piece and the ceiling map `mbarPt : E3 → M̄`, with their properties.

This file isolates the part of that datum which the gluing itself needs — the **ceiling maps** — as
one small structure, and (in `CuspCeilingGlue`) proves that it yields `GlueHomeo`.  The remaining
part (`mbarLow`, needed for the filling charts of item 2) is recorded in the area notes §2.1.

The intended inhabitant, for the concrete `M̄` of the area `FoldInst`:

* `mbarPt v x` — the point of the `v`-th truncation torus whose upper half space cusp coordinates are
  `x`; the five truncation tori are the images of the truncation facets `Work.FoldInst.Xtrunc`
  (`{truncSlack w = 0}`) grouped by the five cusps of the truncated 24-cell `Q̄`;
* `tauHomeo v` — the coordinate form of `τ_v`: the cusp torus `ℝ³/Λ_v` (`Work.Cusp.CuspTorus`,
  `Λ_v = ℤσ_v ⊕ ℤλ₂ ⊕ ℤλ₃`, the data of `rtdata/data/uhs_cusp_data.json`) is the range of `mbarPt v`
  (this is `Work.Cusp.exists_tauHomeoMbar` for a given `CuspGlueData`);
* `tset_eq`, `disjoint` — the truncation set is the disjoint union of the five ceiling maps.
-/
import Mathlib
import Submission.Work.FoldInst.Quotient
import Submission.Work.Cusp.exists_tauHomeoMbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

/-- **The ceiling data of the five cusps of `M̄`.**  For each cusp `v` a map `mbarPt v` from the
upper half space cusp coordinates `E3` to `M̄` whose range is the `v`-th truncation torus — with the
cusp-lattice coordinate of `tauHomeo` — and whose five ranges are disjoint and cover `Tset`. -/
structure CuspCeilingData where
  /-- The ceiling map of the `v`-th cusp. -/
  mbarPt : Work.Space.Cusp → Work.Cusp.E3 → Work.FoldInst.Mbar
  /-- The truncation torus is the range of the ceiling map, with the cusp-lattice coordinate
  (the coordinate form of `τ_v : ℝ³/Λ_v ≃ₜ T_v`). -/
  tauHomeo : ∀ v : Work.Space.Cusp, Work.Cusp.CuspTorus v ≃ₜ Set.range (mbarPt v)
  /-- **The truncation set is the union of the five ceiling maps.** -/
  tset_eq : Work.FoldInst.Tset = ⋃ v : Work.Space.Cusp, Set.range (mbarPt v)
  /-- The five ceiling maps have pairwise disjoint ranges. -/
  disjoint : ∀ v v' : Work.Space.Cusp, v ≠ v' →
    Disjoint (Set.range (mbarPt v)) (Set.range (mbarPt v'))

end Work.RTOwed
