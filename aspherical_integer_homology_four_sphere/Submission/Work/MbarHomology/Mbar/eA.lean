/-
# `eA = H_*(M̄)`: the last homology input of the challenge theorem

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`, the deliverable of the area
`Work.MbarHomology`.

```lean
Work.MbarHomology.eA (k : ℕ) : Work.HomologyIso.ModelA (k : ℤ) ≅
    LeanEval.Topology.intHomology k (TopCat.of Work.FoldInst.Mbar)
```

is exactly the `hmbar` argument of `Work.PieceHomology.cuspData_of_concrete`
(`Work.RTInstance.assemblyOf` sets `Mbar := Work.FoldInst.Mbar`).

Everything except the atlas data (work package W7: `Mbar.mbarAtlas_exists`) is proved:
`Mbar.eA_of_atlas` assembles
* `CellAtlas.zMap_quasiIso` (W6, the cellular comparison),
* `Work.HomologyIso.Gen.mbarCx_homology_modelA` (the generated homology of `Gen.mbarCx`),
* `Work.PieceHomology.DeltaModel.ofHatcher mbarReal` (Hatcher 2.27),
given the local sphericality of `QbarCW`, which follows from
`Work.MbarHomology.Local.locallySpherical_of_closed` and the `865` certificates
`Work.MbarHomology.Qbar.QbarCW_cellAcyclic`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.Assemble
import Submission.Work.MbarHomology.Mbar.eA_of_atlas
import Submission.Work.MbarHomology.Local.locallySpherical_of_closed
import Submission.Work.MbarHomology.Qbar.QbarCW_cellAcyclic
import Submission.Work.MbarHomology.Qbar.QbarCW_hasDdZero
import Submission.Work.MbarHomology.Qbar.QbarCW_hasAugZero
import Submission.Work.MbarHomology.Mbar.mbarAtlas_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

/-- The local sphericality of the face poset of `Q̄`, from the closed-cell certificates. -/
theorem QbarCW_locallySpherical :
    QbarCW.LocallySpherical Qbar.QbarCW_hasDdZero Qbar.QbarCW_hasAugZero :=
  Local.locallySpherical_of_closed QbarCW Qbar.QbarCW_hasDdZero Qbar.QbarCW_hasAugZero
    (Qbar.QbarCW_cellAcyclic Qbar.QbarCW_hasDdZero)

/-- **`eA` from an atlas**: the identification of the model `ℤ^{rankA k}` with the singular homology
of `M̄`, given a cell atlas of the barycentric subdivision of `M̄` with its boundary compatibility
(`Mbar.mbarAtlas_exists` is the existence statement). -/
def eAOf (A : CellAtlas mbarSd QbarCW Work.HomologyIso.Gen.mbarCx) (h : A.BoundaryCompat)
    (k : ℕ) : Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of Work.FoldInst.Mbar) :=
  Classical.choice (Mbar.eA_of_atlas A Qbar.QbarCW_hasDdZero Qbar.QbarCW_hasAugZero
    QbarCW_locallySpherical h k)

/-! ### The atlas and the final identification -/

/-- **The cell atlas of the barycentric subdivision of `M̄`** (work package W7): the `Δ`-complex
`mbarSd` organised by the cells of `Gen.mbarCx`, with regular local models in the face poset
`QbarCW` of `Q̄`. -/
noncomputable def mbarAtlas :
    CellAtlas mbarSd QbarCW Work.HomologyIso.Gen.mbarCx :=
  Classical.choose Mbar.mbarAtlas_exists

/-- The boundary compatibility of the atlas, checked against `Gen.mbarBd`. -/
theorem mbarAtlas_boundaryCompat : (mbarAtlas).BoundaryCompat :=
  Classical.choose_spec Mbar.mbarAtlas_exists

/-- **The last homology input of the challenge theorem**: `H_k(M̄) ≅ ℤ^{rankA k}`, i.e. the `hmbar`
argument of `Work.PieceHomology.cuspData_of_concrete`. -/
def eA (k : ℕ) : Work.HomologyIso.ModelA (k : ℤ) ≅
    LeanEval.Topology.intHomology k (TopCat.of Work.FoldInst.Mbar) :=
  eAOf mbarAtlas mbarAtlas_boundaryCompat k

end

end Work.MbarHomology
