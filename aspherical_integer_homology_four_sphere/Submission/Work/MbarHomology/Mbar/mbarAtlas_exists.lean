import Mathlib
import Submission.Work.MbarHomology.Mbar.Assemble
import Submission.Work.MbarHomology.Mbar.AtlasBoundary
import Submission.Work.MbarHomology.CellAtlas.Defs
import Submission.Work.HomologyIso.Gen.Mbar
import Submission.Work.Subdivision.D_subdivCell
import Submission.Work.Subdivision.starLM_subdivCell
import Submission.Work.MbarHomology.Data.MbarOrbits

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.Mbar

/-- **The cell atlas of the barycentric subdivision of `M̄`** (work package W7 of
`Submission/Work/NOTES_LEAD_eA.md`): a `CellAtlas` over `K = mbarSd`, `P = QbarCW`,
`C = Gen.mbarCx`, together with its boundary compatibility.

Intended construction: `car σ` is the `M̄`-cell of the orbit `σ` (the class of the flag of `Q̄₀ ⊔ Q̄₁`
that `σ` lies over, read in `Gen.mbarCx`'s cell numbering — which is the numbering of
`rtdata/rt_complex.py`'s `build_complex(2)`, the same as `Gen.mbar`'s `mbarDim`/`mbarBd` order);
`root n e` is the root face of that cell in `Q̄`; `lift σ` is a representative flag ending at that
root face, so that `lift_bij` is the statement that the simplices of `mbarSd` with a given carrier
are exactly the flags over it (this uses "no face is glued to itself non-trivially", asserted by
`rt_complex.build_complex`).  `BoundaryCompat` is the comparison of `Gen.mbarBd` with the boundary
of `subdivCell QbarCW` read through `lift`, and is the place where the orientation bookkeeping
`oS` enters (`Qbar/QbarAct.lean`, `qAct_spec`); it should be discharged by `decide` on the `482`
columns, following `D_subdivCell` and the signed star action (see the design note §3 W7). -/
theorem mbarAtlas_exists : ∃ A : Work.MbarHomology.CellAtlas Work.MbarHomology.mbarSd Work.MbarHomology.QbarCW Work.HomologyIso.Gen.mbarCx, A.BoundaryCompat :=
  ⟨mbarAtlasOf, mbarBoundaryCompat⟩

end Work.MbarHomology.Mbar
