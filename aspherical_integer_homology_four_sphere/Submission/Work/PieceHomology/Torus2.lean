/-
# `PieceHomology/`: the standard `Δ`-structure of the `2`-torus, and the torus computation modulo
Hatcher 2.27

The minimal `Δ`-structure of the torus — one vertex, three loops and two triangles, all of whose
faces are identified (the `θ`-graph on `T²` cut open) — is the combinatorial model of
`T² = (ℝ/ℤ)²` used for the cusp computations.  It is built in this area by the delegated modules
`Work.PieceHomology.torus2Data` (`torus2DeltaCx`, with `card = (1,3,2)`; the matrix presentation
`torus2Cx`; the strong-deformation-retract certificate `torus2SDR` with
`torus2SDR_check : torus2SDR.check = true`; the ranks `torus2B = rankT2`) and
`Work.PieceHomology.exists_torus2DeltaCx` (the existence statement, and the chain isomorphism
`torus2ChainIsoAlt : torus2DeltaCx.chain ≅ torus2Cx.toChainComplex`).

This file is the *integration* of that data with the interface of this area: it produces

```
torus2DeltaModel R : DeltaModel (TopCat.of ((ℝ/ℤ)²)) rankT2
eT2_torus2 R       : ModelT2 (k:ℤ) ≅ H_k((ℝ/ℤ)²; ℤ)
```

**modulo exactly one input, which is not yet available**:

* a realization `R : DeltaRealization torus2DeltaCx (TopCat.of ((ℝ/ℤ)²))` — the point-set data of
  the `Δ`-structure (its `χ` maps on the five simplices: the three loops and the two triangles of
  the `θ`-decomposition), which is the geometric half of the area `DeltaHomology`/`G0`.

The second formerly-missing input, the Hatcher 2.27 quasi-isomorphism of the comparison chain map,
is now *delivered* (`Work.DeltaHomology.deltaChainMap_quasiIso`, proved) and is discharged here by
`DeltaModel.ofSDRHatcher`.
-/
import Submission.Work.PieceHomology.Basic
import Submission.Work.PieceHomology.torus2Data
import Submission.Work.PieceHomology.exists_torus2DeltaCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open LeanEval.Topology
open scoped Topology

namespace Work.PieceHomology

noncomputable section

/-- The torus `T² = (ℝ/ℤ)²` as a topological space. -/
abbrev Torus2Space : TopCat := TopCat.of (Fin 2 → AddCircle (1 : ℝ))

/-- **The `Δ`-model of the torus** from a realization of the standard `Δ`-structure
`Work.PieceHomology.torus2DeltaCx`.  The certificate `torus2SDR` and the chain isomorphism
`torus2ChainIsoAlt` supply the homology computation and the Hatcher 2.27 quasi-isomorphism is the
proved `Work.DeltaHomology.deltaChainMap_quasiIso`: the *only* input is the realization. -/
def torus2DeltaModel (R : Work.DeltaHomology.DeltaRealization torus2DeltaCx Torus2Space) :
    DeltaModel Torus2Space Work.HomologyIso.rankT2 :=
  DeltaModel.ofSDRHatcher R torus2Cx torus2SDR torus2SDR_check ExistsTorus2.torus2ChainIsoAlt.symm
    Work.HomologyIso.rankT2 torus2B_eq_rankT2

/-- **The torus computation in the declared type of the per-cusp field `eT2`**
(`Work.HomologyIso.CuspData.eT2`): unconditional in the realization of the standard `Δ`-structure
of `T²`. -/
def eT2_torus2 (R : Work.DeltaHomology.DeltaRealization torus2DeltaCx Torus2Space) (k : ℕ) :
    Work.HomologyIso.ModelT2 (k : ℤ) ≅ LeanEval.Topology.intHomology k Torus2Space :=
  (torus2DeltaModel R).iso k

end

end Work.PieceHomology
