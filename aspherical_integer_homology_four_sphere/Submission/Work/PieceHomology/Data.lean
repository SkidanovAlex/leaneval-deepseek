/-
# `PieceHomology/`: the homology computations of the pieces, in the per-cusp form

This file packages the three computations of `Work.HomologyIso.CuspData` — the cusp cross-sections
`∂[-1,1]² × T²_v`, the hyperbolic piece `M̄`, and the filling tori `T²_v` — as finite-complex
models (`Work.PieceHomology.HomModel`, or the `Δ`-complex form `DeltaModel`), and converts them
into the *declared* fields of `Work.HomologyIso.CuspData` (respectively of
`Work.HomologyIso.PieceData`, for the non-refined form).

## What a provider supplies

* `Work.PieceHomology.CuspModels` — one `HomModel` per cusp (`rankT`), one for `M̄` (`rankA`), one
  per filling torus (`rankT2`); `toCuspData` produces `Work.HomologyIso.CuspData`;
* `Work.PieceHomology.DeltaCuspModels` — the same with `Δ`-complex models (`DeltaModel`), which is
  the form in which the geometry (a `Δ`-complex realized in the space, with the quasi-isomorphism
  of Hatcher 2.27 and an `SDR` certificate for its chain complex) is naturally produced;
* `Work.PieceHomology.PieceModels` / `DeltaPieceModels` — the *unrefined* form, giving
  `Work.HomologyIso.PieceData` directly from the models of `A ∩ B`, `A` and `B`.
-/
import Submission.Work.PieceHomology.Basic

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

variable [rt : Work.Space.RTData]

/-! ## §1  The per-cusp models -/

/-- **The per-cusp homology computations**, as finite-complex models:

* `torus v` — `H_k(∂[-1,1]² × T²_v) ≅ ℤ^{rankT k}` (one cusp cross-section `T³` per cusp);
* `mbar` — `H_k(M̄) ≅ ℤ^{rankA k}`;
* `t2 v` — `H_k(T²_v) ≅ ℤ^{rankT2 k}` (one filling torus per cusp).

These are exactly the fields of `Work.HomologyIso.CuspData`, up to the conversion
`HomModel.iso` of a model to the identification `ℤ^{r k} ≅ H_k(X)`. -/
structure CuspModels where
  /-- `H_k(∂[-1,1]² × T²_v) ≅ ℤ^{rankT k}` for each of the five cusps. -/
  torus : ∀ v : Work.Space.Cusp,
    HomModel (TopCat.of (Work.HomologyIso.BdryPt × rt.core.Torus v)) Work.HomologyIso.rankT
  /-- `H_k(M̄) ≅ ℤ^{rankA k}`. -/
  mbar : HomModel (TopCat.of rt.core.Mbar) Work.HomologyIso.rankA
  /-- `H_k(T²_v) ≅ ℤ^{rankT2 k}` for each of the five cusps. -/
  t2 : ∀ v : Work.Space.Cusp,
    HomModel (TopCat.of (rt.core.Torus v)) Work.HomologyIso.rankT2

/-- **The per-cusp models, as the declared fields of `Work.HomologyIso.CuspData`.** -/
def CuspModels.toCuspData (D : CuspModels (rt := rt)) :
    Work.HomologyIso.CuspData (rt := rt) where
  eTorus := fun v k => D.torus v |>.iso k
  eA := fun k => D.mbar.iso k
  eT2 := fun v k => D.t2 v |>.iso k

/-- **The per-cusp `Δ`-complex models**: the same three computations, each produced by a finite
`Δ`-complex realized in the space, with its comparison chain map a quasi-isomorphism and its
homology computed (`DeltaModel`).

This is the form of the geometric computation: the provider gives, per cusp, the `Δ`-structure
(combinatorial: simplex counts and face maps), its realization in the space
(`Work.DeltaHomology.DeltaRealization`), and the `SDR` certificate of the chain complex. -/
structure DeltaCuspModels where
  /-- The `Δ`-complex model of the cusp cross-section `∂[-1,1]² × T²_v`. -/
  torus : ∀ v : Work.Space.Cusp,
    DeltaModel (TopCat.of (Work.HomologyIso.BdryPt × rt.core.Torus v)) Work.HomologyIso.rankT
  /-- The `Δ`-complex model of `M̄`. -/
  mbar : DeltaModel (TopCat.of rt.core.Mbar) Work.HomologyIso.rankA
  /-- The `Δ`-complex model of the filling torus `T²_v`. -/
  t2 : ∀ v : Work.Space.Cusp,
    DeltaModel (TopCat.of (rt.core.Torus v)) Work.HomologyIso.rankT2

/-- **A `Δ`-model is a model**: the conversion of the `Δ`-complex form to the chain-complex form. -/
def DeltaCuspModels.toCuspModels (D : DeltaCuspModels (rt := rt)) : CuspModels (rt := rt) where
  torus := fun v => (D.torus v).toHomModel
  mbar := D.mbar.toHomModel
  t2 := fun v => (D.t2 v).toHomModel

/-- **The per-cusp `Δ`-models, as the declared fields of `Work.HomologyIso.CuspData`.** -/
def DeltaCuspModels.toCuspData (D : DeltaCuspModels (rt := rt)) :
    Work.HomologyIso.CuspData (rt := rt) :=
  D.toCuspModels.toCuspData

/-! ## §2  The unrefined (per-piece) models -/

/-- **The three homology computations of the pieces of the cover**, in the unrefined form:

* `inter` — `H_k(A ∩ B) ≅ ℤ^{rankM k}`;
* `a` — `H_k(A) ≅ ℤ^{rankA k}`;
* `b` — `H_k(B) ≅ ℤ^{rankB k}`.

These are the fields of `Work.HomologyIso.PieceData`.  The per-cusp form `CuspModels` is the one
in which the Ratcliffe–Tschantz data is organised; this form is the fallback for a provider that
computes the pieces directly (e.g. from a cell structure on the whole collar `A ∩ B`). -/
structure PieceModels where
  /-- `H_k(A ∩ B) ≅ ℤ^{rankM k}`. -/
  inter : HomModel (TopCat.of ↥(Work.HomologyIso.Aset (rt := rt)
    ∩ Work.HomologyIso.Bset (rt := rt))) Work.HomologyMV.rankM
  /-- `H_k(A) ≅ ℤ^{rankA k}`. -/
  a : HomModel (TopCat.of ↥(Work.HomologyIso.Aset (rt := rt))) Work.HomologyIso.rankA
  /-- `H_k(B) ≅ ℤ^{rankB k}`. -/
  b : HomModel (TopCat.of ↥(Work.HomologyIso.Bset (rt := rt))) Work.HomologyIso.rankB

/-- **The per-piece models, as the declared fields of `Work.HomologyIso.PieceData`.** -/
def PieceModels.toPieceData (D : PieceModels (rt := rt)) :
    Work.HomologyIso.PieceData (rt := rt) where
  eAB := fun k => D.inter.iso k
  eA := fun k => D.a.iso k
  eB := fun k => D.b.iso k

/-- **The per-piece `Δ`-complex models.** -/
structure DeltaPieceModels where
  /-- The `Δ`-complex model of the collar `A ∩ B`. -/
  inter : DeltaModel (TopCat.of ↥(Work.HomologyIso.Aset (rt := rt)
    ∩ Work.HomologyIso.Bset (rt := rt))) Work.HomologyMV.rankM
  /-- The `Δ`-complex model of `A`. -/
  a : DeltaModel (TopCat.of ↥(Work.HomologyIso.Aset (rt := rt))) Work.HomologyIso.rankA
  /-- The `Δ`-complex model of `B`. -/
  b : DeltaModel (TopCat.of ↥(Work.HomologyIso.Bset (rt := rt))) Work.HomologyIso.rankB

/-- A `Δ`-model is a model. -/
def DeltaPieceModels.toPieceModels (D : DeltaPieceModels (rt := rt)) : PieceModels (rt := rt) where
  inter := D.inter.toHomModel
  a := D.a.toHomModel
  b := D.b.toHomModel

/-- **The per-piece `Δ`-models, as the declared fields of `Work.HomologyIso.PieceData`.** -/
def DeltaPieceModels.toPieceData (D : DeltaPieceModels (rt := rt)) :
    Work.HomologyIso.PieceData (rt := rt) :=
  D.toPieceModels.toPieceData

end

end Work.PieceHomology
