import Mathlib
import Submission.Work.PTGeometric.RawAmbientData
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.Surgery.Collar
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the boundary-coordination predicate of the source construction

`Work.ThomBordism.SourceBoundaryCoord D0` is the **boundary coordination** of a raw datum `D0` of the
source construction: the class of the pieces — the sum of the pieces' fundamental classes pushed
along the collapse identification `D0.hend` of the collapse end `D0.S ∩ {v = 0}` with the pieces —
vanishes under the map induced on `H₈` by the inclusion of the boundary part of the level set
`{v = 0}` into the level set itself.

Equivalently (long exact sequence of the pair): the pieces bound the level set *with the given
orientations* (`Work.Cohomology.hPair_exact₁`), which is exactly the geometric content of the
boundary sign of the last mile (`NOTE_SIGN_S6.md` §5–§6, `NOTE_nullhomologous_interface.md`).

This file only *names* the predicate, together with the set/class/inclusion vocabulary it is built
from, so that the strengthened existence lemma of the source construction (and hence the
specification of `Work.PTGeometric.producedRawData`) can carry it as a conjunct without unfolding the
source construction.

The three ingredients are:

* `sourceLevelSet`, `sourceLevelBdry` — the level set `{v = 0}` of the raw datum and its boundary part
  `{v = 0} ∩ ∂M` (the latter as a subset of the level set);
* `sourceBoundaryClass` — the class `ῆ` of the pieces in `H₈` of the boundary part, pushed along the
  collapse identification `D0.hend`;
* `SourceBoundaryCoord` — the vanishing `i_* ῆ = 0`.

## Main definitions

* `Work.ThomBordism.sourceLevelSet`, `…sourceLevelBdry`, `…sourceLevelIncl`
* `Work.ThomBordism.piecePush`, `…sourceBoundaryClass`, `…SourceBoundaryCoord`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric

variable {k mU m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The level set of a raw datum**: the zero set of its ambient field. -/
def sourceLevelSet (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2)) : Set D0.M :=
  {x : D0.M | D0.v x = 0}

/-- **The boundary part of the level set**, as a subset of the level set. -/
def sourceLevelBdry (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2)) :
    Set ↥(sourceLevelSet D0) :=
  {x : ↥(sourceLevelSet D0) | (x : D0.M) ∈ (𝓡∂ ((8 + k) + 1)).boundary D0.M}

/-- **The inclusion of the boundary part into the level set.** -/
def sourceLevelIncl (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2)) :
    C(TopCat.of ↥(sourceLevelBdry D0), TopCat.of ↥(sourceLevelSet D0)) where
  toFun x := ⟨x.1.1, x.1.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp continuous_subtype_val

/-- **The `a`-th piece pushed into the boundary part of the level set** along the collapse
identification `D0.hend` (whose values lie in `S ∩ {v = 0} ⊆ ∂M`, by `hSsub`). -/
def piecePush (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    (a : Fin m × ι) : C((Fam a.2).X, TopCat.of ↥(sourceLevelBdry D0)) where
  toFun y := ⟨⟨(D0.hend.symm ⟨a, y⟩ : D0.M), (D0.hend.symm ⟨a, y⟩).2.2⟩,
    D0.hSsub (D0.hend.symm ⟨a, y⟩).2.1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (continuous_subtype_val.comp D0.hend.continuous_invFun).comp continuous_sigmaMk

/-- **The class of the pieces**: the sum of the pieces' fundamental classes, pushed along the collapse
identification `D0.hend` of the collapse end with the pieces, in the homology of the boundary part. -/
def sourceBoundaryClass (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2)) :
    (Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(sourceLevelBdry D0))).homology 8 :=
  ∑ a : Fin m × ι, HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (Fam a.2).X (TopCat.of ↥(sourceLevelBdry D0))
      (TopCat.ofHom (piecePush D0 a))) 8 (Fam a.2).c

/-- **The boundary coordination of the source construction**: the pieces bound the level set with the
given orientations — the class of the pieces dies under the inclusion of the boundary part of the
level set into the level set.

For a datum satisfying the recorded hypotheses of the source construction this is the geometric
content of the boundary sign of the last mile: on the long exact sequence of the pair
`(↥levelSet, boundary part)`, exact at `H₈` of the boundary part (`Work.Cohomology.hPair_exact₁`), it
is *equivalent* to the existence of a relative fundamental class whose boundary is the class of the
pieces (`NOTE_SIGN_S6.md` §5, `NOTE_nullhomologous_interface.md` §5): the connecting map `hPairδ` has
image exactly the kernel of the inclusion. -/
def SourceBoundaryCoord (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2)) : Prop :=
  (HomologicalComplex.homologyMap
    (Work.Cohomology.inclChains (TopCat.of ↥(sourceLevelSet D0)) (sourceLevelBdry D0)) 8)
    (sourceBoundaryClass D0) = 0



/-- **The collar and the orientation family of the level model of a raw datum.**

This is the pair of clauses that the *last mile* of the orientation datum needs about the level set
`{v = 0}` of a raw datum `D0`: a collar of the canonical level model `levelModel (sourceLevelSet D0)`
in the `Lvl` chart structure, and a half-orientation family of that model.

It is stated here, *below* the source construction (this module is imported by
`Submission/Work/ThomBordism/sourceRawAmbientData_tied_collar.lean`), so that the strengthened
existence lemma of the construction can carry it as a conjunct without unfolding the construction.
The shape is deliberately the same as `Work.ThomBordism.LevelOrientationHyp`
(`Submission/Work/ThomBordism/levelModelAssembly.lean`), which is the form the wiring consumes. -/
def SourceOrientHyp (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    (hWcl : IsClosed (sourceLevelSet D0))
    (L : Work.PTGeometric.LocalLevelData k D0.M (sourceLevelSet D0)) : Prop :=
  letI : ChartedSpace (EuclideanHalfSpace 9)
      (Work.PTGeometric.levelModel (sourceLevelSet D0) hWcl L) :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace
      (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L)
  Nonempty (Work.Surgery.Collar 8 (Work.PTGeometric.levelModel (sourceLevelSet D0) hWcl L)) ∧
    ∃ γ : ∀ x : (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre,
        x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre →
        Work.Orient.LocH (TopCat.of
          (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre) 9 x,
      Work.Orient.IsHalfOrientationFamily 8
        (TopCat.of (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre) γ

end

end Work.ThomBordism
