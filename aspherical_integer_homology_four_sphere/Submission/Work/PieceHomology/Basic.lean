/-
# `PieceHomology/`: finite-complex models of the homology of a space

The area `Work.HomologyIso` reduces the whole Mayer–Vietoris computation of `M̂` to three homology
computations of the geometry

* `eTorus` — `H_k(∂[-1,1]² × T²_v) ≅ ℤ^{rankT k}` for each of the five cusps,
* `eA` — `H_k(M̄) ≅ ℤ^{rankA k}`,
* `eT2` — `H_k(T²_v) ≅ ℤ^{rankT2 k}`,

together with a bridge (the Mayer–Vietoris map is the concrete matrix `wConcrete`).  This area
supplies those three computations and the bridge *from the cell-complex data produced by the
area `Certificates` and the Python agent (`rtdata/`)*, and assembles the result into
`Work.HomologyIso.CuspInputs`.

## The shape of the input

Every computation of the geometry has the same shape, formalised here by the two structures

```
HomModel X r    -- a chain complex C, a quasi-isomorphism C ⟶ C_*(X), and H_k(C) ≅ ℤ^{r k}
DeltaModel X r  -- the same, but C is the Δ-chain complex of a finite Δ-complex realized in X
```

`HomModel.iso : ℤ^{r k} ≅ H_k(X)` is the deliverable of a model: it composes the identification
`H_k(C) ≅ ℤ^{r k}` with the inverse of the quasi-isomorphism, through
`Work.HomologyMV.intHomology_iso_of_quasiIso`.

`DeltaModel` is the form in which the providers of the geometry naturally land: a finite
`Δ`-complex `K` (`Work.DeltaHomology.DeltaCx`) realized in the space (`DeltaRealization`), whose
comparison chain map `σ ↦ χ σ` to the singular chains is a quasi-isomorphism (Hatcher 2.27 —
`Work.DeltaHomology.deltaChainMap_quasiIso`, the frontier of the area `DeltaHomology`, taken here
as a *hypothesis* until it lands), together with the computation of the homology of the chain
complex (from a `Certificates.SDR` certificate on a `FinChainCx` isomorphic to it, or from the
generated data `Work.HomologyIso.Gen`).

## Main definitions and results

* `Work.PieceHomology.HomModel`, `Work.PieceHomology.HomModel.iso`;
* `Work.PieceHomology.DeltaModel`, `DeltaModel.toHomModel`, `DeltaModel.ofSDR`,
  `DeltaModel.iso`;
* `Work.PieceHomology.HomModel.ofSDR` — the same from a `Certificates.SDR` certificate.
-/
import Mathlib
import Submission.Work.HomologyIso.Final
import Submission.Work.HomologyMV.Interface
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.chainD_comp
import Submission.Work.DeltaHomology.chainMapFun_comm
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.deltaChainMap_comm
import Submission.Work.DeltaHomology.deltaChainMapFun_natural
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.isClosed_skelSet
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt
import Submission.Work.DeltaHomology.SkelProps
import Submission.Work.DeltaHomology.SkelChain
import Submission.Work.DeltaHomology.GoodPairDefs
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.chain_homology_isZero_of_dim_lt
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt
import Submission.Work.DeltaHomology.Main
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.exists_deformationRetract_punctSkel
import Submission.Work.DeltaHomology.relHomology_iso_clopen_sum
import Submission.Work.DeltaHomology.skelQuotient_shortExact
import Submission.Work.DeltaHomology.skelQuotient_X_isZero
import Submission.Work.Homology.Basic
import Submission.Work.DeltaHomology.cell_relHomology_iso
import Submission.Work.DeltaHomology.relHomology_skel_succ_excision
import Submission.Work.DeltaHomology.relHomology_cell_splitting
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.punctCell_eq_sdiff
import Submission.Work.DeltaHomology.simplexGenMap_isIso
import Submission.Work.DeltaHomology.cellClassMapCell_isIso
import Submission.Work.DeltaHomology.quasiOso_deltaChainMapSkel
import Submission.Work.DeltaHomology.quasiOso_deltaChainMap
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.DeltaHomology.exists_homeomorph_intCell
import Submission.Work.DeltaHomology.closure_skelSet_interior_punctSkel
import Submission.Work.DeltaHomology.relHomology_stdSimplexBoundary
import Submission.Work.DeltaHomology.isQuotientMap_punctToPiece
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.Certificates.SDR.homology_iso_of_iso

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

/-- **A finite-complex model of the integral homology of a space `X`, in the ranks `r`.**

The data is a chain complex `C` (in practice the cellular or `Δ`-chain complex of a finite cell
structure on `X`), a quasi-isomorphism `q : C ⟶ C_*(X; ℤ)` from it to the singular chain complex,
and an identification of the homology of `C` with the free model `ℤ^{r k}` in every degree. -/
structure HomModel (X : TopCat) (r : ℤ → ℕ) where
  /-- The finite chain complex computing the homology. -/
  C : ChainComplex (ModuleCat ℤ) ℕ
  /-- The comparison chain map to the singular chains of `X`. -/
  q : C ⟶ Work.HomologyMV.singCx X
  /-- It is a quasi-isomorphism (the realisation step). -/
  hq : QuasiIso q
  /-- The homology of `C` in the model ranks. -/
  e : ∀ k : ℕ, C.homology k ≅ Work.HomologyMV.freeMod (r (k : ℤ))

namespace HomModel

variable {X : TopCat} {r : ℤ → ℕ}

/-- **The deliverable of a model**: the identification of the free model `ℤ^{r k}` with the
singular homology of `X`. -/
def iso (M : HomModel X r) (k : ℕ) :
    Work.HomologyMV.freeMod (r (k : ℤ)) ≅ LeanEval.Topology.intHomology k X :=
  ((Work.HomologyMV.intHomology_iso_of_quasiIso X M.q M.hq (M.e k)).some).symm

/-- The same, for a provider that only has a `Nonempty` statement (the generated data
`Work.HomologyIso.Gen.mbarCx_homology_modelA` and friends have this form). -/
def ofNonempty (C : ChainComplex (ModuleCat ℤ) ℕ) (q : C ⟶ Work.HomologyMV.singCx X)
    (hq : QuasiIso q) (e : ∀ k : ℕ, Nonempty (C.homology k ≅ Work.HomologyMV.freeMod (r (k : ℤ)))) :
    HomModel X r where
  C := C
  q := q
  hq := hq
  e := fun k => (e k).some

/-- **A model from a `Certificates.SDR` certificate** on a finite complex `C` which is isomorphic
(as a chain complex) to the provider's complex `K`: this is the composition
`H_k(K) ≅ H_k(C) ≅ ℤ^{b k} ≅ ℤ^{r k}` used for every piece of the geometry. -/
def ofSDR {K : ChainComplex (ModuleCat ℤ) ℕ} (q : K ⟶ Work.HomologyMV.singCx X)
    (hq : QuasiIso q) (C : Work.Certificates.FinChainCx) (S : Work.Certificates.SDR C)
    (hS : S.check = true) (eC : C.toChainComplex ≅ K) (r : ℤ → ℕ)
    (hb : ∀ k : ℕ, S.b k = r (k : ℤ)) : HomModel X r where
  C := K
  q := q
  hq := hq
  e := fun k => (Work.Certificates.SDR.homology_iso_of_iso S hS eC k).some
    ≪≫ Work.HomologyIso.freeModCast (hb k)

end HomModel

/-- **A `Δ`-complex model of the integral homology of a space `X`, in the ranks `r`.**

This is the form of the geometric input: a finite `Δ`-complex `K` (`DeltaCx`) together with a
realization of `K` in `X` (`DeltaRealization`, i.e. the characteristic maps `χ` and the point-set
conditions), the statement that the comparison chain map `σ ↦ χ σ` is a quasi-isomorphism
(Hatcher Theorem 2.27, the frontier of the area `DeltaHomology`, whose conclusion is
`Work.DeltaHomology.deltaChainMap_quasiIso`), and the computation of the homology of the
`Δ`-chain complex `K.chain` in the ranks `b` (which are `r` up to the identification `hb`).

The homology computation is where the generated Ratcliffe–Tschantz data enters: the provider
supplies `Work.Certificates.SDR` certificates (or the corollaries of `Work.HomologyIso.Gen`). -/
structure DeltaModel (X : TopCat) (r : ℤ → ℕ) where
  /-- The finite `Δ`-complex. -/
  K : Work.DeltaHomology.DeltaCx
  /-- Its realization in `X`. -/
  R : Work.DeltaHomology.DeltaRealization K X
  /-- **Hatcher 2.27: the comparison chain map is a quasi-isomorphism.**  This is
  `Work.DeltaHomology.deltaChainMap_quasiIso K R`, *proved* in the area `DeltaHomology`; it is kept
  as a field so that the structure can also record a comparison map obtained by another route, and
  the constructors `DeltaModel.ofHatcher` / `DeltaModel.ofSDRHatcher` fill it with the theorem. -/
  hq : QuasiIso R.toDeltaSimplexMap.deltaChainMap
  /-- The computed ranks of the homology of `K.chain`. -/
  b : ℕ → ℕ
  /-- They are the model ranks. -/
  hb : ∀ k : ℕ, b k = r (k : ℤ)
  /-- The homology of the `Δ`-chain complex in those ranks. -/
  e : ∀ k : ℕ, K.chain.homology k ≅ Work.HomologyMV.freeMod (b k)

namespace DeltaModel

variable {X : TopCat} {r : ℤ → ℕ}

/-- **A `Δ`-model is a model**: the comparison chain map of the realization is the
quasi-isomorphism `q`, and the ranks are transported along `hb`. -/
def toHomModel (M : DeltaModel X r) : HomModel X r where
  C := M.K.chain
  q := M.R.toDeltaSimplexMap.deltaChainMap
  hq := M.hq
  e := fun k => M.e k ≪≫ Work.HomologyIso.freeModCast (M.hb k)

/-- **The deliverable of a `Δ`-model**: `ℤ^{r k} ≅ H_k(X)`. -/
def iso (M : DeltaModel X r) (k : ℕ) :
    Work.HomologyMV.freeMod (r (k : ℤ)) ≅ LeanEval.Topology.intHomology k X :=
  M.toHomModel.iso k

/-- **A `Δ`-model from an `SDR` certificate** on a `FinChainCx` whose chain complex is isomorphic
to the `Δ`-chain complex of the realization.  This is the plug through which the generated
`rtdata` certificates (`Submission/Work/HomologyIso/Gen`, `Submission/Work/Certificates`) enter. -/
def ofSDR {K : Work.DeltaHomology.DeltaCx} (R : Work.DeltaHomology.DeltaRealization K X)
    (hq : QuasiIso R.toDeltaSimplexMap.deltaChainMap) (C : Work.Certificates.FinChainCx)
    (S : Work.Certificates.SDR C) (hS : S.check = true) (eC : C.toChainComplex ≅ K.chain)
    (r : ℤ → ℕ) (hb : ∀ k : ℕ, S.b k = r (k : ℤ)) : DeltaModel X r where
  K := K
  R := R
  hq := hq
  b := S.b
  hb := hb
  e := fun k => (Work.Certificates.SDR.homology_iso_of_iso S hS eC k).some

/-- **A `Δ`-model from the generated data**: the `Nonempty`-form of the homology computation
(`Work.HomologyIso.Gen.mbarCx_homology_modelA`, `Gen.cuspCx_homology_modelT`,
`Gen.t2Cx_homology_modelT2`) transported along an equality of ranks. -/
def ofNonempty {K : Work.DeltaHomology.DeltaCx} (R : Work.DeltaHomology.DeltaRealization K X)
    (hq : QuasiIso R.toDeltaSimplexMap.deltaChainMap) (b : ℕ → ℕ)
    (e : ∀ k : ℕ, Nonempty (K.chain.homology k ≅ Work.HomologyMV.freeMod (b k)))
    (hb : ∀ k : ℕ, b k = r (k : ℤ)) : DeltaModel X r where
  K := K
  R := R
  hq := hq
  b := b
  hb := hb
  e := fun k => (e k).some

/-- **A `Δ`-model with the Hatcher 2.27 quasi-isomorphism discharged**: from a realized
`Δ`-complex and the computation of the homology of its `Δ`-chain complex in the ranks `r`.  The
comparison quasi-isomorphism is `Work.DeltaHomology.deltaChainMap_quasiIso` (proved). -/
def ofHatcher {K : Work.DeltaHomology.DeltaCx} (R : Work.DeltaHomology.DeltaRealization K X)
    (e : ∀ k : ℕ, K.chain.homology k ≅ Work.HomologyMV.freeMod (r (k : ℤ))) : DeltaModel X r where
  K := K
  R := R
  hq := Work.DeltaHomology.deltaChainMap_quasiIso K R
  b := fun k => r (k : ℤ)
  hb := fun _ => rfl
  e := e

/-- **A `Δ`-model from an `SDR` certificate, with Hatcher 2.27 discharged**: the shape in which the
`rtdata` certificates enter, with no remaining hypothesis. -/
def ofSDRHatcher {K : Work.DeltaHomology.DeltaCx} (R : Work.DeltaHomology.DeltaRealization K X)
    (C : Work.Certificates.FinChainCx) (S : Work.Certificates.SDR C) (hS : S.check = true)
    (eC : C.toChainComplex ≅ K.chain) (r : ℤ → ℕ) (hb : ∀ k : ℕ, S.b k = r (k : ℤ)) :
    DeltaModel X r :=
  ofSDR R (Work.DeltaHomology.deltaChainMap_quasiIso K R) C S hS eC r hb

end DeltaModel

end

end Work.PieceHomology
