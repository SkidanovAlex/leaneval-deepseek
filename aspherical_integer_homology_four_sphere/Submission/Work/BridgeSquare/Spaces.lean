/-
# `BridgeSquare/Spaces.lean` — the five spaces of the cover, with explicit identifications

The pieces of the Mayer–Vietoris cover `M̂ = A ∪ B`, as spaces, and the *explicit* homotopy
equivalences of the area `Work.Space.Split` that describe them:

```
A        ≃ₕ  M̄                     (`eACompat`)
B        ≃ₕ  ⊔_v T²_v              (`eBCompat`)
A ∩ B    ≃ₕ  ⊔_v (∂[-1,1]² × T²_v)  (`eABCompat`)
```

The two homotopy equivalences `eACompat`, `eABCompat` additionally satisfy
`eACompat ∘ inclAB_A = τ ∘ eABACompat` and `eBCompat ∘ inclAB_B = projBdry ∘ eABCompat`
(`Work.Space.Split.retrA_compat`, `Work.Space.Split.retrAB_compat`, both *proved*, with equality of
continuous maps).  Consequently the Mayer–Vietoris map

`mvLeft : C_*(A ∩ B) → C_*(A) ⊞ C_*(B)`, `z ↦ (z, z)`

becomes, in the explicit identifications, the map `(H_k(τ), H_k(projBdry))` on the five cusps:

* `Work.BridgeSquare.cuspMap` — `τ : ⊔_v (∂[-1,1]² × T²_v) → M̄`, the inverse of the gluing
  restricted to the boundary (the cusp parametrisation);
* `Work.BridgeSquare.projMap` — `projBdry : ⊔_v (∂[-1,1]² × T²_v) → ⊔_v T²_v`, the projection
  forgetting the boundary coordinate.

This reduces the bridge square to a statement about these two maps in the per-cusp bases — the
*only* remaining geometric input (`NOTES.md` §3, `Work.BridgeSquare.Compatible`).

## Conventions

* `Aop`, `Bop`, `Iop` are the subspaces `A`, `B`, `A ∩ B` of `M̂` as objects of `TopCat`;
  `Mop` is `M̄` and `Dop` is the glued boundary `{q : a.Y // q ∈ a.boundarySet}` of the filling
  pieces (the domain of the cusp parametrisation `τ`), while `Cop = ⊔_v (∂[-1,1]² × T²_v)` is the
  same space in the cusp-major form used by the model `ModelM k`.
* all identifications below are the *choice-free* ones of `Work.BridgeSquare.Explicit`.
-/
import Submission.Work.BridgeSquare.Explicit
import Submission.Work.Space.Split.retrA_compat
import Submission.Work.Space.Split.retrAB_compat
import Submission.Work.HomologyIso.CuspData

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

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.BridgeSquare

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The spaces -/

/-- `A`, the thickened hyperbolic piece of `M̂`, as an object of `TopCat`. -/
abbrev Aop : TopCat :=
  TopCat.of {z : rt.core.Mhat // z ∈ rt.core.Aset}

/-- `B`, the union of the filling pieces of `M̂`, as an object of `TopCat`. -/
abbrev Bop : TopCat :=
  TopCat.of {z : rt.core.Mhat // z ∈ rt.core.Bset}

/-- `A ∩ B`, the collar annuli, as an object of `TopCat`. -/
abbrev Iop : TopCat :=
  TopCat.of {z : rt.core.Mhat // z ∈ rt.core.Aset ∧ z ∈ rt.core.Bset}

/-- `M̄`, the hyperbolic piece, as an object of `TopCat`. -/
abbrev Mop : TopCat := TopCat.of rt.core.Mbar

/-- The glued boundary `{q : a.Y // q ∈ a.boundarySet}` of the filling pieces (the domain of the
cusp parametrisation `τ`), as an object of `TopCat`. -/
abbrev Dop : TopCat := TopCat.of {q : rt.core.Y // q ∈ rt.core.boundarySet}

/-- `⊔_v (∂[-1,1]² × T²_v)`, the five cusp cross-sections in cusp-major form (the codomain of the
homotopy equivalence `eABCompat`, matching the model `ModelM k`). -/
abbrev Cop : TopCat := TopCat.of (Σ v : Work.Space.Cusp, Work.Space.Split.BdryPt × rt.core.Torus v)

/-- `⊔_v T²_v`, the five filling tori, as an object of `TopCat`. -/
abbrev Top : TopCat := TopCat.of (Σ v : Work.Space.Cusp, rt.core.Torus v)

/-! ## §2  The two maps of the cusp picture -/

/-- **The cusp parametrisation** `τ : ⊔_v (∂[-1,1]² × T²_v) → M̄`: the inverse of the gluing
homeomorphism restricted to the boundary of the filling pieces, in the cusp-major form.  (It is the
composite of `Work.Space.Assembly.tauBdry` with the canonical homeomorphism
`{q : a.Y // q ∈ a.boundarySet} ≃ₜ ⊔_v (∂[-1,1]² × T²_v)`.) -/
def cuspMap : Cop (rt := rt) ⟶ Mop (rt := rt) :=
  TopCat.ofHom ((Work.Space.Assembly.tauBdry rt.core).comp
    ⟨fun x => (Work.Space.Split.homeoBdrySubSig rt.core).symm x,
     (Work.Space.Split.homeoBdrySubSig rt.core).symm.continuous⟩)

/-- **The projection** `projBdry : ⊔_v (∂[-1,1]² × T²_v) → ⊔_v T²_v` forgetting the boundary
coordinate. -/
def projMap : Cop (rt := rt) ⟶ Top (rt := rt) :=
  TopCat.ofHom (Work.Space.Assembly.projBdry rt.core)

/-- The inclusion `A ∩ B ↪ A`, as a morphism of `TopCat`. -/
def inclA : Iop (rt := rt) ⟶ Aop (rt := rt) :=
  TopCat.ofHom (Work.Space.Assembly.inclAB_A rt.core)

/-- The inclusion `A ∩ B ↪ B`, as a morphism of `TopCat`. -/
def inclB : Iop (rt := rt) ⟶ Bop (rt := rt) :=
  TopCat.ofHom (Work.Space.Assembly.inclAB_B rt.core)

/-- The value of the cusp parametrisation, in terms of the glued boundary: it is `tauBdry` after
the canonical homeomorphism. -/
def cuspMapFn (x : Cop (rt := rt)) : rt.core.Mbar :=
  Work.Space.Assembly.tauBdry rt.core ((Work.Space.Split.homeoBdrySubSig rt.core).symm x)

/-! ## §3  The explicit identifications of the three pieces -/

/-- **`H_k(A) ≅ H_k(M̄)`**, explicitly: the map induced by the retraction `r : A → M̄`
(`Work.Space.Split.eACompat`, whose forward map is `a.r`). -/
def isoA (k : ℕ) : LeanEval.Topology.intHomology k (Aop (rt := rt)) ≅
    LeanEval.Topology.intHomology k (Mop (rt := rt)) :=
  intHomologyIsoOfHomotopyEquiv (Work.Space.Split.eACompat rt.core) k

/-- **`H_k(A ∩ B) ≅ H_k(⊔_v ∂[-1,1]² × T²_v)`**, explicitly: the radial rescaling of the collar
annulus onto the boundary of the square, in cusp-major form
(`Work.Space.Split.eABCompat`). -/
def isoInter (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ≅
    LeanEval.Topology.intHomology k (Cop (rt := rt)) :=
  intHomologyIsoOfHomotopyEquiv (Work.Space.Split.eABCompat rt.core) k

/-- **`H_k(A ∩ B) ≅ H_k({q : a.Y // q ∈ boundarySet})`**, explicitly: the same rescaling, in the
form in which the compatibility with the retraction `r : A → M̄` is *proved*
(`Work.Space.Split.eABACompat`, `Work.Space.Split.eACompat_comp_inclAB_A_eq`). -/
def isoABA (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ≅
    LeanEval.Topology.intHomology k (Dop (rt := rt)) :=
  intHomologyIsoOfHomotopyEquiv (Work.Space.Split.eABACompat rt.core) k

/-- **The homology isomorphism induced by the canonical homeomorphism** between the glued boundary
`{q : a.Y // q ∈ a.boundarySet}` (the domain of `τ`) and the cusp boundary
`⊔_v (∂[-1,1]² × T²_v)`.  This is the change of coordinates that relates the two forms in which the
compatibility with the retraction `A → M̄` is proved (`isoABA`) respectively used by the models
(`isoInter`). -/
def isoDopCop (k : ℕ) : LeanEval.Topology.intHomology k (Dop (rt := rt)) ≅
    LeanEval.Topology.intHomology k (Cop (rt := rt)) :=
  intHomologyIsoOfHomotopyEquiv ((Work.Space.Split.homeoBdrySubSig rt.core)).toHomotopyEquiv k

/-- **`H_k(B) ≅ H_k(⊔_v T²_v)`**, explicitly: the collar retracts onto its cores `p ↦ 0`
(`Work.Space.Split.eBCompat`). -/
def isoB (k : ℕ) : LeanEval.Topology.intHomology k (Bop (rt := rt)) ≅
    LeanEval.Topology.intHomology k (Top (rt := rt)) :=
  intHomologyIsoOfHomotopyEquiv (Work.Space.Split.eBCompat rt.core) k


/-- **The two forms of the `A ∩ B` identification.**  `isoInter` (cusp-major, used by the models)
and `isoABA` (the glued boundary, the form in which the compatibility with the retraction is proved)
differ by the homology isomorphism induced by the canonical homeomorphism `isoDopCop`.  This is the
change of coordinates that lets `compatA` and `compatB` be combined into a single statement in the
cusp-major bases. -/
def isoInterAlt (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ≅
    LeanEval.Topology.intHomology k (Cop (rt := rt)) :=
  isoABA (rt := rt) k ≪≫ isoDopCop (rt := rt) k

/-! ## §3.5  Splitting the Mayer–Vietoris map into its two components -/

/-- **The first Mayer–Vietoris map, split into the two components of the target.**  This is
`mvFhat k` followed by the explicit additivity of homology over the binary biproduct
(`Work.BridgeSquare.biprodHomology`), i.e. the map `H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` whose two
components are the inclusions. -/
def mvSplit (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ⟶
    (LeanEval.Topology.intHomology k (Aop (rt := rt)) ⊞
      LeanEval.Topology.intHomology k (Bop (rt := rt))) :=
  Work.HomologyIso.mvFhat (rt := rt) k
    ≫ (biprodHomology (Work.Homology.singChain Work.Homology.ZMod (Aop (rt := rt)))
        (Work.Homology.singChain Work.Homology.ZMod (Bop (rt := rt))) k).hom

/-- The same map, written as the pair of its two components: the inclusions `A ∩ B ↪ A` and
`A ∩ B ↪ B`. -/
def mvLift (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ⟶
    (LeanEval.Topology.intHomology k (Aop (rt := rt)) ⊞
      LeanEval.Topology.intHomology k (Bop (rt := rt))) :=
  biprod.lift
    (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Aop (rt := rt)) (inclA (rt := rt))) k)
    (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Bop (rt := rt)) (inclB (rt := rt))) k)

/-- **The map induced on `k`-th integral homology by a continuous map** (in the explicit
spelling of this area: `homologyMap` of the induced singular chain map). -/
abbrev homMap {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    LeanEval.Topology.intHomology k X ⟶ LeanEval.Topology.intHomology k Y :=
  HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) k

/-! ## §4  The two sides of the two compatibility squares

The two maps of the Mayer–Vietoris square, on each piece, in the explicit identifications:

* the **`A`-side**: `mvA` is `H_k(A ∩ B) → H_k(A)` (the inclusion) followed by the retraction
  `H_k(A) ≅ H_k(M̄)`; `cuspA` is the radial rescaling `H_k(A ∩ B) ≅ H_k(boundary)` followed by the
  cusp parametrisation `H_k(τ)`.  They are equal — this is
  `Work.Space.Split.eACompat_comp_inclAB_A_eq` at the level of homology;
* the **`B`-side**: `mvB` is `H_k(A ∩ B) → H_k(B)` (the inclusion) followed by the collar retraction
  `H_k(B) ≅ H_k(⊔_v T²_v)`; `cuspB` is the rescaling followed by the projection `H_k(projBdry)`.
  They are equal — `Work.Space.Split.eBCompat_comp_inclAB_B_eq`.

The two equalities (`compatA`, `compatB`) are the content of the "bridge": they turn the
Mayer–Vietoris map of the cover into the *cusp* maps `τ` and `projBdry`, whose matrices in the
per-cusp bases are the remaining geometric input.
-/

/-- The `A`-component of the Mayer–Vietoris map in the explicit identifications: the inclusion
`A ∩ B ↪ A` followed by the retraction `H_k(A) ≅ H_k(M̄)`. -/
def mvA (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ⟶
    LeanEval.Topology.intHomology k (Mop (rt := rt)) :=
  HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Aop (rt := rt)) (inclA (rt := rt))) k
    ≫ (isoA (rt := rt) k).hom

/-- The cusp side of `mvA`: the radial rescaling of the collar annulus onto the boundary of the
square, followed by the cusp parametrisation `τ`. -/
def cuspA (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ⟶
    LeanEval.Topology.intHomology k (Mop (rt := rt)) :=
  (isoABA (rt := rt) k).hom
    ≫ HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Dop (rt := rt)) (Mop (rt := rt))
        (TopCat.ofHom (Work.Space.Assembly.tauBdry rt.core))) k

/-- The `B`-component of the Mayer–Vietoris map in the explicit identifications: the inclusion
`A ∩ B ↪ B` followed by the collar retraction `H_k(B) ≅ H_k(⊔_v T²_v)`. -/
def mvB (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ⟶
    LeanEval.Topology.intHomology k (Top (rt := rt)) :=
  HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Bop (rt := rt)) (inclB (rt := rt))) k
    ≫ (isoB (rt := rt) k).hom

/-- The cusp side of `mvB`: the radial rescaling followed by the projection `projBdry` forgetting
the boundary coordinate. -/
def cuspB (k : ℕ) : LeanEval.Topology.intHomology k (Iop (rt := rt)) ⟶
    LeanEval.Topology.intHomology k (Top (rt := rt)) :=
  (isoInter (rt := rt) k).hom ≫ HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (Cop (rt := rt)) (Top (rt := rt)) (projMap (rt := rt))) k
end

end Work.BridgeSquare
