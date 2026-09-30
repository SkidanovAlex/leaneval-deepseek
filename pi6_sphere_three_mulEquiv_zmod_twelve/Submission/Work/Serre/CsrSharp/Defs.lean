import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.cubePairDefs
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sharp (rational) cell step: definitions and interfaces

This file contains the vocabulary used by the sharp rational cell step
`Work.Serre.cellStepSharp` (`Submission/Work/Serre/cellStepSharp.lean`):

* `Work.Serre.CsrSharp.cubePairRat` — the rational version of the cube pair map
  `Work.Serre.cubePairMap` of `Submission/Work/Serre/cubePairDefs.lean`;
* `Work.Serre.CsrSharp.CubeIsoRat` — the rational version of `Work.Serre.cubeRelIso`, as a `Prop`
  (the per-cube computation `(P_D)` over `ℚ`);
* `Work.Serre.CsrSharp.perCellMap` — the per-cell comparison over the open half-ball
  `Work.Serre.csrOpenBall n Y ι f i` of an attached cell;
* `Work.Serre.CsrSharp.PerCellIso`, `Work.Serre.CsrSharp.SigmaIso` — the two remaining interfaces
  (the per-cell statement in the sharp range, and the additivity of relative homology over a
  disjoint union of pairs) as `Prop`s.

The sharp form is essential: the cell step gives the isomorphism in degrees `< (n+2) + φ` and
surjectivity in degree `(n+2) + φ`, where `φ` is the (rational) connectivity of the fibres.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CsrSharp

noncomputable section

/-- **The rational cube pair map** `(τ^*E, τ^*E|_{∂I^D}) ⟶ (I^D, ∂I^D)` induced by a continuous
map `p : E → B` along `τ : I^D → B` (the `ℚ`-coefficient version of `Work.Serre.cubePairMap`). -/
def cubePairRat {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (D : ℕ)
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B)) :
    Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
        (Work.Serre.cubeBdryS D) :=
  Work.Serre.relChainsRPairMap (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))
    (Work.Serre.cubeBdryS D) (Work.StemsB.pullbackSnd p τ) (fun _ hx => hx)

/-- **The per-cell comparison over the open half-ball** of the `i`-th attached cell, on relative
rational chains: `(q⁻¹o_i, q⁻¹(o_i ∖ {c_i})) ⟶ (o_i, o_i ∖ {c_i})`, where `o_i` is the open
half-ball `Work.Serre.csrOpenBall n Y ι f i` and `c_i = Work.Serre.csrCentre n Y ι f i`. -/
def perCellMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i))
      {x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) |
        (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})} ⟶
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.csrOpenBall n Y ι f i))
      {x : ↥(Work.Serre.csrOpenBall n Y ι f i) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}} :=
  Work.Serre.relChainsRPairMap _ _ (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i))
    (fun _ hx => hx)

/-- **The rational per-cube computation `(P_D)`.**  For a Serre fibration `p : E → B`, a map
`τ : I^D → B` and fibres which are rationally acyclic in degrees `0 < j < φ` and rationally
connected, the cube pair map `Work.Serre.CsrSharp.cubePairRat D p τ` is an isomorphism on rational
homology in degrees `< D + φ` and surjective in degree `D + φ`.

This is the `ℚ`-coefficient analogue of `Work.Serre.cubeRelIso` (`Submission/Work/Serre/cubeRelIso.lean`),
which proves the same statement over `ℤ` with *integrally* acyclic fibres, and it is the geometric
input of the per-cell computation `Work.Serre.CsrSharp.PerCellIso`.

Proof route: mirror the proof of `Work.Serre.cubeRelIso` verbatim, replacing each integral
auxiliary by its `ℚ` version.  All the auxiliaries are coefficient-unconditional and base-change
along `- ⊗[ℤ] ℚ` (`Work.StemsB.RatBC`, and `Work.Serre.bcRat` of
`Submission/Work/Serre/csrExcisionRat.lean`, whose proof is a template for this base change):

* `Work.Serre.serreE2d` (`H_{k+D}(τ^*E, τ^*E|_{∂I^D}; ℤ) ≅ H_k(F; ℤ)`, no fibre hypothesis),
* `Work.Serre.cubeBdry_isZero` (`H_m(I^D, ∂I^D; ℤ) = 0` for `m ≠ D`),
* `Work.Serre.cubeBdry_top_iso` (`H_D(I^D, ∂I^D; ℤ) ≅ ℤ`),
* `Work.Serre.cubeAmbient_isZero` (`H_m(τ^*E, τ^*E|_{∂I^D}; ℤ) = 0` for `m < D`, unconditional),

while `Work.Serre.exists_section_cubePullback` and `Work.Serre.cubeSectionMap` are coefficient-free
(they give the top-degree surjectivity, and the `ℚ`-analogue of
`isIso_of_surjective_of_intIso` gives the top-degree isomorphism from the hypothesis `h0`). -/
def CubeIsoRat : Prop :=
  ∀ (D : ℕ) (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B))
    (φ : ℕ)
    (hfib : ∀ y : Work.Stems.Cubical.IC D, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j))
    (h0 : ∀ y : Work.Stems.Cubical.IC D,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre p (τ y)))).homology 0 ≅ ModuleCat.of ℚ ℚ)),
    (∀ i : ℕ, i < D + φ →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (cubePairRat D p τ) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (cubePairRat D p τ) (D + φ)).hom

/-- **The per-cell computation of the sharp rational cell step.**  For a Serre fibration
`q : E → Z` over `Z = attachCells n Y ι f` whose fibres are rationally acyclic in degrees
`0 < j < φ` and rationally connected, the per-cell map `Work.Serre.CsrSharp.perCellMap n Y ι f q i`
is an isomorphism on rational homology in degrees `< (n+2) + φ` and surjective in degree
`(n+2) + φ`.

Proof route (given the per-cube computation `Work.Serre.CsrSharp.CubeIsoRat`).  Write
`Z = attachCells n Y ι f`, `χ = cellMap n Y ι f i : cellDisk n → Z`, `c = csrCentre n Y ι f i`,
`o = csrOpenBall n Y ι f i = χ '' {y | ‖y‖ < 1/2}` and `B = χ '' {y | ‖y‖ ≤ 1/2}`.  By
`Work.RatHurewicz.cellMap_injective_cellInner` (`cellDisk n ⊆ cellInner n` on the open ball of
radius `1/2`, `Submission/Work/RatHurewicz/AttachPush/CellInterior.lean`) the maps

* `χ⁻¹ : o → {y : cellDisk n | ‖y‖ < 1/2}` (with `Work.RatHurewicz.cellInterior_section`),
* `χ⁻¹` on `o ∖ {c}`, which is the image of the punctured ball,

are continuous bijections, so the per-cell pair is the pair `(q⁻¹(Y), q⁻¹(Y ∖ 0))` of the pullback
of `q` along `χ`, and the pullback of a map along `χ` is `q⁻¹(χ _)` (compare
`Work.StemsB.pullbackSnd` and `Work.Serre.pbPre_eq_preimage`, and the homeomorphisms
`Work.Serre.pbHomeo`/`Work.StemsB.sphHomeoHom` used in `Submission/Work/Serre/CellStep/discPairIso.lean`).
Then

* replace the relative part `o ∖ {c}` by the boundary sphere
  `csrSphere n Y ι f i = χ '' {y | ‖y‖ = 1/2}`: the pair
  `(B ∖ {c}, csrSphere n Y ι f i)` is compressible (radial push of the punctured closed ball onto
  its boundary sphere), so `Work.Serre.csrRelIso` gives an isomorphism on homology in *every*
  degree, on the base side and (via `Work.Serre.isZero_relChainsR_rat_of_isZero_relChains`-style
  transfers, cf. `Submission/Work/Serre/CellStep/Tools.lean`) on the total side;
* replace `(B, csrSphere …)` by `(cellDisk n, {y | ‖y‖ = 1})` by rescaling, and then by
  `(I^{n+2}, ∂I^{n+2})` along `Work.Serre.cellHomeo` (`Submission/Work/Serre/cubeDiskHomeo.lean`),
  exactly as in `Submission/Work/Serre/CellStep/discPairIso.lean`;
* apply `Work.Serre.CsrSharp.CubeIsoRat` with `D = n+2` and `τ = χ ∘ cellHomeo.symm`, whose fibre
  hypotheses are the given `hfib`/`h0` (they hold over all of `Z`, hence over the image of `τ`). -/
def PerCellIso : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Y ι f,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (i : ι),
    (∀ m : ℕ, m < (n + 2) + φ →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (perCellMap n Y ι f q i) m)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (perCellMap n Y ι f q i)
      ((n + 2) + φ)).hom

/-- **Additivity of relative rational homology over a disjoint union of pairs.**  For a family of
pairs `(X i, A i) → (Y i, B i)` whose members are isomorphisms on `H_m` (resp. surjective on `H_m`),
the same holds for the disjoint union `Σ i, X i → Σ i, Y i`.

This is the `ℚ`-coefficient, sharp-range form of `Work.Serre.csrSigmaAdditivity`
(`Submission/Work/Serre/csrSigmaAdditivity.lean`), with the surjectivity clause (needed for the
boundary degree of the sharp cell step) added.  The route is
`Work.Serre.relChains_coproduct_iso` (relative chains of a disjoint union are the coproduct of the
relative chains of the pieces) together with `Work.Serre.isIso_homologyMap_sigma`
(`Submission/Work/Serre/sigmaHomologyRat.lean`) and the fact that a coproduct of surjections is
surjective. -/
def SigmaIso : Prop :=
  ∀ {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i)) (g : ∀ i, C(X i, Y i))
    (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ),
    ((∀ i, CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i)) m)) →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
          {x : (Σ i, Y i) | x.2 ∈ B x.1}
          ⟨Sigma.map id (fun i => g i), by fun_prop⟩
          (by rintro ⟨i, x⟩ hx; exact hg i hx)) m)) ∧
    ((∀ i, Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i)) m).hom) →
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
          {x : (Σ i, Y i) | x.2 ∈ B x.1}
          ⟨Sigma.map id (fun i => g i), by fun_prop⟩
          (by rintro ⟨i, x⟩ hx; exact hg i hx)) m).hom)

end

end Work.Serre.CsrSharp
