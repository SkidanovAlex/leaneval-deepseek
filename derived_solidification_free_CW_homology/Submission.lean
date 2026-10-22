import Mathlib
import Submission.Helpers
import ChallengeDeps
import Submission.Work.REFL.Main
import Submission.Work.ATOM.Main
import Submission.Work.TOOLKIT.Main
import Submission.Work.RESOL.Main
import Submission.Work.DERFORMAL.Main
import Submission.Work.ANALYTIC.hi_prop
import Submission.Work.DISC.Main
import Submission.Work.CONDMV.Main
import Submission.Work.SingMV.Main
import Submission.Work.CWTOP.Main
import Submission.Work.CWIND.Main
import Submission.Work.HOMOL.Main
/-!
# Derived solidification of free CW complexes

This challenge is extracted from the LeanCondensed project
<https://github.com/dagurtomas/LeanCondensed>, which develops the theory of light condensed
mathematics of Clausen–Scholze in Lean.  The target statement is the comparison theorem for a CW
complex `X`: the homology of the derived solidification of the free light condensed abelian group
on `X` is integral singular homology.

The non-`sorry` part of this file develops, using only Mathlib, the definition of
*light solid abelian groups*: a light condensed abelian group `A` is solid if the map
`1 - shift` on the free light condensed abelian group `P = ℤ[ℕ∪{∞}]/ℤ[∞]` induces an isomorphism
on internal homs into `A`.  The full subcategory `Solid` of solid objects is closed under limits,
kernels, cokernels and finite products, hence abelian, and the inclusion into light condensed
abelian groups is exact, so it induces a functor on derived categories.

The `sorry`ed declarations (the holes of this multi-hole problem) are:

* `solidification` — the solidification functor `LightCondAb ⥤ Solid`;
* `solidification_additive` — additivity of the solidification functor;
* `solidificationAdjunction` — solidification is left adjoint to the inclusion;
* `derivedSolidification` — the derived solidification functor
  `DerivedCategory LightCondAb ⥤ DerivedCategory Solid`;
* `derivedSolidificationCounit` — the comparison map exhibiting `derivedSolidification` as a
  functor under degreewise solidification;
* `derivedSolidification_isLeftDerivedFunctor` — `derivedSolidification` is the total left
  derived functor of degreewise solidification;
* `derivedSolidificationAdjunction` — derived solidification is left adjoint to the derived
  inclusion;
* `derivedSolidificationFreeCWFunctor` — the functor on CW complexes whose values are the derived
  inclusion of the derived solidification of the free light condensed abelian group;
* `derivedSolidificationFreeCWFunctorSpec` — an isomorphism identifying
  `derivedSolidificationFreeCWFunctor` with the expected composite functor;
* `derivedSolidification_free_CW_derivedNatIso` — naturally in a CW complex `X`, the derived
  inclusion of the derived solidification of `ℤ[X]` is isomorphic in the derived category of light
  condensed abelian groups to the integral singular chain complex of `X`, viewed as a complex of
  discrete light condensed abelian groups with homological degree `n` placed in cohomological
  degree `-n`, this is the main challenge;
* `derivedSolidification_free_CW_homologyIso` — for a CW complex `X`, the homology of the derived
  solidification of `ℤ[X]` is integral singular homology (the derived category is cohomologically
  indexed, so the `n`-th singular homology group appears in degree `-n`);
* `derivedSolidification_free_CW_homology` — the theorem form of the previous isomorphism.

All holes must be filled compatibly: the adjunctions and derived functor property pin down
`solidification` and `derivedSolidification` up to natural isomorphism, so the final derived
comparison theorem and its pointwise homology form have their intended mathematical content.

Note that the LeanCondensed project contains significant progress towards some of the earlier holes
in this challenge.
-/


namespace Submission

universe u

open _root_.LightCondensed
open _root_.LightCondensed.Solid
open _root_.LightCondensed.Solid.CWTopCat
open _root_.LightProfinite
open CategoryTheory Limits LightProfinite OnePoint LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace LightProfinite



end LightProfinite

namespace LightCondensed



























/-- The class expressing that a light condensed abelian group is solid. -/
abbrev IsSolid (A : LightCondAb) := isSolid.Is A



namespace Solid



































/-! ### Assembly of the area deliverables (see `Submission/Blueprint/Interfaces.lean`). -/

/-- AREA REFL: the inclusion of solid objects is a right adjoint. -/
instance instReflProp : isSolid.ι.IsRightAdjoint := Work.REFL.refl_prop

/-- AREA RESOL (from ATOM and TOOLKIT). -/
theorem assembly_resolutionProp : _root_.Submission.Blueprint.ResolutionProp :=
  Work.RESOL.resolution_prop Work.ATOM.atom_prop Work.TOOLKIT.toolkit_prop

/-- AREA DERFORMAL (from RESOL). -/
theorem assembly_derivedProp : _root_.Submission.Blueprint.DerivedProp :=
  Work.DERFORMAL.derived_prop assembly_resolutionProp

/-- The derived package (holes 4–7 are its fields). -/
def assemblyPackage : _root_.Submission.Blueprint.DerivedPackage :=
  assembly_derivedProp.1.some

/-- AREA CWIND (hole 10 input), with all eight hypotheses discharged by the area deliverables. -/
theorem assembly_cwIsoProp : _root_.Submission.Blueprint.CWIsoProp :=
  Work.CWIND.cwIso_prop assembly_derivedProp assembly_resolutionProp Work.TOOLKIT.toolkit_prop
    Work.ANALYTIC.hi_prop Work.DISC.disc_prop Work.CONDMV.condMV_prop Work.SingMV.singMV_prop
    Work.CWTOP.cwTop_prop

/-- **Hole 1.** The solidification functor, left adjoint to the inclusion of solid objects. -/
def solidification : LightCondAb ⥤ Solid := isSolid.ι.leftAdjoint

/-- **Hole 2.** The solidification functor is additive.  (This follows from the adjunction of the
next hole, but is needed as an instance to state the holes below.) -/
instance solidification_additive : solidification.Additive :=
  _root_.Submission.Blueprint.sol_additive

/-- **Hole 3.** The solidification adjunction: solidification is left adjoint to the inclusion of
solid objects in light condensed abelian groups. -/
def solidificationAdjunction : solidification ⊣ isSolid.ι :=
  _root_.Submission.Blueprint.solAdj

/-- **Hole 4.** The derived solidification functor. -/
def derivedSolidification : DLightCondAb ⥤ DSolid := assemblyPackage.L

/-- **Hole 5.** The comparison map from derived solidification to degreewise solidification. -/
def derivedSolidificationCounit :
    DerivedCategory.Q ⋙ derivedSolidification ⟶
      solidification.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  assemblyPackage.α

/-- **Hole 6.** Derived solidification, together with the comparison map of the previous hole, is
the total left derived functor of degreewise solidification followed by localization. -/
instance derivedSolidification_isLeftDerivedFunctor :
    derivedSolidification.IsLeftDerivedFunctor derivedSolidificationCounit
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) :=
  assemblyPackage.isLeft

/-- The inclusion of solid abelian groups, applied degreewise to cochain complexes. -/
abbrev inclusionComplexes :
    CochainComplex Solid ℤ ⥤ CochainComplex LightCondAb ℤ :=
  isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ)



/-- The derived inclusion is induced by applying the inclusion degreewise to complexes. -/
abbrev derivedInclusionFactors :
    DerivedCategory.Q ⋙ derivedInclusion ≅ inclusionComplexes ⋙ DerivedCategory.Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- The comparison map exhibiting `derivedInclusion` as a right derived functor of the degreewise
inclusion. -/
abbrev derivedInclusionComparison :
    inclusionComplexes ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ derivedInclusion :=
  derivedInclusionFactors.inv

/-- The exact derived inclusion is the right derived functor of the degreewise inclusion. -/
instance derivedInclusion_isRightDerivedFunctor :
    derivedInclusion.IsRightDerivedFunctor derivedInclusionComparison
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) derivedInclusion
    derivedInclusionFactors

/-- **Hole 7.** The derived solidification adjunction: derived solidification is left adjoint to
the derived inclusion. -/
def derivedSolidificationAdjunction : derivedSolidification ⊣ derivedInclusion :=
  assemblyPackage.adj











/-- The integral singular chain complex of a topological space as a derived object. -/
abbrev singularChainsLightCondAbDerived (X : TopCat) : DLightCondAb :=
  singularChainsLightCondAbDerivedFunctor.obj X





namespace CWTopCat

instance (X : CWTopCat) : T2Space X.obj := X.property.1

instance (X : CWTopCat) : Topology.CWComplex (Set.univ : Set X.obj) :=
  Classical.choice X.property.2



end CWTopCat

/-! ### Universe bookkeeping for hole 8

The challenge statement of hole 8 is universe polymorphic (`CWTopCat.{u_1} ⥤ DLightCondAb`),
while the free light condensed abelian group is only defined on `TopCat.{0}`.  Hole 8 is therefore
defined for every universe by transporting a space along `Shrink.{0}` whenever `UnivLE.{u, 0}`
holds (and is a constant functor otherwise).  At universe `0`, which is the only universe at which
holes 9–12 use it, `UnivLE.{0, 0}` holds and hole 9 identifies it with the expected composite. -/

/-- Topology on `Shrink X` transported along `equivShrink`. -/
abbrev shrinkTopology (X : TopCat.{u}) [Small.{0} X] : TopologicalSpace (Shrink.{0} X) :=
  TopologicalSpace.induced (equivShrink X).symm inferInstance

/-- Shrinking topological spaces along `UnivLE.{u, 0}`. -/
def shrinkTop [UnivLE.{u, 0}] : TopCat.{u} ⥤ TopCat.{0} where
  obj X := @TopCat.of (Shrink.{0} X) (shrinkTopology X)
  map {X Y} f := @TopCat.ofHom _ _ (shrinkTopology X) (shrinkTopology Y)
    ⟨fun x => equivShrink Y (f ((equivShrink X).symm x)), by
      let _ := shrinkTopology X; let _ := shrinkTopology Y
      apply continuous_induced_rng.2
      simpa [Function.comp_def] using f.hom.continuous.comp continuous_induced_dom⟩
  map_id X := by ext x; simp
  map_comp f g := by ext x; simp

/-- The shrinking homeomorphism. -/
def shrinkHomeo (X : TopCat.{0}) : (shrinkTop.obj X) ≃ₜ X :=
  letI := shrinkTopology X
  (equivShrink X).symm.toHomeomorphOfIsInducing (Topology.IsInducing.induced _)

/-- At universe `0`, shrinking is isomorphic to the identity. -/
def shrinkTopIso : shrinkTop.{0} ≅ 𝟭 TopCat.{0} :=
  NatIso.ofComponents (fun X => TopCat.isoOfHomeo (shrinkHomeo X)) (by
    intro X Y f; ext x
    change (equivShrink Y).symm ((equivShrink Y) (f ((equivShrink X).symm x))) =
      f ((equivShrink X).symm x)
    simp)

open scoped Classical in
/-- The universe-polymorphic functor underlying hole 8. -/
def freeCWAux : CWTopCat.{u} ⥤ DLightCondAb :=
  if h : UnivLE.{u, 0} then
    haveI := h
    CWTopCat.toTopCat ⋙ shrinkTop ⋙ freeLightCondAbOfTopFunctor ⋙
      DerivedCategory.singleFunctor LightCondAb 0 ⋙ derivedSolidification ⋙ derivedInclusion
  else
    (Functor.const _).obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
      (freeLightCondAbOfTop (TopCat.of PEmpty)))

open scoped Classical in
theorem freeCWAux_zero : freeCWAux.{0} =
    CWTopCat.toTopCat ⋙ shrinkTop ⋙ freeLightCondAbOfTopFunctor ⋙
      DerivedCategory.singleFunctor LightCondAb 0 ⋙ derivedSolidification ⋙ derivedInclusion := by
  unfold freeCWAux
  rw [dif_pos (inferInstance : UnivLE.{0, 0})]

/-- **Hole 8.** The functor sending a CW complex to the derived inclusion of the derived
solidification of the free light condensed abelian group on it. -/
def derivedSolidificationFreeCWFunctor : CWTopCat ⥤ DLightCondAb := freeCWAux

/-- **Hole 9.** The specification identifying `derivedSolidificationFreeCWFunctor` with the
expected composite functor. -/
def derivedSolidificationFreeCWFunctorSpec :
    derivedSolidificationFreeCWFunctor ≅
      CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙
        derivedSolidification ⋙ derivedInclusion :=
  eqToIso freeCWAux_zero ≪≫
    Functor.isoWhiskerLeft CWTopCat.toTopCat
      (Functor.isoWhiskerRight shrinkTopIso _ ≪≫ Functor.leftUnitor _)



/-- **Hole 10.** The derived comparison theorem, naturally in a CW complex `X`: after applying the
exact derived inclusion from solid light condensed abelian groups to light condensed abelian groups,
the derived solidification of the free light condensed abelian group on `X` is the integral singular
chain complex of `X` as a derived object of light condensed abelian groups. -/
def derivedSolidification_free_CW_derivedNatIso :
    derivedSolidificationFreeCWFunctor ≅ singularChainsLightCondAbCWDerivedFunctor :=
  derivedSolidificationFreeCWFunctorSpec ≪≫ (assembly_cwIsoProp assemblyPackage).some

/-- The pointwise component of `derivedSolidification_free_CW_derivedNatIso`. -/
def derivedSolidification_free_CW_derivedIso
    (X : TopCat) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] :
    derivedInclusion.obj
      (derivedSolidification.obj
        ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X))) ≅
      singularChainsLightCondAbDerived X :=
  (derivedSolidificationFreeCWFunctorSpec.app ⟨X, inferInstance, ⟨inferInstance⟩⟩).symm.trans
    (derivedSolidification_free_CW_derivedNatIso.app ⟨X, inferInstance, ⟨inferInstance⟩⟩)

/-- **Hole 11.** For a CW complex `X`, the homology of the derived solidification of the free
light condensed abelian group on `X` is integral singular homology.  Since the derived category
is cohomologically indexed, the `n`-th singular homology group occurs in degree `-n`. -/
def derivedSolidification_free_CW_homologyIso
    (X : TopCat) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    isSolid.ι.obj
      ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
        (derivedSolidification.obj
          ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X)))) ≅
      singularHomologyLightCondAb X n :=
  (Work.HOMOL.homology_prop.2 _ _).some ≪≫
    (DerivedCategory.homologyFunctor LightCondAb (-(n : ℤ))).mapIso
      (derivedSolidification_free_CW_derivedIso X) ≪≫
    (Work.HOMOL.homology_prop.1 X n).some

/-- **Hole 12.** The theorem form of `derivedSolidification_free_CW_homologyIso`: the derived
solidification of the free light condensed abelian group on a CW complex computes integral
singular homology. -/
theorem derivedSolidification_free_CW_homology
    (X : TopCat) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Nonempty
      (isSolid.ι.obj
        ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
          (derivedSolidification.obj
            ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X)))) ≅
        singularHomologyLightCondAb X n) :=
  ⟨derivedSolidification_free_CW_homologyIso X n⟩

end Solid

end LightCondensed

end

end Submission
