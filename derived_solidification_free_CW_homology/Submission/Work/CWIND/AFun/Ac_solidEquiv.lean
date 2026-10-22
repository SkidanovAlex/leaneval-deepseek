import Mathlib
import Submission.Work.CWIND.AFun.Setup

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.AFun

/-- **CWIND/T4-b.** The comparison map `Ac X : ℤ[X] ⟶ Aconst X` is a solid-equivalence.
Proof route: `Ac X = (E' X).hom ≫ sE X` by definition (`Work.CWIND.AFun.Ac_eq`), where `E' X` is
Mathlib's isomorphism `extendSingleIso` between the single cochain complex on `ℤ[X]` and the
extension of the single chain complex on `ℤ[X]`, and `sE X = extendMap (chEquiv X).inv` is the
extension of `(chEquiv X).inv`, the inverse of the extra-degeneracy homotopy equivalence
`chEquiv X : AchainConst X ≃ (single₀ ℤ[X])` of `Work.CWIND.AFun`.  A composite of isomorphisms in
`D(LightCondAb)` is an isomorphism, so `ToolkitProp.of_iso` concludes.  For the second factor use
`NatIso.isIso_map_iff (ComplexShape.Embedding.extendHomotopyFunctorFactors
ComplexShape.embeddingDownNat LightCondAb)` together with
`HomotopyCategory.isoOfHomotopyEquiv (chEquiv X)` (whose `inv` is
`(HomotopyCategory.quotient _ _).map (chEquiv X).inv`) to see that
`(HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map (sE X)` is an isomorphism, then
`DerivedCategory.quotientCompQhIso` to pass to `DerivedCategory.Q`. -/
theorem Ac_solidEquiv (hTK : Submission.Blueprint.ToolkitProp) (X : TopCat.{0}) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.Q).map (Work.CWIND.AFun.Ac X)) := by
  refine hTK.of_iso _ ?_
  rw [Work.CWIND.AFun.Ac_eq, Functor.map_comp]
  -- The first factor `(E' X).hom` is an isomorphism of complexes, hence so is its image in `D`.
  have hE : IsIso ((DerivedCategory.Q).map (Work.CWIND.AFun.E' X).hom) := inferInstance
  -- The second factor `sE X = extendMap (chEquiv X).inv embeddingDownNat`.
  have hS : IsIso ((DerivedCategory.Q).map (Work.CWIND.AFun.sE X)) := by
    rw [Work.CWIND.AFun.sE]
    -- `(chEquiv X).inv` is a homotopy equivalence; extending along the shape embedding
    -- `down ℕ ↪ up ℤ` preserves homotopy equivalences.
    have h1 : HomologicalComplex.homotopyEquivalences LightCondAb (ComplexShape.down ℕ)
        (Work.CWIND.AFun.chEquiv X).inv :=
      HomotopyEquiv.homotopyEquivalences_inv (Work.CWIND.AFun.chEquiv X)
    have h2 : HomologicalComplex.homotopyEquivalences LightCondAb (ComplexShape.up ℤ)
        (HomologicalComplex.extendMap (Work.CWIND.AFun.chEquiv X).inv
          ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.homotopyEquivalences_extendMap_iff _
        ComplexShape.embeddingDownNat).mpr h1
    -- Homotopy equivalences are quasi-isomorphisms, and `Q` inverts quasi-isomorphisms.
    exact HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences LightCondAb
      (ComplexShape.up ℤ)
      (HomologicalComplex.extendMap (Work.CWIND.AFun.chEquiv X).inv
        ComplexShape.embeddingDownNat) h2
  exact IsIso.comp_isIso' hE hS

end Work.CWIND.AFun
