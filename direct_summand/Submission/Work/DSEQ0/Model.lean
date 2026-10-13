import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.Basic

/-!
# DSEQ0 (area EQ0): the chain-model criterion for derived splitting

This module isolates the *derived-category* half of the equal-characteristic-zero
argument (area `EQ0` of `sources/dsmap/direct_summand_proof_map.md`, §5 and §4).

The frozen area `DSMap.area_F1_cech` produces, for a finite affine cover of `X`, a chain map
`cc : A[0] ⟶ cechZ` and an isomorphism `e : ι (RG) ≅ Q (cechZ)` intertwining the challenge
unit with `Q cc`.  The area `EQ0` has to *retract* `cc` at the level of chain complexes: this
is what the trace on a perfect model `RΓ(X,𝒪)` does.  The two halves are glued here.

The main theorem `Work.DSEQ0.isSplitMono_of_chainModel` states: if the challenge unit, read in
the derived category through the Čech model isomorphism `e`, is `Q c` for a chain map
`c : A[0] ⟶ P`, and if `c` has a chain-level retraction `φ : P ⟶ A[0]`, then the challenge
unit is a split monomorphism.  Nothing else is used: no finiteness, no projectivity, no
regularity.  All of that is hidden in the *construction* of `P`, `c`, `φ`.

The rest of the area (construction of the model and of `φ`) is in the modules
`Submission.Work.DSEQ0.Trace` and `Submission.Work.DSEQ0.Main`.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe u v w w₁ w₂ w₃

variable (A : Type u) [CommRing A]

/-- `A` as a cochain complex concentrated in degree `0`; this is the source of the frozen
Čech model map `DSMap.area_F1_cech`. -/
noncomputable abbrev singleZ : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

/-- The canonical isomorphism `Plus.singleFunctor 0 (A) ≅ Q (singleZ)`, i.e. the composite
appearing in the second clause of the frozen statement `DSMap.area_F1_cech`. -/
noncomputable def singleIsoCompQ [HasDerivedCategory (ModuleCat.{u} A)] :
    DerivedCategory.Plus.ι.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      DerivedCategory.Q.obj (singleZ A) :=
  (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} A) 0).app (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)

/-- **The chain-model criterion.**  If the challenge unit is, under the model isomorphism
`e`, the image under `Q` of a chain map `c : A[0] ⟶ P`, and `c` is retracted on the chain level
by `φ : P ⟶ A[0]`, then the challenge unit is a split monomorphism in the (bounded below)
derived category. -/
theorem isSplitMono_of_chainModel [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (c : singleZ A ⟶ P) (φ : P ⟶ singleZ A)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅ DerivedCategory.Q.obj P)
    (hF1 : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map c)
    (hφ : c ≫ φ = 𝟙 (singleZ A)) :
    IsSplitMono (DSMap.rgUnit A X f) := by
  have key : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫
      (e.hom ≫ DerivedCategory.Q.map φ ≫ (singleIsoCompQ A).inv) = 𝟙 _ := by
    rw [← Category.assoc, hF1]
    nth_rewrite 1 [← Category.assoc]
    nth_rewrite 2 [Category.assoc]
    rw [← DerivedCategory.Q.map_comp, hφ, DerivedCategory.Q.map_id, Category.comp_id,
      Iso.hom_inv_id]
  obtain ⟨r, hr⟩ := DerivedCategory.Plus.ι.map_surjective
    (e.hom ≫ DerivedCategory.Q.map φ ≫ (singleIsoCompQ A).inv)
  refine IsSplitMono.mk' ⟨r, DerivedCategory.Plus.ι.map_injective ?_⟩
  rw [Functor.map_comp, hr, key]
  simp

/-- **The chain-model criterion, in the form of `DSplit`.**  The hypotheses are exactly the
output of the frozen `DSMap.area_F1_cech` (`cc` and `e` together with its compatibility
clause) plus a chain-level retraction of `cc` on any model complex `P`. -/
theorem dsplit_of_chainModel (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (h : ∀ (_ : HasDerivedCategory.{w₁} (ModuleCat.{u} A))
      (_ : HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      IsSplitMono (DSMap.rgUnit A X f)) :
    DSMap.DSplit.{u, w₁, w₂} A X f := h

end Work.DSEQ0
