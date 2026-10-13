import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG4a: flat base change of the Čech model — geometric vocabulary

This file fixes the vocabulary for the *base change* half of the local-to-global area `G4a`
(see `NOTES.md`, item 3): the pullback `X_{A'} = X ×_{Spec A} Spec A'` of `f : X ⟶ Spec A`
along `Spec A' ⟶ Spec A`, its two projections, and the preimage of an open of `X`.

Everything here is notation-free in its *statements* (the scoped notation `f ⁻¹ᵁ U` is only
used inside definitions), so that the lemmas of the next files can be stated and proved
without any `open` necessary.

The intended content, following the design of the area in
`sources/dsmap/direct_summand_proof_map.md` §4 ("`P ⊗ A'` models `Č(X_{A'})`, because the
Čech terms base-change exactly for affine opens and `A'` is flat") is:

* `sectionBaseChange` : the canonical comparison `Γ(X,U) ⊗[A] A' ⟶ Γ(X_{A'}, U_{A'})`;
* it is an isomorphism for `U` affine (affine base change), naturally in `U`;
* hence the Čech complex of the pulled-back affine cover is the base change of the Čech
  complex of the cover, which is what discharges the hypothesis `hbc` of
  `area_G4a_localGlobal_of_models` once the areas `F1` and `COH` provide the model.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG4a

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- The morphism `Spec A' ⟶ Spec A` induced by an algebra structure. -/
noncomputable abbrev specAlgebraMap : Spec (.of A') ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

/-- The base change `X_{A'} = X ×_{Spec A} Spec A'` of `f : X ⟶ Spec A`. -/
noncomputable abbrev baseChangeScheme (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) : Scheme.{u} :=
  pullback f (specAlgebraMap (A := A) (A' := A'))

/-- The projection `X_{A'} ⟶ X` of the base change. -/
noncomputable abbrev baseChangeFst (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    baseChangeScheme (A := A) (A' := A') X f ⟶ X :=
  pullback.fst f (specAlgebraMap (A := A) (A' := A'))

/-- The projection `X_{A'} ⟶ Spec A'` of the base change. -/
noncomputable abbrev baseChangeSnd (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    pullback f (specAlgebraMap (A := A) (A' := A')) ⟶ Spec (.of A') :=
  pullback.snd f (specAlgebraMap (A := A) (A' := A'))

/-- The preimage in `X_{A'}` of an open of `X`. -/
noncomputable abbrev baseChangeOpen (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) :
    (pullback f (specAlgebraMap (A := A) (A' := A'))).Opens :=
  (pullback.fst f (specAlgebraMap (A := A) (A' := A'))) ⁻¹ᵁ U

/-- The preimage of an open under a morphism of schemes (notation-free form of `g ⁻¹ᵁ U`). -/
noncomputable abbrev preimageOpen {X X' : Scheme.{u}} (g : X' ⟶ X) (U : X.Opens) : X'.Opens :=
  g ⁻¹ᵁ U

/-- The restriction map `Γ(X,U) ⟶ Γ(X,V)` for `V ≤ U` (notation-free). -/
noncomputable abbrev resLE {X : Scheme.{u}} {V U : X.Opens} (h : V ≤ U) : Γ(X, U) ⟶ Γ(X, V) :=
  X.presheaf.map (homOfLE h).op

/-- The composite `X' ⟶ X ⟶ Spec A`. -/
noncomputable abbrev compToSpec {X X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Spec (.of A)) :
    X' ⟶ Spec (.of A) :=
  g ≫ f

end Work.DSG4a
