import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.K3Inputs.Defs
import Submission.Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv
import Submission.Work.CY3Stab.Prod.isDomain_cylTriplet_tensor
import Submission.Work.CY3Stab.Prod.coheight_specTensorTo_bot
import Submission.Work.CY3Stab.Prod.isIntegral_wProd
import Submission.Work.K3.eq_genericPoint_of_coheight_eq_zero
import Submission.Work.CY3.resEquiv_genericPoint_birationalMap
import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.Cylinder
import Submission.Work.K3Inputs.cylFieldAlgEquiv
import Submission.Work.K3Inputs.cylIsoPullbackAffineLine
import Submission.Work.CrauderKatz.residueField_genericPoint_resAlgEquiv
import Submission.Work.CY3Stab.Variety
import Submission.Work.Totaro.stablyBirational_instance_independent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.CylResEquivAux`

Auxiliary lemmas for `Work.CY3Stab.Prod.stablyBirational_of_resEquiv_cyl_of_p1Bundle`:

* `coheight_genericPoint_eq_zero` — the generic point of an irreducible scheme has coheight zero;
* `prodPt_genericPoint` — **the cylinder point over the generic point is the generic point of the
  cylinder** (coheight computation + `Work.K3.eq_genericPoint_of_coheight_eq_zero`);
* `resEquiv_of_iso` — an isomorphism of `𝕜`-schemes induces a `ResEquiv` between corresponding
  points;
* `resAlgEquiv_comp`, `resEquiv_of_resAlgEquiv`, `resAlgEquiv_of_resEquiv` — the elementary
  transports between `ResEquiv` and `ResAlgEquiv`.
-/


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The generic point of an irreducible scheme has coheight zero** (with respect to the
specialisation order). -/
theorem coheight_genericPoint_eq_zero {X : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X] :
    Order.coheight (genericPoint X) = 0 := by
  rw [Order.coheight_eq_zero]
  intro b _
  rw [Scheme.le_iff_specializes]
  exact genericPoint_specializes b

/-- **The cylinder point over the generic point is the generic point of the cylinder.**  For an
integral, locally noetherian `𝕜`-scheme `X` and `m : ℕ`, the point `prodPt X (genericPoint X) m` of
`𝔸ᵐ × X` — the generic point of the `Triplet` fibre over `(genericPoint 𝔸ᵐ, genericPoint X)` — is
the generic point of `𝔸ᵐ × X`.

Both points have coheight `0`: for `prodPt` this is the local computation
`Work.CY3Stab.Prod.coheight_specTensorTo_bot` (`coheight (prodPt X x m) = coheight x`), and
`coheight (genericPoint X) = 0` for an irreducible `X`; a point of coheight zero in an irreducible
scheme is the generic point (`Work.K3.eq_genericPoint_of_coheight_eq_zero`). -/
theorem prodPt_genericPoint (𝕜 : Type) [Field 𝕜] {X : AlgebraicGeometry.Scheme.{0}}
    [X.Over (Spec (CommRingCat.of 𝕜))] [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ)
    [hD : IsDomain (cylTriplet (𝕜 := 𝕜) X (genericPoint X) m).tensor]
    [IrreducibleSpace (WProd (𝕜 := 𝕜) X m)] :
    prodPt (𝕜 := 𝕜) X (genericPoint X) m = genericPoint (WProd (𝕜 := 𝕜) X m) := by
  have hco : Order.coheight ((cylTriplet (𝕜 := 𝕜) X (genericPoint X) m).SpecTensorTo
      (⊥ : PrimeSpectrum (cylTriplet (𝕜 := 𝕜) X (genericPoint X) m).tensor)) =
      Order.coheight (genericPoint X) := by
    exact Work.CY3Stab.Prod.coheight_specTensorTo_bot (n := Fin m) (X := X)
      (x := genericPoint X) (T := cylTriplet (𝕜 := 𝕜) X (genericPoint X) m) rfl rfl
  have hc : Order.coheight (prodPt (𝕜 := 𝕜) X (genericPoint X) m) = 0 := by
    change Order.coheight ((cylTriplet (𝕜 := 𝕜) X (genericPoint X) m).SpecTensorTo
      (⊥ : PrimeSpectrum (cylTriplet (𝕜 := 𝕜) X (genericPoint X) m).tensor)) = 0
    rw [hco]
    exact coheight_genericPoint_eq_zero
  exact Work.K3.eq_genericPoint_of_coheight_eq_zero _ hc

/-! ## 2. Elementary transports of `ResEquiv` and `ResAlgEquiv` -/

/-- An isomorphism of `𝕜`-schemes induces a `ResEquiv` between corresponding points. -/
lemma resEquiv_of_iso {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))]
    [Y.Over (Spec (CommRingCat.of 𝕜))] (e : X ≅ Y) [e.hom.IsOver (Spec (CommRingCat.of 𝕜))]
    (x : X) : ResEquiv 𝕜 x (e.hom x) := by
  have hf : e.hom ≫ (Y ↘ Spec (CommRingCat.of 𝕜)) = (X ↘ Spec (CommRingCat.of 𝕜)) :=
    CategoryTheory.comp_over e.hom (Spec (CommRingCat.of 𝕜))
  have : IsIso (e.hom.residueFieldMap x) := by infer_instance
  exact Work.Motivic.ResEquiv.symm (Work.Motivic.resEquiv_of_morphism (𝕜 := 𝕜) e.hom hf x)

/-- `ResAlgEquiv` is transported along a ring isomorphism of the presenting fields. -/
lemma resAlgEquiv_comp {𝕜 : Type} [Field 𝕜] {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))]
    (x : X) {A B : Type} [Field A] [Field B] (φ : 𝕜 →+* A) (ψ : 𝕜 →+* B) (e : A ≃+* B)
    (he : e.toRingHom.comp φ = ψ) (h : Work.LLink.ResAlgEquiv 𝕜 x A φ) :
    Work.LLink.ResAlgEquiv 𝕜 x B ψ := by
  obtain ⟨e', he'⟩ := h
  exact ⟨e'.trans e, by rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, he', he]⟩

/-- Two points presented by the same `𝕜`-field have `𝕜`-isomorphic residue fields. -/
lemma resEquiv_of_resAlgEquiv {𝕜 : Type} [Field 𝕜] {X Z : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of 𝕜))] [Z.Over (Spec (CommRingCat.of 𝕜))] {x : X} {z : Z}
    {A : Type} [Field A] {φ : 𝕜 →+* A} (hx : Work.LLink.ResAlgEquiv 𝕜 x A φ)
    (hz : Work.LLink.ResAlgEquiv 𝕜 z A φ) : ResEquiv 𝕜 x z := by
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨ez, hez⟩ := hz
  refine ⟨ex.trans ez.symm, ?_⟩
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, hex]
  rw [← hez]
  ext a
  simp

/-- `ResEquiv` composes with `ResAlgEquiv` on the right. -/
lemma resAlgEquiv_of_resEquiv {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of 𝕜))] [Y.Over (Spec (CommRingCat.of 𝕜))] {x : X} {y : Y}
    {A : Type} [Field A] {φ : 𝕜 →+* A} (h : ResEquiv 𝕜 x y)
    (hy : Work.LLink.ResAlgEquiv 𝕜 y A φ) : Work.LLink.ResAlgEquiv 𝕜 x A φ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := hy
  refine ⟨e.trans e', ?_⟩
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, he, he']


end

end Work.CY3Stab.Prod
