import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map

/-!
# DSG1 (area G1): transfer of splittings along a morphism `X' ⟶ X`

This is the base layer of the area `G1` of the direct-summand proof map
(`sources/dsmap/direct_summand_proof_map.md`, and the review
`sources/dsmap/direct_summand_proof_map_REVIEW.md`).

The vocabulary (`DSMap.phi`, `DSMap.GammaA`, `DSMap.RG`, `DSMap.rgUnit`, `DSMap.DSplit`, ...)
lives in the frozen file `Submission/Work/DSMap/Map.lean` and is imported, never redefined.

Contents of this file:

* `Work.DSG1.gammaMap`: the restriction `Γ(X,⊤) →+* Γ(X',⊤)` along `g : X' ⟶ X`.
* `Work.DSG1.phi_comp`: the structure map `A →+* Γ(X',⊤)` of `g ≫ f` is the structure map of
  `f` followed by that restriction.  This is the compatibility of the two `A`-algebra structures
  which makes the transfer possible at all.
* `Work.DSG1.transfer`: the purely formal core of area `G1`: a morphism
  `φ : RG A X f ⟶ RG A X' (g ≫ f)` carrying the challenge unit of `X` to the challenge unit of
  `X'` retracts the challenge unit of `X` as soon as the one of `X'` is split.  Everything
  specific to the geometry is hidden in the *construction* of `φ`.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSG1

universe u v w w₁ w₂ w₃

section Phi

variable {A : Type u} [CommRing A]

/-- The restriction map `Γ(X, ⊤) →+* Γ(X', ⊤)` associated with a morphism `g : X' ⟶ X`. -/
noncomputable def gammaMap {X X' : Scheme.{u}} (g : X' ⟶ X) : Γ(X, ⊤) →+* Γ(X', ⊤) :=
  (Scheme.Hom.appTop g).hom

@[simp]
lemma gammaMap_apply {X X' : Scheme.{u}} (g : X' ⟶ X) (a : Γ(X, ⊤)) :
    gammaMap g a = Scheme.Hom.appTop g a := rfl

/-- `γ` as a morphism of `CommRingCat` is the opposite of the functoriality map of `Scheme.Γ`. -/
lemma gammaMap_op {X X' : Scheme.{u}} (g : X' ⟶ X) :
    (Scheme.Hom.appTop g).op = Scheme.Γ.rightOp.map g := by
  rw [Functor.rightOp_map, Scheme.Γ_map_op]
  rfl

/-- `γ` is the underlying map of the functoriality of `Scheme.Γ`. -/
lemma gammaMap_unop {X X' : Scheme.{u}} (g : X' ⟶ X) :
    Quiver.Hom.unop (Scheme.Γ.rightOp.map g) = Scheme.Hom.appTop g := by
  rw [Functor.rightOp_map, Scheme.Γ_map_op]
  rfl

/-- **Compatibility of the `A`-algebra structures.**  For `f : X ⟶ Spec A` and `g : X' ⟶ X`,
the structure map `A →+* Γ(X', ⊤)` of the composite `g ≫ f` is the structure map of `f`
followed by the restriction along `g`. -/
theorem phi_comp {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (g : X' ⟶ X) :
    DSMap.phi A X' (g ≫ f) = (gammaMap g).comp (DSMap.phi A X f) := by
  let φ : CommRingCat.of A ⟶ Γ(X, ⊤) :=
    Quiver.Hom.unop ((ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f)
  let ψ : CommRingCat.of A ⟶ Γ(X', ⊤) :=
    Quiver.Hom.unop ((ΓSpec.adjunction.homEquiv X' (Opposite.op (CommRingCat.of A))).symm (g ≫ f))
  have hφ : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) φ.op = f :=
    (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).apply_symm_apply f
  have hψ : (ΓSpec.adjunction.homEquiv X' (Opposite.op (CommRingCat.of A))) ψ.op = g ≫ f :=
    (ΓSpec.adjunction.homEquiv X' (Opposite.op (CommRingCat.of A))).apply_symm_apply (g ≫ f)
  have hkey : (ΓSpec.adjunction.homEquiv X' (Opposite.op (CommRingCat.of A)))
      (Scheme.Γ.rightOp.map g ≫ φ.op) = g ≫ f :=
    (ΓSpec.adjunction.homEquiv_naturality_left (Y := Opposite.op (CommRingCat.of A)) g φ.op).trans
      (congrArg (fun t => g ≫ t) hφ)
  have h5 : ψ.op = Scheme.Γ.rightOp.map g ≫ φ.op :=
    (ΓSpec.adjunction.homEquiv X' (Opposite.op (CommRingCat.of A))).injective (hψ.trans hkey.symm)
  have h3 : ψ = φ ≫ Scheme.Hom.appTop g := by
    have h := congrArg Quiver.Hom.unop h5
    simpa [Quiver.Hom.unop_op, gammaMap_unop] using h
  have hcomp : CommRingCat.Hom.hom (φ ≫ Scheme.Hom.appTop g) =
      (gammaMap g).comp (CommRingCat.Hom.hom φ) := by
    rw [CommRingCat.hom_comp]
    rfl
  show CommRingCat.Hom.hom ψ = (gammaMap g).comp (CommRingCat.Hom.hom φ)
  rw [h3, hcomp]

end Phi

section Transfer

variable {A : Type u} [CommRing A]

/-- `R^+(Γ(X,−))(M)`: the right derived functor of global sections evaluated at an arbitrary sheaf
of modules `M` on `X` (so that `RG A X f` is the special case `M = 𝒪_X`). -/
noncomputable abbrev RGof (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (M : SheafOfModules X.ringCatSheaf) : DerivedCategory.Plus (ModuleCat.{u} A) :=
  (DSMap.GammaA A X f).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M)

/-- `RG` is `RGof` at the structure sheaf. -/
lemma RGof_unit (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] :
    RGof A X f (SheafOfModules.unit X.ringCatSheaf) = DSMap.RG A X f := rfl

/-- **The formal core of G1.**  If the challenge unit of `X` factors through the challenge unit
of `X'` (via a morphism `φ` of the bounded below derived categories compatible with the two
units), then a splitting of the unit of `X'` retracts the unit of `X`. -/
theorem transfer {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (g : X' ⟶ X)
    [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    [HasDerivedCategory.{w₃} (SheafOfModules X'.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X'.ringCatSheaf)]
    (φ : DSMap.RG A X f ⟶ DSMap.RG A X' (g ≫ f))
    (hφ : DSMap.rgUnit A X f ≫ φ = DSMap.rgUnit A X' (g ≫ f)) :
    IsSplitMono (DSMap.rgUnit A X' (g ≫ f)) → IsSplitMono (DSMap.rgUnit A X f) := by
  intro h
  obtain ⟨r, hr⟩ := h.exists_splitMono
  exact IsSplitMono.mk' ⟨φ ≫ r, by rw [← Category.assoc, hφ, hr]⟩

/-- `DSplit` transfer, with the comparison map supplied for every choice of the instances of `X`
(the instances of `X'` being fixed). -/
theorem dsplit_of_comparison {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (g : X' ⟶ X)
    [HasDerivedCategory.{w₃} (SheafOfModules X'.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X'.ringCatSheaf)]
    (h : ∀ (_ : HasDerivedCategory.{w₁} (ModuleCat.{u} A))
      (_ : HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      ∃ φ : DSMap.RG A X f ⟶ DSMap.RG A X' (g ≫ f),
        DSMap.rgUnit A X f ≫ φ = DSMap.rgUnit A X' (g ≫ f)) :
    DSMap.DSplit.{u, w₁, w₃} A X' (g ≫ f) → DSMap.DSplit.{u, w₁, w₂} A X f := by
  intro h'
  intro hDC hS hEI
  letI := hDC
  letI := hS
  letI := hEI
  obtain ⟨φ, hφ⟩ := h _ _ _
  exact transfer f g φ hφ (h' _ _ _)

end Transfer

end Work.DSG1
