import Mathlib
import Submission.Work.DSMap.Mix2Fix
import Submission.Work.DSM8m2.Algebra.finiteDimensional_of_finite_isFractionRing

/-!
# The function field of a generically finite integral scheme over a domain

Let `A` be a domain and `f : X ⟶ Spec A` a surjective morphism from an integral scheme `X`
which is finite over a basic open `D(g) ⊆ Spec A` (`g ≠ 0`, `DSMap.IsGenFinite`).  Then the
function field `K(X)` is a finite extension of `Frac A`.

The proof: put `U = D(g)` and `V = f⁻¹U`.  Since `f` is finite over the affine open `U`, `V` is
affine and `Γ(X, V)` is a finite module over `Γ(Spec A, U) ≅ A[1/g]`, whose fraction field is
`Frac A`; moreover `Γ(X, V)` is a domain with fraction field `K(X)`.  The abstract lemma
`Work.DSM8m2.Algebra.finiteDimensional_of_finite_isFractionRing` then finishes the argument.

The one scheme-theoretic input beyond Mathlib's API is the compatibility of the `A`-algebra
structure on `K(X)` (given by the hypothesis `hφ` of the theorem) with the `A`-algebra structure
on the sections of `O_{Spec A}` on `D(g)`: this is `germ_comp_app_Dspec` below.
-/

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Work.DSM8m2.Zariski

universe u

/-! ## Auxiliary lemmas -/

/-- Sections of `O_{Spec A}` on an open set, in the presentation used by `StructureSheaf`
(the `A`-algebra structure on the sections and the localization structure on a basic open are
both stated in this presentation). -/
abbrev specSections (A : Type u) [CommRing A] (U : (Spec (CommRingCat.of A)).Opens) : Type u :=
  ↥((Spec.structureSheaf (CommRingCat.of A)).obj.obj (op U))

/-- Being a basic open, `D(g)` is affine. -/
theorem isAffineOpen_Dspec {A : Type u} [CommRing A] (g : A) :
    IsAffineOpen (X := Spec (CommRingCat.of A))
      (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of A)).Opens) :=
  IsAffineOpen.Spec_basicOpen (R := CommRingCat.of A) g

/-- `RingHom.Finite` is preserved by composing on the left with a ring isomorphism. -/
theorem finite_of_comp_ringEquiv {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    (e : C ≃+* D) {g : B →+* C} (h : (e.toRingHom.comp g).Finite) : g.Finite := by
  let : Algebra B C := g.toAlgebra
  let : Algebra B D := (e.toRingHom.comp g).toAlgebra
  haveI hD : Module.Finite B D := h
  have hlin : ∀ (a : B) (b : C), e (a • b) = a • e b := by
    intro a b
    show e (g a * b) = e (g a) * e b
    rw [map_mul]
  let ee : C ≃ₗ[B] D := { e.toAddEquiv with map_smul' := hlin }
  exact Module.Finite.equiv ee.symm

/-- For an affine open `U` of the target, `IsFinite (f ∣_ U)` gives finiteness of the induced
map on sections `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`. -/
theorem finite_app_of_isFinite_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) [IsFinite (f ∣_ U)] : (f.app U).hom.Finite := by
  haveI : IsAffine (U : Scheme) := hU
  have h0 : ((f ∣_ U).app ⊤).hom.Finite := IsFinite.finite_app (f ∣_ U) ⊤ (isAffineOpen_top _)
  have h1 : ((f ∣_ U).appTop).hom.Finite := h0
  rw [morphismRestrict_appTop] at h1
  have h2 : ((X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op).hom.comp
      (Scheme.Hom.app f (U.ι ''ᵁ ⊤)).hom).Finite := h1
  have hbij : Function.Bijective
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op).hom := by
    haveI : IsIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) :=
      Functor.map_isIso _ _
    exact ConcreteCategory.bijective_of_isIso _
  have heq : (RingEquiv.ofBijective
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op).hom hbij).toRingHom
      = (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op).hom := rfl
  have h3 : (Scheme.Hom.app f (U.ι ''ᵁ ⊤)).hom.Finite :=
    finite_of_comp_ringEquiv _ (by rw [heq]; exact h2)
  rw [Scheme.Opens.ι_image_top] at h3
  exact h3

section PhiEq

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `DSMap.phi A X f` is `f.appTop` composed with the inverse of the canonical isomorphism
`Γ(Spec A, ⊤) ≅ A`. -/
theorem phi_eq_appTop_apply (a : A) :
    DSMap.phi A X f a = (f.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hkey : (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of A)))
      (CommRingCat.ofHom (DSMap.phi A X f)).op = f := Equiv.apply_symm_apply _ _
  have h := ΓSpec_adjunction_homEquiv_eq (X := X) (B := CommRingCat.of A)
    (CommRingCat.ofHom (DSMap.phi A X f))
  rw [hkey] at h
  rw [h]
  simp

/-- The `A`-algebra structure on the sections of `O_{Spec A}` on `⊤` is `ΓSpecIso.inv`. -/
theorem algebraMap_specSections_top :
    (algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens)))
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  rw [Scheme.ΓSpecIso_inv]
  rfl

end PhiEq

section BasicOpen

variable {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}} [IsIntegral X]

/-- The basic open `D(g)` of `Spec A`. -/
abbrev Dspec (g : A) : (Spec (CommRingCat.of A)).Opens :=
  (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of A)).Opens)

variable (f : X ⟶ Spec (.of A))

/-- The generic point of an integral scheme mapping surjectively to the spectrum of a domain maps
to the generic point. -/
theorem map_genericPoint_eq (hs : Function.Surjective f) :
    f (genericPoint X) = genericPoint (Spec (.of A)) := by
  have h : IsGenericPoint (f (genericPoint X)) (Set.univ : Set (Spec (.of A))) := by
    have h := (genericPoint_spec X).image f.continuous
    rwa [Set.image_univ, Function.Surjective.range_eq hs, closure_univ] at h
  exact h.eq (genericPoint_spec _)

variable {g : A}

/-- The generic point of `X` lies over `D(g)`. -/
theorem mem_preimage_Dspec_genericPoint (hg : g ≠ 0) (hs : Function.Surjective f) :
    genericPoint X ∈ f ⁻¹ᵁ Dspec g := by
  rw [Scheme.Hom.mem_preimage, map_genericPoint_eq f hs, genericPoint_eq_bot_of_affine]
  show g ∉ (⊥ : Ideal A)
  simp [hg]

/-- The preimage of `D(g)` is nonempty. -/
theorem nonempty_preimage_Dspec (hg : g ≠ 0) (hs : Function.Surjective f) :
    Nonempty (f ⁻¹ᵁ Dspec g) := by
  let p : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hgmem : g ∉ p.asIdeal := by
    change g ∉ (⊥ : Ideal A); simpa using hg
  obtain ⟨x, hx⟩ := hs p
  refine ⟨⟨x, ?_⟩⟩
  rw [Scheme.Hom.mem_preimage, hx]
  exact hgmem

/-- `Γ(Spec A, D(g)) ⟶ Γ(X, f ⁻¹ᵁ D(g)) ⟶ K(X)` sends the image of `a ∈ A` in `Γ(Spec A, D(g))`
to the image of `a` in `K(X)`, where the `A`-algebra structure on `K(X)` is the one induced by
`DSMap.phi` (as in the hypothesis `hφ` of the main theorem). -/
theorem germ_comp_app_Dspec [Nonempty (⊤ : X.Opens)] (hg : g ≠ 0) (hs : Function.Surjective f)
    (a : A) :
    (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec g)
        (h := nonempty_preimage_Dspec f hg hs)).hom
        ((f.app (Dspec g)).hom (algebraMap A (specSections A (Dspec g)) a))
      = (Scheme.germToFunctionField X ⊤).hom (DSMap.phi A X f a) := by
  have hζ := mem_preimage_Dspec_genericPoint f hg hs
  -- the two `A`-algebra structures on `Γ(Spec A, D(g))` agree
  have ha : ∀ x : A, (algebraMap A (specSections A (Dspec g))) x
      = (((Spec (.of A)).presheaf.map (homOfLE le_top).op).hom)
          ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) x) := fun _ => rfl
  -- naturality of `f.app`
  have hnat : ∀ x, ((f.app (Dspec g)).hom)
        ((((Spec (.of A)).presheaf.map (homOfLE le_top).op).hom) x)
      = (((X.presheaf.map ((TopologicalSpace.Opens.map f.base).map
            (homOfLE le_top)).op).hom) ((f.app ⊤).hom x)) :=
    fun x => RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.naturality f (U := Dspec g) (U' := ⊤) (homOfLE le_top).op)) x
  -- the germ at the generic point is compatible with restriction
  have hgr : ∀ y, ((Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec g)
        (h := nonempty_preimage_Dspec f hg hs)).hom)
        (((X.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE le_top)).op).hom) y)
      = (Scheme.germToFunctionField X ⊤).hom y :=
    fun y => RingHom.congr_fun (congrArg CommRingCat.Hom.hom (TopCat.Presheaf.germ_res (X.presheaf)
      ((TopologicalSpace.Opens.map f.base).map (homOfLE (le_top : Dspec g ≤ ⊤)))
      (genericPoint X) hζ)) y
  -- the identification of `f.appTop` with `phi`
  have hphi : ∀ x : A, ((f.app ⊤).hom) ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) x)
      = DSMap.phi A X f x := by
    intro x
    rw [algebraMap_specSections_top]
    exact (phi_eq_appTop_apply f x).symm
  calc (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec g)
          (h := nonempty_preimage_Dspec f hg hs)).hom
        ((f.app (Dspec g)).hom (algebraMap A (specSections A (Dspec g)) a))
      = (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec g)
          (h := nonempty_preimage_Dspec f hg hs)).hom
          ((f.app (Dspec g)).hom
            ((((Spec (.of A)).presheaf.map (homOfLE le_top).op).hom)
              ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) a))) := by
        rw [ha a]
    _ = (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec g)
          (h := nonempty_preimage_Dspec f hg hs)).hom
          (((X.presheaf.map ((TopologicalSpace.Opens.map f.base).map
              (homOfLE le_top)).op).hom)
            ((f.app ⊤).hom ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) a))) := by
        rw [hnat ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) a)]
    _ = (Scheme.germToFunctionField X ⊤).hom
          ((f.app ⊤).hom ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) a)) :=
        hgr ((f.app ⊤).hom ((algebraMap A (specSections A (⊤ : (Spec (.of A)).Opens))) a))
    _ = (Scheme.germToFunctionField X ⊤).hom (DSMap.phi A X f a) := by
        rw [hphi a]

end BasicOpen

/-! ## The main theorem -/

theorem functionField_finiteDimensional {A : Type u} [CommRing A] [IsDomain A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [AlgebraicGeometry.IsIntegral X] [Nonempty (⊤ : X.Opens)]
    (hs : Function.Surjective f) (hg : DSMap.IsGenFinite A f)
    [Algebra A (X.functionField)]
    (hφ : ∀ a : A, algebraMap A (X.functionField) a =
      (AlgebraicGeometry.Scheme.germToFunctionField X ⊤).hom (DSMap.phi A X f a))
    [Algebra (FractionRing A) (X.functionField)]
    [IsScalarTower A (FractionRing A) (X.functionField)] :
    FiniteDimensional (FractionRing A) (X.functionField) := by
  classical
  obtain ⟨g, hg_ne, hfin⟩ := hg
  -- the basic open `D(g)`
  have hUaff : IsAffineOpen (Dspec (A := A) g) := isAffineOpen_Dspec g
  have hfinU : IsFinite (f ∣_ Dspec (A := A) g) := hfin
  -- `V = f⁻¹(D(g))` is affine (finite over the affine `D(g)`)
  haveI hDaff : IsAffine ((Dspec (A := A) g) : Scheme) := hUaff
  have hVaff : IsAffineOpen (f ⁻¹ᵁ Dspec (A := A) g) :=
    isAffine_of_isAffineHom (f := f ∣_ Dspec (A := A) g)
  haveI hVne : Nonempty (f ⁻¹ᵁ Dspec (A := A) g) := nonempty_preimage_Dspec f hg_ne hs
  haveI hSdom : IsDomain Γ(X, f ⁻¹ᵁ Dspec (A := A) g) :=
    Function.Injective.isDomain _ (Scheme.germToFunctionField_injective X _)
  -- the `A`-algebra structures
  letI : Algebra (specSections A (Dspec (A := A) g))
      Γ(X, f ⁻¹ᵁ Dspec (A := A) g) :=
    (f.app (Dspec (A := A) g)).hom.toAlgebra
  letI : Algebra (specSections A (Dspec (A := A) g)) (X.functionField) :=
    ((Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec (A := A) g)).hom.comp
      (f.app (Dspec (A := A) g)).hom).toAlgebra
  haveI hst1 : IsScalarTower (specSections A (Dspec (A := A) g))
      Γ(X, f ⁻¹ᵁ Dspec (A := A) g) (X.functionField) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinApp : (f.app (Dspec (A := A) g)).hom.Finite :=
    finite_app_of_isFinite_restrict f _ hUaff
  haveI hModFin : Module.Finite (specSections A (Dspec (A := A) g))
      Γ(X, f ⁻¹ᵁ Dspec (A := A) g) := hfinApp
  -- the localization map `Γ(Spec A, D(g)) → Frac A`
  have hgunit : IsUnit (algebraMap A (FractionRing A) g) := by
    rw [isUnit_iff_ne_zero]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg_ne)
  let psi : specSections A (Dspec (A := A) g) →+* FractionRing A :=
    IsLocalization.Away.lift (S := specSections A (Dspec (A := A) g)) g
      (g := algebraMap A (FractionRing A)) hgunit
  letI : Algebra (specSections A (Dspec (A := A) g)) (FractionRing A) := psi.toAlgebra
  haveI hstA : IsScalarTower A (specSections A (Dspec (A := A) g)) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (IsLocalization.Away.lift_eq (x := g) (S := specSections A (Dspec (A := A) g))
        (g := algebraMap A (FractionRing A)) hgunit a).symm
  -- hence the `Γ(Spec A, D(g))`-algebra structure on `K(X)` factors through `Frac A`
  haveI hst2 : IsScalarTower (specSections A (Dspec (A := A) g)) (FractionRing A)
      (X.functionField) := by
    have hcomp : (algebraMap (FractionRing A) (X.functionField)).comp
        (algebraMap (specSections A (Dspec (A := A) g)) (FractionRing A))
        = (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec (A := A) g)).hom.comp
          (f.app (Dspec (A := A) g)).hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
      show (algebraMap (FractionRing A) (X.functionField))
          ((algebraMap (specSections A (Dspec (A := A) g)) (FractionRing A))
            ((algebraMap A (specSections A (Dspec (A := A) g))) a))
        = (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec (A := A) g)).hom
            ((f.app (Dspec (A := A) g)).hom
              (algebraMap A (specSections A (Dspec (A := A) g)) a))
      rw [RingHom.algebraMap_toAlgebra,
        IsLocalization.Away.lift_eq (x := g) (S := specSections A (Dspec (A := A) g))
          (g := algebraMap A (FractionRing A)) hgunit a,
        ← IsScalarTower.algebraMap_apply A (FractionRing A) (X.functionField), hφ a]
      exact (germ_comp_app_Dspec f hg_ne hs a).symm
    have hcompL : (algebraMap (specSections A (Dspec (A := A) g)) (X.functionField))
        = (Scheme.germToFunctionField X (f ⁻¹ᵁ Dspec (A := A) g)).hom.comp
          (f.app (Dspec (A := A) g)).hom := rfl
    exact IsScalarTower.of_algebraMap_eq fun b => by
      rw [hcompL]
      exact (RingHom.congr_fun hcomp b).symm
  -- the fraction field of `Γ(X, V)` is `K(X)`
  haveI hFrac : IsFractionRing Γ(X, f ⁻¹ᵁ Dspec (A := A) g) (X.functionField) :=
    functionField_isFractionRing_of_isAffineOpen X _ hVaff
  exact Work.DSM8m2.Algebra.finiteDimensional_of_finite_isFractionRing
    (B := specSections A (Dspec (A := A) g))
    (S := Γ(X, f ⁻¹ᵁ Dspec (A := A) g)) (K := FractionRing A) (L := X.functionField)

end Work.DSM8m2.Zariski
