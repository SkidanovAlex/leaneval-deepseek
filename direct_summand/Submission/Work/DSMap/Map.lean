import Mathlib
import ChallengeDeps

/-! LEAD-OWNED (curric-46, 2026-10-13): frozen area interfaces of the reviewed proof map
(cbc/direct_summand_proof_map.md + _REVIEW.md, copies in sources/dsmap/). Do not edit. The M2/M3/M5/M6 stubs are
KNOWN DEFECTIVE (review §3) and must not be dispatched until restated. -/
/-!
# direct_summand — top-down proof map (compiled stub file)

Areas are `theorem area_*` with `sorry` bodies (frozen interfaces).  `R0` is fully proved here.
The assembly `main_dsplit`, `Submission...derived_direct_summand` and
`Submission...direct_summand` compile from the area statements.
Design notes: `cbc/direct_summand_proof_map.md`.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

instance {C : Type*} [Category* C] {J : GrothendieckTopology C} (R : Sheaf J RingCat) (X : Cᵒᵖ) :
    (SheafOfModules.evaluation R X).Additive where
  map_add := rfl

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DSMap

universe u v w₁ w₂ w₃ w₄

/-! ## V0: vocabulary (frozen) -/

section Vocab
variable (A : Type u) [CommRing A]

/-- `A → Γ(X, ⊤)` induced by `f : X ⟶ Spec A` (exactly the challenge's `φ`). -/
noncomputable def phi (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((ΓSpec.adjunction.homEquiv _ _).symm f).unop.hom

/-- The challenge functor `Γ(X, -)` viewed in `A`-modules. -/
noncomputable abbrev GammaA (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    SheafOfModules X.ringCatSheaf ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation X.ringCatSheaf ⟨⊤⟩ ⋙ ModuleCat.restrictScalars (phi A X f)

/-- `RΓ(X, 𝒪_X)` in `D⁺(A)` (challenge API). -/
noncomputable def RG [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] : DerivedCategory.Plus (ModuleCat.{u} A) :=
  (GammaA A X f).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- The challenge composite `A[0] → Γ(X,𝒪)[0] → RΓ(X,𝒪)`. -/
noncomputable def rgUnit [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] :
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ RG A X f :=
  letI : Algebra A Γ(X, ⊤) := (phi A X f).toAlgebra
  (DerivedCategory.Plus.singleFunctor _ 0).map
      (ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))) ≫
    (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
      (SheafOfModules.unit X.ringCatSheaf)

/-- Derived splitting, for every choice of derived-category instances. -/
def DSplit (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) : Prop :=
  ∀ (_ : HasDerivedCategory.{w₁} (ModuleCat.{u} A))
    (_ : HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf))
    (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)), IsSplitMono (rgUnit A X f)

/-- `ℙᴺ_A = Proj A[x₀,…,x_N]`. -/
abbrev PGr (N : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A
noncomputable abbrev PSpace (N : ℕ) : Scheme.{u} := Proj (PGr A N)
noncomputable def PSpace.toSpec (N : ℕ) : PSpace A N ⟶ Spec (.of A) :=
  Proj.toSpecZero (PGr A N) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (PGr A N 0)))

/-- `f` factors through a closed immersion into some `ℙᴺ_A`. -/
def IsProjOver {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace A N), IsClosedImmersion i ∧ i ≫ PSpace.toSpec A N = f

/-- `f` is finite over a basic open `D(g)`, `g ≠ 0` (generically finite; used over domains). -/
def IsGenFinite {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) : Prop :=
  ∃ g : A, g ≠ 0 ∧ IsFinite (f ∣_ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens))

noncomputable def phiU (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) : A →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp (phi A X f)

lemma phiU_res (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {U V : X.Opens} (i : V ⟶ U) (a : A) :
    (X.presheaf.map i.op).hom (phiU A X f U a) = phiU A X f V a := by
  simp only [phiU, RingHom.coe_comp, Function.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  rfl

/-- `𝒪_X` as a presheaf of `A`-modules. -/
noncomputable def cechPresheaf (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} A where
  obj U := letI := (phiU A X f U.unop).toAlgebra; ModuleCat.of A Γ(X, U.unop)
  map {U V} i := letI := (phiU A X f U.unop).toAlgebra; letI := (phiU A X f V.unop).toAlgebra
    ModuleCat.ofHom
      { toFun := (X.presheaf.map i).hom
        map_add' := by simp
        map_smul' := by
          intro a x
          simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.id_apply]
          rw [← phiU_res A X f i.unop]; rfl }
  map_id U := by first | (ext1; simp; done) | (ext1; simp; rfl)
  map_comp i j := by first | (ext1; simp; done) | (ext1; simp; rfl)

/-- Mathlib's Čech complex of `𝒪_X` (as `A`-modules) for a family of opens. -/
noncomputable def cech (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  (cechComplexFunctor U).obj (cechPresheaf A X f)

/-- The Čech complex in `ℤ`-degrees `≥ 0`. -/
noncomputable def cechZ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (cech A X f U).extend ComplexShape.embeddingUpNat

/-- `A → Γ(X, ⊤)` as a map into `cechPresheaf.obj ⊤`. -/
noncomputable def unitTop (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    ModuleCat.of A A ⟶ (cechPresheaf A X f).obj (Opposite.op ⊤) :=
  letI := (phiU A X f ⊤).toAlgebra
  ModuleCat.ofHom (Algebra.linearMap A Γ(X, (⊤ : X.Opens)))

/-- Degree-0 coaugmentation `A → ∏ᵢ Γ(Uᵢ, 𝒪)`. -/
noncomputable def coaug0 (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    ModuleCat.of A A ⟶ (cech A X f U).X 0 :=
  Pi.lift fun _ => unitTop A X f ≫ (cechPresheaf A X f).map (homOfLE le_top).op

end Vocab

/-! ## R0 (PROVED): plain DSC from derived DSC for finite covers -/

section R0
variable (A : Type u) [CommRing A]

instance plusSingleFull (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] (n : ℤ) :
    (DerivedCategory.Plus.singleFunctor C n).Full := by
  have : (DerivedCategory.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.ι).Full :=
    Functor.Full.of_iso (DerivedCategory.Plus.singleFunctorιIso C n).symm
  exact Functor.Full.of_comp_faithful _ DerivedCategory.Plus.ι

instance plusSingleFaithful (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] (n : ℤ) :
    (DerivedCategory.Plus.singleFunctor C n).Faithful := by
  have : (DerivedCategory.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.ι).Faithful :=
    Functor.Faithful.of_iso (DerivedCategory.Plus.singleFunctorιIso C n).symm
  exact Functor.Faithful.of_comp _ DerivedCategory.Plus.ι

theorem retraction_of_split [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] (h : IsSplitMono (rgUnit A X f)) :
    letI : Algebra A Γ(X, ⊤) := (phi A X f).toAlgebra
    ∃ π : Γ(X, ⊤) →ₗ[A] A, π ∘ₗ Algebra.linearMap A Γ(X, ⊤) = .id := by
  let : Algebra A Γ(X, ⊤) := (phi A X f).toAlgebra
  obtain ⟨⟨r, hr⟩⟩ := h.exists_splitMono
  let s := (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit'
      (GammaA A X f) 0).app (SheafOfModules.unit X.ringCatSheaf) ≫ r
  obtain ⟨π0, hπ0⟩ := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map_surjective s
  refine ⟨π0.hom, ?_⟩
  have key : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map
      (ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤)) ≫ π0) =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map (𝟙 _) := by
    calc _ = (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map
            (ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))) ≫
          (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map π0 := Functor.map_comp _ _ _
      _ = rgUnit A X f ≫ r := by erw [hπ0]; exact (Category.assoc _ _ _).symm
      _ = _ := hr
      _ = _ := (CategoryTheory.Functor.map_id _ _).symm
  have := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map_injective key
  exact congrArg ModuleCat.Hom.hom this

lemma phi_SpecMap {B : Type u} [CommRing B] (g : CommRingCat.of A ⟶ CommRingCat.of B) :
    ((ΓSpec.adjunction.homEquiv _ _).symm (Spec.map g)).unop =
      g ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
  set φ' := ((ΓSpec.adjunction.homEquiv _ _).symm (Spec.map g)).unop with hφ'
  have h1 : (ΓSpec.adjunction.homEquiv (Spec (CommRingCat.of B)) (Opposite.op (CommRingCat.of A)))
      φ'.op = Spec.map g := by
    rw [hφ']; exact (ΓSpec.adjunction.homEquiv _ _).apply_symm_apply _
  have h2 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := Spec (CommRingCat.of B)) φ'
  simp only [Opposite.unop_op] at h2
  erw [h1] at h2
  rw [← h2, Scheme.ΓSpecIso_inv_naturality]

lemma surj_of_finite_faithful (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B]
    [FaithfulSMul A B] :
    Function.Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  intro x
  have := x.isPrime
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    x.asIdeal (⊥ : Ideal B) (by
      intro a ha
      simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at ha
      rw [hinj (ha.trans (map_zero _).symm)]; exact zero_mem _)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩

theorem dsc_of_dsplit_small (hyp : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f],
      Function.Surjective f → DSplit.{u, u+1, u+1} A X f)
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] :
    ∃ π : B →ₗ[A] A, π ∘ₗ Algebra.linearMap A B = .id := by
  let g : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have : IsFinite (Spec.map g) := by
    rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr inferInstance
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (SheafOfModules (Spec (.of B)).ringCatSheaf)
  have hs := hyp (Spec (.of B)) (Spec.map g) (surj_of_finite_faithful A B) ‹_› ‹_› inferInstance
  obtain ⟨π0, hπ0⟩ := retraction_of_split A _ _ hs
  let : Algebra A Γ(Spec (.of B), ⊤) := (phi A _ (Spec.map g)).toAlgebra
  have hφ := phi_SpecMap A g
  let e := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have he : ∀ a : A, phi A _ (Spec.map g) a = e (algebraMap A B a) := fun a => by
    simp only [phi]; rw [hφ]; rfl
  refine ⟨{ toFun := fun b => π0 (e b), map_add' := fun x y => by simp, map_smul' := ?_ }, ?_⟩
  · intro a b
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
    rw [← he]
    exact π0.map_smul a (e b)
  · refine LinearMap.ext fun a => ?_
    have := congrArg (fun F => F a) hπ0
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      LinearMap.id_coe, id_eq] at this ⊢
    change π0 (e (algebraMap A B a)) = a
    rw [← he a]; exact this

/-- **R0**: the plain DSC for `A` from derived splitting of finite covers (any universe for `B`). -/
theorem dsc_of_dsplit (hyp : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f],
      Function.Surjective f → DSplit.{u, u+1, u+1} A X f)
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] :
    ∃ π : B →ₗ[A] A, π ∘ₗ Algebra.linearMap A B = .id := by
  have : Small.{u} B := Module.Finite.small A B
  let eB : Shrink.{u} B ≃ₐ[A] B := Shrink.algEquiv A B
  have : @Module.Finite A (Shrink.{u} B) _ _ (Algebra.toModule) :=
    @Module.Finite.equiv A B (Shrink.{u} B) _ _ _ _ (Algebra.toModule) _ eB.symm.toLinearEquiv
  have : FaithfulSMul A (Shrink.{u} B) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h := FaithfulSMul.algebraMap_injective A B
    intro x y hxy
    apply h
    rw [← eB.commutes, ← eB.commutes, hxy]
  obtain ⟨π', hπ'⟩ := dsc_of_dsplit_small A hyp (Shrink.{u} B)
  refine ⟨π' ∘ₗ eB.symm.toLinearEquiv.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have := congrArg (fun F => F a) hπ'
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
    LinearMap.id_coe, id_eq, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.commutes] at this ⊢
  exact this

end R0

/-! ## Areas (frozen interfaces, `sorry`) -/

/-- **F1** Čech model of `RΓ(X,𝒪_X)` in the challenge API (separated `X`, finite affine cover):
`ι(RΓ) ≅ Q(Čech)` carrying the challenge unit to the Čech coaugmentation. -/
theorem area_F1_cech.{a, b, c} (A : Type a) [CommRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] [IsSeparated f] [QuasiCompact f]
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∃ (cc : (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A) ⟶ cechZ A X f U)
      (e : DerivedCategory.Plus.ι.obj (RG A X f) ≅ DerivedCategory.Q.obj (cechZ A X f U)),
      cc.f 0 ≫ ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
            coaug0 A X f U ∧
      DerivedCategory.Plus.ι.map (rgUnit A X f) ≫ e.hom =
        (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{a} A) 0).hom.app _ ≫
          (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{a} A) 0).hom.app _ ≫
            DerivedCategory.Q.map cc := sorry

/-- **COH** finiteness + boundedness of `Hⁱ(X, 𝒪_X)` for `X ⊂ ℙᴺ_A`, `A` Noetherian. -/
theorem area_COH.{a, b, c} (A : Type a) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] (hp : IsProjOver A f) :
    ∃ N : ℤ, ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (RG A X f))) ∧
      (N < i → Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (RG A X f)))) := sorry

/-- **G1** splitting pulls back along any `g : X' ⟶ X` over `Spec A`
(`A → RΓ(X) → RΓ(X')`; a retraction of the composite retracts the first map).
Properness lets the proof go through F1 Čech models; drop it if done via flasque sheaves. -/
theorem area_G1_pullback.{a, b, c, d} (A : Type a) [CommRing A] {X X' : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) (g : X' ⟶ X) [IsProper f] [IsProper (g ≫ f)] :
    DSplit.{a, b, d} A X' (g ≫ f) → DSplit.{a, b, c} A X f := sorry

/-- **G2** Chow: a proper `X` over Noetherian `A` is dominated by a projective `X'`. -/
theorem area_G2_chow.{a} (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    ∃ (X' : Scheme.{a}) (g : X' ⟶ X), Function.Surjective g ∧ IsProper (g ≫ f) ∧
      IsProjOver A (g ≫ f) := sorry

/-- **G3** multisection: over a Noetherian local domain, a projective surjective `X` contains a
closed integral `Z` that is still surjective, projective, and generically finite. -/
theorem area_G3_multisection.{a} (A : Type a) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f]
    (hs : Function.Surjective f) (hp : IsProjOver A f) :
    ∃ (Z : Scheme.{a}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ IsIntegral Z ∧
      Function.Surjective (ι ≫ f) ∧ IsProper (ι ≫ f) ∧ IsGenFinite A (ι ≫ f) ∧
      IsProjOver A (ι ≫ f) := sorry

/-- **G4a** local-to-global: splitting over flat local extensions at every maximal ideal
implies splitting over `A` (needs COH + F1 flat base change + Ext descent). -/
theorem area_G4a_localGlobal.{a, b, c, d, e} (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : IsProjOver A f)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (maximalIdeal A').comap ψ = m ∧
      DSplit.{a, d, e} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSplit.{a, b, c} A X f := sorry

/-- **G4b** gonflement: `A_m → Â_m → ` complete regular local with algebraically closed
residue field, flat over `A`, lying over `m`. -/
theorem area_G4b_gonflement.{a} (A : Type a) [CommRing A] [IsRegularRing A] (m : Ideal A)
    (hm : m.IsMaximal) :
    ∃ (A' : Type a) (_ : CommRing A') (_ : IsRegularLocalRing A') (ψ : A →+* A'),
      IsAdicComplete (maximalIdeal A') A' ∧ IsAlgClosed (ResidueField A') ∧ ψ.Flat ∧
      (maximalIdeal A').comap ψ = m := sorry

/-- **G4c** base change along `Spec A' → Spec A` keeps proper, surjective, projective. -/
theorem area_G4c_baseChange.{a} (A A' : Type a) [CommRing A] [CommRing A'] (ψ : A →+* A')
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hp : IsProjOver A f) :
    IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) ∧
      Function.Surjective (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) ∧
      IsProjOver A' (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) := sorry

/-- **REG** regular local rings are domains. -/
theorem area_REG.{a} (R : Type a) [CommRing R] [IsRegularLocalRing R] : IsDomain R := sorry

/-- **TRI** characteristic trichotomy for a local domain. -/
theorem area_TRI.{a} (R : Type a) [CommRing R] [IsLocalRing R] [IsDomain R] :
    CharZero (ResidueField R) ∨ (∃ p : ℕ, p.Prime ∧ CharP R p) ∨
      (∃ p : ℕ, p.Prime ∧ CharZero R ∧ CharP (ResidueField R) p) := sorry

/-- **EQ0** equal characteristic 0 (trace on the perfect complex `RΓ`; Bhatt's remark). -/
theorem area_EQ0.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)]
    [CharZero (ResidueField A)] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f) (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := sorry

/-- **EQP** equal characteristic `p` (perfection + char-p Prop 5.2 / Bhatt 2012). -/
theorem area_EQP.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharP A p] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f) (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := sorry

/-- **MIX** mixed characteristic `(0,p)` (Bhatt 2018 §4–§5). The research crux. -/
theorem area_MIX.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f)
    (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := sorry

/-! ## MIX internal vocabulary + sub-areas (proposed; not used by the assembly) -/

section MixInternal

/-- p-torsion-free integral perfectoid ring with a chosen `ϖ`, `ϖ^p = p·unit`, roots `ϖ_k`
(BMS1 Lemma 3.10 form; covers Bhatt's "generalized" perfectoids). -/
structure PerfectoidData (p : ℕ) (A : Type u) [CommRing A] where
  ϖ : ℕ → A
  root : ∀ k, ϖ (k + 1) ^ p = ϖ k
  unit : ∃ v : Aˣ, ϖ 0 ^ p = (p : A) * v
  torsionFree : IsSMulRegular A (p : A)
  complete : IsAdicComplete (Ideal.span {(p : A)}) A
  frobSurj : ∀ x : A, ∃ y : A, x - y ^ p ∈ Ideal.span {(p : A)}
  frobInj : ∀ y : A, y ^ p ∈ Ideal.span {(p : A)} → y ∈ Ideal.span {ϖ 0}

/-- almost zero w.r.t. `(ϖ_k)_k` -/
def AlmostZero {A : Type u} [CommRing A] (ϖ : ℕ → A) (M : Type v) [AddCommGroup M] [Module A M] :
    Prop := ∀ k (x : M), ϖ k • x = 0

/-- `A → B` almost faithfully flat: kernels of base-changed injections are almost zero, and
almost-zero base change detects zero. -/
def AlmostFF {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B] (ϖ : ℕ → B) :
    Prop :=
  (∀ (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (g : M →ₗ[A] N),
      Function.Injective g → AlmostZero ϖ (LinearMap.ker (g.baseChange B))) ∧
  (∀ (M : Type u) [AddCommGroup M] [Module A M], AlmostZero ϖ (TensorProduct A B M) →
      Subsingleton M)

/-- almost splitting of the challenge unit w.r.t. `(ϖ_k)` -/
def AlmostDSplit (A : Type u) [CommRing A] (ϖ : ℕ → A) (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    Prop :=
  ∀ (_ : HasDerivedCategory.{w₁} (ModuleCat.{u} A))
    (_ : HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf))
    (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)) (k : ℕ),
    ∃ r : RG A X f ⟶ (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A),
      rgUnit A X f ≫ r = (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (LinearMap.lsmul A A (ϖ k)))

/-- **M1** (Bhatt Prop 4.2): complete regular local mixed-char `A` has an almost faithfully
flat perfectoid cover. Uses Cohen structure (unramified) / almost purity (ramified). -/
theorem area_M1_perfectoidCover.{a} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (P : PerfectoidData p B),
      AlmostFF (A := A) B P.ϖ :=
  sorry

/-- **M2** André's flatness lemma (Bhatt Thm 2.3; elementary proof Česnavičius–Scholze §2.3):
adjoin compatible `p`-power roots of `g`, almost faithfully flat mod `p`. -/
theorem area_M2_andreFlatness.{a} (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (g : A) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B) (gr : ℕ → B),
      gr 0 = algebraMap A B g ∧ (∀ k, gr (k + 1) ^ p = gr k) ∧
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      AlmostFF (A := A ⧸ (Ideal.span {(p : B)}).comap (algebraMap A B)) (B ⧸ Ideal.span {(p : B)})
        (fun k => Ideal.Quotient.mk _ (Q.ϖ k)) := sorry

/-- **M3** almost purity, in the form "the integral closure in a finite étale `A[1/p]`-algebra is
almost split over `A`" (Scholze 7.9(iii) / Bhatt–Scholze 10.9). -/
theorem area_M3_almostPurity.{a} (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (S : Type a) [CommRing S] [Algebra (Localization.Away (p : A)) S]
    [Algebra A S] [IsScalarTower A (Localization.Away (p : A)) S]
    [Algebra.Etale (Localization.Away (p : A)) S] [Module.Finite (Localization.Away (p : A)) S] :
    ∀ k, ∃ σ : integralClosure A S →ₗ[A] A, σ 1 = P.ϖ k := sorry

/-- **M5** (Bhatt Prop 5.2, birational core): `Y → Spec A` proper and an isomorphism after
inverting `p` ⇒ `A → RΓ(Y,𝒪)` almost split. Needs admissible-blowup domination + Scholze 6.14
(`H^i(S_η, 𝒪⁺) ≈ 0` on affinoid perfectoids). -/
theorem area_M5_birationalCore.{a, b, c} (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (Y : Scheme.{a}) (f : Y ⟶ Spec (.of A)) [IsProper f]
    [IsIso (f ∣_ (PrimeSpectrum.basicOpen (p : A) : (Spec (.of A)).Opens))] :
    AlmostDSplit.{a, b, c} A P.ϖ Y f := sorry

/-- **M6** (Bhatt Prop 5.2): `f[1/p]` finite étale ⇒ almost split (M3 + M5 + G1-type pullback). -/
theorem area_M6_prop52.{a, b, c} (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (Y : Scheme.{a}) (f : Y ⟶ Spec (.of A)) [IsProper f]
    [IsFinite (f ∣_ (PrimeSpectrum.basicOpen (p : A) : (Spec (.of A)).Opens))]
    [Etale (f ∣_ (PrimeSpectrum.basicOpen (p : A) : (Spec (.of A)).Opens))] :
    AlmostDSplit.{a, b, c} A P.ϖ Y f := sorry

end MixInternal

/-! ## Assembly -/

theorem main_dsplit (A : Type u) [CommRing A] [IsRegularRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) :
    DSplit.{u, w₁, w₂} A X f := by
  obtain ⟨X', g, hg, hprop, hproj⟩ := area_G2_chow A X f
  refine area_G1_pullback.{u, w₁, w₂, u + 1} A f g ?_
  have hsf : Function.Surjective (g ≫ f) := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    obtain ⟨z, rfl⟩ := hg y
    exact ⟨z, by simp⟩
  refine area_G4a_localGlobal.{u, w₁, u + 1, u + 1, u + 1} A X' (g ≫ f) hproj ?_
  intro m hm
  obtain ⟨A', _, _, ψ, hcomp, hac, hflat, hcomap⟩ := area_G4b_gonflement A m hm
  refine ⟨A', inferInstance, inferInstance, ψ, hflat, hcomap, ?_⟩
  obtain ⟨hP, hS, hPr⟩ := area_G4c_baseChange A A' ψ X' (g ≫ f) hsf hproj
  have := area_REG A'
  obtain ⟨Z, ι, -, hZ, hsZ, hpZ, hgfZ, hprZ⟩ :=
    area_G3_multisection A' _ (pullback.snd (g ≫ f) (Spec.map (CommRingCat.ofHom ψ))) hS hPr
  refine area_G1_pullback.{u, u + 1, u + 1, u + 1} A' _ ι ?_
  rcases area_TRI A' with h0 | ⟨p, hp, hcp⟩ | ⟨p, hp, hc0, hcr⟩
  · exact area_EQ0 A' Z _ hsZ hgfZ hprZ
  · have := Fact.mk hp
    exact area_EQP A' p Z _ hsZ hgfZ hprZ
  · have := Fact.mk hp
    exact area_MIX A' p Z _ hsZ hgfZ hprZ

end DSMap
