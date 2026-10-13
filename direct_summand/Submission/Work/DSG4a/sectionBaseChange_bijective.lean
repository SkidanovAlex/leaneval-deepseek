import Mathlib
import Submission.Work.DSG4a.SectionBaseChange

/-!
# DSG4a: affine base change of sections (the comparison map is bijective)

Let `f : X ⟶ Spec A` be a morphism of schemes, `A → A'` an algebra, `X' = X ×_{Spec A} Spec A'`
its base change (`baseChangeScheme`, `baseChangeFst`, `baseChangeSnd`, `baseChangeOpen` of
`Submission/Work/DSG4a/BaseChange.lean`), and `U ⊆ X` an open.

The goal (`Submission/Work/DSG4a/SectionBaseChange.lean`) is that for `U` **affine** the
comparison map

`sectionBaseChange : Γ(X,U) ⊗[A] A' ⟶ Γ(X', U')`,  `u ⊗ a ↦ (fst.app U u) * (snd.app U' a)`

is bijective.  The strategy is purely geometric and builds the inverse as the map induced on
sections by a scheme-theoretic isomorphism

`σ : U' = fst ⁻¹ᵁ U ⟶ Spec (Γ(X,U) ⊗[A] A')`,

which exists because `U ≅ Spec Γ(X,U)` is affine over `Spec A`:

* the canonical map `Ψ : Spec (Γ(X,U) ⊗[A] A') ⟶ X'` (`baseChangePullbackMap`, the base
  change of the open immersion `U ≅ Spec Γ(X,U)`) is an open immersion with range `U'`
  (this is `Scheme.pullback_map_isOpenImmersion` and `Scheme.Pullback.range_map`); this gives
  an isomorphism `Spec (Γ(X,U) ⊗[A] A') ≅ U'` (`IsOpenImmersion.isoOfRangeEq`);
* its two projections are the maps corresponding to `fst.app U` and the `A'`-structure, which
  identifies the induced ring isomorphism with `sectionBaseChange`.

The constructions below are stated with the `A`-algebra structure on `Γ(X, U)` as an instance
argument together with a proof `hφ : algebraMap A Γ(X,U) = DSMap.phiU A X f U` that it is the
one induced by `f`; the main theorem instantiates both with the `letI` of
`IsBaseChangeIso` and `rfl`.
-/

namespace Work.DSG4a

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

variable {A : Type u} [CommRing A]

/-! ## Two ring homomorphisms out of a tensor product of algebras -/

/-- Two ring homomorphisms out of a tensor product of algebras agree as soon as they agree on
`r ⊗ 1` and on `1 ⊗ s`. -/
lemma ringHom_ext_tmul {B R S C : Type u} [CommRing B] [CommRing R] [Algebra B R]
    [CommRing S] [Algebra B S] [CommRing C] {f g : TensorProduct B R S →+* C}
    (h1 : ∀ r : R, f (TensorProduct.tmul B r (1 : S)) = g (TensorProduct.tmul B r (1 : S)))
    (h2 : ∀ s : S, f (TensorProduct.tmul B (1 : R) s) = g (TensorProduct.tmul B (1 : R) s)) :
    f = g := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul r s =>
      have hz : TensorProduct.tmul B r s
          = TensorProduct.tmul B r (1 : S) * TensorProduct.tmul B (1 : R) s := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hz, map_mul, map_mul, h1, h2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ## Elementary consequences of the `Γ ⊣ Spec` adjunction -/

/-- The structure morphism `f : X ⟶ Spec A` is recovered by the unit `X.toSpecΓ`
(the `Γ ⊣ Spec` triangle). -/
lemma toSpecΓ_specMap_phi (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (DSMap.phi A X f)) = f := by
  have hkey : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A)))
      (CommRingCat.ofHom (DSMap.phi A X f)).op = f :=
    Equiv.apply_symm_apply _ _
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := X) (B := CommRingCat.of A)
    (CommRingCat.ofHom (DSMap.phi A X f))
  rw [hkey] at h
  have hphi : CommRingCat.ofHom (DSMap.phi A X f)
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop := h.symm
  rw [hphi, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    ← SpecMap_ΓSpecIso_hom (CommRingCat.of A), ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

/-- The same for the restriction of `f` to an open `U`. -/
lemma toSpecΓ_specMap_phiU (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (DSMap.phiU A X f U)) = U.ι ≫ f := by
  have h1 : CommRingCat.ofHom (DSMap.phiU A X f U)
      = CommRingCat.ofHom (DSMap.phi A X f) ≫
        X.presheaf.map (homOfLE (x := U) le_top).op := by
    show CommRingCat.ofHom (DSMap.phiU A X f U)
      = CommRingCat.ofHom (DSMap.phi A X f) ≫ X.presheaf.map (homOfLE (x := U) le_top).op
    simp only [DSMap.phiU, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]
  rw [h1, Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
    Category.assoc, toSpecΓ_specMap_phi]

/-- `appTop` of `Spec.map` of a ring homomorphism, in terms of `ΓSpecIso`. -/
lemma appTop_specMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc (CommRingCat.ofHom φ), Iso.hom_inv_id,
    Category.comp_id]

/-- Pointwise form of `appTop_specMap`. -/
lemma appTop_specMap_apply {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Spec.map (CommRingCat.ofHom φ)).appTop x
      = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)) := by
  rw [appTop_specMap φ, CommRingCat.comp_apply, CommRingCat.comp_apply]
  rfl

/-! ## The transport between sections on an open and on the open subscheme -/

/-- Pulling back sections along a morphism and then restricting to an open subscheme is the
same as restricting to the open subscheme and pulling back. -/
lemma topIso_inv_comp_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
  simp only [morphismRestrict_appLE, Scheme.Hom.app_eq_appLE, Scheme.Opens.topIso_inv,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

/-- The composite `Γ(X,⊤) → Γ(U,⊤) → Γ(X,U)` (`topIso.hom` after the restriction) is the
restriction to `U`. -/
lemma topIso_hom_comp_ι_appTop {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE le_top).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  congr 1

/-- Pointwise form of `topIso_hom_comp_ι_appTop`. -/
lemma topIso_hom_ι_appTop {X : Scheme.{u}} (U : X.Opens) (x : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop x) = X.presheaf.map (homOfLE (x := U) le_top).op x := by
  have h := congr($(topIso_hom_comp_ι_appTop U) x)
  simp only [CommRingCat.comp_apply] at h
  exact h

/-- Pointwise form of `topIso_inv_comp_morphismRestrict`. -/
lemma topIso_hom_app_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) :
    (f ⁻¹ᵁ U).topIso.hom ((f ∣_ U).appTop (U.topIso.inv a)) = f.app U a := by
  have h := congr($(topIso_inv_comp_morphismRestrict f U) a)
  simp only [CommRingCat.comp_apply] at h
  rw [h, Iso.inv_hom_id_apply]

/-! ## Generic compatibility of `pullback.map` with the two projections -/

lemma pullback_map_fst {W X Y Z S T : Scheme.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

lemma pullback_map_snd {W X Y Z S T : Scheme.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

/-! ## The geometric comparison isomorphism -/

/-- `U.toSpecΓ ≫ Spec.map` of the structure map of `U` is the restriction of `f`. -/
lemma toSpecΓ_specMap_algebraMap
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, U))) = U.ι ≫ f := by
  rw [hφ]
  exact toSpecΓ_specMap_phiU X f U

/-- The compatibility condition making the base change of the open immersion `U ≅ Spec Γ(X,U)`
well defined. -/
lemma baseChangePullbackMap_compat (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) [Algebra A Γ(X, U)]
    (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U) (hU : IsAffineOpen U) :
    specAlgebraMap (A := A) (A' := Γ(X, U)) ≫ 𝟙 (Spec (.of A)) =
      (hU.isoSpec.inv ≫ U.ι) ≫ f := by
  have hkey : (hU.isoSpec.inv ≫ U.ι) ≫ f = specAlgebraMap (A := A) (A' := Γ(X, U)) := by
    rw [Category.assoc, ← toSpecΓ_specMap_algebraMap X f U hφ,
      ← Category.assoc hU.isoSpec.inv U.toSpecΓ (specAlgebraMap (A := A) (A' := Γ(X, U))),
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  rw [Category.comp_id]
  exact hkey.symm

/-- The base change of the open immersion `U ≅ Spec Γ(X,U)` along `Spec A' ⟶ Spec A`,
as a morphism `Spec (Γ(X,U) ⊗[A] A') ⟶ X'`.  (It is an open immersion with range
`fst ⁻¹ᵁ U`, see `isOpenImmersion_baseChangePullbackMap` and `range_baseChangePullbackMap`.) -/
noncomputable def baseChangePullbackMap (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    pullback (specAlgebraMap (A := A) (A' := Γ(X, U))) (specAlgebraMap (A := A) (A' := A'))
      ⟶ pullback f (specAlgebraMap (A := A) (A' := A')) :=
  pullback.map (specAlgebraMap (A := A) (A' := Γ(X, U))) (specAlgebraMap (A := A) (A' := A'))
    f (specAlgebraMap (A := A) (A' := A')) (hU.isoSpec.inv ≫ U.ι) (𝟙 (Spec (.of A')))
    (𝟙 (Spec (.of A)))
    (baseChangePullbackMap_compat A' X f U hφ hU)
    (by rw [Category.comp_id, Category.id_comp])

lemma baseChangePullbackMap_fst (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    baseChangePullbackMap A' X f U hφ hU ≫ pullback.fst f (specAlgebraMap (A := A) (A' := A')) =
      pullback.fst (specAlgebraMap (A := A) (A' := Γ(X, U)))
        (specAlgebraMap (A := A) (A' := A')) ≫ (hU.isoSpec.inv ≫ U.ι) :=
  pullback.lift_fst _ _ _

lemma baseChangePullbackMap_snd (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    baseChangePullbackMap A' X f U hφ hU ≫ pullback.snd f (specAlgebraMap (A := A) (A' := A')) =
      pullback.snd (specAlgebraMap (A := A) (A' := Γ(X, U)))
        (specAlgebraMap (A := A) (A' := A')) ≫ (𝟙 (Spec (.of A'))) :=
  pullback.lift_snd _ _ _

lemma isOpenImmersion_baseChangePullbackMap (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (U : X.Opens) [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    IsOpenImmersion (baseChangePullbackMap A' X f U hφ hU) := by
  exact Scheme.pullback_map_isOpenImmersion (specAlgebraMap (A := A) (A' := Γ(X, U)))
    (specAlgebraMap (A := A) (A' := A')) f (specAlgebraMap (A := A) (A' := A'))
    (hU.isoSpec.inv ≫ U.ι) (𝟙 (Spec (.of A'))) (𝟙 (Spec (.of A)))
    (baseChangePullbackMap_compat A' X f U hφ hU)
    (by rw [Category.comp_id, Category.id_comp])

lemma range_baseChangePullbackMap (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    Set.range (baseChangePullbackMap A' X f U hφ hU) =
      Set.range (baseChangeOpen (A := A) (A' := A') X f U).ι := by
  rw [show baseChangePullbackMap A' X f U hφ hU = pullback.map
      (specAlgebraMap (A := A) (A' := Γ(X, U))) (specAlgebraMap (A := A) (A' := A'))
      f (specAlgebraMap (A := A) (A' := A')) (hU.isoSpec.inv ≫ U.ι) (𝟙 (Spec (.of A')))
      (𝟙 (Spec (.of A))) (baseChangePullbackMap_compat A' X f U hφ hU)
      (by rw [Category.comp_id, Category.id_comp]) from rfl,
    Scheme.Pullback.range_map]
  have h1 : Set.range ⇑(hU.isoSpec.inv ≫ U.ι) = (↑U : Set ↑X) := by
    have hrange : Set.range ⇑(hU.isoSpec.inv) = Set.univ := by simp
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange, Set.image_univ,
      Scheme.Opens.range_ι]
  have h2 : Set.range ⇑(𝟙 (Spec (.of A'))) = Set.univ := by
    rw [Set.range_eq_univ]; exact Function.surjective_id
  have hgoal : ⇑(pullback.fst f (specAlgebraMap (A := A) (A' := A'))) ⁻¹'
        Set.range ⇑(hU.isoSpec.inv ≫ U.ι) ∩
        ⇑(pullback.snd f (specAlgebraMap (A := A) (A' := A'))) ⁻¹'
          Set.range ⇑(𝟙 (Spec (.of A')))
      = Set.range ⇑(baseChangeOpen (A := A) (A' := A') X f U).ι := by
    rw [h1, h2, Set.preimage_univ, Set.inter_univ, Scheme.Opens.range_ι]
    rfl
  exact hgoal

/-- The canonical map `U' = fst ⁻¹ᵁ U ⟶ Spec (Γ(X,U) ⊗[A] A')`; it is an isomorphism
(`isIso_baseChangeOpenIso`). -/
noncomputable def baseChangeOpenIso (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    (baseChangeOpen (A := A) (A' := A') X f U).toScheme ⟶
      Spec (.of (TensorProduct A Γ(X, U) A')) := by
  haveI : IsOpenImmersion (baseChangePullbackMap A' X f U hφ hU) :=
    isOpenImmersion_baseChangePullbackMap A' X f U hφ hU
  exact (IsOpenImmersion.isoOfRangeEq (baseChangePullbackMap A' X f U hφ hU)
      (baseChangeOpen (A := A) (A' := A') X f U).ι
      (range_baseChangePullbackMap A' X f U hφ hU)).inv ≫
    (pullbackSpecIso A Γ(X, U) A').hom

lemma isIso_baseChangeOpenIso (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    IsIso (baseChangeOpenIso A' X f U hφ hU) := by
  haveI : IsOpenImmersion (baseChangePullbackMap A' X f U hφ hU) :=
    isOpenImmersion_baseChangePullbackMap A' X f U hφ hU
  show IsIso ((IsOpenImmersion.isoOfRangeEq (baseChangePullbackMap A' X f U hφ hU)
      (baseChangeOpen (A := A) (A' := A') X f U).ι
      (range_baseChangePullbackMap A' X f U hφ hU)).inv ≫ (pullbackSpecIso A Γ(X, U) A').hom)
  infer_instance

/-- The comparison map, against the first projection of the affine base change. -/
lemma baseChangeOpenIso_includeLeft (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    baseChangeOpenIso A' X f U hφ hU ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) =
      (baseChangeFst (A := A) (A' := A') X f) ∣_ U ≫ U.toSpecΓ := by
  haveI : IsOpenImmersion (baseChangePullbackMap A' X f U hφ hU) :=
    isOpenImmersion_baseChangePullbackMap A' X f U hφ hU
  show (IsOpenImmersion.isoOfRangeEq (baseChangePullbackMap A' X f U hφ hU)
      (baseChangeOpen (A := A) (A' := A') X f U).ι
      (range_baseChangePullbackMap A' X f U hφ hU)).inv ≫ (pullbackSpecIso A Γ(X, U) A').hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) =
      ((baseChangeFst (A := A) (A' := A') X f) ∣_ U ≫ U.toSpecΓ)
  rw [pullbackSpecIso_hom_fst]
  have hα : ((baseChangeFst (A := A) (A' := A') X f) ∣_ U ≫ U.toSpecΓ) ≫
      (hU.isoSpec.inv ≫ U.ι) =
      (baseChangeOpen (A := A) (A' := A') X f U).ι ≫
        baseChangeFst (A := A) (A' := A') X f := by
    rw [Category.assoc, ← Category.assoc U.toSpecΓ hU.isoSpec.inv U.ι,
      IsAffineOpen.toSpecΓ_isoSpec_inv, Category.id_comp]
    exact morphismRestrict_ι _ _
  refine (cancel_mono (hU.isoSpec.inv ≫ U.ι)).mp ?_
  rw [Category.assoc, ← baseChangePullbackMap_fst A' X f U hφ hU,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, hα]

/-- The comparison map, against the second projection of the affine base change. -/
lemma baseChangeOpenIso_includeRight (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    baseChangeOpenIso A' X f U hφ hU ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')))) =
      (baseChangeOpen (A := A) (A' := A') X f U).ι ≫
        baseChangeSnd (A := A) (A' := A') X f := by
  haveI : IsOpenImmersion (baseChangePullbackMap A' X f U hφ hU) :=
    isOpenImmersion_baseChangePullbackMap A' X f U hφ hU
  show (IsOpenImmersion.isoOfRangeEq (baseChangePullbackMap A' X f U hφ hU)
      (baseChangeOpen (A := A) (A' := A') X f U).ι
      (range_baseChangePullbackMap A' X f U hφ hU)).inv ≫ (pullbackSpecIso A Γ(X, U) A').hom ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')))) =
      ((baseChangeOpen (A := A) (A' := A') X f U).ι ≫
        baseChangeSnd (A := A) (A' := A') X f)
  rw [pullbackSpecIso_hom_snd]
  rw [← Category.comp_id (pullback.snd (specAlgebraMap (A := A) (A' := Γ(X, U)))
      (specAlgebraMap (A := A) (A' := A'))), ← baseChangePullbackMap_snd A' X f U hφ hU,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]

/-- `Γ(X,U) ⊗[A] A' ⟶ Γ(X', U')`, the ring-theoretic shadow of the geometric isomorphism
`baseChangeOpenIso`. -/
noncomputable def sectionBaseChangeInverse (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (U : X.Opens) [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) :
    TensorProduct A Γ(X, U) A' →+*
      Γ(baseChangeScheme (A := A) (A' := A') X f,
        baseChangeOpen (A := A) (A' := A') X f U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (TensorProduct A Γ(X, U) A'))).inv ≫
    Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU) ≫
      (baseChangeOpen (A := A) (A' := A') X f U).topIso.hom).hom

/-! ## The two generator conditions -/

lemma sectionBaseChangeInverse_tmul_one (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) (a : Γ(X, U)) :
    sectionBaseChangeInverse A' X f U hφ hU (TensorProduct.tmul A a (1 : A')) =
      ((baseChangeFst (A := A) (A' := A') X f).app U).hom a := by
  haveI : IsIso (baseChangeOpenIso A' X f U hφ hU) := isIso_baseChangeOpenIso A' X f U hφ hU
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct A Γ(X, U) A'))).inv.hom
        (Algebra.TensorProduct.includeLeftRingHom a)
      = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a) := by
    rw [appTop_specMap_apply]
    exact congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct A Γ(X, U) A'))).inv.hom
      (Algebra.TensorProduct.includeLeftRingHom x))
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))) a).symm
  have h2 : Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU)
        (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom)))
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a))
      = Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom)))
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h3 : Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom)))
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a)
      = Scheme.Hom.appTop
          ((baseChangeFst (A := A) (A' := A') X f) ∣_ U ≫ U.toSpecΓ)
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a) := by
    rw [baseChangeOpenIso_includeLeft A' X f U hφ hU]
    rfl
  have h4 : Scheme.Hom.appTop ((baseChangeFst (A := A) (A' := A') X f) ∣_ U ≫ U.toSpecΓ)
        ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a)
      = Scheme.Hom.appTop ((baseChangeFst (A := A) (A' := A') X f) ∣_ U)
        (Scheme.Hom.appTop U.toSpecΓ
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a)) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h5 : Scheme.Hom.appTop U.toSpecΓ
        ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a) = U.topIso.inv a := by
    have h := congr($(Scheme.Opens.toSpecΓ_appTop U)
      ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv.hom a))
    rw [CommRingCat.comp_apply] at h
    rw [h]
    exact congrArg (fun y => U.topIso.inv y)
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))) a)
  rw [show TensorProduct.tmul A a (1 : A') =
      Algebra.TensorProduct.includeLeftRingHom a from
    (Algebra.TensorProduct.includeLeftRingHom_apply a).symm]
  rw [sectionBaseChangeInverse, CommRingCat.comp_apply, CommRingCat.comp_apply, h1, h2, h3, h4, h5]
  exact topIso_hom_app_eq (baseChangeFst (A := A) (A' := A') X f) U a

lemma sectionBaseChangeInverse_tmul_one_right (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (U : X.Opens) [Algebra A Γ(X, U)] (hφ : algebraMap A Γ(X, U) = DSMap.phiU A X f U)
    (hU : IsAffineOpen U) (b : A') :
    sectionBaseChangeInverse A' X f U hφ hU (TensorProduct.tmul A (1 : Γ(X, U)) b) =
      DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (baseChangeOpen (A := A) (A' := A') X f U) b := by
  haveI : IsIso (baseChangeOpenIso A' X f U hφ hU) := isIso_baseChangeOpenIso A' X f U hφ hU
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct A Γ(X, U) A'))).inv.hom
        (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')) b)
      = (Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A'))))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b) := by
    rw [appTop_specMap_apply]
    exact congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct A Γ(X, U) A'))).inv.hom
      (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')) x))
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of A')) b).symm
  have h2 : Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU)
        (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')))))
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b))
      = Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU ≫
          Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')))))
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h3 : Scheme.Hom.appTop (baseChangeOpenIso A' X f U hφ hU ≫
          Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')))))
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b)
      = Scheme.Hom.appTop
          ((baseChangeOpen (A := A) (A' := A') X f U).ι ≫ baseChangeSnd (A := A) (A' := A') X f)
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b) := by
    rw [baseChangeOpenIso_includeRight A' X f U hφ hU]
  have h4 : Scheme.Hom.appTop
        ((baseChangeOpen (A := A) (A' := A') X f U).ι ≫ baseChangeSnd (A := A) (A' := A') X f)
        ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b)
      = Scheme.Hom.appTop (baseChangeOpen (A := A) (A' := A') X f U).ι
        (Scheme.Hom.appTop (baseChangeSnd (A := A) (A' := A') X f)
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b)) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h5 : Scheme.Hom.appTop (baseChangeSnd (A := A) (A' := A') X f)
      ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom b)
      = DSMap.phi A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f) b :=
    (phiU_baseChange_phi_eq (X := baseChangeScheme (A := A) (A' := A') X f)
      (f := baseChangeSnd (A := A) (A' := A') X f) b).symm
  have h6 : (baseChangeOpen (A := A) (A' := A') X f U).topIso.hom
        (Scheme.Hom.appTop (baseChangeOpen (A := A) (A' := A') X f U).ι
          (DSMap.phi A' (baseChangeScheme (A := A) (A' := A') X f)
            (baseChangeSnd (A := A) (A' := A') X f) b))
      = (baseChangeScheme (A := A) (A' := A') X f).presheaf.map (homOfLE le_top).op
          (DSMap.phi A' (baseChangeScheme (A := A) (A' := A') X f)
            (baseChangeSnd (A := A) (A' := A') X f) b) := by
    have h := congr($(topIso_hom_comp_ι_appTop
      (baseChangeOpen (A := A) (A' := A') X f U))
      (DSMap.phi A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f) b))
    simpa only [CommRingCat.comp_apply] using h
  rw [show TensorProduct.tmul A (1 : Γ(X, U)) b = RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight (R := A) (A := Γ(X, U)) (B := A')) b from
    (Algebra.TensorProduct.includeRight_apply b).symm]
  rw [sectionBaseChangeInverse, CommRingCat.comp_apply, CommRingCat.comp_apply, h1, h2, h3, h4, h5,
    h6]
  rfl

/-- `sectionBaseChange` is the ring map induced by the geometric comparison isomorphism. -/
lemma sectionBaseChange_eq (A' : Type u) [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    (hU : IsAffineOpen U) :
    letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
    sectionBaseChangeInverse A' X f U rfl hU = sectionBaseChange (A := A) (A' := A') X f U := by
  letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  refine ringHom_ext_tmul (fun a => ?_) (fun b => ?_)
  · rw [sectionBaseChangeInverse_tmul_one A' X f U rfl hU]
    rw [show (TensorProduct.tmul A a (1 : A')) =
        TensorProduct.mk A Γ(X, U) A' a 1 from rfl, sectionBaseChange_tmul]
    simp
  · rw [sectionBaseChangeInverse_tmul_one_right A' X f U rfl hU]
    rw [show (TensorProduct.tmul A (1 : Γ(X, U)) b) =
        TensorProduct.mk A Γ(X, U) A' 1 b from rfl, sectionBaseChange_tmul]
    simp

theorem sectionBaseChange_bijective {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    Work.DSG4a.IsBaseChangeIso (A := A) (A' := A') X f U := by
  letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  have hbij : Function.Bijective (sectionBaseChangeInverse A' X f U rfl hU) := by
    haveI : IsIso (baseChangeOpenIso A' X f U rfl hU) :=
      isIso_baseChangeOpenIso A' X f U rfl hU
    exact ConcreteCategory.bijective_of_isIso _
  rw [sectionBaseChange_eq A' X f U hU] at hbij
  exact hbij

end Work.DSG4a
