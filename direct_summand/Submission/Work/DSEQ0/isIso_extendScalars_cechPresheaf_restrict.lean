import Mathlib
import Submission.Work.DSEQ0.eulerCharDefs
import Submission.Work.DSEQ0.isBaseChange_id_localizationAway

/-!
# The restriction of the Čech presheaf becomes an isomorphism after inverting `g`

For `f : X ⟶ Spec A`, `g : A`, `W = f ⁻¹ᵁ D(g)` and an **affine** open `V ⊆ X`, the restriction map
`𝒪_X(V) → 𝒪_X(W ⊓ V)` of the structure sheaf of `X` (viewed as the value of the Čech presheaf
`DSMap.cechPresheaf` at `op V`, resp. `op (W ⊓ V)`) becomes an isomorphism after extending scalars
along `A → A_g = Localization.Away g`.

Both sides are localizations of `R = Γ(X, V)` at `b = phiU A X f V g`:

* `Γ(X, W ⊓ V)` is `R_b`, because `W ⊓ V = X.basicOpen b` and `V` is affine
  (`IsAffineOpen.isLocalization_of_eq_basicOpen`);
* `A_g ⊗[A] R` is `R_b`, because `A_g ⊗[A] R` is the localization of `R` at the image of `g`
  (`IsLocalization.Away.tensorRight`).

Comparing the two localizations (`IsLocalization.algEquiv`, `IsLocalization.ringHom_ext`) shows that
`β : A_g ⊗[A] R → Γ(X, W ⊓ V)`, `s ⊗ x ↦ s • x` is bijective.  On the other hand, for an `A_g`-module
`N` the canonical map `γ : A_g ⊗[A] N → N`, `s ⊗ y ↦ s • y` is an isomorphism
(`IsBaseChange` of the identity, `Work.DSEQ0.isBaseChange_id_localizationAway`), and

`γ ∘ (A_g ⊗[A] (restriction)) = β`,

by definition of `β` on pure tensors.  Hence `A_g ⊗[A] (restriction) = β ≫ γ⁻¹` is an isomorphism.

Technically, `A_g ⊗[A] (-)` occurs in two *spellings*: the `ModuleCat.extendScalars` one
(`TensorProduct A ((ModuleCat.restrictScalars (algebraMap A A_g)).obj (ModuleCat.of A_g A_g)) -`,
whose first factor carries the `Module.compHom` instance) and the plain `TensorProduct` one used by
`Algebra.TensorProduct.lift` and `IsLocalization.Away.tensorRight` (whose first factor carries the
`Algebra.toModule` instance).  The two are interchanged by `TensorProduct.congr` of the two identity
linear equivalences (`flipR`, `flipN` below), which is what the proof uses to compare the goal
morphism with `β` and `γ`.
-/

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace Work.DSEQ0

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace IsIsoExtendScalarsCechPresheafRestrict

/-- `f ⁻¹ᵁ D(g)` is the basic open of the image of `g` in `Γ(X, ⊤)`. -/
theorem basicOpen_phi_eq_awayOpen (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (g : A) :
    X.basicOpen (DSMap.phi A X f g) = awayOpen A X f g := by
  have key : (f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens))
      = X.basicOpen (DSMap.phi A X f g) := by
    have hcong := congrArg (fun U : (Spec (.of A)).Opens => f ⁻¹ᵁ U)
      (basicOpen_eq_of_affine g).symm
    exact hcong.trans (Scheme.preimage_basicOpen_top f _)
  exact key.symm

/-- The basic open of the image of `g` in the sections over `V` is `V ⊓ f ⁻¹ᵁ D(g)`. -/
theorem basicOpen_phiU_eq (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (g : A) (V : X.Opens) :
    X.basicOpen (DSMap.phiU A X f V g) = V ⊓ awayOpen A X f g := by
  rw [show DSMap.phiU A X f V g
      = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (DSMap.phi A X f g) from rfl,
    Scheme.basicOpen_res, basicOpen_phi_eq_awayOpen]

end IsIsoExtendScalarsCechPresheafRestrict

theorem isIso_extendScalars_cechPresheaf_restrict
    (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (g : A)
    (V : X.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) :
    CategoryTheory.IsIso ((ModuleCat.extendScalars (algebraMap A (Localization.Away g))).map
      ((DSMap.cechPresheaf A X f).map
        (CategoryTheory.homOfLE (inf_le_right : Work.DSEQ0.awayOpen A X f g ⊓ V ≤ V)).op)) := by
  -- The `A`-algebra structures on the two rings of sections, and the restriction `Γ(X,V) → Γ(X,W⊓V)`
  -- as a `Γ(X,V)`-algebra structure.
  letI : Algebra A ↑Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
  letI : Algebra A ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    (DSMap.phiU A X f (Work.DSEQ0.awayOpen A X f g ⊓ V)).toAlgebra
  letI : Algebra ↑Γ(X, V) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    (X.presheaf.map (homOfLE (inf_le_right : Work.DSEQ0.awayOpen A X f g ⊓ V ≤ V)).op).hom.toAlgebra
  have hres : ∀ a : A,
      (X.presheaf.map (homOfLE (inf_le_right : Work.DSEQ0.awayOpen A X f g ⊓ V ≤ V)).op).hom
          (DSMap.phiU A X f V a)
        = DSMap.phiU A X f (Work.DSEQ0.awayOpen A X f g ⊓ V) a :=
    fun a => DSMap.phiU_res A X f
      (homOfLE (inf_le_right : Work.DSEQ0.awayOpen A X f g ⊓ V ≤ V)) a
  -- `V ⊓ W = X.basicOpen (phiU A X f V g)`, so the sections over `W ⊓ V` are the localization of
  -- `Γ(X,V)` at the image of `g`.
  have hbOpen : Work.DSEQ0.awayOpen A X f g ⊓ V = X.basicOpen (DSMap.phiU A X f V g) := by
    rw [IsIsoExtendScalarsCechPresheafRestrict.basicOpen_phiU_eq, inf_comm]
  haveI hlocS : IsLocalization.Away (DSMap.phiU A X f V g)
      ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    hV.isLocalization_of_eq_basicOpen (DSMap.phiU A X f V g)
      (homOfLE (inf_le_right : Work.DSEQ0.awayOpen A X f g ⊓ V ≤ V)) hbOpen
  haveI hST : IsScalarTower A ↑Γ(X, V) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact (hres a).symm)
  -- The `A_g`-algebra structure `ψ` on `Γ(X, W ⊓ V)`: the unique extension of `phiU` along which `g`
  -- becomes invertible.
  have hgunit : IsUnit (DSMap.phiU A X f (Work.DSEQ0.awayOpen A X f g ⊓ V) g) := by
    have h1 : IsUnit (algebraMap ↑Γ(X, V) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)
        (DSMap.phiU A X f V g)) :=
      IsLocalization.Away.algebraMap_isUnit (S := ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V))
        (DSMap.phiU A X f V g)
    rwa [RingHom.algebraMap_toAlgebra, hres g] at h1
  let ψ : Localization.Away g →+* ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    IsLocalization.Away.lift (S := Localization.Away g)
      (g := DSMap.phiU A X f (Work.DSEQ0.awayOpen A X f g ⊓ V)) g hgunit
  have hψ : ψ.comp (algebraMap A (Localization.Away g))
      = algebraMap A ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) := by
    rw [RingHom.algebraMap_toAlgebra
      (DSMap.phiU A X f (Work.DSEQ0.awayOpen A X f g ⊓ V))]
    exact IsLocalization.Away.lift_comp g hgunit
  letI : Algebra (Localization.Away g) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) := ψ.toAlgebra
  haveI hST2 : IsScalarTower A (Localization.Away g) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      show (algebraMap A ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) a
        = ψ ((algebraMap A (Localization.Away g)) a)
      exact (RingHom.congr_fun hψ a).symm)
  -- The comparison map `β : A_g ⊗[A] Γ(X,V) → Γ(X, W ⊓ V)`, `s ⊗ x ↦ s • x`.
  let gg : ↑Γ(X, V) →ₐ[A] ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    { toRingHom := algebraMap ↑Γ(X, V) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)
      commutes' := fun a => (IsScalarTower.algebraMap_apply A ↑Γ(X, V)
        ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) a).symm }
  let β : Localization.Away g ⊗[A] ↑Γ(X, V)
      →ₐ[Localization.Away g] ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    Algebra.TensorProduct.lift
      (Algebra.ofId (Localization.Away g) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) gg
      (fun x y => mul_comm _ _)
  -- `β` is bijective: both sides are the localization of `Γ(X,V)` at the image of `g`.
  have hβbij : Function.Bijective β := by
    letI : Algebra ↑Γ(X, V) (Localization.Away g ⊗[A] ↑Γ(X, V)) :=
      Algebra.TensorProduct.rightAlgebra
    haveI hlocT : IsLocalization.Away (algebraMap A ↑Γ(X, V) g)
        (Localization.Away g ⊗[A] ↑Γ(X, V)) :=
      IsLocalization.Away.tensorRight (S := ↑Γ(X, V)) g (Localization.Away g)
    let e : (Localization.Away g ⊗[A] ↑Γ(X, V))
        ≃ₐ[↑Γ(X, V)] ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
      IsLocalization.algEquiv (Submonoid.powers (DSMap.phiU A X f V g)) _ _
    have hβe : β.toRingHom = e.toRingHom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (DSMap.phiU A X f V g)) ?_
      ext x
      simp only [RingHom.comp_apply]
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      show β (1 ⊗ₜ[A] x) = e (1 ⊗ₜ[A] x)
      rw [show β (1 ⊗ₜ[A] x)
          = (Algebra.ofId (Localization.Away g)
              ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) 1 * gg x from
        Algebra.TensorProduct.lift_tmul _ _ _ 1 x]
      rw [← Algebra.TensorProduct.right_algebraMap_apply (A := Localization.Away g)
        (B := ↑Γ(X, V)) x, e.commutes]
      show (Algebra.ofId (Localization.Away g) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) 1 * gg x
        = algebraMap ↑Γ(X, V) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) x
      rw [Algebra.ofId_apply, map_one, one_mul]
      show gg x = algebraMap ↑Γ(X, V) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) x
      rw [RingHom.algebraMap_toAlgebra]
      rfl
    have h2 : Function.Bijective (β.toRingHom : _ →+* _) := by
      rw [hβe]
      exact e.bijective
    exact h2
  -- ## The assembly
  -- The restriction `Γ(X,V) → Γ(X,W⊓V)` as a morphism of `A`-modules and the goal morphism.
  let R₀ := (DSMap.cechPresheaf A X f).obj (op V)
  let N₀ := (DSMap.cechPresheaf A X f).obj (op (Work.DSEQ0.awayOpen A X f g ⊓ V))
  let F := ModuleCat.extendScalars (algebraMap A (Localization.Away g))
  let r₀ : R₀ ⟶ N₀ := (DSMap.cechPresheaf A X f).map
    (homOfLE (inf_le_right : Work.DSEQ0.awayOpen A X f g ⊓ V ≤ V)).op
  let M₀ : F.obj R₀ ⟶ F.obj N₀ := F.map r₀
  change CategoryTheory.IsIso M₀
  -- An `A_g`-module is its own base change along `A → A_g`: `s ⊗ y ↦ s • y` is an isomorphism.
  haveI hγ : IsBaseChange (Localization.Away g)
      (LinearMap.id (R := A) (M := ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) :
        ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) →ₗ[A]
          ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) :=
    isBaseChange_id_localizationAway g
  -- The two spellings of a base changed term: the `extendScalars` one (whose first factor carries the
  -- `Module.compHom` instance) and the plain `TensorProduct` one.  The `TensorProduct.congr` of the
  -- two identity equivalences passes between them.
  let S₁ : ModuleCat A := (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).obj
    (ModuleCat.of (Localization.Away g) (Localization.Away g))
  let eA : ↑S₁ ≃ₗ[A] Localization.Away g :=
    { toFun := fun x => (x : Localization.Away g)
      invFun := fun y => y
      map_add' := fun x y => rfl
      map_smul' := fun r x => by
        rw [ModuleCat.restrictScalars.smul_def, Algebra.smul_def, Algebra.algebraMap_self_apply,
          Algebra.smul_def, RingHom.id_apply]
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let eR : ↑R₀ ≃ₗ[A] ↑Γ(X, V) :=
    { toFun := fun x => (x : ↑Γ(X, V))
      invFun := fun y => y
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let eN : ↑N₀ ≃ₗ[A] ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    { toFun := fun x => (x : ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V))
      invFun := fun y => y
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let flipR : (TensorProduct A S₁ ↑R₀) ≃ₗ[A] TensorProduct A (Localization.Away g) ↑Γ(X, V) :=
    TensorProduct.congr eA eR
  let flipN : (TensorProduct A S₁ ↑N₀) ≃ₗ[A]
      TensorProduct A (Localization.Away g) ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V) :=
    TensorProduct.congr eA eN
  have flipR_tmul (s : ↑S₁) (x : ↑R₀) :
      flipR ((s ⊗ₜ[A] x : TensorProduct A S₁ ↑R₀)) =
        ((s : Localization.Away g) ⊗ₜ[A] (x : ↑Γ(X, V)) :
          TensorProduct A (Localization.Away g) ↑Γ(X, V)) :=
    TensorProduct.congr_tmul eA eR s x
  have flipN_tmul (s : ↑S₁) (y : ↑N₀) :
      flipN ((s ⊗ₜ[A] y : TensorProduct A S₁ ↑N₀)) =
        ((s : Localization.Away g) ⊗ₜ[A]
            (y : ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) :
          TensorProduct A (Localization.Away g)
            ↑Γ(X, Work.DSEQ0.awayOpen A X f g ⊓ V)) :=
    TensorProduct.congr_tmul eA eN s y
  -- The comparison of the goal morphism with the two maps above, on pure tensors.
  have hkey : ∀ z : ↑(F.obj R₀),
      hγ.equiv (flipN ((ConcreteCategory.hom M₀) z)) = β (flipR z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [ModuleCat.ExtendScalars.map_tmul, flipN_tmul, IsBaseChange.equiv_tmul, flipR_tmul,
        Algebra.TensorProduct.lift_tmul]
      simp only [LinearMap.id_coe, id_eq, Algebra.ofId_apply, AlgHom.coe_mk,
        RingHom.algebraMap_toAlgebra, gg]
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra ψ]
      congr 1
    | add u v hu hv => simp only [map_add, hu, hv]
  refine (ConcreteCategory.isIso_iff_bijective M₀).mpr ?_
  have hβfun : Function.Bijective (fun z : ↑(F.obj R₀) => β (flipR z)) :=
    hβbij.comp flipR.bijective
  have hγfun : Function.Bijective (fun w : ↑(F.obj N₀) => hγ.equiv (flipN w)) :=
    hγ.equiv.bijective.comp flipN.bijective
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine hβfun.1 ?_
    show β (flipR x) = β (flipR y)
    rw [← hkey x, ← hkey y, hxy]
  · obtain ⟨z, hz⟩ := hβfun.2 ((fun w : ↑(F.obj N₀) => hγ.equiv (flipN w)) y)
    refine ⟨z, hγfun.1 ?_⟩
    show hγ.equiv (flipN ((ConcreteCategory.hom M₀) z)) = hγ.equiv (flipN y)
    rw [hkey z]
    exact hz

end Work.DSEQ0
