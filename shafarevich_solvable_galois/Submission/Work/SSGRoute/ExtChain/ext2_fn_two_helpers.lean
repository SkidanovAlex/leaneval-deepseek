import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Helpers for the `p = 2` Hasse-principle transfer over a group of order two

Shared vocabulary for `Work.SSGRoute.ExtChain.ext2_fn_two_of_trivial_proved`:

* scalar bookkeeping for the coefficient ring `Coeff = ULift ℤ` (`Coeff`-scalars act as the
  canonical `ℤ`-action, so every additive map is automatically `Coeff`-linear);
* the packaging of an equivariant additive bijection as an isomorphism of representations;
* the product `repProd A B` of two representations, whose underlying type is *definitionally* the
  product `A.V × B.V` (the biproduct `A ⊞ B` has an opaque underlying type), together with the
  additivity of `Ext` in the first variable for it;
* `Ext` of a representation whose underlying type is a subsingleton.

Because `Coeff = ULift ℤ`, there are competing `Module Coeff` instances on the carrier of a
representation (the field `Rep.hV2` versus the global `ULift.module`); the local instance
priority bump below makes type class search pick the representation's own field, which is the
instance appearing in the types of `Rep.ρ` and `Rep.Hom`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

attribute [local instance] Classical.decEq

attribute [local instance 2000] Rep.hV2

attribute [local instance 2000] Prod.instModule

/-! ## The product of two representations, with its explicit underlying product type -/

section Prod

variable {H : Type} [Group H]

/-- The product of two representations, with the underlying type *definitionally* the product
`A.V × B.V` (unlike the biproduct `A ⊞ B`, whose underlying type is opaque). -/
def repProd (A B : Rep.{0} SSGRoute.PTExt.Coeff H) : Rep.{0} SSGRoute.PTExt.Coeff H :=
  Rep.of (A.ρ.prod B.ρ)

/-- The action on `repProd A B` is the product action. -/
@[simp] theorem repProd_ρ_apply (A B : Rep.{0} SSGRoute.PTExt.Coeff H) (g : H) (x : A.V × B.V) :
    (repProd A B).ρ g x = (A.ρ g x.1, B.ρ g x.2) := by
  change ((A.ρ g).prodMap (B.ρ g)) x = _
  rw [LinearMap.prodMap_apply]

/-- The first projection of a product of representations. -/
def repProdFst (A B : Rep.{0} SSGRoute.PTExt.Coeff H) : repProd A B ⟶ A :=
  Rep.ofHom ⟨LinearMap.fst SSGRoute.PTExt.Coeff A.V B.V, fun g => by
    apply LinearMap.ext
    intro x
    show (((A.ρ g).prodMap (B.ρ g)) x).1 = (A.ρ g) x.1
    rw [LinearMap.prodMap_apply]⟩

/-- The second projection of a product of representations. -/
def repProdSnd (A B : Rep.{0} SSGRoute.PTExt.Coeff H) : repProd A B ⟶ B :=
  Rep.ofHom ⟨LinearMap.snd SSGRoute.PTExt.Coeff A.V B.V, fun g => by
    apply LinearMap.ext
    intro x
    show (((A.ρ g).prodMap (B.ρ g)) x).2 = (B.ρ g) x.2
    rw [LinearMap.prodMap_apply]⟩

/-- The first inclusion into a product of representations. -/
def repProdInl (A B : Rep.{0} SSGRoute.PTExt.Coeff H) : A ⟶ repProd A B :=
  Rep.ofHom ⟨LinearMap.prod (LinearMap.id : A.V →ₗ[SSGRoute.PTExt.Coeff] A.V)
      (0 : A.V →ₗ[SSGRoute.PTExt.Coeff] B.V), fun g => by
    apply LinearMap.ext
    intro x
    show ((A.ρ g) x, (0 : B.V)) = ((A.ρ g) x, (B.ρ g) 0)
    rw [map_zero]⟩

/-- The second inclusion into a product of representations. -/
def repProdInr (A B : Rep.{0} SSGRoute.PTExt.Coeff H) : B ⟶ repProd A B :=
  Rep.ofHom ⟨LinearMap.prod (0 : B.V →ₗ[SSGRoute.PTExt.Coeff] A.V)
      (LinearMap.id : B.V →ₗ[SSGRoute.PTExt.Coeff] B.V), fun g => by
    apply LinearMap.ext
    intro x
    show ((0 : A.V), (B.ρ g) x) = ((A.ρ g) 0, (B.ρ g) x)
    rw [map_zero]⟩

end Prod

/-! ## Additivity of `Ext` in the first variable for an explicit product of representations -/

section ExtAddProd

variable {H : Type} [Group H]

/-- The first projection of a product of representations is a retraction of the first
inclusion. -/
theorem repProdInl_fst (A B : Rep.{0} SSGRoute.PTExt.Coeff H) :
    repProdInl A B ≫ repProdFst A B = 𝟙 A := by
  apply ConcreteCategory.hom_ext
  intro x
  show (LinearMap.fst SSGRoute.PTExt.Coeff A.V B.V)
      (((LinearMap.id : A.V →ₗ[SSGRoute.PTExt.Coeff] A.V).prod
        (0 : A.V →ₗ[SSGRoute.PTExt.Coeff] B.V)) x) = x
  rw [LinearMap.fst_apply]
  rfl

/-- The second projection of a product of representations is a retraction of the second
inclusion. -/
theorem repProdInr_snd (A B : Rep.{0} SSGRoute.PTExt.Coeff H) :
    repProdInr A B ≫ repProdSnd A B = 𝟙 B := by
  apply ConcreteCategory.hom_ext
  intro x
  show (LinearMap.snd SSGRoute.PTExt.Coeff A.V B.V)
      (((0 : B.V →ₗ[SSGRoute.PTExt.Coeff] A.V).prod
        (LinearMap.id : B.V →ₗ[SSGRoute.PTExt.Coeff] B.V)) x) = x
  rw [LinearMap.snd_apply]
  rfl

/-- The first inclusion followed by the second projection is zero. -/
theorem repProdInl_snd (A B : Rep.{0} SSGRoute.PTExt.Coeff H) :
    repProdInl A B ≫ repProdSnd A B = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  show (LinearMap.snd SSGRoute.PTExt.Coeff A.V B.V)
      (((LinearMap.id : A.V →ₗ[SSGRoute.PTExt.Coeff] A.V).prod
        (0 : A.V →ₗ[SSGRoute.PTExt.Coeff] B.V)) x) = 0
  rw [LinearMap.snd_apply]
  rfl

/-- The second inclusion followed by the first projection is zero. -/
theorem repProdInr_fst (A B : Rep.{0} SSGRoute.PTExt.Coeff H) :
    repProdInr A B ≫ repProdFst A B = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  show (LinearMap.fst SSGRoute.PTExt.Coeff A.V B.V)
      (((0 : B.V →ₗ[SSGRoute.PTExt.Coeff] A.V).prod
        (LinearMap.id : B.V →ₗ[SSGRoute.PTExt.Coeff] B.V)) x) = 0
  rw [LinearMap.fst_apply]
  rfl

/-- The product of representations splits as the sum of its two projections. -/
theorem repProdFst_inl_add_snd_inr (A B : Rep.{0} SSGRoute.PTExt.Coeff H) :
    repProdFst A B ≫ repProdInl A B + repProdSnd A B ≫ repProdInr A B = 𝟙 (repProd A B) := by
  apply ConcreteCategory.hom_ext
  intro x
  show ((x.1, (0 : B.V)) : A.V × B.V) + (((0 : A.V), x.2)) = x
  exact Prod.ext (by simp) (by simp)

/-- **Additivity of `Ext` in the first variable, for an explicit product of representations.**
A hand-rolled version of `CategoryTheory.Abelian.Ext.biprodAddEquiv`, stated for `repProd A B`
(whose underlying type is the explicit product `A.V × B.V`). -/
def ext_addEquiv_repProd (A B C : Rep.{0} SSGRoute.PTExt.Coeff H) (n : ℕ) :
    Abelian.Ext.{0} (repProd A B) C n ≃+
      Abelian.Ext.{0} A C n × Abelian.Ext.{0} B C n where
  toFun z := ((Abelian.Ext.mk₀ (repProdInl A B)).comp z (zero_add n),
              (Abelian.Ext.mk₀ (repProdInr A B)).comp z (zero_add n))
  invFun w := (Abelian.Ext.mk₀ (repProdFst A B)).comp w.1 (zero_add n)
            + (Abelian.Ext.mk₀ (repProdSnd A B)).comp w.2 (zero_add n)
  left_inv z := by
    have h₁ : (Abelian.Ext.mk₀ (repProdFst A B)).comp
          ((Abelian.Ext.mk₀ (repProdInl A B)).comp z (zero_add n)) (zero_add n)
        = ((Abelian.Ext.mk₀ (repProdFst A B)).comp (Abelian.Ext.mk₀ (repProdInl A B))
            (zero_add 0)).comp z (zero_add n) :=
      (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdFst A B))
        (Abelian.Ext.mk₀ (repProdInl A B)) z (zero_add 0) (zero_add n) (by omega)).symm
    have h₂ : (Abelian.Ext.mk₀ (repProdSnd A B)).comp
          ((Abelian.Ext.mk₀ (repProdInr A B)).comp z (zero_add n)) (zero_add n)
        = ((Abelian.Ext.mk₀ (repProdSnd A B)).comp (Abelian.Ext.mk₀ (repProdInr A B))
            (zero_add 0)).comp z (zero_add n) :=
      (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdSnd A B))
        (Abelian.Ext.mk₀ (repProdInr A B)) z (zero_add 0) (zero_add n) (by omega)).symm
    show (Abelian.Ext.mk₀ (repProdFst A B)).comp
          ((Abelian.Ext.mk₀ (repProdInl A B)).comp z (zero_add n)) (zero_add n)
        + (Abelian.Ext.mk₀ (repProdSnd A B)).comp
          ((Abelian.Ext.mk₀ (repProdInr A B)).comp z (zero_add n)) (zero_add n) = z
    rw [h₁, h₂, ← Abelian.Ext.add_comp, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_add, repProdFst_inl_add_snd_inr,
      Abelian.Ext.mk₀_id_comp]
  right_inv w := by
    obtain ⟨z₁, z₂⟩ := w
    have h₁ : (Abelian.Ext.mk₀ (repProdInl A B)).comp
          ((Abelian.Ext.mk₀ (repProdFst A B)).comp z₁ (zero_add n)) (zero_add n)
        = ((Abelian.Ext.mk₀ (repProdInl A B)).comp (Abelian.Ext.mk₀ (repProdFst A B))
            (zero_add 0)).comp z₁ (zero_add n) :=
      (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdInl A B))
        (Abelian.Ext.mk₀ (repProdFst A B)) z₁ (zero_add 0) (zero_add n) (by omega)).symm
    have h₂ : (Abelian.Ext.mk₀ (repProdInl A B)).comp
          ((Abelian.Ext.mk₀ (repProdSnd A B)).comp z₂ (zero_add n)) (zero_add n)
        = ((Abelian.Ext.mk₀ (repProdInl A B)).comp (Abelian.Ext.mk₀ (repProdSnd A B))
            (zero_add 0)).comp z₂ (zero_add n) :=
      (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdInl A B))
        (Abelian.Ext.mk₀ (repProdSnd A B)) z₂ (zero_add 0) (zero_add n) (by omega)).symm
    have h₃ : (Abelian.Ext.mk₀ (repProdInr A B)).comp
          ((Abelian.Ext.mk₀ (repProdFst A B)).comp z₁ (zero_add n)) (zero_add n)
        = ((Abelian.Ext.mk₀ (repProdInr A B)).comp (Abelian.Ext.mk₀ (repProdFst A B))
            (zero_add 0)).comp z₁ (zero_add n) :=
      (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdInr A B))
        (Abelian.Ext.mk₀ (repProdFst A B)) z₁ (zero_add 0) (zero_add n) (by omega)).symm
    have h₄ : (Abelian.Ext.mk₀ (repProdInr A B)).comp
          ((Abelian.Ext.mk₀ (repProdSnd A B)).comp z₂ (zero_add n)) (zero_add n)
        = ((Abelian.Ext.mk₀ (repProdInr A B)).comp (Abelian.Ext.mk₀ (repProdSnd A B))
            (zero_add 0)).comp z₂ (zero_add n) :=
      (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdInr A B))
        (Abelian.Ext.mk₀ (repProdSnd A B)) z₂ (zero_add 0) (zero_add n) (by omega)).symm
    refine Prod.ext ?_ ?_
    · show (Abelian.Ext.mk₀ (repProdInl A B)).comp
            ((Abelian.Ext.mk₀ (repProdFst A B)).comp z₁ (zero_add n)
              + (Abelian.Ext.mk₀ (repProdSnd A B)).comp z₂ (zero_add n)) (zero_add n) = z₁
      rw [Abelian.Ext.comp_add, h₁, h₂, Abelian.Ext.mk₀_comp_mk₀,
        Abelian.Ext.mk₀_comp_mk₀, repProdInl_fst, repProdInl_snd, Abelian.Ext.mk₀_id_comp,
        Abelian.Ext.mk₀_zero]
      simp only [Abelian.Ext.zero_comp A 0 z₂ n (zero_add n), add_zero]
    · show (Abelian.Ext.mk₀ (repProdInr A B)).comp
            ((Abelian.Ext.mk₀ (repProdFst A B)).comp z₁ (zero_add n)
              + (Abelian.Ext.mk₀ (repProdSnd A B)).comp z₂ (zero_add n)) (zero_add n) = z₂
      rw [Abelian.Ext.comp_add, h₃, h₄, Abelian.Ext.mk₀_comp_mk₀,
        Abelian.Ext.mk₀_comp_mk₀, repProdInr_fst, repProdInr_snd, Abelian.Ext.mk₀_id_comp,
        Abelian.Ext.mk₀_zero]
      simp only [Abelian.Ext.zero_comp B 0 z₁ n (zero_add n), zero_add]
  map_add' x y := by
    show ((Abelian.Ext.mk₀ (repProdInl A B)).comp (x + y) (zero_add n),
          (Abelian.Ext.mk₀ (repProdInr A B)).comp (x + y) (zero_add n))
        = (((Abelian.Ext.mk₀ (repProdInl A B)).comp x (zero_add n),
            (Abelian.Ext.mk₀ (repProdInr A B)).comp x (zero_add n))
          + ((Abelian.Ext.mk₀ (repProdInl A B)).comp y (zero_add n),
            (Abelian.Ext.mk₀ (repProdInr A B)).comp y (zero_add n)))
    rw [Abelian.Ext.comp_add, Abelian.Ext.comp_add]
    rfl

end ExtAddProd

/-! ## Scalars -/

section Scalars

/-- The `Coeff`-scalar `2` agrees with the natural-number scalar `2`. -/
theorem coeff_two_smul_eq_two_nsmul {M : Type} [AddCommGroup M]
    [Module SSGRoute.PTExt.Coeff M] (x : M) :
    (2 : SSGRoute.PTExt.Coeff) • x = (2 : ℕ) • x := by
  rw [ULift.smul_def]
  show (2 : ℤ) • x = 2 • x
  rw [two_zsmul, two_nsmul]

/-- A `Coeff`-scalar acts as the canonical `ℤ`-action (`ULift.down`). -/
lemma ulift_smul_eq_down {M : Type} [AddCommGroup M] (inst : Module SSGRoute.PTExt.Coeff M)
    (u : SSGRoute.PTExt.Coeff) (x : M) :
    @SMul.smul SSGRoute.PTExt.Coeff M inst.toDistribMulAction.toSMul u x = u.down • x := by
  cases u with
  | up z => exact @Int.cast_smul_eq_zsmul (ULift ℤ) M _ _ inst z x

/-- An additive map between `Coeff`-modules, packaged as a `Coeff`-linear map (with the
`Module` instances prescribed explicitly, to avoid the `ULift ℤ` instance diamond). -/
def coeffLinearMapOfAddHom {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (iM : Module SSGRoute.PTExt.Coeff M) (iN : Module SSGRoute.PTExt.Coeff N) (f : M →+ N) :
    @LinearMap SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _ (RingHom.id _) M N _ _ iM iN :=
  { toFun := f, map_add' := f.map_add, map_smul' := fun c x => by
      obtain ⟨k⟩ := c
      show f (@SMul.smul SSGRoute.PTExt.Coeff M iM.toDistribMulAction.toSMul (ULift.up k) x) =
        @SMul.smul SSGRoute.PTExt.Coeff N iN.toDistribMulAction.toSMul (ULift.up k) (f x)
      rw [ulift_smul_eq_down iM (ULift.up k) x, ulift_smul_eq_down iN (ULift.up k) (f x),
        map_zsmul] }

/-- An additive map of representations, packaged as an intertwining map. -/
def intertwiningMapOfAddHom {H : Type} [Group H] {V W : Type} [AddCommGroup V]
    [AddCommGroup W] (iV : Module SSGRoute.PTExt.Coeff V) (iW : Module SSGRoute.PTExt.Coeff W)
    {ρ : Representation SSGRoute.PTExt.Coeff H V} {σ : Representation SSGRoute.PTExt.Coeff H W}
    (f : V →+ W) (he : ∀ (g : H) (v : V), f (ρ g v) = σ g (f v)) :
    @Representation.IntertwiningMap SSGRoute.PTExt.Coeff H V W _ _ _ _ iV iW ρ σ :=
  @Representation.IntertwiningMap.mk SSGRoute.PTExt.Coeff H V W _ _ _ _ iV iW ρ σ
    (coeffLinearMapOfAddHom iV iW f)
    (fun g => @LinearMap.ext SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff V W _ _ _ _ iV iW
      (RingHom.id _) _ _ (fun v => he g v))

/-- An equivariant additive bijection of the underlying modules is an isomorphism of
representations. -/
def repIsoOfAddBijective {H : Type} [Group H] {A B : Rep.{0} SSGRoute.PTExt.Coeff H}
    (f : A.V →+ B.V) (hf : Function.Bijective f)
    (he : ∀ (g : H) (v : A.V), f (A.ρ g v) = B.ρ g (f v)) : A ≅ B := by
  classical
  haveI : Nonempty A.V := ⟨0⟩
  have hleft : ∀ x : A.V, Function.invFun f (f x) = x := fun x =>
    hf.1 (Function.invFun_eq ⟨x, rfl⟩)
  have hright : ∀ y : B.V, f (Function.invFun f y) = y := fun y =>
    Function.invFun_eq (hf.2 y)
  set finv : B.V →+ A.V :=
    { toFun := Function.invFun f
      map_zero' := hf.1 (by rw [hright 0, map_zero f])
      map_add' := fun y₁ y₂ => hf.1 (by
        rw [map_add, hright y₁, hright y₂, hright (y₁ + y₂)]) } with hfinv
  exact
  { hom := Rep.ofHom (intertwiningMapOfAddHom A.hV2 B.hV2 f he)
    inv := Rep.ofHom (intertwiningMapOfAddHom B.hV2 A.hV2 finv (fun g y => by
      show finv (B.ρ g y) = A.ρ g (finv y)
      apply hf.1
      change f (Function.invFun f (B.ρ g y)) = f (A.ρ g (Function.invFun f y))
      rw [hright, he g (Function.invFun f y), hright]))
    hom_inv_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext x
      show finv (f x) = x
      exact hleft x
    inv_hom_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext y
      show f (finv y) = y
      exact hright y }

end Scalars

/-! ## Naturality of the additivity of `Ext` in the first variable (biproduct form) -/

section ExtNaturality

/-- Postcomposition in the second variable commutes with the first component of Mathlib's
additivity isomorphism `Ext (X₁ ⊞ X₂) Y n ≃ Ext X₁ Y n × Ext X₂ Y n`. -/
theorem ext_biprodAddEquiv_postcomp_fst {H : Type} [Group H] {X₁ X₂ A B : Rep.{0}
    SSGRoute.PTExt.Coeff H} (φ : A ⟶ B) (z : Abelian.Ext.{0} (X₁ ⊞ X₂) A 2) :
    (Abelian.Ext.biprodAddEquiv (Y := B) (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))).1
    = ((Abelian.Ext.biprodAddEquiv (Y := A) z).1).comp (Abelian.Ext.mk₀ φ) (add_zero 2) := by
  rw [Abelian.Ext.biprodAddEquiv_apply_fst, Abelian.Ext.biprodAddEquiv_apply_fst]
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (Limits.biprod.inl : X₁ ⟶ X₁ ⊞ X₂)) z
    (Abelian.Ext.mk₀ φ) (zero_add 2) (add_zero 2) (by omega)).symm

/-- Postcomposition in the second variable commutes with the second component of Mathlib's
additivity isomorphism `Ext (X₁ ⊞ X₂) Y n ≃ Ext X₁ Y n × Ext X₂ Y n`. -/
theorem ext_biprodAddEquiv_postcomp_snd {H : Type} [Group H] {X₁ X₂ A B : Rep.{0}
    SSGRoute.PTExt.Coeff H} (φ : A ⟶ B) (z : Abelian.Ext.{0} (X₁ ⊞ X₂) A 2) :
    (Abelian.Ext.biprodAddEquiv (Y := B) (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))).2
    = ((Abelian.Ext.biprodAddEquiv (Y := A) z).2).comp (Abelian.Ext.mk₀ φ) (add_zero 2) := by
  rw [Abelian.Ext.biprodAddEquiv_apply_snd, Abelian.Ext.biprodAddEquiv_apply_snd]
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (Limits.biprod.inr : X₂ ⟶ X₁ ⊞ X₂)) z
    (Abelian.Ext.mk₀ φ) (zero_add 2) (add_zero 2) (by omega)).symm

/-- Precomposition with a morphism of the first variable commutes with postcomposition in the
second (associativity of the Yoneda product). -/
theorem ext_comp_comp {H : Type} [Group H] {X Y A B : Rep.{0} SSGRoute.PTExt.Coeff H}
    (u : X ⟶ Y) (φ : A ⟶ B) (z : Abelian.Ext.{0} Y A 2) :
    (Abelian.Ext.mk₀ u).comp (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) (zero_add 2)
    = ((Abelian.Ext.mk₀ u).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2) := by
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ u) z (Abelian.Ext.mk₀ φ) (zero_add 2)
    (add_zero 2) (by omega)).symm

/-- `Ext` of a representation with subsingleton underlying type vanishes in positive degree. -/
theorem subsingleton_ext_of_subsingleton_V {H : Type} [Group H] {X : Rep.{0}
    SSGRoute.PTExt.Coeff H} (hX : Subsingleton X.V) (A : Rep.{0} SSGRoute.PTExt.Coeff H) (n : ℕ) :
    Subsingleton (Abelian.Ext.{0} X A (n + 1)) := by
  have hz : Limits.IsZero X := (Rep.isZero_iff SSGRoute.PTExt.Coeff H X).mpr hX
  have hid : (𝟙 X : X ⟶ X) = 0 := (Limits.IsZero.iff_id_eq_zero X).mp hz
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    calc a = (Abelian.Ext.mk₀ (𝟙 X)).comp a (zero_add (n + 1)) :=
          (Abelian.Ext.mk₀_id_comp a).symm
      _ = (Abelian.Ext.mk₀ (0 : X ⟶ X)).comp a (zero_add (n + 1)) := by rw [hid]
      _ = 0 := by
          rw [Abelian.Ext.mk₀_zero]
          exact Abelian.Ext.zero_comp X 0 a (n + 1) (zero_add (n + 1))
  have hb : b = 0 := by
    calc b = (Abelian.Ext.mk₀ (𝟙 X)).comp b (zero_add (n + 1)) :=
          (Abelian.Ext.mk₀_id_comp b).symm
      _ = (Abelian.Ext.mk₀ (0 : X ⟶ X)).comp b (zero_add (n + 1)) := by rw [hid]
      _ = 0 := by
          rw [Abelian.Ext.mk₀_zero]
          exact Abelian.Ext.zero_comp X 0 b (n + 1) (zero_add (n + 1))
  rw [ha, hb]

/-- Composition with an isomorphism of the first variable inverts it. -/
theorem ext_comp_iso_inv_hom {H : Type} [Group H] {X Y A : Rep.{0}
    SSGRoute.PTExt.Coeff H} (e : X ≅ Y) (z : Abelian.Ext.{0} Y A 2) :
    (Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ e.hom).comp z (zero_add 2)) (zero_add 2)
      = z := by
  rw [show (Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ e.hom).comp z (zero_add 2))
        (zero_add 2)
      = ((Abelian.Ext.mk₀ e.inv).comp (Abelian.Ext.mk₀ e.hom) (zero_add 0)).comp z
          (zero_add 2) from
    (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ e.inv) (Abelian.Ext.mk₀ e.hom) z (zero_add 0)
      (zero_add 2) (by omega)).symm]
  rw [Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.mk₀_id_comp]

/-- `Subsingleton` of `Ext`-groups transfers from the source to the target of an isomorphism of
the first variable. -/
theorem ext_subsingleton_of_iso {H : Type} [Group H] {X Y A : Rep.{0}
    SSGRoute.PTExt.Coeff H} (e : X ≅ Y)
    (h : Subsingleton (Abelian.Ext.{0} X A 2)) : Subsingleton (Abelian.Ext.{0} Y A 2) := by
  refine ⟨fun x y => ?_⟩
  have hxy : (Abelian.Ext.mk₀ e.hom).comp x (zero_add 2)
      = (Abelian.Ext.mk₀ e.hom).comp y (zero_add 2) := h.elim _ _
  rw [← ext_comp_iso_inv_hom e x, ← ext_comp_iso_inv_hom e y, hxy]

/-- Injectivity of postcomposition transfers from the source to the target of an isomorphism of
the first variable. -/
theorem ext_postcomp_injective_of_iso {H : Type} [Group H] {X Y A B : Rep.{0}
    SSGRoute.PTExt.Coeff H} (e : X ≅ Y) (φ : A ⟶ B)
    (h : Function.Injective (fun z : Abelian.Ext.{0} X A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : Abelian.Ext.{0} Y A 2 =>
      z.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) := by
  intro x y hxy
  have hxy' : x.comp (Abelian.Ext.mk₀ φ) (add_zero 2)
      = y.comp (Abelian.Ext.mk₀ φ) (add_zero 2) := hxy
  have hx : (Abelian.Ext.mk₀ e.hom).comp (x.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) (zero_add 2)
      = (Abelian.Ext.mk₀ e.hom).comp (y.comp (Abelian.Ext.mk₀ φ) (add_zero 2)) (zero_add 2) := by
    rw [hxy']
  have key : ((Abelian.Ext.mk₀ e.hom).comp x (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2)
      = ((Abelian.Ext.mk₀ e.hom).comp y (zero_add 2)).comp (Abelian.Ext.mk₀ φ) (add_zero 2) := by
    rw [← ext_comp_comp e.hom φ x, ← ext_comp_comp e.hom φ y]
    exact hx
  have hxy'' := h key
  rw [← ext_comp_iso_inv_hom e x, ← ext_comp_iso_inv_hom e y, hxy'']

end ExtNaturality

/-- Naturality of `ext_addEquiv_repProd` in the second variable, first component. -/
theorem ext_addEquiv_repProd_postcomp_fst {H : Type} [Group H] (A B C D : Rep.{0}
    SSGRoute.PTExt.Coeff H) (φ : C ⟶ D) (z : Abelian.Ext.{0} (repProd A B) C 2) :
    (ext_addEquiv_repProd A B D 2 (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))).1
    = ((ext_addEquiv_repProd A B C 2 z).1).comp (Abelian.Ext.mk₀ φ) (add_zero 2) := by
  show (Abelian.Ext.mk₀ (repProdInl A B)).comp (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))
      (zero_add 2)
    = ((Abelian.Ext.mk₀ (repProdInl A B)).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ)
        (add_zero 2)
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdInl A B)) z (Abelian.Ext.mk₀ φ)
    (zero_add 2) (add_zero 2) (by omega)).symm

/-- Naturality of `ext_addEquiv_repProd` in the second variable, second component. -/
theorem ext_addEquiv_repProd_postcomp_snd {H : Type} [Group H] (A B C D : Rep.{0}
    SSGRoute.PTExt.Coeff H) (φ : C ⟶ D) (z : Abelian.Ext.{0} (repProd A B) C 2) :
    (ext_addEquiv_repProd A B D 2 (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))).2
    = ((ext_addEquiv_repProd A B C 2 z).2).comp (Abelian.Ext.mk₀ φ) (add_zero 2) := by
  show (Abelian.Ext.mk₀ (repProdInr A B)).comp (z.comp (Abelian.Ext.mk₀ φ) (add_zero 2))
      (zero_add 2)
    = ((Abelian.Ext.mk₀ (repProdInr A B)).comp z (zero_add 2)).comp (Abelian.Ext.mk₀ φ)
        (add_zero 2)
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (repProdInr A B)) z (Abelian.Ext.mk₀ φ)
    (zero_add 2) (add_zero 2) (by omega)).symm

end


end Work.SSGRoute.ExtChain
