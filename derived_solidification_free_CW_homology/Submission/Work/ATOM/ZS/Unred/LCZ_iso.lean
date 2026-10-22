import Mathlib
import Submission.Work.ATOM.ZS.Unred.LCZ

/-!
# `ℤ[∗] ≅ LCZ` carrying `e₁` to the constant function `1`

The locally constant `ℤ`-valued light condensed abelian group `LCZ = LC(-, ℤ)` is the free
light condensed abelian group on one generator: a morphism `LCZ ⟶ A` is the same as a section
of `A` over the point.  This file proves that the canonical identification
`Work.ATOM.zfree Work.ATOM.pt ≅ LCZ` (`Work.ATOM.pt = ∗`) exists and sends the canonical generator
`e₁ = homFreeEquiv ∗ 𝟙` of `ℤ[∗](∗)` to the constant function `oneLCZ`.

The proof has two independent halves.

* The value of the generator: the unit of the adjunction
  `LightCondMod.LocallyConstant.functor ℤ ⊣ underlying (ModuleCat ℤ)` at `ℤ` is the "constant
  map" `functorIsoDiscreteAux₁`, whence `unit.hom 1 = oneLCZ`.  This is `unit_app_eq_aux₁` and
  `unit_hom_one` below.
* The freeness: `Hom(LCZ, A) ≃ A(∗)` is the composite of the adjunction bijection with the
  evaluation `Hom_{ℤ}(ℤ, M) ≃ M` at `1`, and this bijection is *equal* to `f ↦ f(∗)(oneLCZ)`
  (`homLCZEquiv_apply`).  Yoneda then turns it into the isomorphism.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

noncomputable section

namespace Work.ATOM.ZS.Unred

set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
/-- **The unit of the `LocallyConstant` adjunction is the "constant map".**  The unit of
`LightCondMod.LocallyConstant.functor ℤ ⊣ underlying (ModuleCat ℤ)` at a `ℤ`-module `M` is the
linear map `m ↦ const m : M → LC(∗, M)` of `functorIsoDiscreteAux₁`. -/
theorem unit_app_eq_aux₁ (M : ModuleCat.{0} ℤ) :
    (LightCondMod.LocallyConstant.adjunction ℤ).unit.app M
      = (LightCondMod.LocallyConstant.functorIsoDiscreteAux₁ ℤ M).hom := by
  have key : ∀ (X : ModuleCat.{0} ℤ), (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app X
      = ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).obj (op ↧PUnit.{1})).map
        ((sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).unit.app
          ((Functor.const LightProfiniteᵒᵖ).obj X)) := by
    intro X
    simp only [LightCondensed.discreteUnderlyingAdj, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
      Functor.comp_obj, CategoryTheory.evaluation_obj_obj, Category.id_comp]
  rw [LightCondMod.LocallyConstant.adjunction]
  simp only [Adjunction.ofNatIsoLeft]
  simp only [LightCondensed.discreteUnderlyingAdj, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    Functor.comp_obj, CategoryTheory.evaluation_obj_obj, Category.id_comp]
  rw [show (LightCondMod.LocallyConstant.functorIsoDiscrete (R := ℤ)).symm.hom.app M
      = (LightCondMod.LocallyConstant.functorIsoDiscreteComponents ℤ M).hom by
    rw [Iso.symm_hom]
    simp only [LightCondMod.LocallyConstant.functorIsoDiscrete, NatIso.ofComponents_inv_app,
      Iso.symm_inv]]
  simp only [LightCondMod.LocallyConstant.functorIsoDiscreteComponents,
    LightCondMod.LocallyConstant.functorIsoDiscreteAux₂, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom]
  rw [Functor.map_comp, ← Category.assoc]
  have hnat := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.naturality
    (LightCondMod.LocallyConstant.functorIsoDiscreteAux₁ ℤ M).hom
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have htri := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).right_triangle_components
    ((LightCondMod.LocallyConstant.functor ℤ).obj M)
  rw [← key M, ← hnat, Category.assoc]
  erw [htri]
  exact Category.comp_id _

/-- **The canonical generator of `LCZ(∗)`.**  The unit of the `LocallyConstant` adjunction at
`ℤ` sends `1` to the constant function `1`. -/
theorem unit_hom_one :
    (ModuleCat.Hom.hom ((LightCondMod.LocallyConstant.adjunction ℤ).unit.app
      (ModuleCat.of ℤ ℤ))) (1 : ℤ) = oneLCZ := by
  rw [unit_app_eq_aux₁]
  rfl

/-- **Evaluation at `1`**: `Hom_{ℤ}(ℤ, M) ≃ M`, `g ↦ g 1`.  (The `ℕ`-linear structure is used
only to avoid the `ℤ`-instance diamond in the round trips.) -/
noncomputable def homOfZModEquiv (M : ModuleCat.{0} ℤ) :
    (ModuleCat.of ℤ ℤ ⟶ M) ≃ ↥M where
  toFun g := g.hom 1
  invFun m := ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf (R := ℤ) (S := ℕ) (M := ↥M)).symm m)
  left_inv g := by
    apply ModuleCat.hom_ext
    exact (LinearMap.ringLmapEquivSelf (R := ℤ) (S := ℕ) (M := ↥M)).left_inv g.hom
  right_inv m := by
    exact (LinearMap.ringLmapEquivSelf (R := ℤ) (S := ℕ) (M := ↥M)).apply_symm_apply m

/-- **`LCZ` is free on one generator**: `Hom(LCZ, A) ≃ A(∗)`, by the `LocallyConstant`
adjunction followed by evaluation at `1`. -/
noncomputable def homLCZEquiv (A : LightCondAb) :
    (LCZ ⟶ A) ≃ ↥(A.obj.obj (op Work.ATOM.pt)) :=
  ((LightCondMod.LocallyConstant.adjunction ℤ).homEquiv (ModuleCat.of ℤ ℤ) A).trans
    (homOfZModEquiv ((LightCondensed.underlying (ModuleCat ℤ)).obj A))

/-- The bijection `homLCZEquiv` is *evaluation at `oneLCZ`*. -/
theorem homLCZEquiv_apply (A : LightCondAb) (f : LCZ ⟶ A) :
    homLCZEquiv A f = (f.hom.app (op Work.ATOM.pt)) oneLCZ := by
  show (ModuleCat.Hom.hom (((LightCondMod.LocallyConstant.adjunction ℤ).homEquiv
    (ModuleCat.of ℤ ℤ) A) f)) (1 : ℤ) = (f.hom.app (op Work.ATOM.pt)) oneLCZ
  rw [Adjunction.homEquiv_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [unit_hom_one]
  rw [show (LightCondensed.underlying (ModuleCat ℤ)).map f
      = f.hom.app (op Work.ATOM.pt) from rfl]
  rfl

/-- The canonical morphism `ℤ[∗] ⟶ LCZ` corresponding to the generator `oneLCZ`. -/
noncomputable def LCZhom : Work.ATOM.zfree Work.ATOM.pt ⟶ LCZ :=
  (Work.ATOM.homFreeEquiv Work.ATOM.pt LCZ).symm oneLCZ

/-- `LCZhom` is the value of `homFreeEquiv` at `oneLCZ`. -/
theorem homFreeEquiv_LCZhom :
    Work.ATOM.homFreeEquiv Work.ATOM.pt LCZ LCZhom = oneLCZ :=
  Equiv.apply_symm_apply _ _

/-- `LCZhom` carries the canonical generator `e₁` of `ℤ[∗](∗)` to `oneLCZ`. -/
theorem LCZhom_e1 : (LCZhom.hom.app (op Work.ATOM.pt)) e1 = oneLCZ := by
  rw [← homFreeEquiv_comp (𝟙 (Work.ATOM.zfree Work.ATOM.pt)) LCZhom, Category.id_comp,
    homFreeEquiv_LCZhom]

/-- Precomposition with `LCZhom` is a bijection, as both sides are naturally `A ↦ A(∗)`. -/
theorem precomp_LCZhom_bijective (A : LightCondAb) :
    Function.Bijective (fun f : LCZ ⟶ A => LCZhom ≫ f) := by
  have h1 : ∀ f : LCZ ⟶ A,
      Work.ATOM.homFreeEquiv Work.ATOM.pt A (LCZhom ≫ f) = homLCZEquiv A f := by
    intro f
    rw [homFreeEquiv_comp LCZhom f, homFreeEquiv_LCZhom]
    exact (homLCZEquiv_apply A f).symm
  have hfun : (fun f : LCZ ⟶ A => LCZhom ≫ f)
      = fun f => (Work.ATOM.homFreeEquiv Work.ATOM.pt A).symm (homLCZEquiv A f) := by
    funext f
    rw [← h1 f, Equiv.symm_apply_apply]
  rw [hfun]
  exact Equiv.bijective ((homLCZEquiv A).trans ((Work.ATOM.homFreeEquiv Work.ATOM.pt A).symm))

/-- `LCZhom : ℤ[∗] ⟶ LCZ` is an isomorphism: postcomposition with it is a bijection, hence so is
precomposition (pass to the opposite category). -/
theorem isIso_LCZhom : IsIso LCZhom := by
  refine (isIso_op_iff LCZhom).mp ?_
  refine isIso_of_yoneda_map_bijective LCZhom.op (fun T => ?_)
  obtain ⟨A⟩ := T
  constructor
  · intro x y hxy
    have h : x.unop = y.unop := by
      refine (precomp_LCZhom_bijective A).1 ?_
      have h2 := congrArg Quiver.Hom.unop hxy
      simpa using h2
    have h3 := congrArg Quiver.Hom.op h
    simpa using h3
  · intro y
    obtain ⟨f, hf⟩ := (precomp_LCZhom_bijective A).2 y.unop
    dsimp only at hf
    refine ⟨f.op, ?_⟩
    show f.op ≫ LCZhom.op = y
    rw [(CategoryTheory.op_comp (f := LCZhom) (g := f)).symm, hf]
    exact Quiver.Hom.op_unop y

theorem LCZ_iso : ∃ e : Work.ATOM.zfree Work.ATOM.pt ≅ Work.ATOM.ZS.Unred.LCZ, (e.hom.hom.app (Opposite.op Work.ATOM.pt)) Work.ATOM.ZS.Unred.e1 = Work.ATOM.ZS.Unred.oneLCZ := by
  refine ⟨@asIso _ _ _ _ LCZhom isIso_LCZhom, ?_⟩
  show (LCZhom.hom.app (op Work.ATOM.pt)) e1 = oneLCZ
  exact LCZhom_e1

end Work.ATOM.ZS.Unred
