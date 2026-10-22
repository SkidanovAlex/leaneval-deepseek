import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.zdesc

/-!
# The "locally constant ℤ" light condensed abelian group `LCZ`

This file collects the general toolkit used to prove
`Work.ATOM.ZS.Unred.LocallyConstantIndicator`.

The target is: for a light profinite set `T` and a locally constant function `f : ↥T → ℤ` there is
a morphism `φ : ℤ[T] ⟶ ℤ[*]` with `zmap (ptAt t) ≫ φ = f t • 𝟙` for every `t : ↥T`.

The morphism `φ` is built as follows.  A morphism `j : LCZ ⟶ ℤ[*]` out of the locally-constant-ℤ
sheaf (where `LCZ(S) = LocallyConstant ↥S ℤ`) induces, for every `T` and every `f : ↥T → ℤ`
locally constant, the element `j_T(f) ∈ ℤ[*](T)` and hence, by `homFreeEquiv`, a morphism
`φ : ℤ[T] ⟶ ℤ[*]`.  Its values are computed by naturality of `j` and of `homFreeEquiv`:
`zmap (ptAt t) ≫ φ` has value `f t · j_*(1)`.  So we need a `j` whose value at the point is the
canonical generator `e₁ = homFreeEquiv * 𝟙` of `ℤ[*](*)`, i.e. an identification
`ℤ[*] ≅ ℤ` carrying the constant function `1` to `e₁`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

noncomputable section

namespace Work.ATOM.ZS.Unred

/-- The locally constant `ℤ` light condensed abelian group: the value at a light profinite set `S`
is `LocallyConstant ↥S ℤ`.  (Stated as an `abbrev` so that the definitional unfolding is available
at the transparency levels used by `rw` and type class search.) -/
noncomputable abbrev LCZ : LightCondAb :=
  (LightCondMod.LocallyConstant.functor ℤ).obj (ModuleCat.of ℤ ℤ)

/-- The constant function `1` in `LCZ(*) = LocallyConstant ↥* ℤ = ℤ`.  This is the image of the
generator of `ℤ` under the identification `ℤ ≅ LCZ(*)`. -/
noncomputable abbrev oneLCZ : ↥(LCZ.obj.obj (op Work.ATOM.pt)) :=
  LocallyConstant.const (↥Work.ATOM.pt.toTop) (1 : ℤ)

/-- The canonical generator `e₁ = homFreeEquiv * 𝟙` of `ℤ[*](*) = End(ℤ[*])`. -/
noncomputable abbrev e1 : ↥((Work.ATOM.zfree Work.ATOM.pt).obj.obj (op Work.ATOM.pt)) :=
  Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
    (𝟙 (Work.ATOM.zfree Work.ATOM.pt))

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `homFreeEquiv` in the target.**  Precomposition of a morphism `ℤ[S] ⟶ A` with
`α : A ⟶ B` corresponds to applying the section map of `α` at `S`. -/
theorem homFreeEquiv_comp {S : LightProfinite.{0}} {A B : LightCondAb}
    (g : Work.ATOM.zfree S ⟶ A) (α : A ⟶ B) :
    Work.ATOM.homFreeEquiv S B (g ≫ α) = (α.hom.app (op S)) (Work.ATOM.homFreeEquiv S A g) := by
  show (coherentTopology LightProfinite).yonedaEquiv
      ((freeForgetAdjunction ℤ).homEquiv (lightProfiniteToLightCondSet.obj S) B (g ≫ α)) =
    (ConcreteCategory.hom (α.hom.app (op S)))
      ((coherentTopology LightProfinite).yonedaEquiv
        ((freeForgetAdjunction ℤ).homEquiv (lightProfiniteToLightCondSet.obj S) A g))
  rw [Adjunction.homEquiv_naturality_right]
  rw [GrothendieckTopology.yonedaEquiv_comp]
  rw [LightCondensed.forget_map_hom_app_hom_apply]

/-- **The endomorphism `a • 𝟙` acts on sections as multiplication by `a`** (at the level of
`ModuleCat`, used in `smul_id_section`). -/
theorem moduleCat_smul_id_apply (M : ModuleCat ℤ) (a : ℤ) (x : M) : (a • 𝟙 M) x = a • x := by
  rw [← int_smul_eq_zsmul M.isModule a x]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  exact (int_smul_eq_zsmul M.isModule a x).symm

/-- The endomorphism `a • 𝟙 X` of a light condensed abelian group acts on sections of `X` over any
light profinite set `S` as multiplication by `a`. -/
theorem smul_id_section (X : LightCondAb) (S : LightProfinite.{0}) (a : ℤ)
    (x : ↥(X.obj.obj (op S))) :
    (((a • (𝟙 X : X ⟶ X)) : X ⟶ X).hom.app (op S)) x = a • x := by
  have h1 : ((a • (𝟙 X : X ⟶ X)) : X ⟶ X).hom = a • (𝟙 X : X ⟶ X).hom := rfl
  rw [h1, NatTrans.app_smul]
  rw [show (𝟙 X : X ⟶ X).hom = 𝟙 X.obj from ObjectProperty.FullSubcategory.id_hom _ X,
    NatTrans.id_app]
  exact moduleCat_smul_id_apply (X.obj.obj (op S)) a x

/-- **The section map of a morphism is `ℤ`-linear.** -/
theorem section_map_smul (A B : LightCondAb) (φ : A ⟶ B) (S : LightProfinite.{0}) (a : ℤ)
    (x : ↥(A.obj.obj (op S))) :
    φ.hom.app (op S) (a • x) = a • (φ.hom.app (op S) x) := by
  rw [← int_smul_eq_zsmul (A.obj.obj (op S)).isModule a x,
    ← int_smul_eq_zsmul (B.obj.obj (op S)).isModule a (φ.hom.app (op S) x)]
  exact LinearMap.map_smul (ModuleCat.Hom.hom (φ.hom.app (op S))) a x

end Work.ATOM.ZS.Unred
