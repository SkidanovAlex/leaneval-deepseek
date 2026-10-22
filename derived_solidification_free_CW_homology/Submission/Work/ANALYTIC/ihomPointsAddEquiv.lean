import Mathlib
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ATOM.Toolkit.MonoidalPreadditive

/-!
# Additivity of `LightCondensed.ihomPoints`

`LightCondensed.ihomPoints R A B S` is the bijection
`(A ⟶[LightCondMod R] B)(S) ≃ (A ⊗ R[S] ⟶ B)` between the sections of the internal hom and the
morphisms out of the tensor product.  This file proves that, for `R = ℤ`, it is *additive*: both
sides are `ℤ`-modules and the equivalence is `ℤ`-linear.  Concretely we show that the inverse
`(A ⊗ ℤ[S] ⟶ B) ≃ (A ⟹ B)(S)` is additive, which is the form needed when one wants to transport
linear-algebraic arguments (sums, scalar multiples) through `ihomPoints`.

The mathematical content is small: `ihomPoints` is built from the currying adjunction
`MonoidalClosed.curry` and from the free/forget adjunction `ℤ[S] ⟶ -` (evaluated at the section
`secUnit S` corresponding to `1`), both of which are additive.  The only bookkeeping is to express
`(ihomPoints _ _ _ S).symm` as the evaluation of `MonoidalClosed.curry` at `secUnit S`
(`ihomPoints_symm_apply'`), so that additivity of `curry` and of the evaluation map applies.

Main results:
* `Work.ANALYTIC.uncurry_add'`, `Work.ANALYTIC.curry_add'`: `curry`/`uncurry` are additive;
* `Work.ANALYTIC.ihomPoints_symm_apply'`: `(ihomPoints).symm` is evaluation of `curry` at
  `secUnit S`;
* `Work.ANALYTIC.ihomPoints_symm_add'`: `(ihomPoints).symm` is additive;
* `Work.ANALYTIC.ihomPointsSymmAddEquiv`: the additive equivalence with underlying function
  `(ihomPoints).symm`, and `Work.ANALYTIC.ihomPoints_symm_zsmul'`: its `ℤ`-linearity;
* `Work.ANALYTIC.ihomPointsAddEquiv`: the existence of such an additive equivalence.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-! ## Additivity of `curry` and `uncurry`

Both are consequences of additivity of the tensor product in the first variable
(`MonoidalPreadditive.whiskerLeft_add`) and of composition
(`Preadditive.add_comp`/`Preadditive.comp_add`). -/

/-- `uncurry` is additive: it is composition with the evaluation `(ihom.ev A).app Y`, which is
additive in its first argument. -/
theorem uncurry_add' {A X Y : LightCondAb} (f g : X ⟶ (ihom A).obj Y) :
    MonoidalClosed.uncurry (f + g) = MonoidalClosed.uncurry f + MonoidalClosed.uncurry g := by
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

/-- `curry` is additive: `uncurry` is injective (it is the inverse of `curry`). -/
theorem curry_add' {A X Y : LightCondAb} (f g : A ⊗ X ⟶ Y) :
    MonoidalClosed.curry (f + g) = MonoidalClosed.curry f + MonoidalClosed.curry g :=
  MonoidalClosed.uncurry_injective (by
    rw [MonoidalClosed.uncurry_curry, uncurry_add', MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_curry])

/-! ## `(ihomPoints).symm` as evaluation of `curry` at `secUnit` -/

/-- The inverse of `ihomPoints` is the evaluation of `MonoidalClosed.curry` at the section
`secUnit S` of `ℤ[S]` corresponding to the unit of the free module: this is the definition of
`ihomPoints` (`ihomPoints_symm_apply`) combined with the identification
`Hom(ℤ[S], M) ≃ M(S)`, `g ↦ g(secUnit S)` (`freeHomEquiv_eq`). -/
theorem ihomPoints_symm_apply' {A B : LightCondAb} (S : LightProfinite.{0})
    (w : A ⊗ Work.ATOM.zfree S ⟶ B) :
    (LightCondensed.ihomPoints ℤ A B S).symm w
      = (MonoidalClosed.curry w).hom.app (Opposite.op S) (secUnit S) := by
  rw [LightCondensed.ihomPoints_symm_apply]
  exact Work.ANALYTIC.freeHomEquiv_eq S ((ihom A).obj B) (MonoidalClosed.curry w)

/-- **Additivity of the inverse of `ihomPoints`.**  Rewriting both sides by
`ihomPoints_symm_apply'`, the claim becomes additivity of `curry` followed by evaluation at
`secUnit S`, which is `curry_add'` and the additivity of the module-hom evaluation. -/
theorem ihomPoints_symm_add' {A B : LightCondAb} (S : LightProfinite.{0})
    (x y : A ⊗ Work.ATOM.zfree S ⟶ B) :
    (LightCondensed.ihomPoints ℤ A B S).symm (x + y)
      = (LightCondensed.ihomPoints ℤ A B S).symm x
        + (LightCondensed.ihomPoints ℤ A B S).symm y := by
  rw [ihomPoints_symm_apply', ihomPoints_symm_apply', ihomPoints_symm_apply', curry_add',
    Sheaf.Hom.add_app]
  exact moduleCat_hom_add_apply _ _ (secUnit S)

/-! ## The main statement -/

/-- The inverse of `ihomPoints` as an additive equivalence, i.e. *the statement* of
`ihomPointsAddEquiv` with the witness exposed (so that it can be applied, e.g. to derive
`ℤ`-linearity, without going through `Exists.choose`). -/
noncomputable def ihomPointsSymmAddEquiv (A B : LightCondAb) (S : LightProfinite.{0}) :
    AddEquiv ((CategoryTheory.MonoidalCategoryStruct.tensorObj A
        ((LightCondensed.free ℤ).obj S.toCondensed)) ⟶ B)
        (↥(((CategoryTheory.ihom A).obj B).obj.obj (Opposite.op S))) :=
  { (LightCondensed.ihomPoints ℤ A B S).symm with
      map_add' := fun x y => ihomPoints_symm_add' (A := A) (B := B) S x y }

/-- The underlying function of `ihomPointsSymmAddEquiv` is `(ihomPoints).symm` (by definition). -/
theorem ihomPointsSymmAddEquiv_apply {A B : LightCondAb} (S : LightProfinite.{0})
    (x : A ⊗ Work.ATOM.zfree S ⟶ B) :
    ihomPointsSymmAddEquiv A B S x = (LightCondensed.ihomPoints ℤ A B S).symm x := rfl

/-- `ℤ`-linearity of `(ihomPoints).symm`, deduced from its additivity (both sides are
`ℤ`-modules). -/
theorem ihomPoints_symm_zsmul' {A B : LightCondAb} (S : LightProfinite.{0}) (c : ℤ)
    (x : A ⊗ Work.ATOM.zfree S ⟶ B) :
    (LightCondensed.ihomPoints ℤ A B S).symm (c • x)
      = c • (LightCondensed.ihomPoints ℤ A B S).symm x := by
  rw [← ihomPointsSymmAddEquiv_apply S (c • x), ← ihomPointsSymmAddEquiv_apply S x]
  exact map_zsmul (ihomPointsSymmAddEquiv A B S) c x

/-- **The additivity of `ihomPoints`.**  For light condensed abelian groups `A`, `B` and a light
profinite set `S`, the bijection `(A ⊗ ℤ[S] ⟶ B) ≃ (A ⟹ B)(S)` induced by
`LightCondensed.ihomPoints` is additive (equivalently, `ℤ`-linear: the source and target are
`ℤ`-modules). -/
theorem ihomPointsAddEquiv (A B : LightCondAb) (S : LightProfinite.{0}) :
    ∃ e : AddEquiv ((CategoryTheory.MonoidalCategoryStruct.tensorObj A
        ((LightCondensed.free ℤ).obj S.toCondensed)) ⟶ B)
        (↥(((CategoryTheory.ihom A).obj B).obj.obj (Opposite.op S))),
      ⇑e = (LightCondensed.ihomPoints ℤ A B S).symm :=
  ⟨ihomPointsSymmAddEquiv A B S, rfl⟩

end Work.ANALYTIC
