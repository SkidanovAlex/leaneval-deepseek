import Mathlib
import Submission.Work.ANALYTIC.CechPt.Bridge
import Submission.Work.ANALYTIC.CechPt.solidFreeNaturalMu
import Submission.Work.ANALYTIC.CechPt.IntervalAug
import Submission.Work.ANALYTIC.CechPt.CechTermDefs
import Submission.Work.ANALYTIC.CechPt.LevelModelDefs
import Submission.Work.ANALYTIC.CechPt.binaryExp_epi
import Submission.Work.DERFORMAL.B1B2
import Submission.Work.REFL.Main

/-!
# The canonical (double-dual) model of the solid Čech complex

This module sets up the *canonical* model of the solid Čech complex of the Cantor cover.  The
differentials come from the intrinsic double duality `X ↦ (X ⟹ 𝟙) ⟹ 𝟙` of the monoidal-closed
structure of `LightCondAb`, rather than from the choice-based `Aux.sdMap` of
`Submission/Work/ANALYTIC/CechPt/solidFreeNaturalMu.lean`.

The point of the canonical model is that the contractibility of the augmented *dual* Čech complex
(REFS/04 §1: `0 → ℤ → C(C_0,ℤ) → C(C_1,ℤ) → ⋯` is a bounded-below exact complex of free abelian
groups, hence contractible) is contravariantly functorial: the dual complex is
`E_• = (𝟙 → (ℤ[C_0] ⟹ 𝟙) → (ℤ[C_1] ⟹ 𝟙) → ⋯)`, and the solid Čech complex is `Hom(-, 𝟙)` of it,
so a contraction of `E_•` dualises to a contraction of the solid complex.  Nothing here uses the
non-canonical `Aux.sdMap`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- The free light condensed abelian group on a light profinite set. -/
abbrev zf (T : LightProfinite.{0}) : LightCondAb :=
  (LightCondensed.free (R := ℤ)).obj T.toCondensed

/-- The single dual `X ↦ (X ⟹ 𝟙)`. -/
abbrev sd (X : LightCondAb) : LightCondAb := (ihom X).obj (𝟙_ LightCondAb)

/-- The double dual `X ↦ (X ⟹ 𝟙) ⟹ 𝟙`. -/
abbrev dd (X : LightCondAb) : LightCondAb := sd (sd X)

/-! ## Linearity of currying and of precomposition -/

theorem uncurry_add {A X Y : LightCondAb} (f g : Y ⟶ (ihom A).obj X) :
    MonoidalClosed.uncurry (f + g) = MonoidalClosed.uncurry f + MonoidalClosed.uncurry g := by
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

/-- Additivity of precomposition in the internal hom. -/
theorem pre_add {A B : LightCondAb} (f g : B ⟶ A) :
    MonoidalClosed.pre (f + g) = MonoidalClosed.pre f + MonoidalClosed.pre g := by
  apply CategoryTheory.NatTrans.ext
  funext X
  apply MonoidalClosed.uncurry_injective
  show MonoidalClosed.uncurry ((MonoidalClosed.pre (f + g)).app X) =
    MonoidalClosed.uncurry ((MonoidalClosed.pre f).app X + (MonoidalClosed.pre g).app X)
  rw [uncurry_add, MonoidalClosed.uncurry_pre, MonoidalClosed.uncurry_pre,
    MonoidalClosed.uncurry_pre, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

/-- Pointwise form of additivity of precomposition. -/
theorem pre_app_add {A B X : LightCondAb} (f g : B ⟶ A) :
    (MonoidalClosed.pre (f + g)).app X =
      (MonoidalClosed.pre f).app X + (MonoidalClosed.pre g).app X := by
  rw [pre_add]
  rfl

/-- Precomposition with the zero morphism is zero. -/
theorem pre_zero {A B : LightCondAb} : MonoidalClosed.pre (0 : B ⟶ A) = 0 := by
  apply CategoryTheory.NatTrans.ext
  funext X
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre, MonoidalClosed.uncurry_eq]
  simp



/-! ## The double-dual on morphisms -/

/-- The double dual of a morphism, `X ⟶ ((X ⟹ 𝟙) ⟹ 𝟙) ⟶ ((Y ⟹ 𝟙) ⟹ 𝟙)`. -/
noncomputable def ddFMap {X Y : LightCondAb} (f : X ⟶ Y) : dd X ⟶ dd Y :=
  (MonoidalClosed.pre ((MonoidalClosed.pre f).app (𝟙_ LightCondAb))).app (𝟙_ LightCondAb)

theorem ddFMap_id (X : LightCondAb) : ddFMap (𝟙 X) = 𝟙 (dd X) := by
  show (MonoidalClosed.pre ((MonoidalClosed.pre (𝟙 X)).app (𝟙_ LightCondAb))).app
    (𝟙_ LightCondAb) = 𝟙 (dd X)
  rw [MonoidalClosed.pre_id, CategoryTheory.NatTrans.id_app, MonoidalClosed.pre_id,
    CategoryTheory.NatTrans.id_app]

theorem ddFMap_comp {X Y Z : LightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ddFMap (f ≫ g) = ddFMap f ≫ ddFMap g := by
  show (MonoidalClosed.pre ((MonoidalClosed.pre (f ≫ g)).app (𝟙_ LightCondAb))).app
    (𝟙_ LightCondAb) =
    (MonoidalClosed.pre ((MonoidalClosed.pre f).app (𝟙_ LightCondAb))).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.pre ((MonoidalClosed.pre g).app (𝟙_ LightCondAb))).app (𝟙_ LightCondAb)
  rw [MonoidalClosed.pre_map f g, CategoryTheory.NatTrans.comp_app,
    MonoidalClosed.pre_map ((MonoidalClosed.pre g).app (𝟙_ LightCondAb))
      ((MonoidalClosed.pre f).app (𝟙_ LightCondAb)), CategoryTheory.NatTrans.comp_app]

theorem ddFMap_zero {X Y : LightCondAb} : ddFMap (0 : X ⟶ Y) = 0 := by
  show (MonoidalClosed.pre ((MonoidalClosed.pre (0 : X ⟶ Y)).app (𝟙_ LightCondAb))).app
    (𝟙_ LightCondAb) = 0
  simp only [pre_zero, CategoryTheory.NatTrans.app_zero]

theorem ddFMap_add {X Y : LightCondAb} (f g : X ⟶ Y) :
    ddFMap (f + g) = ddFMap f + ddFMap g := by
  show (MonoidalClosed.pre ((MonoidalClosed.pre (f + g)).app (𝟙_ LightCondAb))).app
      (𝟙_ LightCondAb) = (MonoidalClosed.pre ((MonoidalClosed.pre f).app (𝟙_ LightCondAb))).app
      (𝟙_ LightCondAb) + (MonoidalClosed.pre ((MonoidalClosed.pre g).app (𝟙_ LightCondAb))).app
      (𝟙_ LightCondAb)
  rw [pre_app_add, pre_add]
  rw [CategoryTheory.NatTrans.app_add]

/-- The double dual as an endofunctor of `LightCondAb`. -/
noncomputable def ddF : LightCondAb ⥤ LightCondAb where
  obj X := dd X
  map f := ddFMap f
  map_id X := ddFMap_id X
  map_comp f g := ddFMap_comp f g

/-! ## The double-dual unit -/

/-- The double-dual unit `X ⟶ ((X ⟹ 𝟙) ⟹ 𝟙)`, obtained by currying the evaluation pairing
`(X ⟹ 𝟙) ⊗ X ⟶ 𝟙`. -/
noncomputable def doubleDualUnit (X : LightCondAb) : X ⟶ dd X :=
  MonoidalClosed.curry
    ((BraidedCategory.braiding (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb))

/-- The canonical evaluation pairing `ℤ[T] ⟶ ℤ■[T]`, in the canonical double-dual model. -/
noncomputable abbrev evT (T : LightProfinite.{0}) : zf T ⟶ dd (zf T) :=
  doubleDualUnit (zf T)

/-- Uncurried form of the double-dual unit. -/
theorem doubleDualUnit_uncurry (X : LightCondAb) :
    MonoidalClosed.uncurry (doubleDualUnit X) =
      (BraidedCategory.braiding (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb) :=
  MonoidalClosed.uncurry_curry _

/-- Uncurried form of the naturality square. -/
theorem uncurry_doubleDual_map {X Y : LightCondAb} (f : X ⟶ Y) :
    MonoidalClosed.uncurry (doubleDualUnit X ≫ ddFMap f) =
      ((MonoidalClosed.pre f).app (𝟙_ LightCondAb)) ▷ X ≫
        MonoidalClosed.uncurry (doubleDualUnit X) :=
  MonoidalClosed.uncurry_pre_app (A := sd X) (X := 𝟙_ LightCondAb) (B := sd Y) (Y := X)
    (doubleDualUnit X) ((MonoidalClosed.pre f).app (𝟙_ LightCondAb))

/-- Naturality of the double-dual unit: this is what makes the canonical comparison
`ℤ[T_p] → ℤ■[T_p]` a chain map. -/
theorem doubleDualUnit_natural {X Y : LightCondAb} (f : X ⟶ Y) :
    f ≫ doubleDualUnit Y = doubleDualUnit X ≫ ddFMap f := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, doubleDualUnit_uncurry, uncurry_doubleDual_map,
    doubleDualUnit_uncurry]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_left_assoc]
  congr 1
  exact (MonoidalClosed.id_tensor_pre_app_comp_ev f (𝟙_ LightCondAb)).symm

end Work.ANALYTIC.CechPt
