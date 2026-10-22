import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.zfree_iso_pt_biprod_zred
import Submission.Work.ATOM.projective_P
import Submission.Work.ATOM.zmap_ext_of_closed_cover

/-!
# Setup for `points_detect_zfree_NatUnionInfty`

The point class `[t] ∈ ℤ[T](*)` of a point `t` of a light profinite set `T`, and the basic
computations with it, phrased at the level of morphisms.

The route to `points_detect_zfree_NatUnionInfty` follows Scholze, *Lectures on Analytic Geometry*,
Proposition 2.1: the sheafification unit `S ↦ ℤ[Hom(S,T)] → ℤ[T]` is locally surjective, and a
finite point-null combination of `zmap`s is locally zero (by induction on the number of terms,
using that a finite family of distinct points has linearly independent point classes).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-- The canonical "generic element" of `ℤ[S]` over `S`. -/
def unitElemA (S : LightProfinite.{0}) : ↥((Work.ATOM.zfree S).obj.obj (op S)) :=
  ((freeForgetAdjunction ℤ).unit.app S.toCondensed).1.app (op S) (𝟙 S)

/-- Evaluation formula for `homFreeEquiv`. -/
theorem homFreeEquiv_eq_evalA (S : LightProfinite.{0}) (A : LightCondAb)
    (g : Work.ATOM.zfree S ⟶ A) :
    Work.ATOM.homFreeEquiv S A g = g.1.app (op S) (unitElemA S) := by
  simp only [unitElemA, Work.ATOM.homFreeEquiv]
  rfl

/-- `homFreeEquiv` is additive in the morphism. -/
theorem homFreeEquiv_addA (S : LightProfinite.{0}) (A : LightCondAb)
    (g g' : Work.ATOM.zfree S ⟶ A) :
    Work.ATOM.homFreeEquiv S A (g + g') =
      Work.ATOM.homFreeEquiv S A g + Work.ATOM.homFreeEquiv S A g' := by
  rw [homFreeEquiv_eq_evalA, homFreeEquiv_eq_evalA, homFreeEquiv_eq_evalA]
  have h : (g + g').1.app (op S) = g.1.app (op S) + g'.1.app (op S) :=
    Sheaf.Hom.add_app g g' (op S)
  rw [h]
  exact LinearMap.add_apply _ _ _

/-- The point class `[t]`: the image of the canonical generator of `ℤ[*]` under the map
`ℤ[*] ⟶ ℤ[T]` induced by the point `t`. -/
def pointClass (T : LightProfinite.{0}) (t : ↥T) :
    ↥((Work.ATOM.zfree T).obj.obj (op Work.ATOM.pt)) :=
  Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree T) (Work.ATOM.zmap (Work.ATOM.ptAt t))

/-- The point class `[t]` as a morphism `ℤ[*] ⟶ ℤ[T]`. -/
abbrev pointClassM (T : LightProfinite.{0}) (t : ↥T) :
    Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree T :=
  Work.ATOM.zmap (Work.ATOM.ptAt t)

/-- The point class is the morphism-level point class under `homFreeEquiv`. -/
theorem pointClass_eq (T : LightProfinite.{0}) (t : ↥T) :
    pointClass T t = Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree T)
      (pointClassM T t) := rfl

/-- The point class pushed forward along `u` is the point class of the image. -/
theorem pointClassM_comp {T T' : LightProfinite.{0}} (u : T ⟶ T') (t : ↥T) :
    pointClassM T t ≫ Work.ATOM.zmap u = pointClassM T' (u t) := by
  rw [pointClassM, pointClassM, ← Work.ATOM.zmap_comp_zfree (Work.ATOM.ptAt t) u]
  rfl

/-- The `ℤ`-linear combination `∑ j, c j • zmap (φ j)` of `zmap`s, as a morphism. -/
abbrev zmapCombo {V T : LightProfinite.{0}} {m : ℕ} (φ : Fin m → (V ⟶ T)) (c : Fin m → ℤ) :
    Work.ATOM.zfree V ⟶ Work.ATOM.zfree T :=
  ∑ j, c j • (Work.ATOM.zmap (φ j))

/-- Evaluation of a morphism out of a free object at a point of its source. -/
abbrev prePt {V T : LightProfinite.{0}} (v : ↥V) (g : Work.ATOM.zfree V ⟶ Work.ATOM.zfree T) :
    Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree T :=
  CategoryTheory.CategoryStruct.comp (Work.ATOM.zmap (Work.ATOM.ptAt v)) g

/-- Restricting a `ℤ`-linear combination of `zmap`s to a point `u` of the source gives the
corresponding combination of point classes (morphism form). -/
theorem pointValue_zmap_combo (T U : LightProfinite.{0})
    (m : ℕ) (φ : Fin m → (U ⟶ T)) (c : Fin m → ℤ) (u : ↥U) :
    Work.ATOM.zmap (Work.ATOM.ptAt u) ≫ (∑ j, c j • (Work.ATOM.zmap (φ j)))
      = ∑ j, c j • pointClassM T (φ j u) := by
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Preadditive.comp_zsmul, pointClassM_comp]

end Work.ANALYTIC
