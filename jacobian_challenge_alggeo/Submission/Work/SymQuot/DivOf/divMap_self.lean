import Mathlib
import Submission.Work.SymQuot.DivOf.TowerSquare
import Submission.Work.CurveBasics.BCSquare

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-! ### The base-change square of the identity field extension is the identity square

For `F' = F` the tower morphism `C_F ⟶ C_F` is the identity, and the three ingredients of
`Curve.BCSquare.divMapCoeff` degenerate:

* `towerHom_self` — the projection of `bcSquareTower F F` is `𝟙`;
* `under_self` — the place below a place is the place itself;
* `fieldMap_self` — the induced map of function fields is the identity;
* `ramIdx_self` — the ramification index is `1`.

Together they give `divMap_self`: base change along the identity field extension does nothing. -/

/-- The structure morphism `Spec F ⟶ Spec F` of the identity field extension is the identity. -/
theorem specMap_self (F : Type u) [Field F] :
    Curve.specMap F F = 𝟙 (Spec (CommRingCat.of F)) := by
  rw [Curve.specMap]
  simp

/-- **The tower morphism of the identity field extension is the identity.** -/
theorem towerHom_self {K : Type u} [Field K] {C : Curve K} (F : Type u) [Field F]
    [Algebra K F] :
    BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F) =
      𝟙 (Curve.baseChangeLeft C F) := by
  rw [BCSquareBaseChange.towerHom]
  simp [Curve.specMap, Curve.baseChangeFst, Curve.baseChangeHom]

variable {k : Type u} [Field k] {C : Curve k}

/-- If the projection of a base-change square `S : BCSquare C C` is the identity, then the
place of `C` below a place of `C` is the place itself. -/
theorem under_self (S : Curve.BCSquare C C) (hπ : S.π = 𝟙 C.left) (Q' : C.Place)
    (h : IsClosed ({S.π Q'.point} : Set C.left)) : S.under Q' h = Q' := by
  obtain ⟨π, hpb⟩ := S
  simp only at hπ
  subst hπ
  ext
  simp [Curve.BCSquare.under]

/-- If the projection of a base-change square `S : BCSquare C C` is the identity, then the
induced map of function fields is the identity. -/
theorem fieldMap_self (S : Curve.BCSquare C C) (hπ : S.π = 𝟙 C.left) :
    S.fieldMap = 𝟙 C.functionField := by
  obtain ⟨π, hpb⟩ := S
  simp only at hπ
  subst hπ
  rw [Curve.BCSquare.fieldMap]
  simp [Scheme.Hom.stalkMap_id, TopCat.Presheaf.stalkSpecializes_refl]

/-- If the projection of a base-change square `S : BCSquare C C` is the identity, then the
ramification index of every place of `C` is `1`. -/
theorem ramIdx_self (S : Curve.BCSquare C C) (hπ : S.π = 𝟙 C.left) (Q' : C.Place) :
    S.ramIdx Q' = 1 := by
  have hf : S.fieldMap = 𝟙 C.functionField := fieldMap_self S hπ
  have hfield : ∀ x, (S.fieldMap).hom x = x := by
    intro x
    rw [congrArg CommRingCat.Hom.hom hf, CommRingCat.hom_id, RingHom.id_apply]
  rw [Curve.BCSquare.ramIdx]
  split_ifs with h
  · rw [Curve.ordAt, under_self S hπ Q' h]
    rw [hfield]
    exact Place.ord_uniformizer Q'
  · exact absurd (by rw [hπ]; exact Curve.Place.isClosed Q') h

theorem divMap_self {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} (F : Type u) [Field F]
    [Algebra K F] (D : (C.baseChange F).Div) :
    (bcSquareTower (C := C) F F).divMap D = D := by
  have hπ : (bcSquareTower (C := C) F F).π = 𝟙 ((C.baseChange F).left) := towerHom_self F
  ext Q'
  rw [Curve.BCSquare.divMap_apply, Curve.BCSquare.divMapCoeff]
  split_ifs with h
  · rw [under_self _ hπ Q' h, ramIdx_self _ hπ Q', mul_one]
  · exact absurd (by rw [hπ]; exact Curve.Place.isClosed Q') h

end Work.SymQuot.DivOf

open Work.CurveBasics

/-- The statement as requested at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.divMap_self` (the declaration above, which sits in the
doubly opened namespace inherited from this file's original skeleton). -/
theorem divMap_self {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} (F : Type u) [Field F]
    [Algebra K F] (D : (C.baseChange F).Div) :
    (bcSquareTower (C := C) F F).divMap D = D :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.divMap_self F D

end Work.SymQuot.DivOf
