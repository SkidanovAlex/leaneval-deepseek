import Mathlib
import Submission.Work.ORBassSerre.Action.Quotient

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action

open Quiver

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasReverse V] [MulAction G V]
  [Work.ORBassSerre.GraphAction G V]

/-- Casting the final arrow of a `cons` path along equalities of the endpoints: the two ways of
transporting `p.cons e` (transporting the intermediate vertex with `hm`) agree. -/
theorem orbitSmul_cons_cast {V : Type*} [Quiver V] {u v w u' v' w' : V}
    (p : Quiver.Path u v) (e : v ⟶ w) (hu : u = u') (hm : v = v') (hw : w = w') :
    (p.cast hu hm).cons (e.cast hm hw) = (p.cons e).cast hu hw := by
  cases hu; cases hm; cases hw; rfl

/-- The class in `V/G` of `g • x` is the class of `x`. -/
theorem orbitSmul_obj_eq_obj (g : G) (x : V) :
    (orbitPrefunctor (G := G) (V := V)).obj x =
      (orbitPrefunctor (G := G) (V := V)).obj (g • x) :=
  Quotient.sound ⟨g⁻¹, by simp⟩

/-- The total arrow `z • e` agrees with the transported arrow `smulArrow z e`. -/
theorem orbitSmul_total_mk (z : G) {b c : V} (e : b ⟶ c) :
    Quiver.Total.mk (z • b) (z • c) (GraphAction.smulArrow z e) =
      z • Quiver.Total.mk b c e := by
  apply Quiver.Total.ext
  · exact (GraphAction.smul_left z (Quiver.Total.mk b c e)).symm
  · exact (GraphAction.smul_right z (Quiver.Total.mk b c e)).symm
  · exact GraphAction.smulArrow_heq z e

/-- The images in the quotient graph of `smulArrow z e` and of `e` are (heterogeneously) equal. -/
theorem orbitSmul_map_smulArrow_heq (z : G) {b c : V} (e : b ⟶ c) :
    HEq ((orbitPrefunctor (G := G) (V := V)).map (GraphAction.smulArrow z e))
        ((orbitPrefunctor (G := G) (V := V)).map e) := by
  show HEq (orbitArrow (G := G) (GraphAction.smulArrow z e)) (orbitArrow (G := G) e)
  refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
  · intro E
    constructor <;> rintro ⟨t, h1, h2, h3⟩
    · exact ⟨t, h1, h2.trans (orbitSmul_obj_eq_obj (G := G) (V := V) z b).symm,
        h3.trans (orbitSmul_obj_eq_obj (G := G) (V := V) z c).symm⟩
    · exact ⟨t, h1, h2.trans (orbitSmul_obj_eq_obj (G := G) (V := V) z b),
        h3.trans (orbitSmul_obj_eq_obj (G := G) (V := V) z c)⟩
  · rw [orbitArrow_val, orbitArrow_val, orbitSmul_total_mk]
    exact Quotient.sound ⟨z, by simp⟩

/-- The cast form of the previous statement: transporting the image of `e` to the endpoints of
`smulArrow z e` yields the image of `smulArrow z e`. -/
theorem orbitSmul_map_smulArrow_cast (z : G) {b c : V} (e : b ⟶ c) :
    (orbitPrefunctor (G := G) (V := V)).map (GraphAction.smulArrow z e) =
      ((orbitPrefunctor (G := G) (V := V)).map e).cast
        (orbitSmul_obj_eq_obj (G := G) (V := V) z b)
        (orbitSmul_obj_eq_obj (G := G) (V := V) z c) :=
  (Quiver.Hom.eq_cast_iff_heq _ _ _ _).2 (orbitSmul_map_smulArrow_heq z e)

/-- The image in the quotient of a translated path is the transport of the image of the path. -/
theorem orbitSmul_mapPath_cast (z : G) {a b : V} (d : Quiver.Path a b) :
    (orbitPrefunctor (G := G) (V := V)).mapPath (smulPath z d) =
      ((orbitPrefunctor (G := G) (V := V)).mapPath d).cast
        (orbitSmul_obj_eq_obj (G := G) (V := V) z a)
        (orbitSmul_obj_eq_obj (G := G) (V := V) z b) := by
  induction d with
  | nil =>
      rw [smulPath_nil, Prefunctor.mapPath_nil]
      exact (Quiver.Path.cast_nil (orbitSmul_obj_eq_obj (G := G) (V := V) z a)).symm
  | cons p e ih =>
      rw [smulPath_cons, Prefunctor.mapPath_cons, ih, Prefunctor.mapPath_cons]
      rw [← orbitSmul_cons_cast (p := (orbitPrefunctor (G := G) (V := V)).mapPath p)
            (e := (orbitPrefunctor (G := G) (V := V)).map e)]
      rw [orbitSmul_map_smulArrow_cast]

/-- The action of the group on the quotient graph is trivial: for `z : G` and any path `d` in `V`, the image in `V/G` of the translated path `z • d` is (heterogeneously) equal to the image of `d`. -/
theorem orbitPrefunctor_mapPath_smul_heq {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V] (z : G) {u w : V}
    (d : Quiver.Path u w) :
    HEq ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath
        (Work.ORBassSerre.smulPath z d))
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d) := by
  exact ((Quiver.Path.cast_eq_iff_heq (orbitSmul_obj_eq_obj (G := G) (V := V) z u)
      (orbitSmul_obj_eq_obj (G := G) (V := V) z w)
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d)
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath
        (Work.ORBassSerre.smulPath z d))).1 (orbitSmul_mapPath_cast z d).symm).symm

end Work.ORBassSerre.Action
