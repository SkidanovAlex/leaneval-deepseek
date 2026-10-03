import Mathlib
import Submission.Work.ORBassSerre.Action.Quotient

namespace Work.ORBassSerre.Action.Quotient

open Quiver

/-- Translating an arrow and then viewing it as an element of `Quiver.Total V` coincides with
translating that element of `Quiver.Total V`. -/
theorem total_mk_smulArrow {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasReverse V]
    [MulAction G V] [GraphAction G V] (g : G) (u : Quiver.Total V) :
    Quiver.Total.mk (g • u.left) (g • u.right) (GraphAction.smulArrow g u.hom) = g • u := by
  obtain ⟨l, r, f⟩ := u
  refine Quiver.Total.ext ?_ ?_ ?_
  · show g • l = (g • Quiver.Total.mk l r f).left
    rw [GraphAction.smul_left_mk]
  · show g • r = (g • Quiver.Total.mk l r f).right
    rw [GraphAction.smul_right_mk]
  · show HEq (GraphAction.smulArrow g f) (g • Quiver.Total.mk l r f).hom
    exact GraphAction.smulArrow_heq g f

/-- **Path lifting with a prescribed source.**  A path in the quotient graph `V/G` which starts at
the orbit of a vertex `a` lifts to a path in `V` starting at `a`; the target of the lift is a
vertex of the prescribed target orbit. -/
theorem qpath_exists_lift_aux {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasReverse V]
    [MulAction G V] [GraphAction G V] (a : V) (B : orbitV G V)
    (p : Quiver.Path (Quotient.mk'' a) B) :
    ∃ (b : V) (p' : Quiver.Path a b), Quotient.mk'' b = B ∧
      HEq ((orbitPrefunctor (G := G) (V := V)).mapPath p') p := by
  refine Quiver.Path.rec (motive := fun (B : orbitV G V) (p : Quiver.Path (Quotient.mk'' a) B) =>
    ∃ (b : V) (p' : Quiver.Path a b), Quotient.mk'' b = B ∧
      HEq ((orbitPrefunctor (G := G) (V := V)).mapPath p') p) ?_ ?_ p
  · exact ⟨a, Quiver.Path.nil, rfl, heq_of_eq (Prefunctor.mapPath_nil _ a)⟩
  · intro B c q e ih
    obtain ⟨b, q', hb, hq⟩ := ih
    subst hb
    obtain ⟨u, hu, hl, hr⟩ := e.2
    obtain ⟨g, hg⟩ := Quotient.exact hl
    have hb' : b = g⁻¹ • u.left := by rw [← hg, inv_smul_smul]
    subst hb'
    have hqe : (orbitPrefunctor (G := G) (V := V)).mapPath q' = q := eq_of_heq hq
    have hc : Quotient.mk'' (g⁻¹ • u.right) = c := by
      rw [← hr]
      exact Quotient.sound ⟨g⁻¹, rfl⟩
    subst hc
    refine ⟨g⁻¹ • u.right, q'.cons (GraphAction.smulArrow g⁻¹ u.hom), rfl, ?_⟩
    rw [Prefunctor.mapPath_cons, hqe]
    apply heq_of_eq
    congr 1
    apply Subtype.ext
    show Quotient.mk'' (Quiver.Total.mk (g⁻¹ • u.left) (g⁻¹ • u.right)
      (GraphAction.smulArrow g⁻¹ u.hom)) = e.1
    rw [← hu, total_mk_smulArrow]
    exact Quotient.sound ⟨g⁻¹, rfl⟩

/-- Every path in the quotient graph `V/G` lifts to a path in `V`. -/
theorem qpath_exists_lift {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasReverse V]
    [MulAction G V] [Work.ORBassSerre.GraphAction G V] (A B : Work.ORBassSerre.orbitV G V)
    (p : Quiver.Path A B) :
    ∃ (a b : V) (p' : Quiver.Path a b), Quotient.mk'' a = A ∧ Quotient.mk'' b = B ∧
      HEq ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p') p := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep A
  subst ha
  obtain ⟨b, p', hb, hp⟩ := qpath_exists_lift_aux (G := G) (V := V) a B p
  exact ⟨a, b, p', rfl, hb, hp⟩

end Work.ORBassSerre.Action.Quotient
