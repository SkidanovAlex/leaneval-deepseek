import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.bsSetup
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver

variable {Γ : Type u} {V : Type u} [Group Γ] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]

/-! ## The arrow underlying a lift

`liftPath` (`Submission/Work/ORLocInd/CohenLyndon/bsSetup.lean`) lifts a path of the quotient
graph `V/Γ` to a path of `V`, using, for each arrow `e` of the quotient, the chosen lift `L A B e`
of `e`, viewed as an arrow of `V` via the endpoint equalities `hL`.  We record that arrow. -/

/-- The arrow of `V` underlying the lift `L A B e` of an arrow `e` of the quotient graph. -/
def liftArrow (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B) : x A ⟶ x B :=
  (L A B e).hom.cast (hL A B e).1 (hL A B e).2

theorem liftPath_cons_liftArrow (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    {A C B : Work.ORBassSerre.orbitV Γ V} (q : Quiver.Path A C) (e : C ⟶ B) :
    liftPath x L hL A (q.cons e) =
      (liftPath x L hL A q).cons (liftArrow x L hL C B e) := rfl

/-- The `Quiver.Total` determined by the lifted arrow is the chosen lift. -/
theorem total_liftArrow (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B) :
    Quiver.Total.mk (x A) (x B) (liftArrow x L hL A B e) = L A B e := by
  refine Quiver.Total.ext (hL A B e).1.symm (hL A B e).2.symm ?_
  exact Quiver.Hom.cast_heq (hL A B e).1 (hL A B e).2 (L A B e).hom

/-- The edge orbit of the lifted arrow is the edge orbit of the arrow it lifts. -/
theorem quot_mk_liftArrow (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (hLorb : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      Quotient.mk'' (L A B e) = e.1)
    (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B) :
    Quotient.mk'' (Quiver.Total.mk (x A) (x B) (liftArrow x L hL A B e)) = e.1 := by
  rw [total_liftArrow x L hL A B e]
  exact hLorb A B e

/-! ## Descending the last arrow of a lift -/

/-- If a lift ends with an arrow `e'`, then the lifted path is the lift of a path ending with an
arrow whose lift is `e'`. -/
theorem liftPathDescent_aux (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    {A D : Work.ORBassSerre.orbitV Γ V} {q : Quiver.Path A D}
    {b : V} {p' : Quiver.Path (x A) b} {e' : b ⟶ x D}
    (h : liftPath x L hL A q = p'.cons e') :
    ∃ (D' : Work.ORBassSerre.orbitV Γ V) (q' : Quiver.Path A D') (e'' : D' ⟶ D),
      q = q'.cons e'' ∧ Quiver.Total.mk b (x D) e' = L D' D e'' := by
  cases q with
  | nil =>
    rw [liftPath_nil] at h
    exact absurd h.symm (Quiver.Path.cons_ne_nil p' e')
  | cons q' e'' =>
    rw [liftPath_cons_liftArrow] at h
    refine ⟨_, q', e'', rfl, ?_⟩
    refine Quiver.Total.ext ?_ ?_ ?_
    · exact ((Quiver.Path.obj_eq_of_cons_eq_cons h).symm).trans ((hL _ _ e'').1).symm
    · exact ((hL _ _ e'').2).symm
    · exact (Quiver.Path.hom_heq_of_cons_eq_cons h).symm.trans (Quiver.Hom.cast_heq _ _ _)

/-! ## The endpoints of an arrow of the quotient are determined by its edge orbit -/

/-- Two arrows of the quotient graph with the same edge orbit have the same source and the same
target. -/
theorem orbitQuiverEqOfValEq_aux
    {A A' B B' : Work.ORBassSerre.orbitV Γ V} {e : A ⟶ B} {e' : A' ⟶ B'}
    (h : e.1 = e'.1) : A = A' ∧ B = B' := by
  obtain ⟨u, hu, hl, hr⟩ := e.2
  obtain ⟨v, hv, hl', hr'⟩ := e'.2
  have huv : (Quotient.mk'' u : Work.ORBassSerre.orbitE Γ V) = Quotient.mk'' v := by
    rw [hu, hv, h]
  constructor
  · rw [← hl, ← hl', Work.ORBassSerre.Action.mk_left_eq_of_mk_eq huv]
  · rw [← hr, ← hr', Work.ORBassSerre.Action.mk_right_eq_of_mk_eq huv]

/-! ## Lifts of reduced paths are reduced -/

/-- **A reduced path of the quotient graph lifts to a reduced path of `V`.**  The lift of a
reduced path has a backtrack only if the original path has one: a backtrack of the lift is a pair
of consecutive arrows `liftArrow e''`, `liftArrow e₀` which are mutually inverse in `V`, and
projecting to the quotient graph shows that `e''`, `e₀` are mutually inverse in the quotient. -/
theorem liftPath_isReduced (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (hLorb : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      Quotient.mk'' (L A B e) = e.1)
    {A B : Work.ORBassSerre.orbitV Γ V} (q : Quiver.Path A B) (hq : q.IsReduced) :
    (liftPath x L hL A q).IsReduced := by
  revert hq
  refine Quiver.Path.rec (motive := fun B q => q.IsReduced → (liftPath x L hL A q).IsReduced)
    ?_ ?_ q
  · intro _
    rw [liftPath_nil]
    exact Quiver.Path.IsReduced.nil (x A)
  · intro Z B q₀ e₀ ih hq
    rw [liftPath_cons_liftArrow]
    rw [Quiver.Path.IsReduced]
    intro r hr
    rcases (Work.ORBassSerre.Tree.Map.deleteBacktrack_cons_iff (liftPath x L hL A q₀)
        (liftArrow x L hL Z B e₀) r).mp hr with ⟨r₀, hr₀, -⟩ | ⟨p', e', hmap, he', -⟩
    · exact ih (Quiver.Path.IsReduced.of_comp (p := q₀) (q := e₀.toPath) hq) r₀ hr₀
    · -- The last two arrows of the lift are mutually inverse.
      obtain ⟨D', q', e'', hq₀eq, htot⟩ := liftPathDescent_aux x L hL hmap
      have hstep : Quiver.Total.mk (x Z) (x B) (liftArrow x L hL Z B e₀) =
          (Quiver.Total.mk (x B) (x Z) e').reverse := by
        rw [he', Quiver.Total.reverse_mk]
      have hmark : Quotient.mk'' (Quiver.Total.mk (x Z) (x B) (liftArrow x L hL Z B e₀)) =
          e₀.1 := quot_mk_liftArrow x L hL hLorb Z B e₀
      have hmark' : Quotient.mk'' (Quiver.Total.mk (x B) (x Z) e') = e''.1 := by
        rw [htot]
        exact hLorb D' Z e''
      have he1 : e₀.1 = (Quiver.reverse e'').1 := by
        calc e₀.1
            = Quotient.mk'' (Quiver.Total.mk (x Z) (x B) (liftArrow x L hL Z B e₀)) :=
              hmark.symm
          _ = Quotient.mk'' ((Quiver.Total.mk (x B) (x Z) e').reverse) := by rw [hstep]
          _ = Work.ORBassSerre.orbitEReverse
                (Quotient.mk'' (Quiver.Total.mk (x B) (x Z) e')) :=
              (Work.ORBassSerre.orbitEReverse_mk _).symm
          _ = Work.ORBassSerre.orbitEReverse e''.1 := by rw [hmark']
          _ = (Quiver.reverse e'').1 := rfl
      -- hence `e₀` and `Quiver.reverse e''` are arrows with the same endpoints
      have hBD : B = D' := (orbitQuiverEqOfValEq_aux he1).2
      subst hBD
      have he₀ : e₀ = Quiver.reverse e'' := Subtype.ext he1
      have hdb : Quiver.Path.DeleteBacktrack ((q'.cons e'').cons e₀) q' :=
        (Work.ORBassSerre.Tree.Map.deleteBacktrack_cons_iff (q'.cons e'') e₀ q').mpr
          (Or.inr ⟨q', e'', rfl, he₀, rfl⟩)
      rw [hq₀eq] at hq
      exact hq q' hdb

theorem bsGeodesicLift {Γ : Type u} {V : Type u} [Group Γ] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]
    (hT : Work.ORBassSerre.IsTree V) (hquot : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV Γ V))
    (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (hLorb : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      Quotient.mk'' (L A B e) = e.1)
    (A B : Work.ORBassSerre.orbitV Γ V) :
    hT.geodesic (x A) (x B) = liftPath x L hL A (hquot.geodesic A B) := by
  exact (hT.eq_geodesic (liftPath_isReduced x L hL hLorb (hquot.geodesic A B)
    (hquot.geodesic_isReduced A B))).symm

end Work.ORLocInd.CohenLyndon

