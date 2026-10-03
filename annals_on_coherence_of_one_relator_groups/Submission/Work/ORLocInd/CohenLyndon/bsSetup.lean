/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bass--Serre structure theorem: the lifted fundamental domain

This file sets up the vocabulary for the proof of the Bass--Serre structure theorem
(`Work.ORLocInd.CohenLyndon.bsStructure`):

* `lastHom`, `lastTotal`: the last arrow of a nonempty path;
* `liftPath`: the lift of a path of the quotient graph `V/Γ` to a path of `V`, along a section of
  the vertex orbits together with lifts of the arrows with matching endpoints;
* the equivariance of the geodesic of a tree under the group action, and the compatibility of the
  last arrow with translation;
* the fact that the source and target of an arrow of the quotient graph are the source and target
  of its edge orbit.

The main file `Submission/Work/ORLocInd/CohenLyndon/bsStructure.lean` uses these to turn the
reduced word in the free product of the vertex stabilisers into a closed walk in `V`, whose
junction backtrack is then a contradiction.
-/
import Mathlib
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORBassSerre.Tree.Seg.smul_reducedSpan
import Submission.Work.ORBassSerre.Action.Quotient.qpath_exists_lift
import Submission.Work.ORBassSerre.Action.fg_of_isCocompact_tree
import Submission.Work.ORBassSerre.Tree.Walk.exists_consecutive_backtrack_of_closed_walk

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver

variable {Γ : Type u} {V : Type u} [Group Γ] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]

/-! ## The last arrow of a path -/

/-- The last arrow of a nonempty path, as an arrow of the quiver together with its source. -/
noncomputable def lastHom {a b : V} :
    (p : Quiver.Path a b) → 0 < p.length → Sigma fun x : V => (x ⟶ b)
  | .nil, h => (Nat.lt_irrefl 0 h).elim
  | @Quiver.Path.cons _ _ _ _ _ q e, _ => ⟨_, e⟩

/-- The last arrow of a nonempty path, as a `Quiver.Total`. -/
noncomputable def lastTotal {a b : V} (p : Quiver.Path a b) (h : 0 < p.length) : Quiver.Total V :=
  ⟨(lastHom p h).1, b, (lastHom p h).2⟩

@[simp] theorem lastTotal_right {a b : V} (p : Quiver.Path a b) (h : 0 < p.length) :
    (lastTotal p h).right = b := rfl

@[simp] theorem lastTotal_left {a b : V} (p : Quiver.Path a b) (h : 0 < p.length) :
    (lastTotal p h).left = (lastHom p h).1 := rfl

@[simp] theorem lastTotal_cons {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (h : 0 < (p.cons e).length) : lastTotal (p.cons e) h = ⟨b, c, e⟩ := rfl

/-- The last arrow of a composition is the last arrow of the right factor. -/
theorem lastTotal_comp {a b : V} (p : Quiver.Path a b) :
    ∀ {c : V} (q : Quiver.Path b c) (hq : 0 < q.length) (h : 0 < (p.comp q).length),
      lastTotal (p.comp q) h = lastTotal q hq := by
  intro c q
  induction q with
  | nil => intro hq; simp at hq
  | cons q e ih => intro hq h; rfl

/-- The last arrow of a path ending with a single arrow. -/
theorem lastTotal_comp_toPath {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (h : 0 < (p.comp e.toPath).length) : lastTotal (p.comp e.toPath) h = ⟨b, c, e⟩ := rfl

/-! ## Lifting a path of the quotient graph -/

/-- **The lift of a path of the quotient graph.**  Given a section `x` of the vertex orbits and a
choice `L` of a lift of every arrow of the quotient graph with matching endpoints, every path of
the quotient graph lifts to a path of `V` starting at the lift of its source and ending at the
lift of its target. -/
noncomputable def liftPath (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (A : Work.ORBassSerre.orbitV Γ V) :
    {B : Work.ORBassSerre.orbitV Γ V} → Quiver.Path A B → Quiver.Path (x A) (x B)
  | _, .nil => Quiver.Path.nil
  | B, .cons q e =>
      (liftPath x L hL A q).cons ((L _ B e).hom.cast (hL _ B e).1 (hL _ B e).2)

@[simp] theorem liftPath_nil (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (A : Work.ORBassSerre.orbitV Γ V) :
    liftPath x L hL A (B := A) (.nil) = Quiver.Path.nil := rfl

theorem liftPath_cons (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    {A C B : Work.ORBassSerre.orbitV Γ V} (q : Quiver.Path A C) (e : C ⟶ B) :
    liftPath x L hL A (q.cons e) =
      (liftPath x L hL A q).cons ((L C B e).hom.cast (hL C B e).1 (hL C B e).2) := rfl

@[simp] theorem length_liftPath (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    {A B : Work.ORBassSerre.orbitV Γ V} (q : Quiver.Path A B) :
    (liftPath x L hL A q).length = q.length := by
  induction q with
  | nil => rfl
  | cons q e ih => simp [liftPath_cons, ih]

/-- The last arrow of the lift of a nonempty path is the lift of the last arrow of the path. -/
theorem lastTotal_liftPath (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    {A B : Work.ORBassSerre.orbitV Γ V} (q : Quiver.Path A B) (hq : 0 < q.length)
    (h : 0 < (liftPath x L hL A q).length) :
    lastTotal (liftPath x L hL A q) h = L (lastHom q hq).1 B (lastHom q hq).2 := by
  induction q with
  | nil => simp at hq
  | cons q e ih =>
    simp only [liftPath_cons, lastTotal_cons]
    refine Quiver.Total.ext ?_ ?_ ?_
    · exact ((hL _ _ e).1).symm
    · exact ((hL _ _ e).2).symm
    · exact Quiver.Hom.cast_heq _ _ _

/-! ## Translation of paths and of the last arrow -/

/-- Translating a path and taking its last arrow: the translate of the last arrow. -/
theorem lastTotal_smulPath (g : Γ) {a b : V} (p : Quiver.Path a b) (h : 0 < p.length)
    (h' : 0 < (Work.ORBassSerre.smulPath g p).length) :
    lastTotal (Work.ORBassSerre.smulPath g p) h' = g • lastTotal p h := by
  induction p with
  | nil => simp at h
  | cons p e ih =>
    simp only [Work.ORBassSerre.smulPath_cons, lastTotal_cons]
    exact Work.ORBassSerre.Action.Quotient.total_mk_smulArrow (G := Γ) (V := V) g
      (Quiver.Total.mk _ _ e)

/-- The geodesic is equivariant under the group action. -/
theorem geodesic_smul (hT : Work.ORBassSerre.IsTree V) (g : Γ) (a b : V) :
    hT.geodesic (g • a) (g • b) = Work.ORBassSerre.smulPath g (hT.geodesic a b) :=
  (hT.eq_geodesic (Work.ORBassSerre.Tree.Seg.smulPath_isReduced g
    (hT.geodesic_isReduced a b))).symm

/-- The length of the geodesic between two distinct vertices is positive. -/
theorem geodesic_length_pos (hT : Work.ORBassSerre.IsTree V) {a b : V} (h : a ≠ b) :
    0 < (hT.geodesic a b).length := by
  by_contra hc
  push Not at hc
  exact h (Quiver.Path.eq_of_length_zero (hT.geodesic a b) (Nat.le_zero.mp hc))

/-- The reverse of the geodesic from `a` to `b` is the geodesic from `b` to `a`. -/
theorem geodesic_reverse (hT : Work.ORBassSerre.IsTree V) (a b : V) :
    (hT.geodesic a b).reverse = hT.geodesic b a :=
  hT.eq_geodesic (hT.geodesic_isReduced a b).reverse

/-! ## The endpoints of an arrow of the quotient graph -/

/-- The source of an arrow of the quotient graph is the source of its edge orbit. -/
theorem srcE_hom {A B : Work.ORBassSerre.orbitV Γ V} (e : A ⟶ B) :
    Work.ORBassSerre.Action.srcE (G := Γ) (V := V) e.1 = A := by
  obtain ⟨u, hu, hl, -⟩ := e.2
  show Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := Γ) (V := V) e.1).left = A
  rw [Work.ORBassSerre.Action.mk_left_eq_of_mk_eq (G := Γ) (V := V)
    (u := Work.ORBassSerre.Action.orbitRepE (G := Γ) (V := V) e.1) (w := u)
    ((Work.ORBassSerre.Action.orbitRepE_mk e.1).trans hu.symm)]
  exact hl

/-- The target of an arrow of the quotient graph is the target of its edge orbit. -/
theorem tgtE_hom {A B : Work.ORBassSerre.orbitV Γ V} (e : A ⟶ B) :
    Work.ORBassSerre.Action.tgtE (G := Γ) (V := V) e.1 = B := by
  obtain ⟨u, hu, -, hr⟩ := e.2
  show Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := Γ) (V := V) e.1).right = B
  rw [Work.ORBassSerre.Action.mk_right_eq_of_mk_eq (G := Γ) (V := V)
    (u := Work.ORBassSerre.Action.orbitRepE (G := Γ) (V := V) e.1) (w := u)
    ((Work.ORBassSerre.Action.orbitRepE_mk e.1).trans hu.symm)]
  exact hr

/-! ## Auxiliary facts -/

/-- The reverse of a composition whose left factor is a single arrow. -/
theorem reverse_toPath_comp {x y z : V} (e : x ⟶ y) (v' : Quiver.Path y z) :
    (e.toPath.comp v').reverse = v'.reverse.comp (Quiver.reverse e).toPath := by
  induction v' with
  | nil => rfl
  | cons p f ih => simp [ih]

/-- In a tree there is at most one arrow between two vertices. -/
theorem subsingleton_hom_of_isTree (hT : Work.ORBassSerre.IsTree V) (a b : V) :
    Subsingleton (a ⟶ b) := by
  refine ⟨fun e e' => ?_⟩
  have h1 : e.toPath = hT.geodesic a b :=
    hT.eq_geodesic (Quiver.Path.IsReduced.of_length_lt_two (by simp))
  have h2 : e'.toPath = hT.geodesic a b :=
    hT.eq_geodesic (Quiver.Path.IsReduced.of_length_lt_two (by simp))
  have h3 : e.toPath = e'.toPath := h1.trans h2.symm
  exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h3)

/-- In a tree two `Quiver.Total`s with the same endpoints are equal. -/
theorem total_eq_of_isTree (hT : Work.ORBassSerre.IsTree V) {t t' : Quiver.Total V}
    (h1 : t.left = t'.left) (h2 : t.right = t'.right) : t = t' := by
  obtain ⟨l, r, f⟩ := t
  obtain ⟨l', r', f'⟩ := t'
  simp only at h1 h2
  subst h1
  subst h2
  haveI := subsingleton_hom_of_isTree (V := V) hT l r
  exact Quiver.Total.ext rfl rfl (heq_of_eq (Subsingleton.elim f f'))

/-- The orbit of a translated arrow is the orbit of the arrow. -/
theorem orbit_mk_smul (g : Γ) (u : Quiver.Total V) :
    (Quotient.mk'' (g • u) : Work.ORBassSerre.orbitE Γ V) = Quotient.mk'' u :=
  Quotient.sound ⟨g, rfl⟩

/-- The last arrow does not depend on the proof of non-emptiness. -/
theorem lastHom_eq_of_pos {a b : V} (p : Quiver.Path a b) (h h' : 0 < p.length) :
    lastHom p h = lastHom p h' := by
  cases p with
  | nil => exact absurd h (by simp)
  | cons p e => rfl

/-- The last arrow does not depend on the proof of non-emptiness. -/
theorem lastTotal_eq_of_pos {a b : V} (p : Quiver.Path a b) (h h' : 0 < p.length) :
    lastTotal p h = lastTotal p h' := by
  simp only [lastTotal, lastHom_eq_of_pos p h h']

/-- Equal paths have equal last arrows. -/
theorem lastTotal_congr {a b : V} {p q : Quiver.Path a b} (h : p = q)
    (hp : 0 < p.length) (hq : 0 < q.length) : lastTotal p hp = lastTotal q hq := by
  subst h
  exact lastTotal_eq_of_pos p hp hq

/-- Translating a path does not change its length. -/
theorem length_smulPath (g : Γ) {a b : V} (p : Quiver.Path a b) :
    (Work.ORBassSerre.smulPath g p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Work.ORBassSerre.smulPath_cons, Quiver.Path.length_cons, ih]

/-- The orbit of a translated vertex is the orbit of the vertex. -/
theorem orbitV_mk_smul (g : Γ) (v : V) :
    (Quotient.mk'' (g • v) : Work.ORBassSerre.orbitV Γ V) = Quotient.mk'' v :=
  Quotient.sound ⟨g, rfl⟩

/-- Equal paths have equal last arrows (as points of a sigma type). -/
theorem lastHom_congr {a b : V} {p q : Quiver.Path a b} (h : p = q)
    (hp : 0 < p.length) (hq : 0 < q.length) : lastHom p hp = lastHom q hq := by
  subst h
  exact lastHom_eq_of_pos p hp hq

/-- The last arrow of a path is unchanged, as to its source, by a change of endpoints. -/
theorem lastTotal_cast_left {a b a' b' : V} (p : Quiver.Path a b) (hu : a = a') (hv : b = b')
    (h : 0 < p.length) (h' : 0 < (p.cast hu hv).length) :
    (lastTotal (p.cast hu hv) h').left = (lastTotal p h).left := by
  cases p with
  | nil => exact absurd h (by simp)
  | cons p e =>
    have hc : (Quiver.Path.cast hu hv (p.cons e)) = (p.cast hu rfl).cons (e.cast rfl hv) :=
      Quiver.Path.cast_cons p e hu hv
    have h1 : (lastHom (Quiver.Path.cast hu hv (p.cons e)) h').1
        = (lastHom ((p.cast hu rfl).cons (e.cast rfl hv)) (by rw [← hc]; exact h')).1 := by
      rw [lastHom_congr hc h' _]
    rw [show (lastTotal (Quiver.Path.cast hu hv (p.cons e)) h').left
        = (lastHom (Quiver.Path.cast hu hv (p.cons e)) h').1 from rfl, h1]
    rfl

/-! ## The last arrow of the lifted geodesic -/

/-- **The last arrow of the geodesic between translates.**  If the geodesic between the lifts `x A`
and `x B` of two vertex orbits is the lift of the geodesic of the quotient graph, then the last
arrow of the geodesic between the translates `g • x A`, `g • x B` is the translate of the lift of
the last arrow of the quotient geodesic. -/
theorem lastTotal_geodesic_lift (hT : Work.ORBassSerre.IsTree V)
    (hquot : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV Γ V))
    (x : Work.ORBassSerre.orbitV Γ V → V)
    (L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V)
    (hL : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      (L A B e).left = x A ∧ (L A B e).right = x B)
    (hGL : ∀ (A B : Work.ORBassSerre.orbitV Γ V),
      hT.geodesic (x A) (x B) = liftPath x L hL A (hquot.geodesic A B))
    {A B : Work.ORBassSerre.orbitV Γ V} (hq1 : 0 < (hquot.geodesic A B).length)
    (g : Γ) {a b : V}
    (ha : g • x A = a) (hb : g • x B = b)
    (h : 0 < (hT.geodesic a b).length) :
    lastTotal (hT.geodesic a b) h
      = g • L (lastHom (hquot.geodesic A B) hq1).1 B
          (lastHom (hquot.geodesic A B) hq1).2 := by
  have hqL : 0 < (liftPath x L hL A (hquot.geodesic A B)).length := by
    rw [length_liftPath]; exact hq1
  have hcast : hT.geodesic a b
      = (hT.geodesic (g • x A) (g • x B)).cast ha hb := by
    refine (hT.eq_geodesic ?_).symm
    exact Work.ORBassSerre.Tree.Walk.qpath_isReduced_cast ha hb (hT.geodesic_isReduced _ _)
  have hc : 0 < ((hT.geodesic (g • x A) (g • x B)).cast ha hb).length := by
    rw [← hcast]; exact h
  have hg : 0 < (hT.geodesic (g • x A) (g • x B)).length := by
    rw [← Work.ORBassSerre.Tree.Walk.qpath_length_cast ha hb
      (hT.geodesic (g • x A) (g • x B))]; exact hc
  have hV : 0 < (hT.geodesic (x A) (x B)).length := by
    rw [hGL A B, length_liftPath]; exact hq1
  have hsm : 0 < (Work.ORBassSerre.smulPath g (hT.geodesic (x A) (x B))).length := by
    rw [← geodesic_smul hT g (x A) (x B)]; exact hg
  calc lastTotal (hT.geodesic a b) h
      = lastTotal ((hT.geodesic (g • x A) (g • x B)).cast ha hb) hc :=
        lastTotal_congr hcast h hc
    _ = lastTotal (hT.geodesic (g • x A) (g • x B)) hg := by
        refine total_eq_of_isTree hT ?_ ?_
        · rw [lastTotal_cast_left]
        · rw [lastTotal_right, lastTotal_right]
          exact hb.symm
    _ = lastTotal (Work.ORBassSerre.smulPath g (hT.geodesic (x A) (x B))) hsm :=
        lastTotal_congr (geodesic_smul hT g (x A) (x B)) hg hsm
    _ = g • lastTotal (hT.geodesic (x A) (x B)) hV :=
        lastTotal_smulPath g _ hV hsm
    _ = g • lastTotal (liftPath x L hL A (hquot.geodesic A B)) hqL := by
        rw [lastTotal_congr (hGL A B) hV hqL]
    _ = g • L (lastHom (hquot.geodesic A B) hq1).1 B (lastHom (hquot.geodesic A B) hq1).2 := by
        rw [lastTotal_liftPath]

/-! ## The length of the geodesic between translates -/

/-- The length of the geodesic between translates is the length of the geodesic between the
originals. -/
theorem length_geodesic_smul (hT : Work.ORBassSerre.IsTree V) (g : Γ) (a b : V) :
    (hT.geodesic (g • a) (g • b)).length = (hT.geodesic a b).length := by
  rw [geodesic_smul hT g a b, length_smulPath]

/-- The length of the geodesic between a pair of translates. -/
theorem length_geodesic_of_eq_smul (hT : Work.ORBassSerre.IsTree V) {a b a' b' : V} (g : Γ)
    (ha : g • a = a') (hb : g • b = b') :
    (hT.geodesic a' b').length = (hT.geodesic a b).length := by
  subst ha; subst hb
  exact length_geodesic_smul hT g a b

end Work.ORLocInd.CohenLyndon
