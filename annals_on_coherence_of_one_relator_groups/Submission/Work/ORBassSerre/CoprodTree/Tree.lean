
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre tree of a free product `A ∗ B`: the tree property

This file proves that the quiver `Vertex A B` of `Submission.Work.ORBassSerre.CoprodTree.Defs`
has no non-trivial reduced closed path.  Together with the connectedness
`Work.ORBassSerre.CoprodTree.connected_vertex` this says that the quiver is a tree
(`Work.ORBassSerre.IsTree`), so that `Work.ORDunwoody.Lemmas.ofQuiverTree` produces the
Bass--Serre tree of `A ∗ B` as a simplicial tree.
-/
import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.Defs
import Submission.Work.ORBassSerre.CoprodTree.AltList
import Submission.Work.ORBassSerre.CoprodTree.coprod_mk_injective_of_isReduced_univ
import Submission.Work.ORBassSerre.CoprodTree.altList_prod_ne_one
import Submission.Work.ORBassSerre.CoprodTree.false_of_alternating
import Submission.Work.ORBassSerre.CoprodTree.connected_vertex

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORBassSerre.CoprodTree

open Monoid

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-! ## Following an arrow from a state -/

/-- An arrow starting at the vertex `vtx g s` changes the state by an element of the factor of the
side `s`. -/
theorem arrow_state_of {x y : Vertex A B} (e : x ⟶ y) {g : Monoid.Coprod A B} {s : Bool}
    (hx : x = vtx g s) :
    ∃ t ∈ sideFactor A B s, e.1 = g * t ∧ y = vtx (g * t) (!s) := by
  have heq : e.1 = g * (g⁻¹ * e.1) := by simp [mul_assoc]
  cases s
  · rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (hx.symm.trans h1) (vB_ne_vA _ _)
    · have hmem : g⁻¹ * e.1 ∈ SubB A B := vB_eq_vB_iff.1 (hx.symm.trans h1)
      exact ⟨g⁻¹ * e.1, hmem, heq, h2.trans (congrArg vA heq)⟩
  · rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hmem : g⁻¹ * e.1 ∈ SubA A B := vA_eq_vA_iff.1 (hx.symm.trans h1)
      exact ⟨g⁻¹ * e.1, hmem, heq, h2.trans (congrArg vB heq)⟩
    · exact absurd (hx.symm.trans h1) (vA_ne_vB _ _)

/-! ## The state and the steps of a path -/

/-- The label of the last arrow of a path, or `d` for the empty path. -/
def lastLabel (d : Monoid.Coprod A B) {x : Vertex A B} : (y : Vertex A B) →
    Quiver.Path x y → Monoid.Coprod A B
  | _, .nil => d
  | _, .cons p e => e.1

/-- The steps of a path started at a vertex of side `s` whose "state" is `d`: the successive
quotients of states. -/
def stepsOf (d : Monoid.Coprod A B) (s : Bool) {x : Vertex A B} : (y : Vertex A B) →
    Quiver.Path x y → List (Monoid.Coprod A B)
  | _, .nil => []
  | _, .cons p e => stepsOf d s _ p ++ [(lastLabel d _ p)⁻¹ * e.1]

@[simp] theorem lastLabel_nil (d : Monoid.Coprod A B) {x : Vertex A B} :
    lastLabel d x (Quiver.Path.nil : Quiver.Path x x) = d := rfl

@[simp] theorem lastLabel_cons (d : Monoid.Coprod A B) {x y z : Vertex A B}
    (p : Quiver.Path x y) (e : y ⟶ z) : lastLabel d z (p.cons e) = e.1 := rfl

@[simp] theorem stepsOf_nil (d : Monoid.Coprod A B) (s : Bool) {x : Vertex A B} :
    stepsOf d s x (Quiver.Path.nil : Quiver.Path x x) = [] := rfl

@[simp] theorem stepsOf_cons (d : Monoid.Coprod A B) (s : Bool) {x y z : Vertex A B}
    (p : Quiver.Path x y) (e : y ⟶ z) :
    stepsOf d s z (p.cons e) = stepsOf d s y p ++ [(lastLabel d y p)⁻¹ * e.1] := rfl

theorem stepsOf_length (d : Monoid.Coprod A B) (s : Bool) {x y : Vertex A B}
    (p : Quiver.Path x y) : (stepsOf d s y p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

theorem stepsOf_prod (d : Monoid.Coprod A B) (s : Bool) {x y : Vertex A B}
    (p : Quiver.Path x y) : (stepsOf d s y p).prod = d⁻¹ * lastLabel d y p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [stepsOf_cons, List.prod_append, ih]
    simp [mul_assoc]

/-- The endpoint of a path started at a vertex of side `s` and state `d`. -/
theorem stepsOf_endpoint (d : Monoid.Coprod A B) (s : Bool) {x y : Vertex A B}
    (p : Quiver.Path x y) (hx : x = vtx d s) :
    y = vtx (lastLabel d y p) (sideAfter s p.length) := by
  induction p with
  | nil => simpa using hx
  | cons p e ih =>
    obtain ⟨t, ht, he, hy⟩ := arrow_state_of e ih
    rw [← he] at hy
    refine hy.trans ?_
    simp [Quiver.Path.length_cons, sideAfter_succ]

/-- Each step of a path started at a vertex of side `s` lies in the factor of the side at which it
is taken. -/
theorem stepsOf_mem (d : Monoid.Coprod A B) (s : Bool) {x y : Vertex A B}
    (p : Quiver.Path x y) (hx : x = vtx d s) :
    ∀ j (hj : j < (stepsOf d s y p).length),
      (stepsOf d s y p)[j] ∈ sideFactor A B (sideAfter s j) := by
  induction p with
  | nil => intro j hj; simp at hj
  | cons p e ih =>
    intro j hj
    obtain ⟨t, ht, he, -⟩ := arrow_state_of e (stepsOf_endpoint d s p hx)
    have hlen : (stepsOf d s _ p).length = p.length := stepsOf_length d s p
    have hj2 : j < (stepsOf d s _ p).length + 1 := by
      have h := hj
      simp only [stepsOf_cons, List.length_append, List.length_cons, List.length_nil,
        Nat.add_zero] at h
      omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj2) with hlt | heq
    · have key : (stepsOf d s _ p ++ [(lastLabel d _ p)⁻¹ * e.1])[j] = (stepsOf d s _ p)[j] :=
        List.getElem_append_left hlt
      refine key.symm ▸ ih j hlt
    · subst heq
      have key : (stepsOf d s _ p ++ [(lastLabel d _ p)⁻¹ * e.1])[(stepsOf d s _ p).length] =
          (lastLabel d _ p)⁻¹ * e.1 :=
        List.getElem_concat_length rfl _
      refine key.symm ▸ ?_
      rw [he, hlen]
      simpa [mul_assoc] using ht

/-- If two consecutive arrows have the same label, then the two-arrow path they form is not
reduced: it contains a backtrack. -/
theorem not_isReduced_cons_cons {x u v z : Vertex A B} (q : Quiver.Path x u) (a : u ⟶ v)
    (e : v ⟶ z) (h : e.1 = a.1) : ¬ ((q.cons a).cons e).IsReduced := by
  have hsz : z = u := by
    rcases arrow_label_eq a with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
      rcases arrow_label_eq e with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · exact absurd (ha2.symm.trans (h ▸ he1)) (vB_ne_vA _ _)
    · exact he2.trans ((congrArg vA h).trans ha1.symm)
    · exact he2.trans ((congrArg vB h).trans ha1.symm)
    · exact absurd (ha2.symm.trans (h ▸ he1)) (vA_ne_vB _ _)
  subst hsz
  have hrev : e = Quiver.reverse a := by
    haveI := subsingleton_arrow (A := A) (B := B) v z
    exact Subsingleton.elim _ _
  intro hred
  refine hred (q.comp (Quiver.Path.nil : Quiver.Path z z)) ?_
  have hpath : ((q.cons a).cons e) = q.comp (a.toPath.comp ((Quiver.reverse a).toPath.comp
      (Quiver.Path.nil : Quiver.Path z z))) := by
    rw [Quiver.Path.comp_nil, ← hrev, ← Quiver.Path.comp_toPath_eq_cons,
      ← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.comp_assoc]
  rw [hpath]
  exact Quiver.Path.DeleteBacktrack.intro q a (Quiver.Path.nil : Quiver.Path z z)

/-- In a reduced path, the step carrying the junction between two consecutive arrows is
non-trivial. -/
theorem stepsOf_ne_one (d : Monoid.Coprod A B) (s : Bool) {x y : Vertex A B}
    (p : Quiver.Path x y) (hp : p.IsReduced) :
    ∀ j (hj : j < (stepsOf d s y p).length), 0 < j → (stepsOf d s y p)[j] ≠ 1 := by
  induction p with
  | nil => intro j hj; simp at hj
  | cons p e ih =>
    intro j hj hpos
    have hp' : p.IsReduced := by
      have h := hp
      rw [← Quiver.Path.comp_toPath_eq_cons p e] at h
      exact Quiver.Path.IsReduced.of_comp h
    have hlen : (stepsOf d s _ p).length = p.length := stepsOf_length d s p
    have hj2 : j < (stepsOf d s _ p).length + 1 := by
      have h := hj
      simp only [stepsOf_cons, List.length_append, List.length_cons, List.length_nil,
        Nat.add_zero] at h
      omega
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj2) with hlt | heq
    · have key : (stepsOf d s _ p ++ [(lastLabel d _ p)⁻¹ * e.1])[j] = (stepsOf d s _ p)[j] :=
        List.getElem_append_left hlt
      refine key.symm ▸ ih hp' j hlt hpos
    · have h0 : j = (stepsOf d s _ p).length := heq
      have key : (stepsOf d s _ p ++ [(lastLabel d _ p)⁻¹ * e.1])[j] = (lastLabel d _ p)⁻¹ * e.1 :=
        List.getElem_concat_length h0 _
      refine key.symm ▸ ?_
      rcases eq_or_ne p.length 0 with hp0 | hpne
      · have h0' : j = 0 := by omega
        exact absurd h0' (by omega)
      · obtain ⟨z, q, a, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hpne
        intro h1
        have heq1 : e.1 = a.1 := (inv_mul_eq_one.mp h1).symm
        exact absurd hp (not_isReduced_cons_cons q a e heq1)


/- A list of elements of the two factors of length at least `3`, with product `1`, whose entries
lie in the factors prescribed by the alternating side sequence and whose interior entries are
non-trivial, cannot exist.  (This is `Work.ORBassSerre.CoprodTree.false_of_alternating`, which is
isolated in its own file.) -/

/-! ## There are no loops, and no reduced closed paths -/

/-- The tree has no loops. -/
theorem noLoop (x : Vertex A B) : ¬ Nonempty (x ⟶ x) := by
  rintro ⟨e⟩
  rcases arrow_label_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact vA_ne_vB e.1 e.1 (h1.symm.trans h2)
  · exact vB_ne_vA e.1 e.1 (h1.symm.trans h2)

/-- **There is no non-trivial reduced closed path** in the Bass--Serre quiver of `A ∗ B`. -/
theorem no_reduced_closed {x : Vertex A B} (p : Quiver.Path x x) (hp : p.IsReduced) :
    p = Quiver.Path.nil := by
  by_contra hne
  have hlen0 : p.length ≠ 0 := fun h => hne (Quiver.Path.eq_nil_of_length_zero p h)
  have hlen2 : 2 ≤ p.length := by
    rcases Nat.lt_or_ge p.length 2 with h | h
    · have hcases : p.length = 0 ∨ p.length = 1 := by omega
      rcases hcases with h0 | h1
      · exact absurd h0 hlen0
      · cases p with
        | nil => simp at h1
        | cons q e =>
          have hq : q.length = 0 := by
            simp only [Quiver.Path.length_cons] at h1
            omega
          have hb := Quiver.Path.eq_of_length_zero q hq
          subst hb
          exact (noLoop x ⟨e⟩).elim
    · exact h
  obtain ⟨d, s, hx⟩ := exists_vtx x
  have hend : x = vtx (lastLabel d x p) (sideAfter s p.length) := stepsOf_endpoint d s p hx
  have hfac : d⁻¹ * lastLabel d x p ∈ sideFactor A B (sideAfter s p.length) := by
    have h := (vtx_eq_vtx_iff.1 (hend.symm.trans hx)).2
    simpa using (sideFactor A B (sideAfter s p.length)).inv_mem h
  refine _root_.Work.ORBassSerre.CoprodTree.false_of_alternating s
    (stepsOf d s x p ++ [(d⁻¹ * lastLabel d x p)⁻¹]) ?_ ?_ ?_ ?_
  · simp only [List.length_append, List.length_cons, List.length_nil, stepsOf_length]
    omega
  · rw [List.prod_append, stepsOf_prod]
    simp
  · intro j hj
    have hj' : j < p.length + 1 := by
      simpa [List.length_append, List.length_cons, List.length_nil, stepsOf_length] using hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hlt | heq
    · have hjlen : j < (stepsOf d s x p).length := by rwa [stepsOf_length]
      have key : (stepsOf d s x p ++ [(d⁻¹ * lastLabel d x p)⁻¹])[j] = (stepsOf d s x p)[j] :=
        List.getElem_append_left hjlen
      refine key.symm ▸ stepsOf_mem d s p hx j hjlen
    · have h0 : j = (stepsOf d s x p).length := by rw [stepsOf_length]; omega
      have hz : (d⁻¹ * lastLabel d x p)⁻¹ ∈ sideFactor A B (sideAfter s j) := by
        rw [h0, stepsOf_length]
        exact (sideFactor A B (sideAfter s p.length)).inv_mem hfac
      exact (List.getElem_concat_length h0 _).symm ▸ hz
  · intro j hj hpos hlt
    have hj' : j < p.length + 1 := by
      simpa [List.length_append, List.length_cons, List.length_nil, stepsOf_length] using hj
    have hlt' : j + 1 < p.length + 1 := by
      simpa [List.length_append, List.length_cons, List.length_nil, stepsOf_length] using hlt
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hlt2 | heq
    · have hjlen : j < (stepsOf d s x p).length := by rwa [stepsOf_length]
      have key : (stepsOf d s x p ++ [(d⁻¹ * lastLabel d x p)⁻¹])[j] = (stepsOf d s x p)[j] :=
        List.getElem_append_left hjlen
      refine key.symm ▸ stepsOf_ne_one d s p hp j hjlen hpos
    · have h0 : j = (stepsOf d s x p).length := by rw [stepsOf_length]; omega
      rw [h0, stepsOf_length] at hlt'
      omega

/-- The Bass--Serre quiver of `A ∗ B` is a tree. -/
theorem isTree_vertex : Work.ORBassSerre.IsTree (Vertex A B) :=
  ⟨fun x y => connected_vertex x y, fun x p hp => no_reduced_closed p hp⟩

end Work.ORBassSerre.CoprodTree

