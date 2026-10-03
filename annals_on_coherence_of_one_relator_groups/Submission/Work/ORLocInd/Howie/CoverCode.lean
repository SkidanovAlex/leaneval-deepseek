/-
# The code list of a lifted path (Howie 2000, Case 1: staggeredness of the cyclic cover)

The lifted presentation of the cyclic cover (`Submission/Work/ORLocInd/Howie/CoverPresentation.lean`)
carries the code

    `coverEdgeOf P L τ f = (ω f.hom, f.left.level + τ f.hom)`

on the *unoriented* edges of the cover `Γ̃`.  The staggeredness of the lifted presentation is a
statement about `pathMax (coverEdgeOf P L τ)` and `pathMin (coverEdgeOf P L τ)` of the lifted
relators `coverPath P L hrel i n`.  This file sets up the combinatorial bookkeeping:

* `coverCodeOf P τ e n` is the code `(ω e, n + τ e)` of the arrow `(e, n)` of the cover;
* `coverCodeList P L τ p n` is the list of codes of the arrows of the lift `liftPath L p n`;
* `codeShift P d` is the translation of the second coordinate of a code by `d`;
* `pathMax_eq_maximum`, `pathMin_eq_minimum` rewrite `pathMax`/`pathMin` (as defined in
  `Relator.lean`) as Mathlib's `List.maximum`/`List.minimum`, which have a rich API.

The three main structural properties of `coverCodeList` (its identification with the arrow list of
`liftPath`, its behaviour under `codeShift`, and the projection to the first coordinate) are proved
in the files `coverCodeList_arrowList`, `coverCodeList_shift`, and below
(`coverCodeList_map_fst`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.liftPath_arrowList

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The code of an arrow of the cover -/

/-- The code of the arrow `(e, n)` of the cyclic cover, i.e. of the base arrow `e` with source
level `n`: `coverEdgeOf P L τ (e, n) = (ω e, n + τ e)`. -/
noncomputable def coverCodeOf (P : Presentation V) (τ : Quiver.Total V → ℤ)
    {b c : V} (e : b ⟶ c) (n : ℤ) : CoverCode P :=
  toLex (P.edgeOf (Quiver.Total.mk b c e), n + τ (Quiver.Total.mk b c e))

/-- The list of codes of the arrows of the lift `liftPath L p n` of the base path `p` starting at
level `n`. -/
noncomputable def coverCodeList (P : Presentation V) (L : Labelling V) (τ : Quiver.Total V → ℤ) :
    ∀ {a b : V} (p : Quiver.Path a b) (n : ℤ), List (CoverCode P)
  | _, _, .nil, _ => []
  | _, _, .cons p e, n => coverCodeList P L τ p n ++ [coverCodeOf P τ e (n + pathSum L.toFun p)]

@[simp]
theorem coverCodeList_nil (P : Presentation V) (L : Labelling V) (τ : Quiver.Total V → ℤ)
    {a : V} (n : ℤ) :
    coverCodeList P L τ (Quiver.Path.nil : Quiver.Path a a) n = [] := by
  simp [coverCodeList]

@[simp]
theorem coverCodeList_cons (P : Presentation V) (L : Labelling V) (τ : Quiver.Total V → ℤ)
    {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) (n : ℤ) :
    coverCodeList P L τ (p.cons e) n =
      coverCodeList P L τ p n ++ [coverCodeOf P τ e (n + pathSum L.toFun p)] := by
  simp [coverCodeList]

/-- The code list of a nonempty closed path is nonempty. -/
theorem coverCodeList_ne_nil_of_ne_nil (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) {a : V} {p : Quiver.Path a a} (h : p ≠ Quiver.Path.nil) (n : ℤ) :
    coverCodeList P L τ p n ≠ [] := by
  cases p with
  | nil => exact absurd rfl h
  | cons p e => rw [coverCodeList_cons]; simp

/-- The first coordinate of the code of an arrow is the code `P.edgeOf` of the projected arrow. -/
theorem coverCodeList_map_fst (P : Presentation V) (L : Labelling V) (τ : Quiver.Total V → ℤ)
    {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    (coverCodeList P L τ p n).map (fun c => (ofLex c).1) = p.arrowList.map P.edgeOf := by
  induction p with
  | nil => simp [coverCodeList]
  | cons p e ih =>
    rw [coverCodeList_cons, Quiver.Path.arrowList_cons, List.map_append, List.map_append, ih]
    rfl

/-! ## Translating the second coordinate of a code -/

/-- Translation of the second coordinate (the level) of a code by `d`. -/
noncomputable def codeShift (P : Presentation V) (d : ℤ) (c : CoverCode P) : CoverCode P :=
  toLex ((ofLex c).1, (ofLex c).2 + d)

@[simp]
theorem ofLex_codeShift (P : Presentation V) (d : ℤ) (c : CoverCode P) :
    ofLex (codeShift P d c) = ((ofLex c).1, (ofLex c).2 + d) := rfl

theorem codeShift_le_iff (P : Presentation V) (d : ℤ) {c c' : CoverCode P} :
    codeShift P d c ≤ codeShift P d c' ↔ c ≤ c' := by
  have hA : toLex ((ofLex c).1, (ofLex c).2 + d) ≤ toLex ((ofLex c').1, (ofLex c').2 + d) ↔
      ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 + d ≤ (ofLex c').2 + d)) :=
    Prod.Lex.toLex_le_toLex
  have hB : c ≤ c' ↔
      ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 ≤ (ofLex c').2)) :=
    Prod.Lex.toLex_le_toLex
  have h2 : ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 + d ≤ (ofLex c').2 + d)) ↔
      ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 ≤ (ofLex c').2)) := by
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
  exact hA.trans (h2.trans hB.symm)

theorem codeShift_lt_iff (P : Presentation V) (d : ℤ) {c c' : CoverCode P} :
    codeShift P d c < codeShift P d c' ↔ c < c' := by
  have hA : toLex ((ofLex c).1, (ofLex c).2 + d) < toLex ((ofLex c').1, (ofLex c').2 + d) ↔
      ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 + d < (ofLex c').2 + d)) :=
    Prod.Lex.toLex_lt_toLex
  have hB : c < c' ↔
      ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 < (ofLex c').2)) :=
    Prod.Lex.toLex_lt_toLex
  have h2 : ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 + d < (ofLex c').2 + d)) ↔
      ((ofLex c).1 < (ofLex c').1 ∨
        ((ofLex c).1 = (ofLex c').1 ∧ (ofLex c).2 < (ofLex c').2)) := by
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
  exact hA.trans (h2.trans hB.symm)

/-- Shifting the level of a code by a strictly larger amount strictly increases it. -/
theorem codeShift_lt_of_lt (P : Presentation V) {d d' : ℤ} (h : d < d') (c : CoverCode P) :
    codeShift P d c < codeShift P d' c :=
  (Prod.Lex.toLex_lt_toLex (x := ((ofLex c).1, (ofLex c).2 + d))
    (y := ((ofLex c).1, (ofLex c).2 + d'))).mpr (Or.inr ⟨rfl, by omega⟩)

/-! ## `pathMax` and `pathMin` as `List.maximum` and `List.minimum` -/

/-- The maximum of the `WithBot α`-valued list obtained from a list of `α` is the fold of its
`WithBot.some`-image. -/
theorem list_maximum_eq_foldr_some {α : Type u} [LinearOrder α] (l : List α) :
    l.maximum = (l.map WithBot.some).foldr max ⊥ := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.maximum_cons, List.map_cons, List.foldr_cons, ih]

theorem list_minimum_eq_foldr_some {α : Type u} [LinearOrder α] (l : List α) :
    l.minimum = (l.map WithTop.some).foldr min ⊤ := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.minimum_cons, List.map_cons, List.foldr_cons, ih]

/-- `pathMax` is Mathlib's `List.maximum` of the list of codes of the arrows of the path. -/
theorem pathMax_eq_maximum {α : Type u} [LinearOrder α] (ω : Quiver.Total V → α) {a b : V}
    (p : Quiver.Path a b) : pathMax ω p = (p.arrowList.map ω).maximum := by
  rw [pathMax, list_maximum_eq_foldr_some, List.map_map]
  rfl

/-- `pathMin` is Mathlib's `List.minimum` of the list of codes of the arrows of the path. -/
theorem pathMin_eq_minimum {α : Type u} [LinearOrder α] (ω : Quiver.Total V → α) {a b : V}
    (p : Quiver.Path a b) : pathMin ω p = (p.arrowList.map ω).minimum := by
  rw [pathMin, list_minimum_eq_foldr_some, List.map_map]
  rfl

/-! ## Two elementary facts about `List.maximum` and `List.minimum` -/

/-- A strict upper bound of a list of codes is a strict upper bound of its maximum. -/
theorem list_maximum_lt_coe_of_forall_lt {α : Type u} [LinearOrder α] {l : List α} {c : α}
    (h : ∀ a ∈ l, a < c) : l.maximum < (c : WithBot α) := by
  refine lt_of_not_ge fun hle => ?_
  obtain ⟨b, hb, hbc⟩ := List.coe_le_maximum_iff.mp hle
  exact (not_le_of_gt (h b hb)) hbc

/-- A strict lower bound of a list of codes is a strict lower bound of its minimum. -/
theorem list_coe_lt_minimum_of_forall_lt {α : Type u} [LinearOrder α] {l : List α} {c : α}
    (h : ∀ a ∈ l, c < a) : (c : WithTop α) < l.minimum := by
  refine lt_of_not_ge fun hle => ?_
  obtain ⟨b, hb, hbc⟩ := List.minimum_le_coe_iff.mp hle
  exact (not_lt_of_ge hbc) (h b hb)

end Work.ORLocInd.Howie
