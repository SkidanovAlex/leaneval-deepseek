/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The chord matching of a list, abstractly

`Dunwoody/Chord.lean` pairs, in each *fibre* (= the set of visits of a face lying in one edge of
`T`), the 1st visit with the 2nd, the 3rd with the 4th, … in the order in which the visits are read
from the face's base point.  The pairing depends only on the *list of labels* of the visits, so it
can be defined abstractly on a list:

    `chordsOf l`  =  for every value `e` occurring in `l`, the list of its positions in `l`, paired
                    two at a time in order.

The mathematical content is in `Chords/nested.lean`: for the list of edges `γ.edges` of a **closed
walk in a forest** the resulting matching is *nested* (non-crossing): the visits strictly between
the two ends of a chord are again a union of chords.  This is the input `(N)` of `DESIGN_N13.md`
§9.3, and it is what makes `alpha τ` invariant under the region relation `RegionRel`.

The definitions here are deliberately independent of the Dunwoody construction, so that the
nestedness theorem is a statement about finite lists and forests.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Chords

/-- The positions at which `e` occurs in a list, from the offset `i`. -/
def posOfAux {α : Type u} [DecidableEq α] : List α → α → ℕ → List ℕ
  | [], _, _ => []
  | a :: rest, e, i => (if a = e then [i] else []) ++ posOfAux rest e (i + 1)

/-- The positions at which `e` occurs in a list. -/
def posOf {α : Type u} [DecidableEq α] (l : List α) (e : α) : List ℕ := posOfAux l e 0

@[simp] theorem posOfAux_nil {α : Type u} [DecidableEq α] (e : α) (i : ℕ) :
    posOfAux ([] : List α) e i = [] := rfl

@[simp] theorem posOfAux_cons {α : Type u} [DecidableEq α] (a : α) (l : List α) (e : α)
    (i : ℕ) :
    posOfAux (a :: l) e i = (if a = e then [i] else []) ++ posOfAux l e (i + 1) := rfl

@[simp] theorem posOf_nil {α : Type u} [DecidableEq α] (e : α) :
    posOf ([] : List α) e = [] := rfl

/-- Pair consecutive elements two at a time: `[a, b, c, d] ↦ [(a, b), (c, d)]`; a final unpaired
element is dropped. -/
def pairUp : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _ => []

@[simp] theorem pairUp_nil : pairUp ([] : List ℕ) = [] := rfl

@[simp] theorem pairUp_singleton (a : ℕ) : pairUp [a] = [] := rfl

@[simp] theorem pairUp_cons_cons (a b : ℕ) (rest : List ℕ) :
    pairUp (a :: b :: rest) = (a, b) :: pairUp rest := rfl

/-- **The chord matching of a list**: for every value occurring in `l`, its positions in `l` are
paired two at a time in order. -/
def chordsOf {α : Type u} [DecidableEq α] (l : List α) : List (ℕ × ℕ) :=
  l.dedup.flatMap (fun e => pairUp (posOf l e))

@[simp] theorem chordsOf_nil {α : Type u} [DecidableEq α] :
    chordsOf ([] : List α) = [] := rfl

/-- The chord relation on the positions of a list. -/
def IsChordOf {α : Type u} [DecidableEq α] (l : List α) (i j : ℕ) : Prop :=
  (i, j) ∈ chordsOf l ∨ (j, i) ∈ chordsOf l

theorem IsChordOf.symm {α : Type u} [DecidableEq α] {l : List α} {i j : ℕ}
    (h : IsChordOf l i j) : IsChordOf l j i := Or.symm h

end Work.ORDunwoody.Chords
