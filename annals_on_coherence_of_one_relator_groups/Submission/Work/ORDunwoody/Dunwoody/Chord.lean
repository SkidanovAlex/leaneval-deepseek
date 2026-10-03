/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The chords of the Dunwoody pattern

For each face of `Λ''` the visits (the pattern points on its boundary walk) are grouped by
*fibre*: two visits are in the same fibre when their cells map onto the same edge of `T`, i.e.
when they have the same label `MidV.label : Sym2 V`.  The number of visits in a fibre is even
(this is the parity lemma: the boundary walk of a face maps to a closed walk in `T`, and a closed
walk in a forest crosses each edge evenly — `Tracks/even_edges_count`).

**The chords** of a face pair, inside each fibre, the 1st with the 2nd visit, the 3rd with the
4th, …  This is canonical: the order is the order of the walk read from the face's base point, so
the chords are `G`-equivariant.  See `DESIGN_N13.md` §2b' for why this choice is the right one
(each chord joins two visits of the same fibre, and its two visits traverse the corresponding
edge of `T` in *opposite* directions, which is the colour consistency of §2c).

This file only sets up the definitions and their elementary API; the parity statement and the
"opposite directions" statement are the next lemmas to prove.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Pattern

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- The positions at which the label is `e`, accumulated from the offset `i`. -/
def positionsOfLabelAux : List (MidV D) → Sym2 V → ℕ → List ℕ
  | [], _, _ => []
  | m :: rest, e, i => (if m.label = e then [i] else []) ++ positionsOfLabelAux rest e (i + 1)

/-- The positions in a list of visits at which the label is `e` (i.e. the visits in the fibre
`e`). -/
def positionsOfLabel (l : List (MidV D)) (e : Sym2 V) : List ℕ :=
  positionsOfLabelAux l e 0

@[simp] theorem positionsOfLabelAux_nil (e : Sym2 V) :
    positionsOfLabelAux (D := D) [] e 0 = [] := rfl

/-- Pair consecutive elements two at a time: `[a, b, c, d] ↦ [(a,b), (c,d)]`. -/
def pairUp : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _ => []

@[simp] theorem pairUp_nil : pairUp ([] : List ℕ) = [] := rfl

@[simp] theorem pairUp_singleton (a : ℕ) : pairUp [a] = [] := rfl

@[simp] theorem pairUp_cons_cons (a b : ℕ) (rest : List ℕ) :
    pairUp (a :: b :: rest) = (a, b) :: pairUp rest := rfl

/-- **The fibres occurring among a list of visits.** -/
def labelSet (l : List (MidV D)) : List (Sym2 V) := (l.map (MidV.label (D := D))).dedup

/-- **The chords of a list of visits**: for every fibre, the visits in that fibre are paired two
at a time in their order of occurrence. -/
def chords (l : List (MidV D)) : List (ℕ × ℕ) :=
  (labelSet l).flatMap (fun e => pairUp (positionsOfLabel l e))

/-- **The chords of the boundary walk of a face.** -/
def faceChords (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List (ℕ × ℕ) :=
  chords (faceVisits D c w)

/-- The chord relation on the visits of a face: `i` and `j` are paired. -/
def IsChord (l : List (MidV D)) (i j : ℕ) : Prop := (i, j) ∈ chords l ∨ (j, i) ∈ chords l

theorem IsChord.symm {l : List (MidV D)} {i j : ℕ} (h : IsChord l i j) : IsChord l j i :=
  Or.symm h

end Work.ORDunwoody.Dunwoody
