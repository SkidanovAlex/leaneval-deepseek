/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The oriented steps of a boundary walk, and the colour condition

This file adds, on top of `Submission.Work.ORDunwoody.faceTriples_arcIndex` (which decomposes the
boundary walk `faceAux D a w` into the list `wordSteps D a w` of *oriented steps* `OStep D`), the
three pieces of data that the proof of `Work.ORDunwoody.colour_of_chord` reads off a step:

* `oMid?` — the pattern point crossed by the step (if any);
* `oTriple?` — that pattern point together with the two old vertices on either side;
* `oLabel?` — the edge of `T` whose midpoint the step crosses;
* `oGood` — the *colour condition*: a crossed step traverses the edge of `T` it labels (its two
  ends have adjacent colours and the colour-pair is the label), while a collapsed step does not
  move the colour at all.

The last one is what turns the list of steps into a walk in `T`: reading the colours of the ends of
the steps in order gives a walk in `T`, whose non-degenerate edges are exactly the labels of the
crossed steps, i.e. of the visits of the face.
-/
import Mathlib
import Submission.Work.ORDunwoody.faceTriples_arcIndex
import Submission.Work.ORDunwoody.colour_arcIndex

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.CW

open Work.ORDunwoody.Dunwoody Work.ORDunwoody.Cayley
open scoped Sym2

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- The pattern point crossed by an oriented step of the boundary walk, if any. -/
def oMid? : OStep D → Option (MidV D)
  | .cross _ m _ => some m
  | .jump _ _ => none

/-- The pattern point of an oriented step, with the two old vertices on either side. -/
def oTriple? : OStep D → Option (BaseV D × MidV D × BaseV D)
  | .cross s m t => some (s, m, t)
  | .jump _ _ => none

/-- The edge of `T` whose midpoint is the pattern point crossed by the step, if any. -/
def oLabel? : OStep D → Option (Sym2 V)
  | .cross _ m _ => some (MidV.label m)
  | .jump _ _ => none

/-- The **colour condition** on a step: a crossed step traverses an edge of `T` (its ends have
adjacent colours in `T`, and the unordered colour-pair is the step's label); a collapsed step does
not move the colour at all. -/
def oGood : OStep D → Prop
  | .cross s m t =>
      T.graph.Adj (colour D s) (colour D t) ∧ s(colour D s, colour D t) = MidV.label m
  | .jump s t => colour D s = colour D t

@[simp] theorem oMid?_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    oMid? (OStep.cross s m t) = some m := rfl

@[simp] theorem oMid?_jump (s t : BaseV D) : oMid? (OStep.jump s t) = none := rfl

@[simp] theorem oTriple?_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    oTriple? (OStep.cross s m t) = some (s, m, t) := rfl

@[simp] theorem oTriple?_jump (s t : BaseV D) : oTriple? (OStep.jump s t) = none := rfl

@[simp] theorem oLabel?_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    oLabel? (OStep.cross s m t) = some (MidV.label m) := rfl

@[simp] theorem oLabel?_jump (s t : BaseV D) : oLabel? (OStep.jump s t) = none := rfl

/-- A step crosses a pattern point exactly when it is not a jump. -/
theorem oMid?_ne_none_iff {s : OStep D} : oMid? s ≠ none ↔ ∃ a m b, s = OStep.cross a m b := by
  cases s with
  | cross a m b => simp
  | jump a b => simp

end Work.ORDunwoody.CW
