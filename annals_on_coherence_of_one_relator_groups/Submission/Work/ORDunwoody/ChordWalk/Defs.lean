/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The boundary walk of a face as a list of *steps*

This file sets up the combinatorial skeleton used to prove
`Work.ORDunwoody.colour_of_chord`: that the two visits of a *chord* of a face traverse the edge of
`T` they label in *opposite* directions.

`faceAux D a w` (`Dunwoody/FaceWalk.lean`) is the tail of the boundary walk of the face `(w, a)` of
`Λ''`; it is the concatenation of one *block* per letter of `w`, each block being a subdivision of
the corresponding generator edge.  We package each block as a list of **steps** (`St D`):

* `cross s m t` — the traversal of a cell of `Λ'`: from the old vertex `s` to the old vertex `t`
  through the pattern point `m` at the midpoint;
* `jump s t` — the traversal of a *collapsed* generator edge (`L (j,true) = 0`), which visits no
  pattern point.

The interest of this decomposition is that on a list of steps that forms a *chain*
(`tgt s = src s'` for consecutive steps)

* the boundary walk is `steps.flatMap St.verts`, so the pattern points visited are exactly the
  `cross` steps (`St.triple?`), and the arc indices of the old vertices are the prefix counts of
  the `cross` steps;
* the *colours* (`Dunwoody/Pattern.lean`) of `src` and `tgt` of a step are the two ends of the edge
  of `T` that the step traverses — adjacent for a `cross`, equal for a `jump` — so the list of
  colours read along the steps is a walk in `T`, whose non-degenerate edges are exactly the labels
  of the visits.

The last point is what turns "two visits of one fibre are paired by a chord" into the geometric
statement "the two visits traverse the edge in opposite directions", proved by the elementary fact
that a walk in a forest that avoids an edge cannot cross from one side of it to the other
(`Work.ORDunwoody.eq_of_walk_avoids_edge`).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.Dunwoody.Pattern
import Submission.Work.ORDunwoody.Dunwoody.Piece
import Submission.Work.ORDunwoody.colour_collapsed
import Submission.Work.ORDunwoody.cell_label_eq_colour

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

/-! ## The steps -/

/-- A **step** of the boundary walk of `Λ''`: the traversal of a cell of `Λ'` (visiting the pattern
point at its midpoint) or of a collapsed generator edge (visiting none). -/
inductive St (D : GeoData T t₀ P) : Type u where
  /-- The traversal of a cell of `Λ'`, from `s` to `t` through the pattern point `m`. -/
  | cross (s : BaseV D) (m : MidV D) (t : BaseV D) : St D
  /-- The traversal of a collapsed generator edge, from `s` to `t`. -/
  | jump (s t : BaseV D) : St D

namespace St

variable {D : GeoData T t₀ P}

/-- The old vertex at which a step starts. -/
def src : St D → BaseV D
  | cross s _ _ => s
  | jump s _ => s

/-- The old vertex at which a step ends. -/
def tgt : St D → BaseV D
  | cross _ _ t => t
  | jump _ t => t

/-- The vertices of `Λ''` visited *after* the starting vertex of a step. -/
def verts : St D → List (Vertex D)
  | cross _ m t => [Sum.inr m, Sum.inl t]
  | jump _ t => [Sum.inl t]

/-- The pattern point visited by a step, if any. -/
def mid? : St D → Option (MidV D)
  | cross _ m _ => some m
  | jump _ _ => none

/-- The pattern point of a step with the two old vertices on either side, if any. -/
def triple? : St D → Option (BaseV D × MidV D × BaseV D)
  | cross s m t => some (s, m, t)
  | jump _ _ => none

/-- The *label* of a step: the edge of `T` whose midpoint is the pattern point of the step. -/
def label? : St D → Option (Sym2 V)
  | cross _ m _ => some (MidV.label m)
  | jump _ _ => none

/-- A step is *compatible* when its two ends are the two ends of the cell of its pattern point
(vacuously for a collapsed edge). -/
def Compat : St D → Prop
  | cross s m t => (s = MidV.src m ∧ t = MidV.tgt m) ∨ (s = MidV.tgt m ∧ t = MidV.src m)
  | jump _ _ => True

/-- The increment of the arc index along a step: `1` for a step through a pattern point. -/
def inc : St D → ℕ
  | cross .. => 1
  | jump .. => 0

/-- A step is *good* when the two old vertices at its ends have adjacent colours in `T` — with the
colour-edge equal to the step's label — or (for a collapsed edge) equal colours.  This is the
statement that `colour` maps the step to an edge (or a point) of `T`. -/
def Good : St D → Prop
  | cross s m t =>
      T.graph.Adj (colour D s) (colour D t) ∧ s(colour D s, colour D t) = MidV.label m
  | jump s t => colour D s = colour D t

@[simp] theorem src_cross (s : BaseV D) (m : MidV D) (t : BaseV D) : src (cross s m t) = s := rfl

@[simp] theorem src_jump (s t : BaseV D) : src (jump s t) = s := rfl

@[simp] theorem tgt_cross (s : BaseV D) (m : MidV D) (t : BaseV D) : tgt (cross s m t) = t := rfl

@[simp] theorem tgt_jump (s t : BaseV D) : tgt (jump s t) = t := rfl

@[simp] theorem verts_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    verts (cross s m t) = ([Sum.inr m, Sum.inl t] : List (Vertex D)) := rfl

@[simp] theorem verts_jump (s t : BaseV D) : verts (jump s t) = ([Sum.inl t] : List (Vertex D)) :=
  rfl

@[simp] theorem mid?_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    mid? (cross s m t) = some m := rfl

@[simp] theorem mid?_jump (s t : BaseV D) : mid? (jump s t) = none := rfl

@[simp] theorem triple?_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    triple? (cross s m t) = some (s, m, t) := rfl

@[simp] theorem triple?_jump (s t : BaseV D) : triple? (jump s t) = none := rfl

@[simp] theorem label?_cross (s : BaseV D) (m : MidV D) (t : BaseV D) :
    label? (cross s m t) = some (MidV.label m) := rfl

@[simp] theorem label?_jump (s t : BaseV D) : label? (jump s t) = none := rfl

@[simp] theorem inc_cross (s : BaseV D) (m : MidV D) (t : BaseV D) : inc (cross s m t) = 1 := rfl

@[simp] theorem inc_jump (s t : BaseV D) : inc (jump s t) = 0 := rfl

/-- The pattern point of a step is the one visited by its vertex list. -/
theorem filterMap_midOf_verts (s : St D) :
    (verts s).filterMap Vertex.midOf = (mid? s).toList := by
  cases s <;> rfl

/-- The label of the pattern point of a step is the edge traversed by the step. -/
theorem map_label_mid? (s : St D) :
    (mid? s).map (MidV.label (D := D)) = label? s := by
  cases s <;> rfl

/-- A step through a pattern point is not a jump. -/
theorem label?_ne_none_iff {s : St D} : label? s ≠ none ↔ ∃ a m b, s = cross a m b := by
  cases s with
  | cross a m b => simp
  | jump a b => simp

end St

/-! ## The steps of one letter -/

/-- The steps of the traversal of the positive letter `(j,true)` based at `a`. -/
def letterStepsPos (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (St D) :=
  if D.L (j, true) = 0 then
    [St.jump ((a, Sum.inl ()) : BaseV D) ((a * CayV.genE P (j, true), Sum.inl ()) : BaseV D)]
  else
    (List.finRange (D.L (j, true))).map (fun k : Fin (D.L (j, true)) =>
      St.cross (pos D a j (k : ℕ)) ⟨a, ⟨j, k⟩⟩ (pos D a j ((k : ℕ) + 1)))

/-- The steps of the traversal of the negative letter `(j,false)` based at `a`. -/
def letterStepsNeg (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (St D) :=
  if D.L (j, true) = 0 then
    [St.jump ((a, Sum.inl ()) : BaseV D)
      ((a * (CayV.genE P (j, true))⁻¹, Sum.inl ()) : BaseV D)]
  else
    ((List.finRange (D.L (j, true))).reverse).map (fun k : Fin (D.L (j, true)) =>
      St.cross (pos D (a * (CayV.genE P (j, true))⁻¹) j ((k : ℕ) + 1))
        ⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩
        (pos D (a * (CayV.genE P (j, true))⁻¹) j (k : ℕ)))

/-- The steps of the traversal of one letter based at `a`. -/
def letterSteps (D : GeoData T t₀ P) (a : G) : Fin P.n × Bool → List (St D)
  | (j, true) => letterStepsPos D a j
  | (j, false) => letterStepsNeg D a j

@[simp] theorem letterSteps_true (D : GeoData T t₀ P) (a : G) (j : Fin P.n) :
    letterSteps D a (j, true) = letterStepsPos D a j := rfl

@[simp] theorem letterSteps_false (D : GeoData T t₀ P) (a : G) (j : Fin P.n) :
    letterSteps D a (j, false) = letterStepsNeg D a j := rfl

/-! ## The steps of a whole word -/

/-- The steps of the boundary walk of the word `w` read at the base point `a`. -/
def wordSteps (D : GeoData T t₀ P) (a : G) : List (Fin P.n × Bool) → List (St D)
  | [] => []
  | x :: w => letterSteps D a x ++ wordSteps D (a * CayV.genE P x) w

@[simp] theorem wordSteps_nil (D : GeoData T t₀ P) (a : G) : wordSteps D a [] = [] := rfl

@[simp] theorem wordSteps_cons (D : GeoData T t₀ P) (a : G) (x : Fin P.n × Bool)
    (w : List (Fin P.n × Bool)) :
    wordSteps D a (x :: w) = letterSteps D a x ++ wordSteps D (a * CayV.genE P x) w := rfl

/-! ## Counting the pattern points before a position of a list -/

/-- **The number of "hits" of `f` before position `i`** of a list `l`: the length of the
`filterMap` of `f` over the prefix `l.take i`.  For `f = St.mid?` this is the arc index of the
old vertex following the `i`-th step. -/
def hitPrefix {α β : Type*} (f : α → Option β) (l : List α) (i : ℕ) : ℕ :=
  ((l.take i).filterMap f).length

end Work.ORDunwoody.CW
