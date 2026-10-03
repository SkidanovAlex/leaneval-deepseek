/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The map `φ : Λ'' → T` and the pattern data of a face

`Dunwoody/Source.lean` defines the subdivided complex `Λ''`; `Dunwoody/FaceWalk.lean` defines the
boundary walk of a face.  This file adds the two pieces of data that the pattern construction
needs from the map `φ`:

* `colour : BaseV D → V`: the image in `T` of an *old* vertex (`c ∗ ↦ c • t₀` and the `i`-th
  interior point of the generator edge `(j,true)` at `c` ↦ `c • geo (j,true) (i+1)`), which is
  `G`-equivariant (`colour_smul`);
* `Vertex.midOf`, `Vertex.oldOf` and `visits`: the pattern points visited by a boundary walk.

The *label* of a pattern point (`MidV.label`, in `Source.lean`) is the edge of `T` that the cell
maps onto; a pattern point of the walk is visited "at" the step whose cell has that label.  The
colour of an old vertex and the label of the pattern point next to it agree:
`MidV.label p = s(colour u, colour w)` for the two old vertices adjacent to `p` — this is
`MidV.label_eq_colour` below, and it is what turns the face walk into a walk in `T`.

Nothing here uses the simple connectivity of `Λ` (see `DESIGN_N13.md` §2a).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The map `φ` on the old vertices -/

/-- **The map `φ` of the construction**, on the old vertices of `Λ''`: the base point `(c, ∗)`
goes to `c • t₀`, and the `i`-th interior point of the generator edge `(j,true)` at `c` goes to
the `(i+1)`-st vertex of the geodesic of that generator edge. -/
def colour (D : GeoData T t₀ P) : BaseV D → V
  | (c, Sum.inl ()) => c • t₀
  | (c, Sum.inr ⟨j, i⟩) => c • D.geo (j, true) ⟨i + 1, by have := i.isLt; omega⟩

@[simp] theorem colour_base (D : GeoData T t₀ P) (c : G) :
    colour D (c, Sum.inl ()) = c • t₀ := rfl

theorem colour_inner (D : GeoData T t₀ P) (c : G) (j : Fin P.n) (i : InnerIdx D j) :
    colour D (c, Sum.inr ⟨j, i⟩) = c • D.geo (j, true) ⟨i + 1, by have := i.isLt; omega⟩ := rfl

/-- The map `φ` is `G`-equivariant. -/
theorem colour_smul (D : GeoData T t₀ P) (g : G) (u : BaseV D) :
    colour D (g • u) = g • colour D u := by
  obtain ⟨c, b⟩ := u
  rcases b with u | ⟨j, i⟩
  · cases u
    simp only [baseV_smul, colour_base, mul_smul]
  · simp only [baseV_smul, colour_inner, mul_smul]

/-! ## The pattern points on a boundary walk -/

/-- The pattern point of a vertex of `Λ''`, if it is one. -/
def Vertex.midOf : Vertex D → Option (MidV D)
  | Sum.inl _ => none
  | Sum.inr p => some p

/-- The old vertex of a vertex of `Λ''`, if it is one. -/
def Vertex.oldOf : Vertex D → Option (BaseV D)
  | Sum.inl u => some u
  | Sum.inr _ => none

@[simp] theorem Vertex.midOf_inl (u : BaseV D) : Vertex.midOf (Sum.inl u : Vertex D) = none := rfl

@[simp] theorem Vertex.midOf_inr (p : MidV D) : Vertex.midOf (Sum.inr p : Vertex D) = some p := rfl

@[simp] theorem Vertex.oldOf_inl (u : BaseV D) : Vertex.oldOf (Sum.inl u : Vertex D) = some u := rfl

@[simp] theorem Vertex.oldOf_inr (p : MidV D) : Vertex.oldOf (Sum.inr p : Vertex D) = none := rfl

/-- **The pattern points visited by the boundary walk of a face.** -/
def visits (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List (MidV D) :=
  (faceWalk D c w).filterMap Vertex.midOf

/-- **The old vertices visited by the boundary walk of a face**, in order. -/
def oldVisits (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List (BaseV D) :=
  (faceWalk D c w).filterMap Vertex.oldOf

/-- The colours, in order, of the old vertices visited by a boundary walk. -/
def colours (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List V :=
  (oldVisits D c w).map (colour D)

@[simp] theorem visits_eq (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) :
    visits D c w = (faceWalk D c w).filterMap Vertex.midOf := rfl

@[simp] theorem oldVisits_eq (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) :
    oldVisits D c w = (faceWalk D c w).filterMap Vertex.oldOf := rfl

@[simp] theorem colours_eq (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) :
    colours D c w = (oldVisits D c w).map (colour D) := rfl


/-! ## The visits, with the old vertices on either side

A boundary walk alternates old vertices and pattern points, so every pattern point on it is
flanked by two old vertices.  Recording these triples gives, for each visit, the two old vertices
whose colours are the endpoints of the visit's label (`cell_label_eq_colour`), and the runs of
old vertices between consecutive visits are the *arcs* of the face. -/

/-- Accumulator for `visitTriples`: the carried old vertex is the one immediately preceding the
material still to be read.  Consecutive old vertices of the walk (a collapsed generator edge)
simply move the accumulator forward. -/
def visitTriplesAux : BaseV D → List (Vertex D) → List (BaseV D × MidV D × BaseV D)
  | _, [] => []
  | _, Sum.inl v :: rest => visitTriplesAux v rest
  | u, Sum.inr _ :: Sum.inr m' :: rest => visitTriplesAux u (Sum.inr m' :: rest)
  | u, Sum.inr m :: Sum.inl w :: rest => (u, m, w) :: visitTriplesAux w rest
  | _, Sum.inr _ :: [] => []

/-- The pattern points of a walk, each with the old vertex immediately before and immediately
after it.  Note that the triples *overlap*: consecutive pattern points of a boundary walk share
the old vertex between them. -/
def visitTriples : List (Vertex D) → List (BaseV D × MidV D × BaseV D)
  | Sum.inl u :: rest => visitTriplesAux u rest
  | Sum.inr _ :: rest => visitTriples rest
  | [] => []

@[simp] theorem visitTriples_nil : visitTriples (D := D) ([] : List (Vertex D)) = [] := rfl

@[simp] theorem visitTriplesAux_nil (u : BaseV D) : visitTriplesAux (D := D) u [] = [] := rfl

@[simp] theorem visitTriplesAux_inl (u v : BaseV D) (rest : List (Vertex D)) :
    visitTriplesAux (D := D) u (Sum.inl v :: rest) = visitTriplesAux v rest := rfl

@[simp] theorem visitTriplesAux_inr (u : BaseV D) (m : MidV D) (w : BaseV D)
    (rest : List (Vertex D)) :
    visitTriplesAux (D := D) u (Sum.inr m :: Sum.inl w :: rest) =
      (u, m, w) :: visitTriplesAux w rest := rfl

@[simp] theorem visitTriplesAux_inr_inr (u : BaseV D) (m m' : MidV D)
    (rest : List (Vertex D)) :
    visitTriplesAux (D := D) u (Sum.inr m :: Sum.inr m' :: rest) =
      visitTriplesAux u (Sum.inr m' :: rest) := rfl

@[simp] theorem visitTriplesAux_inr_nil (u : BaseV D) (m : MidV D) :
    visitTriplesAux (D := D) u (Sum.inr m :: ([] : List (Vertex D))) = [] := rfl

@[simp] theorem visitTriples_inl (u : BaseV D) (rest : List (Vertex D)) :
    visitTriples ((Sum.inl u : Vertex D) :: rest) = visitTriplesAux u rest := rfl

@[simp] theorem visitTriples_inr (m : MidV D) (rest : List (Vertex D)) :
    visitTriples ((Sum.inr m : Vertex D) :: rest) = visitTriples rest := rfl

@[simp] theorem visitTriples_cons (u : BaseV D) (m : MidV D) (w : BaseV D)
    (rest : List (Vertex D)) :
    visitTriples ((Sum.inl u : Vertex D) :: Sum.inr m :: Sum.inl w :: rest) =
      (u, m, w) :: visitTriples (Sum.inl w :: rest) := rfl

/-- **The pattern data of a face**: the visits of its boundary walk, each with the two old
vertices on either side. -/
def faceTriples (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) :
    List (BaseV D × MidV D × BaseV D) :=
  visitTriples (faceWalk D c w)

/-- The *visits* of a face: the pattern points of `faceTriples`. -/
def faceVisits (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List (MidV D) :=
  (faceTriples D c w).map (fun t => t.2.1)

/-- The *labels* of the visits of a face: the edge of `T` that each visit's cell maps onto. -/
def faceLabels (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List (Sym2 V) :=
  (faceVisits D c w).map (MidV.label (D := D))

end Work.ORDunwoody.Dunwoody

