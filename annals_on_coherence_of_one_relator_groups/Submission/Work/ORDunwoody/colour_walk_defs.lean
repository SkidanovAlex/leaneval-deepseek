/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The auxiliary notions for "the colour is constant on an arc"

`Work.ORDunwoody.colour_arcIndex` states that two old vertices of the boundary walk of a face
that have the same *arc index* (the number of pattern points strictly before them, `arcIndex` in
`Dunwoody/Piece.lean`) have the same colour (`colour` in `Dunwoody/Pattern.lean`).  The reason is
that the old vertices with a fixed arc index form a maximal run of *consecutive* old vertices of
the walk, and consecutive old vertices of a boundary walk are joined by a *collapsed* generator
edge, along which the colour is constant (`Work.ORDunwoody.colour_collapsed`).

This file isolates the two list-theoretic notions needed to say this:

* `initOlds l`: the initial run of old vertices of `l`, i.e. the old vertices of `l` up to the
  first pattern point;
* `oldRel v w`: the relation "if `v` and `w` are both old then they have the same colour".

The main facts are then: the entries `(u, k)` of `arcIndexAux l k` with second component `k` are
exactly the old vertices of `initOlds l`; and if `l` is a chain in `oldRel` (i.e. any two
consecutive entries that are both old have the same colour), then all the old vertices of
`initOlds l` have one colour, and more generally all old vertices of `l` occurring with the same
arc index have the same colour.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Piece
import Submission.Work.ORDunwoody.Dunwoody.Pattern

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}

/-! ## The initial run of old vertices -/

/-- The *initial run* of old vertices of a list of vertices of `Λ''`: the old vertices up to the
first pattern point. -/
def initOlds {D : GeoData T t₀ P} : List (Vertex D) → List (BaseV D)
  | Sum.inl u :: rest => u :: initOlds rest
  | _ => []

@[simp] theorem initOlds_nil {D : GeoData T t₀ P} :
    initOlds ([] : List (Vertex D)) = [] := rfl

@[simp] theorem initOlds_inl {D : GeoData T t₀ P} (u : BaseV D) (rest : List (Vertex D)) :
    initOlds (Sum.inl u :: rest) = u :: initOlds rest := rfl

@[simp] theorem initOlds_inr {D : GeoData T t₀ P} (m : MidV D) (rest : List (Vertex D)) :
    initOlds (Sum.inr m :: rest) = [] := rfl

/-! ## The "same colour of consecutive old vertices" relation -/

/-- Two vertices of `Λ''` are **old-compatible** when, if both of them are old, they have the
same colour.  A chain in this relation is exactly a walk whose consecutive old vertices have the
same colour. -/
def oldRel (D : GeoData T t₀ P) (v w : Vertex D) : Prop :=
  ∀ (a b : BaseV D), v = Sum.inl a → w = Sum.inl b → colour D a = colour D b

theorem oldRel_inl_inl {D : GeoData T t₀ P} {a b : BaseV D} :
    oldRel D (Sum.inl a) (Sum.inl b) ↔ colour D a = colour D b := by
  refine ⟨fun h => h a b rfl rfl, fun h a' b' h1 h2 => ?_⟩
  simp only [Sum.inl.injEq] at h1 h2
  rw [← h1, ← h2]
  exact h

theorem oldRel_of_inr_left {D : GeoData T t₀ P} (m : MidV D) (w : Vertex D) :
    oldRel D (Sum.inr m) w := fun a b h1 _ => absurd h1 (by simp)

theorem oldRel_of_inr_right {D : GeoData T t₀ P} (v : Vertex D) (m : MidV D) :
    oldRel D v (Sum.inr m) := fun a b _ h2 => absurd h2 (by simp)

end Work.ORDunwoody.Dunwoody
