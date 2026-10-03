/-
# The rose graph and the word/path dictionary

The *rose* on a generating type `α` is the graph with one vertex and one loop for each `a : α`; its
fundamental group is the free group `F(α)`.  This is the graph on which Howie's Theorem 3.1 is
applied to a one-relator group `⟨α | r⟩`: the single relator `r` becomes a single closed path at the
vertex, and the vertex group of the resulting groupoid presentation is `⟨α | r⟩`.

## Conventions fixed here (used by `Howie/RoseVertexGroup.lean` and `Howie/onePresentation.lean`)

* `Rose α` is a *type synonym* for `PUnit` (`def`, not `abbrev`, so that instance search does not
  confuse the quiver structure below with Mathlib's `Quiver PUnit`), and the single vertex is
  `roseVtx α` (**always use `roseVtx α`, never `PUnit.unit`**: writing `PUnit.unit` makes the
  elaborator unfold `Rose α` to `PUnit` and then pick `CategoryTheory.catToReflQuiver.toQuiver`,
  with the wrong arrow type);
* the arrows at the vertex are `α × Bool`, and the reverse of `(a, b)` is `(a, !b)`; the pair
  `(a, false)` reads as the generator `a` and `(a, true)` as the negative letter `a⁻¹` (this is the
  convention of `FreeGroup.toWord`, `List (α × Bool)`);
* `roseTotal x` is the arrow of the rose corresponding to the letter `x`;
* `rosePath L` is the closed path at the vertex whose arrow list is `L`, read from left to right;
* `roseWord p` is its inverse, `(p.arrowList).map fun e => e.hom`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Cover

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.ambiguousOpen false

universe u

namespace Work.ORLocInd.Howie

open Quiver

/-- The rose graph on the generating type `α`: one vertex, one loop per generator.

A type synonym for `PUnit`, so that the `Quiver` structure below is not confused with Mathlib's
instance on `PUnit`. -/
def Rose (α : Type u) : Type u := PUnit

/-- The single vertex of the rose.  Always use this, not `PUnit.unit`. -/
def roseVtx (α : Type u) : Rose α := PUnit.unit

instance roseQuiver (α : Type u) : Quiver (Rose α) := ⟨fun _ _ => α × Bool⟩

instance roseReverse (α : Type u) : Quiver.HasInvolutiveReverse (Rose α) where
  reverse' := fun {_ _} e => (e.1, !e.2)
  inv' := fun {_ _} e => Prod.ext rfl (Bool.not_not e.2)

instance roseDecidableEq (α : Type u) [DecidableEq α] : DecidableEq (Rose α) :=
  inferInstanceAs (DecidableEq PUnit)

/-- The arrow of the rose corresponding to a letter `(a, b)`. -/
def roseTotal {α : Type u} (x : α × Bool) : Quiver.Total (Rose α) :=
  Quiver.Total.mk (roseVtx α) (roseVtx α) x

@[simp] theorem roseTotal_hom {α : Type u} (x : α × Bool) : (roseTotal x).hom = x := by
  cases x; rfl

@[simp] theorem roseTotal_left {α : Type u} (x : α × Bool) :
    (roseTotal x).left = roseVtx α := rfl

@[simp] theorem roseTotal_right {α : Type u} (x : α × Bool) :
    (roseTotal x).right = roseVtx α := rfl

@[simp] theorem roseTotal_reverse {α : Type u} (x : α × Bool) :
    Quiver.totalReverse (roseTotal x) = roseTotal (x.1, !x.2) := by cases x; rfl

/-- The closed path of the rose reading the word `L` from left to right. -/
def rosePath {α : Type u} : List (α × Bool) → Quiver.Path (roseVtx α) (roseVtx α)
  | [] => Quiver.Path.nil
  | a :: as => (Quiver.Path.nil.cons a).comp (rosePath as)

/-- The word read off a closed path of the rose. -/
def roseWord {α : Type u} (p : Quiver.Path (roseVtx α) (roseVtx α)) : List (α × Bool) :=
  p.arrowList.map (fun e => e.hom)

@[simp] theorem rosePath_nil {α : Type u} :
    rosePath ([] : List (α × Bool)) = Quiver.Path.nil := rfl

theorem rosePath_cons {α : Type u} (a : α × Bool) (as : List (α × Bool)) :
    rosePath (a :: as) = (Quiver.Path.nil.cons a).comp (rosePath as) := rfl

theorem rosePath_singleton {α : Type u} (a : α × Bool) :
    rosePath [a] = Quiver.Path.nil.cons a := by
  rw [rosePath_cons, rosePath_nil, Quiver.Path.comp_nil]

theorem roseWord_cons {α : Type u} (p : Quiver.Path (roseVtx α) (roseVtx α))
    (e : roseVtx α ⟶ roseVtx α) : roseWord (p.cons e) = roseWord p ++ [e] := by
  rw [roseWord, roseWord, Quiver.Path.arrowList_cons, List.map_append]
  rfl

theorem rosePath_append {α : Type u} (L₁ L₂ : List (α × Bool)) :
    rosePath (L₁ ++ L₂) = (rosePath L₁).comp (rosePath L₂) := by
  induction L₁ with
  | nil => rw [List.nil_append, rosePath_nil, Quiver.Path.nil_comp]
  | cons a as ih =>
      rw [List.cons_append, rosePath_cons, rosePath_cons, ih, Quiver.Path.comp_assoc]

theorem rosePath_arrowList {α : Type u} (L : List (α × Bool)) :
    (rosePath L).arrowList = L.map roseTotal := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      rw [rosePath_cons, Quiver.Path.arrowList_comp', ih, Quiver.Path.arrowList_cons,
        Quiver.Path.arrowList_nil, List.nil_append]
      rfl

theorem roseWord_rosePath {α : Type u} (L : List (α × Bool)) : roseWord (rosePath L) = L := by
  rw [roseWord, rosePath_arrowList, List.map_map]
  have hf : ((fun e : Quiver.Total (Rose α) => e.hom)) ∘ roseTotal =
      (id : α × Bool → α × Bool) := by
    funext x
    exact roseTotal_hom x
  rw [hf, List.map_id]

theorem rosePath_length {α : Type u} (L : List (α × Bool)) : (rosePath L).length = L.length := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      rw [rosePath_cons, Quiver.Path.length_comp, ih]
      exact Nat.add_comm 1 _

end Work.ORLocInd.Howie
