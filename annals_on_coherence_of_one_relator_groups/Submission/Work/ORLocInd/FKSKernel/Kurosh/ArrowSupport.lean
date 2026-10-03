import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Paths all of whose arrows lie in a prescribed set

Given a graph `V` and a set `S` of arrows of `V`, we say that a path `p` *consists of `S`-arrows*
(`Quiver.Path.AllArrows S p`, also written `p.AllArrows S`) if every arrow occurring in `p`
belongs to `S`.

This is the bookkeeping needed for the statement "in a tree, a set of arrows closed under
reversal which connects all vertices contains every arrow": one writes a path between two vertices
using only arrows of `S`, reduces it (deleting backtracks, which stay inside `S`), and observes
that adjoining the reverse of an arrow outside `S` then produces a non-trivial reduced closed
path.
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- `p.AllArrows S` means that every arrow of the path `p` lies in the set `S`. -/
def AllArrows (S : Set (Quiver.Total V)) {a b : V} (p : Quiver.Path a b) : Prop :=
  match p with
  | .nil => True
  | .cons p f => AllArrows S p ∧ Quiver.Total.mk _ _ f ∈ S

theorem allArrows_nil (S : Set (Quiver.Total V)) (a : V) :
    (Quiver.Path.nil : Quiver.Path a a).AllArrows S := trivial

theorem allArrows_cons {S : Set (Quiver.Total V)} {a b c : V} (p : Quiver.Path a b)
    (f : b ⟶ c) :
    (p.cons f).AllArrows S ↔ p.AllArrows S ∧ Quiver.Total.mk b c f ∈ S := by
  rw [AllArrows]

theorem allArrows_toPath {S : Set (Quiver.Total V)} {a b : V} (f : a ⟶ b) :
    f.toPath.AllArrows S ↔ Quiver.Total.mk a b f ∈ S := by
  have h : f.toPath = (Quiver.Path.nil : Quiver.Path a a).cons f := rfl
  rw [h, allArrows_cons]
  exact ⟨And.right, fun hf => ⟨trivial, hf⟩⟩

theorem allArrows_comp {S : Set (Quiver.Total V)} {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) :
    (p.comp q).AllArrows S ↔ p.AllArrows S ∧ q.AllArrows S := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil]
           exact ⟨fun h => ⟨h, allArrows_nil S b⟩, fun h => h.1⟩
  | cons q f ih => rw [Quiver.Path.comp_cons, allArrows_cons, ih, allArrows_cons]; tauto

/-- Reversing a path preserves the property of consisting of `S`-arrows, provided `S` is closed
under reversal of arrows (`Quiver.Total.reverse`). -/
theorem allArrows_reverse [Quiver.HasReverse V] {S : Set (Quiver.Total V)}
    (hS : ∀ e : Quiver.Total V, e ∈ S ↔ Quiver.Total.reverse e ∈ S) {a b : V}
    (p : Quiver.Path a b) : p.AllArrows S ↔ p.reverse.AllArrows S := by
  induction p with
  | nil => constructor <;> intro _ <;> trivial
  | cons p f ih =>
    have hrev : (p.cons f).reverse = (Quiver.reverse f).toPath.comp p.reverse := by
      rw [show (p.cons f).reverse = f.toPath.reverse.comp p.reverse from rfl,
        Quiver.Path.reverse_toPath]
    rw [hrev, allArrows_comp, allArrows_toPath, ← ih, allArrows_cons]
    constructor
    · rintro ⟨hp, hf⟩
      exact ⟨(hS (Quiver.Total.mk _ _ f)).mp hf, hp⟩
    · rintro ⟨hf, hp⟩
      exact ⟨hp, (hS (Quiver.Total.mk _ _ f)).mpr hf⟩

/-- Deleting a backtrack from a path consisting of `S`-arrows produces a path consisting of
`S`-arrows. -/
theorem allArrows_of_deleteBacktrack [Quiver.HasReverse V] {S : Set (Quiver.Total V)}
    {a b : V} {p q : Quiver.Path a b} (h : Quiver.Path.DeleteBacktrack p q)
    (hp : p.AllArrows S) : q.AllArrows S := by
  obtain ⟨x, y, p₁, e, p₂, rfl, rfl⟩ :=
    Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_iff.mp h
  rw [allArrows_comp, allArrows_comp, allArrows_toPath, allArrows_comp, allArrows_toPath] at hp
  rw [allArrows_comp]
  tauto

/-- Reduction to a reduced path preserves the property of consisting of `S`-arrows. -/
theorem allArrows_of_reducesTo [Quiver.HasReverse V] {S : Set (Quiver.Total V)} {a b : V}
    {p q : Quiver.Path a b} (h : p.ReducesTo q) (hp : p.AllArrows S) : q.AllArrows S := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih => exact allArrows_of_deleteBacktrack hstep ih

/-- A tree has no loops: there is no arrow from a vertex to itself. -/
theorem false_of_isTree_loop [Quiver.HasInvolutiveReverse V] (hT : Work.ORBassSerre.IsTree V)
    {a : V} (f : a ⟶ a) : False := by
  have hred : f.toPath.IsReduced :=
    Quiver.Path.IsReduced.of_length_lt_two (by rw [Quiver.Path.length_toPath]; norm_num)
  have hnil := hT.2 a f.toPath hred
  have hlen : f.toPath.length = 0 := by rw [hnil]; rfl
  rw [Quiver.Path.length_toPath] at hlen
  exact absurd hlen (by norm_num)

end Quiver.Path
