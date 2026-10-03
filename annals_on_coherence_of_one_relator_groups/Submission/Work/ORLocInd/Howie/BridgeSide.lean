/-
# One-sided reachability for the bridge lemma

This file collects the auxiliary notions and elementary facts used by
`Work.ORLocInd.Howie.false_of_bridge_forest_side` (L5d of `N4_LOCIND_LEAD.md`) and by the
lemmas delegated around it.

Fix a presentation `P` and an arrow `e : e.left ⟶ e.right` of `Γ`.

* `Reach P e y` : `y` is joined to `e.left` by a path of `Γ ∖ {e, e⁻¹}` (the graph obtained by
  deleting all arrows whose code is `P.edgeOf e`).  The hypothesis `hbr` of the bridge lemma
  says `¬ Reach P e e.right`.
* `not_reach_right_of_bridge` : `hbr` reversed.
* `reach_of_reach_of_delArrow` : an arrow of `Γ ∖ e` goes from a reachable vertex to a reachable
  vertex.
* `not_isCyclicallyReduced_of_startsWith_endsWith` : a closed path of length at least two whose
  first arrow is `f` and whose last arrow is `f⁻¹` is not cyclically reduced.  This is the
  "cyclic" input of the bridge lemma.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.PathReduced
import Submission.Work.ORLocInd.Howie.endsWith_comp
import Submission.Work.ORLocInd.Howie.startsWith_comp
import Submission.Work.ORLocInd.Howie.Cover

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The cyclic lemma -/

/-- A closed path of length at least two whose first arrow is `f` and whose last arrow is the
reverse of `f` is not cyclically reduced: reading it cyclically creates the backtrack
`f, f⁻¹` across the join.

The hypothesis `2 ≤ p.length` is necessary: for `p = f.toPath` with `f` a self-inverse loop the
statements `StartsWith p f` and `EndsWith p (reverse f)` both hold, yet `IsCyclicallyReduced p`
holds as well (no cyclic backtrack can be *exhibited* for a path of length one). -/
theorem not_isCyclicallyReduced_of_startsWith_endsWith {v u : V} {p : Quiver.Path v v}
    {f : v ⟶ u} (hlen : 2 ≤ p.length) (h1 : Quiver.Path.StartsWith p f)
    (h2 : Quiver.Path.EndsWith p (Quiver.reverse f)) : ¬ IsCyclicallyReduced p := by
  obtain ⟨p₁, hp₁⟩ := h1
  have hp₁ne : p₁.length ≠ 0 := by
    intro h0
    have hlen' : p.length = 1 := by
      rw [hp₁, Quiver.Path.length_comp, Quiver.Path.length_toPath, h0, add_zero]
    omega
  have h2' : Quiver.Path.EndsWith p₁ (Quiver.reverse f) := by
    rw [hp₁] at h2
    exact (endsWith_comp hp₁ne (Quiver.reverse f)).mp h2
  obtain ⟨p₂, hp₂⟩ := h2'
  intro hcyc
  exact hcyc ⟨u, f, p₂, by rw [hp₁, hp₂]⟩

/-! ## Reachability in `Γ ∖ e` -/

/-- `Reach P e y`: the vertex `y` is joined to `e.left` by a path of `Γ ∖ e`, the graph obtained
from `Γ` by deleting the arrows of code `P.edgeOf e`. -/
def Reach (P : Presentation V) (e : Quiver.Total V) (y : V) : Prop :=
  Nonempty (Quiver.Path (e.left : DelV (P.keepCode (P.edgeOf e)))
    (y : DelV (P.keepCode (P.edgeOf e))))

/-- The bridge hypothesis, read in the other direction: if there is no path of `Γ ∖ e` from
`e.right` to `e.left`, then `e.right` is not reachable from `e.left` either. -/
theorem not_reach_right_of_bridge (P : Presentation V) (e : Quiver.Total V)
    (hbr : ¬ Nonempty (Quiver.Path (e.right : DelV (P.keepCode (P.edgeOf e)))
      (e.left : DelV (P.keepCode (P.edgeOf e))))) :
    ¬ Reach P e e.right := by
  rintro ⟨p⟩
  exact hbr ⟨p.reverse⟩

/-- An arrow of `Γ ∖ e` leads from a reachable vertex to a reachable vertex. -/
theorem reach_of_reach_of_delArrow (P : Presentation V) (e : Quiver.Total V) {x y : V}
    (f : (x : DelV (P.keepCode (P.edgeOf e))) ⟶ (y : DelV (P.keepCode (P.edgeOf e))))
    (h : Reach P e y) : Reach P e x := by
  obtain ⟨p⟩ := h
  exact ⟨p.comp (Quiver.reverse f).toPath⟩

/-- An arrow of `Γ` whose code is not the code of `e` is an arrow of `Γ ∖ e`, so it leads from a
reachable vertex to a reachable vertex.  (`reach_of_reach_of_delArrow` in the form in which it is
applied to an arrow of `Γ`.) -/
theorem reach_of_reach_of_code_ne (P : Presentation V) (e : Quiver.Total V) {x y : V}
    (f : x ⟶ y) (hf : P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e) (h : Reach P e y) :
    Reach P e x := by
  obtain ⟨p⟩ := h
  exact ⟨p.cons (Quiver.reverse f)⟩


end Work.ORLocInd.Howie
