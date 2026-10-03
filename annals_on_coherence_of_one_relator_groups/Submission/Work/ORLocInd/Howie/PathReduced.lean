/-
# The first/last arrow of a path, and reducedness of concatenations

This file begins the combinatorial chapter on *reducedness of concatenations of paths* that
the Howie development (`Submission/Work/ORLocInd/Howie/`) needs:

* `Quiver.Path.EndsWith p e` : the path `p` ends with the arrow `e`;
* `Quiver.Path.StartsWith p e` : the path `p` begins with the arrow `e`;
* `Quiver.Path.JoinConflict p q` : the concatenation `p.comp q` has a backtrack straddling the
  join, i.e. the last arrow of `p` is the reverse of the first arrow of `q`.

The point of these notions is the characterization
`(p.comp q).IsReduced ↔ p.IsReduced ∧ q.IsReduced ∧ ¬ JoinConflict p q`
(`Work.ORLocInd.Howie.isReduced_comp_iff`), and its iterated version for powers of a closed
path (`Work.ORLocInd.Howie.isReduced_compPower_of_comp_self`): a backtrack in a concatenation
is either inside one of the factors or straddles the join.
-/
import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

set_option autoImplicit false

universe u

namespace Quiver.Path

open Quiver

variable {V : Type u} [Quiver V]
variable {a b c : V}

/-- A path `p : Path a b` *ends with* the arrow `e : x ⟶ b`: it is a path `p' : Path a x`
followed by the single arrow `e`. -/
def EndsWith (p : Path a b) {x : V} (e : x ⟶ b) : Prop := ∃ p' : Path a x, p = p'.cons e

/-- A path `p : Path a b` *begins with* the arrow `e : a ⟶ y`: it is the single arrow `e`
followed by a path `p' : Path y b`. -/
def StartsWith (p : Path a b) {y : V} (e : a ⟶ y) : Prop := ∃ p' : Path y b, p = e.toPath.comp p'

theorem endsWith_cons (p : Path a b) (e : b ⟶ c) : EndsWith (p.cons e) e := ⟨p, rfl⟩

theorem cons_eq_comp_toPath (p : Path a b) (e : b ⟶ c) : p.cons e = p.comp e.toPath := rfl

theorem startsWith_toPath_comp (e : a ⟶ b) (p : Path b c) : StartsWith (e.toPath.comp p) e :=
  ⟨p, rfl⟩

theorem not_endsWith_nil {x : V} (e : x ⟶ a) : ¬ EndsWith (Path.nil : Path a a) e := by
  rintro ⟨p', h⟩
  exact Path.nil_ne_cons p' e h

theorem not_startsWith_nil {y : V} (e : a ⟶ y) : ¬ StartsWith (Path.nil : Path a a) e := by
  rintro ⟨p', h⟩
  have hl := congrArg Path.length h
  simp at hl
  omega

section HasReverse

variable [Quiver.HasReverse V]

/-- The concatenation `p.comp q` has a backtrack *straddling its join*: the last arrow of `p`
is the reverse of the first arrow of `q`.  Equivalently, `p.comp q` can be reduced by deleting
the pair consisting of the last arrow of `p` and the first arrow of `q`. -/
def JoinConflict (p : Path a b) (q : Path b c) : Prop :=
  ∃ (x : V) (p' : Path a x) (e : x ⟶ b) (q' : Path x c),
    p = p'.cons e ∧ q = (Quiver.reverse e).toPath.comp q'

/-- A straddling backtrack is a genuine backtrack, so a concatenation with a join conflict is
not reduced. -/
theorem joinConflict_not_isReduced {p : Path a b} {q : Path b c} (h : JoinConflict p q) :
    ¬ (p.comp q).IsReduced := by
  obtain ⟨x, p', e, q', hp, hq⟩ := h
  rintro hred
  refine hred (p'.comp q') ?_
  rw [hp, hq]
  rw [Quiver.Path.cons_eq_comp_toPath, Quiver.Path.comp_assoc]
  exact Quiver.Path.DeleteBacktrack.intro p' e q'

end HasReverse

end Quiver.Path
