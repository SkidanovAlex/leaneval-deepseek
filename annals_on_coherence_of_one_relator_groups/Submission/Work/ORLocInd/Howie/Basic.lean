/-
# The free groupoid of a graph, and its vertex groups

This is the beginning of the formalisation of J. Howie, *A short proof of a theorem of Brodskii*
(Publ. Mat. 44 (2000), 641--647), which proves that every torsion-free one-relator group is
locally indicable.  Howie's proof is combinatorial: a one-relator group is the *vertex group* of a
groupoid presentation `⟨Γ | R⟩` of a graph `Γ` (with one vertex, in the one-relator case), the
presentation is *staggered*, and no element of `R` is a proper power; the theorem is then that
every vertex group is locally indicable.

## Conventions

A *graph* here is Mathlib's `Quiver V` together with `Quiver.HasInvolutiveReverse V` (a directed
multigraph whose arrows are closed under an involutive reversal), exactly as in the Bass--Serre
development `Submission/Work/ORBassSerre`.  A *path* is `Quiver.Path`.

The *free groupoid* `F(Γ)` has the vertices of `Γ` as objects and, as morphisms `a ⟶ b`, the
*reduced* paths from `a` to `b`; composition is concatenation followed by cancellation of
backtracks (`pmul`).  This is the groupoid of Howie's paper: its vertex group at `v`
(`VertexGroup v`, the group of reduced *closed* paths at `v`, under `pmul`) is a free group, and
every free group arises in this way.

The cancellation theory (`Quiver.Path.DeleteBacktrack`, `Quiver.Path.ReducesTo`,
`Quiver.Path.IsReduced`, uniqueness of reduced forms) is developed in
`Submission/Work/ORBassSerre/Tree/Basic.lean` and
`Submission/Work/ORBassSerre/Path/Reduction/`; this file builds the groupoid multiplication on top
of it.
-/
import Mathlib
import Mathlib.Combinatorics.Quiver.Symmetric
import Submission.Work.ORBassSerre.Path.Reduction.reducesTo_of_reducesTo_of_isReduced
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced
import Submission.Work.ORBassSerre.Path.Reduction.reducesTo_nil_comp_reverse

set_option autoImplicit false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {a b c d : V}

/-- A chosen reduced form of a path. -/
noncomputable def red (p : Quiver.Path a b) : Quiver.Path a b :=
  (Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced p).choose

theorem reducesTo_red (p : Quiver.Path a b) : p.ReducesTo (red p) :=
  (Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced p).choose_spec.1

theorem isReduced_red (p : Quiver.Path a b) : (red p).IsReduced :=
  (Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced p).choose_spec.2

/-- The reduced form is the unique reduced reduct. -/
theorem red_eq_of_reducesTo_isReduced {p q : Quiver.Path a b} (h : p.ReducesTo q)
    (hq : q.IsReduced) : red p = q := by
  have h1 := Work.ORBassSerre.Path.Reduction.reducesTo_of_reducesTo_of_isReduced (isReduced_red p)
    (reducesTo_red p) h
  rcases Relation.ReflTransGen.cases_head h1 with h' | ⟨y, hy, _⟩
  · exact h'.symm
  · exact absurd hy (hq y)

theorem red_eq_self {p : Quiver.Path a b} (h : p.IsReduced) : red p = p :=
  red_eq_of_reducesTo_isReduced (Relation.ReflTransGen.refl) h

/-- **The multiplication of the free groupoid `F(Γ)`**: concatenate two paths and cancel all
backtracks.  On reduced paths this turns the set of reduced paths into a groupoid. -/
noncomputable def pmul (p : Quiver.Path a b) (q : Quiver.Path b c) : Quiver.Path a c :=
  red (p.comp q)

theorem comp_reducesTo_pmul (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (p.comp q).ReducesTo (pmul p q) :=
  reducesTo_red _

theorem pmul_isReduced (p : Quiver.Path a b) (q : Quiver.Path b c) : (pmul p q).IsReduced :=
  isReduced_red _

theorem pmul_eq_of_reducesTo {p : Quiver.Path a b} {q : Quiver.Path b c} {r : Quiver.Path a c}
    (h : (p.comp q).ReducesTo r) (hr : r.IsReduced) : pmul p q = r :=
  red_eq_of_reducesTo_isReduced h hr

/-- Deletion of backtracks is compatible with composing on the left. -/
theorem reducesTo_comp_left {p q : Quiver.Path b c} (h : p.ReducesTo q) (r : Quiver.Path a b) :
    (r.comp p).ReducesTo (r.comp q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (hstep.comp_left r)

theorem red_nil (a : V) : red (Quiver.Path.nil : Quiver.Path a a) = Quiver.Path.nil :=
  red_eq_self (Quiver.Path.IsReduced.nil a)

theorem pmul_assoc (p : Quiver.Path a b) (q : Quiver.Path b c) (r : Quiver.Path c d) :
    pmul (pmul p q) r = pmul p (pmul q r) := by
  have h1 : (p.comp (q.comp r)).ReducesTo (pmul (pmul p q) r) := by
    rw [← Quiver.Path.comp_assoc]
    exact (Quiver.Path.ReducesTo.comp_right (comp_reducesTo_pmul p q) r).trans
      (comp_reducesTo_pmul _ r)
  have h2 : (p.comp (q.comp r)).ReducesTo (pmul p (pmul q r)) :=
    (reducesTo_comp_left (comp_reducesTo_pmul q r) p).trans (comp_reducesTo_pmul p _)
  exact (red_eq_of_reducesTo_isReduced h1 (pmul_isReduced _ _)).symm.trans
    (red_eq_of_reducesTo_isReduced h2 (pmul_isReduced _ _))

theorem pmul_nil_left (p : Quiver.Path a b) : pmul (Quiver.Path.nil : Quiver.Path a a) p = red p := by
  rw [pmul, Quiver.Path.nil_comp]

theorem pmul_nil_right (p : Quiver.Path a b) : pmul p (Quiver.Path.nil : Quiver.Path b b) = red p := by
  rw [pmul, Quiver.Path.comp_nil]

/-- The reverse of a reduced path is reduced, and `p * p⁻¹` cancels completely. -/
theorem pmul_reverse (p : Quiver.Path a b) : pmul p p.reverse = Quiver.Path.nil := by
  have h := Work.ORBassSerre.Path.Reduction.reducesTo_nil_comp_reverse p
  show red (p.comp p.reverse) = Quiver.Path.nil
  exact red_eq_of_reducesTo_isReduced h (Quiver.Path.IsReduced.nil a)

theorem pmul_reverse_left (p : Quiver.Path a b) : pmul p.reverse p = Quiver.Path.nil := by
  have h : pmul p.reverse (p.reverse).reverse = Quiver.Path.nil := pmul_reverse p.reverse
  rwa [Quiver.Path.reverse_reverse] at h

/-- The *vertex group* of the free groupoid at `v`: the reduced closed paths at `v`. -/
def VertexGroup (v : V) : Type u := {p : Quiver.Path v v // p.IsReduced}

namespace VertexGroup

variable {v : V}

noncomputable instance (v : V) : Group (VertexGroup v) where
  mul p q := ⟨pmul p.1 q.1, pmul_isReduced _ _⟩
  one := ⟨Quiver.Path.nil, Quiver.Path.IsReduced.nil v⟩
  inv p := ⟨p.1.reverse, p.2.reverse⟩
  mul_assoc p q r := Subtype.ext (pmul_assoc p.1 q.1 r.1)
  one_mul p := Subtype.ext (show pmul (Quiver.Path.nil : Quiver.Path v v) p.1 = p.1 from by
    rw [pmul_nil_left, red_eq_self p.2])
  mul_one p := Subtype.ext (show pmul p.1 (Quiver.Path.nil : Quiver.Path v v) = p.1 from by
    rw [pmul_nil_right, red_eq_self p.2])
  inv_mul_cancel p := Subtype.ext (pmul_reverse_left p.1)

@[simp] theorem coe_mul (p q : VertexGroup v) : (p * q).1 = pmul p.1 q.1 := rfl
@[simp] theorem coe_one (v : V) : (1 : VertexGroup v).1 = Quiver.Path.nil := rfl
@[simp] theorem coe_inv (p : VertexGroup v) : (p⁻¹).1 = p.1.reverse := rfl

end VertexGroup

end Work.ORLocInd.Howie
