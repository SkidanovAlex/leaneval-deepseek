/-
# `pathSum` of a side-restricted labelling on an erased path based outside the bridge

Let `P` be a graph presentation, `e` an arrow of `Γ`, and `K` a `Keep` predicate whose arrows all
avoid the code of `e`.  Let `β` be a closed path of `DelV K` based at a vertex `x` which lies in
*neither* side of the bridge `e` (`¬ ReachRight P e x` and `¬ ReachLeft P e x`).

Then the labelling `L`, restricted to the arrows with both endpoints outside the two sides of the
bridge (and avoiding the code of `e`), has the same `pathSum` on the erasure `DelV.erasePath K x β`
as `L` itself.

The mathematical content is that a path of `Γ ∖ e` starting outside the two sides never enters
either side: reachability from `e.right` (or `e.left`) is transported backwards along an arrow of
`Γ ∖ e` (`reachOut_cons`), so it is constant along every path avoiding the code of `e`
(`outside_path`).  Hence every arrow of the erased path has both endpoints outside the sides and
avoids the code of `e`, i.e. the erased path is a `SideLoop`, and `pathSum_restrictSide` applies.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge

set_option linter.unusedVariables false
set_option linter.ambiguousOpen false
set_option backward.isDefEq.respectTransparency false

namespace Work.ORLocInd.Howie.C2

open Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- If both endpoints of a single arrow `f : x ⟶ y` avoiding the code of `e` lie outside the two
sides of the bridge at the source `x`, then they do so at the target `y` as well.

Indeed, a path of `Γ ∖ e` from `e.right` (or `e.left`) to `y` can be extended by the reverse of `f`
to a path from `e.right` (or `e.left`) to `x`. -/
theorem reachOut_cons (P : Presentation V) (e : Quiver.Total V) {x y : V} (f : x ⟶ y)
    (hf : P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e)
    (hx : ¬ ReachRight P e x ∧ ¬ ReachLeft P e x) :
    ¬ ReachRight P e y ∧ ¬ ReachLeft P e y := by
  constructor
  · rintro ⟨r, hr⟩
    exact hx.1 ⟨r.cons (Quiver.reverse f),
      (avoids_cons_iff P e r (Quiver.reverse f)).mpr
        ⟨hr, (edgeOf_reverse_mk_ne P e f).mpr hf⟩⟩
  · rintro ⟨r, hr⟩
    exact hx.2 ⟨r.cons (Quiver.reverse f),
      (avoids_cons_iff P e r (Quiver.reverse f)).mpr
        ⟨hr, (edgeOf_reverse_mk_ne P e f).mpr hf⟩⟩

/-- If a path `q : a ⟶ b` avoids the code of `e` and its source `a` lies outside both sides of the
bridge, then so do both endpoints of *every* arrow of `q` and the target `b`. -/
theorem outside_path (P : Presentation V) (e : Quiver.Total V) :
    ∀ {a b : V} (q : Quiver.Path a b), Avoids P e q →
      (¬ ReachRight P e a ∧ ¬ ReachLeft P e a) →
      (∀ g ∈ q.arrowList,
        (¬ ReachRight P e g.left ∧ ¬ ReachLeft P e g.left) ∧
        (¬ ReachRight P e g.right ∧ ¬ ReachLeft P e g.right)) ∧
      (¬ ReachRight P e b ∧ ¬ ReachLeft P e b) := by
  intro a b q
  induction q with
  | nil => intro _ hout; exact ⟨by intro g hg; simp at hg, hout⟩
  | cons p f ih =>
      intro h hout
      obtain ⟨hp, hf⟩ := (avoids_cons_iff P e p f).mp h
      obtain ⟨har, hb⟩ := ih hp hout
      have hc := reachOut_cons P e f hf hb
      refine ⟨?_, hc⟩
      rw [Quiver.Path.arrowList_cons]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact har g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        exact ⟨hb, hc⟩

/-- The erasure of a path of `DelV K` whose arrows all avoid the code of `e` is a path that avoids
the code of `e`. -/
theorem avoids_erasePath (P : Presentation V) (e : Quiver.Total V) (K : Keep V)
    (hK : ∀ g : Quiver.Total V, K.pred g → P.edgeOf g ≠ P.edgeOf e) :
    ∀ {a b : V} (β : dpath K a b), Avoids P e (DelV.erasePath K a β) := by
  intro a b β
  induction β with
  | nil =>
      show Avoids P e (Quiver.Path.nil : Quiver.Path a a)
      exact avoids_nil P e
  | cons β f ih =>
      rw [DelV.erasePath_cons]
      exact (avoids_cons_iff P e (DelV.erasePath K a β) f.1).mpr ⟨ih, hK _ f.2⟩

theorem pathSum_restrictSide_erasePath_of_outside {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V)
    (K : Work.ORLocInd.Howie.Keep V)
    (hK : ∀ g : Quiver.Total V, K.pred g → P.edgeOf g ≠ P.edgeOf e)
    (L : Work.ORLocInd.Howie.Labelling V) {x : V}
    (hx : ¬ Work.ORLocInd.Howie.ReachRight P e x ∧
      ¬ Work.ORLocInd.Howie.ReachLeft P e x)
    (β : Work.ORLocInd.Howie.dpath K x x) :
    Work.ORLocInd.Howie.pathSum
        (Work.ORLocInd.Howie.restrictSide P e
          (fun y => ¬ Work.ORLocInd.Howie.ReachRight P e y ∧
            ¬ Work.ORLocInd.Howie.ReachLeft P e y) L).toFun
        (Work.ORLocInd.Howie.DelV.erasePath K x β) =
      Work.ORLocInd.Howie.pathSum L.toFun
        (Work.ORLocInd.Howie.DelV.erasePath K x β) := by
  refine pathSum_restrictSide P e
    (fun y => ¬ Work.ORLocInd.Howie.ReachRight P e y ∧
      ¬ Work.ORLocInd.Howie.ReachLeft P e y) L
    (Work.ORLocInd.Howie.DelV.erasePath K x β) ?_
  have hav := avoids_erasePath P e K hK β
  have hout := (outside_path P e (Work.ORLocInd.Howie.DelV.erasePath K x β) hav hx).1
  intro g hg
  obtain ⟨hgl, hgr⟩ := hout g hg
  exact ⟨hgl, hgr, hav g hg⟩

end Work.ORLocInd.Howie.C2
