/-
# Restricting a labelling to the part of the graph outside both sides of a bridge

Let `P` be a graph presentation, `e` an arrow of `Γ` and `m` a relator containing an arrow of the
code of `e`.  Write

    `S = {y | y is joined to neither `e.left` nor `e.right` by a path of `Γ ∖ e`}`

(the complement of `InSide P e`) and let `restrictSide P e S L` be the labelling which agrees with
`L` on the arrows with both endpoints in `S` and avoiding the code of `e`, and vanishes elsewhere.

The point of this file is that `restrictSide P e S L` **vanishes on every relator of `P`**, provided
`L` vanishes on every relator other than `m`:

* every relator whose path contains an arrow of the code of `e` has all its vertices in a side
  (`inSide_arrow_of_code_eq_of_mem`), so the restricted labelling vanishes on all its arrows;
* every relator whose path avoids the code of `e` either has all its vertices in a side — again the
  restricted labelling vanishes — or has all its vertices in `S` and all its arrows avoiding the
  code of `e`, in which case the restricted labelling agrees with `L` on the whole path.

The second alternative is the one that requires an argument: if a vertex is *outside* both sides,
then so is every vertex of every path out of it, since an arrow either avoids the code of `e` — and
then preserves both `ReachRight` and `ReachLeft` — or *is* `e` or `e⁻¹` (`CodeSeparates`) — and then
both of its endpoints are in a side.  This is `not_inSide_all` below.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.C2.inSide_arrow_of_code_eq_of_mem

namespace Work.ORLocInd.Howie.C2

open Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Vertices outside both sides of the bridge -/

/-- If the source of an arrow lies outside both sides of the bridge, so does its target: an arrow
either avoids the code of `e` — and then the reverse arrow extends an avoiding path — or has the
code of `e` — and then it is `e` or `e⁻¹`, whose endpoints are both in a side. -/
theorem not_inSide_right_of_not_inSide_left (P : Presentation V) (hsep : P.CodeSeparates)
    (e : Quiver.Total V) {x y : V} (f : x ⟶ y) (h : ¬ InSide P e x) : ¬ InSide P e y := by
  intro hy
  by_cases hf : P.edgeOf (Quiver.Total.mk x y f) = P.edgeOf e
  · exact h (inSide_of_code_eq P hsep e _ hf).1
  · exact h (inSide_left_of_inSide_right P hsep e f hy)

/-- If the source of a path lies outside both sides of the bridge, then so does every endpoint of
every arrow of the path, and so does the target of the path. -/
theorem not_inSide_all (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V) :
    ∀ {x y : V} (q : Quiver.Path x y), ¬ InSide P e x →
      (∀ g ∈ q.arrowList, ¬ InSide P e g.left ∧ ¬ InSide P e g.right) ∧ ¬ InSide P e y := by
  intro x y q
  induction q with
  | nil => intro h; exact ⟨fun g hg => by simp at hg, h⟩
  | cons p f ih =>
      intro h
      obtain ⟨hp, hz⟩ := ih h
      have hy : ¬ InSide P e _ := not_inSide_right_of_not_inSide_left P hsep e f hz
      refine ⟨?_, hy⟩
      intro g hg
      rw [Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hp g hg
      · rw [List.mem_singleton] at hg
        subst hg
        exact ⟨hz, hy⟩

/-! ## The main theorem -/

theorem restrictSide_outside_vanishes {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V)
    (hsep : P.CodeSeparates) (m : P.ι) (e : Quiver.Total V)
    (he : ∃ g ∈ (P.path m).arrowList, P.edgeOf g = P.edgeOf e)
    (L : Work.ORLocInd.Howie.Labelling V)
    (hvan : ∀ i : P.ι, i ≠ m →
      Work.ORLocInd.Howie.pathSum L.toFun (P.path i) = 0) :
    Work.ORLocInd.Howie.VanishOnRelators
      (Work.ORLocInd.Howie.restrictSide P e
        (fun y => ¬ Work.ORLocInd.Howie.ReachRight P e y ∧
          ¬ Work.ORLocInd.Howie.ReachLeft P e y) L) P := by
  intro i
  by_cases hmem : ∃ g ∈ (P.path i).arrowList, P.edgeOf g = P.edgeOf e
  · -- The path contains an arrow of the code of `e`: all its vertices lie in a side.
    obtain ⟨g₀, hg₀, hcg⟩ := hmem
    have hAll := inSide_arrow_of_code_eq_of_mem P hsep e (P.path i) hg₀ hcg
    exact pathSum_restrictSide_eq_zero P e
      (fun y => ¬ ReachRight P e y ∧ ¬ ReachLeft P e y) L (P.path i)
      (fun g hg hc => (hAll g hg).1.elim (fun h1 => hc.1.1 h1) (fun h2 => hc.1.2 h2))
  · -- The path avoids the code of `e`, so `i ≠ m`.
    have him : i ≠ m := fun him => hmem (by subst him; exact he)
    by_cases hbase : InSide P e (P.base i)
    · -- The base point lies in a side: all the vertices lie in that side.
      obtain ⟨hAll, _⟩ := allInSide_of_inSide_left P hsep e (P.path i) hbase
      exact pathSum_restrictSide_eq_zero P e
        (fun y => ¬ ReachRight P e y ∧ ¬ ReachLeft P e y) L (P.path i)
        (fun g hg hc => (hAll g hg).1.elim (fun h1 => hc.1.1 h1) (fun h2 => hc.1.2 h2))
    · -- The base point lies outside both sides: the whole path does, and every arrow of it avoids
      -- the code of `e`, so the restricted labelling agrees with `L` on it.
      obtain ⟨hAll, _⟩ := not_inSide_all P hsep e (P.path i) hbase
      rw [pathSum_restrictSide P e
        (fun y => ¬ ReachRight P e y ∧ ¬ ReachLeft P e y) L (P.path i)
        (fun g hg => ⟨⟨fun h1 => (hAll g hg).1 (Or.inl h1),
                        fun h2 => (hAll g hg).1 (Or.inr h2)⟩,
                      ⟨fun h1 => (hAll g hg).2 (Or.inl h1),
                        fun h2 => (hAll g hg).2 (Or.inr h2)⟩,
                      fun hc => (hAll g hg).1 (inSide_of_code_eq P hsep e g hc).1⟩)]
      exact hvan i him

end Work.ORLocInd.Howie.C2
