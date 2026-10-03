import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.Case2Labelling
import Submission.Work.ORLocInd.Howie.exists_comp_of_mem_arrowList

namespace Work.ORLocInd.Howie.C2

/-! ## Reachability in `Γ ∖ e` is constant along a path avoiding `e`

The labelling `keepRight P e` keeps an arrow `g` exactly when `g` avoids the code of `e` and
neither endpoint of `g` lies in the `ReachRight` side of the bridge.  Since every relator `≠ m` of
`P` avoids the code of `e` (`hbrl`), the only thing to decide for such a relator is whether its
base vertex lies in the `ReachRight` side.  The three lemmas below record that this *is* a decision
that is constant along the whole relator: an arrow avoiding the code of `e` can be traversed in both
directions, so it joins vertices that are simultaneously `ReachRight` or simultaneously not. -/

/-- One step of the constancy: an arrow avoiding the code of `e` joins two vertices that are
`ReachRight` simultaneously. -/
theorem reachRight_step {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V) {x y : V} (f : x ⟶ y)
    (hf : P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e) :
    Work.ORLocInd.Howie.ReachRight P e x ↔ Work.ORLocInd.Howie.ReachRight P e y := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.cons f, (Work.ORLocInd.Howie.avoids_cons_iff P e q f).mpr ⟨hq, hf⟩⟩
  · rintro ⟨q, hq⟩
    exact ⟨q.cons (Quiver.reverse f),
      (Work.ORLocInd.Howie.avoids_cons_iff P e q (Quiver.reverse f)).mpr ⟨hq, by
        show P.edgeOf (Quiver.totalReverse (Quiver.Total.mk x y f)) ≠ P.edgeOf e
        rw [P.edgeOf_reverse]; exact hf⟩⟩

/-- `ReachRight` is constant along a path avoiding the code of `e`. -/
theorem reachRight_iff_of_avoids {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V) {x y : V} (q : Quiver.Path x y)
    (hq : Work.ORLocInd.Howie.Avoids P e q) :
    Work.ORLocInd.Howie.ReachRight P e x ↔ Work.ORLocInd.Howie.ReachRight P e y := by
  induction q with
  | nil => exact Iff.rfl
  | cons p f ih =>
      obtain ⟨hp, hf⟩ := (Work.ORLocInd.Howie.avoids_cons_iff P e p f).mp hq
      exact (ih hp).trans (reachRight_step P e f hf)

/-- `ReachRight` is constant along a path avoiding the code of `e`, in the form needed below:
*both* endpoints of every arrow of the path are `ReachRight` exactly when the start of the path
is. -/
theorem reachRight_mem_arrowList {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V) {x y : V} (q : Quiver.Path x y)
    (hq : Work.ORLocInd.Howie.Avoids P e q) :
    ∀ g ∈ q.arrowList, (Work.ORLocInd.Howie.ReachRight P e g.left ↔
        Work.ORLocInd.Howie.ReachRight P e x) ∧
      (Work.ORLocInd.Howie.ReachRight P e g.right ↔ Work.ORLocInd.Howie.ReachRight P e x) := by
  induction q with
  | nil => intro g hg; simp at hg
  | cons p f ih =>
      intro g hg
      obtain ⟨hp, hf⟩ := (Work.ORLocInd.Howie.avoids_cons_iff P e p f).mp hq
      rw [Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ih hp g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        exact ⟨(reachRight_iff_of_avoids P e p hp).symm,
          (reachRight_step P e f hf).symm.trans (reachRight_iff_of_avoids P e p hp).symm⟩

/-! ## A labelling extended by zero vanishes on paths made of unkept arrows -/

/-- If every arrow of a path is deleted by `K`, then the labelling extended by zero vanishes on
that path. -/
theorem pathSum_extendLabelling_eq_zero_of_not_pred {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (K : Work.ORLocInd.Howie.Keep V)
    (L : Work.ORLocInd.Howie.Labelling (Work.ORLocInd.Howie.DelV K)) {a b : V}
    (p : Quiver.Path a b) (h : ∀ g ∈ p.arrowList, ¬ K.pred g) :
    Work.ORLocInd.Howie.pathSum (Work.ORLocInd.Howie.extendLabelling K L).toFun p = 0 := by
  induction p with
  | nil => exact Work.ORLocInd.Howie.pathSum_nil _ _
  | cons p f ih =>
      have h' : ∀ g ∈ p.arrowList, ¬ K.pred g := fun g hg => h g (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
      have hf : ¬ K.pred (Quiver.Total.mk _ _ f) := h _ (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
      rw [Work.ORLocInd.Howie.pathSum_cons, ih h',
        Work.ORLocInd.Howie.extendLabelling_apply_not _ _ _ hf, add_zero]

/-! ## The main lemma -/

/-- **Howie's Case 2, bridge case: the extension of a labelling of the bridge subpresentation
vanishes on all relators except the bridge relator `m`.**

Let `P` be a presentation, `e` an arrow and `m` a relator such that every other relator of `P`
avoids the code of `e` (`hbrl`).  Let `L'` be a labelling of the subgraph `keepRight P e` (the
arrows of `Γ ∖ e` with both endpoints outside the `ReachRight` side of the bridge) which vanishes
on the relators of the bridge subpresentation (those relators `≠ m` based outside the `ReachRight`
side).

Then the labelling of `Γ` obtained by extending `L'` by `0` on the deleted arrows vanishes on
every relator `P.path i` with `i ≠ m`.  Indeed, since `P.path i` avoids the code of `e`, the
`ReachRight` side either meets the whole path or none of it (`reachRight_mem_arrowList`); in the
first case every arrow of the path is deleted and the extension is zero on it, and in the second
case every arrow of the path is kept and `pathSum_extendLabelling` reduces the claim to the
hypothesis `hL'` on the corresponding relator of the subpresentation. -/
theorem extendLabelling_vanishes_of_bridge {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V)
    (m : P.ι) (e : Quiver.Total V)
    (hbrl : ∀ i : P.ι, i ≠ m → Work.ORLocInd.Howie.Avoids P e (P.path i))
    (L' : Work.ORLocInd.Howie.Labelling
      (Work.ORLocInd.Howie.DelV (Work.ORLocInd.Howie.keepRight P e)))
    (hL' : Work.ORLocInd.Howie.VanishOnRelators L'
      (P.deleteSub (Work.ORLocInd.Howie.keepRight P e)
        (Work.ORLocInd.Howie.bridgeRelator P m e))) :
    ∀ i : P.ι, i ≠ m →
      Work.ORLocInd.Howie.pathSum
        (Work.ORLocInd.Howie.extendLabelling (Work.ORLocInd.Howie.keepRight P e) L').toFun
        (P.path i) = 0 := by
  intro i hi
  have hav := hbrl i hi
  by_cases hS : Work.ORLocInd.Howie.ReachRight P e (P.base i)
  · -- the base vertex is `ReachRight`, hence so is every endpoint of every arrow of the relator,
    -- and all the arrows of the relator are deleted
    apply pathSum_extendLabelling_eq_zero_of_not_pred
    intro g hg
    exact fun hk =>
      hk.2 (Or.inl ((reachRight_mem_arrowList P e (P.path i) hav g hg).1.mpr hS))
  · -- no vertex of the relator is `ReachRight`, hence all its arrows are kept
    have hpred : ∀ g ∈ (P.path i).arrowList, (Work.ORLocInd.Howie.keepRight P e).pred g := by
      intro g hg
      refine ⟨hav g hg, ?_⟩
      rintro (h | h)
      · exact hS ((reachRight_mem_arrowList P e (P.path i) hav g hg).1.mp h)
      · exact hS ((reachRight_mem_arrowList P e (P.path i) hav g hg).2.mp h)
    have hrel := hL' ⟨i, ⟨⟨hi, hS⟩, hpred⟩⟩
    rw [Work.ORLocInd.Howie.pathSum_extendLabelling
      (Work.ORLocInd.Howie.keepRight P e) L' (P.path i) hpred]
    exact hrel

end Work.ORLocInd.Howie.C2
