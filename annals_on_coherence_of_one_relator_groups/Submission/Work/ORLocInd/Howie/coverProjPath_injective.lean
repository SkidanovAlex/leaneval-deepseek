/-
# The projection of the cyclic cover is injective on paths

The cyclic cover `Γ̃` of a `ℤ`-labelled graph `Γ`
(`Submission.Work.ORLocInd.Howie.CoverGraph`) has vertex set `V × ℤ`, and
`coverProjPath L p` (`Submission.Work.ORLocInd.Howie.CoverPresentation`) projects a path of `Γ̃`
to a path of `Γ`.

Because the level of the target of a path of the cover is determined by the start vertex and the
projection (`coverProjPath_level` below), and because the projection of an arrow with fixed
endpoints is injective (`coverProjArrow_inj_fixed`), the covering map is injective on paths:

**`coverProjPath_injective`** : two paths of the cover with the same source and target which
project to the same path of the base graph are equal.

This is the "abstract nonsense" statement behind the fact that a path of the base graph has at
most one lift starting at a given vertex: it is used to transfer path-theoretic properties of the
base graph to the cover.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie

/-- Casting a path along equalities of its endpoints does not change the sum of the labels of its
arrows. -/
theorem pathSum_cast' {V : Type*} [Quiver V] (θ : Quiver.Total V → ℤ) {a b a' b' : V}
    (hu : a = a') (hv : b = b') (p : Quiver.Path a b) :
    pathSum θ (p.cast hu hv) = pathSum θ p := by
  cases hu
  cases hv
  rw [Quiver.Path.cast_rfl_rfl]

/-- **The end vertex of a path of the cyclic cover is determined by the start vertex and the
projection.**  The level of the target is the level of the source plus the sum of the labels of the
projected path. -/
theorem coverProjPath_level {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Labelling V) {p q : CoverVertex L} (P : Quiver.Path p q) :
    q.level = p.level + pathSum L.toFun (coverProjPath L p P) := by
  induction P with
  | nil => simp [coverProjPath_nil, pathSum_nil]
  | cons P e ih =>
      rw [coverProjPath_cons, pathSum_cons, ← add_assoc, ← ih, coverProjArrow_total]
      exact e.2.2.2

/-- **The projection of an arrow of the cover is injective** on the arrows with fixed endpoints
(`coverProjArrow_total` identifies the arrow with the total arrow of its projection). -/
theorem coverProjArrow_inj_fixed {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Labelling V) {p q : CoverVertex L} :
    Function.Injective (coverProjArrow (L := L) (p := p) (q := q)) := by
  intro e e' h
  apply Subtype.ext
  rw [← coverProjArrow_total L e, ← coverProjArrow_total L e', h]

theorem coverProjPath_injective {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) (p : Work.ORLocInd.Howie.CoverVertex L)
    (q : Work.ORLocInd.Howie.CoverVertex L) (P Q : Quiver.Path p q)
    (h : Work.ORLocInd.Howie.coverProjPath L p P = Work.ORLocInd.Howie.coverProjPath L p Q) :
    P = Q := by
  revert Q
  induction P with
  | nil =>
      intro Q h
      cases Q with
      | nil => rfl
      | cons Q e =>
          rw [coverProjPath_nil, coverProjPath_cons] at h
          exact absurd h.symm (Quiver.Path.cons_ne_nil _ _)
  | cons P e ih =>
      intro Q h
      cases Q with
      | nil =>
          rw [coverProjPath_nil, coverProjPath_cons] at h
          exact absurd h (Quiver.Path.cons_ne_nil _ _)
      | cons Q e' =>
          rw [coverProjPath_cons, coverProjPath_cons] at h
          obtain ⟨hvv, hp, he⟩ := Quiver.Path.cons.inj h
          rename_i m _ m'
          -- the two middle vertices of the two paths have the same projection
          have hsum : pathSum L.toFun (coverProjPath L p P) =
              pathSum L.toFun (coverProjPath L p Q) := by
            have hcast : (coverProjPath L p P).cast (rfl : p.vert = p.vert) hvv =
                coverProjPath L p Q :=
              (Quiver.Path.cast_eq_iff_heq (rfl : p.vert = p.vert) hvv _ _).2 hp
            rw [← pathSum_cast' L.toFun rfl hvv (coverProjPath L p P)]
            exact congrArg (pathSum L.toFun) hcast
          -- hence they are equal, and we may transport `Q` to `P`'s middle vertex
          have hm : m = m' := by
            refine CoverVertex.ext hvv ?_
            rw [coverProjPath_level L P, coverProjPath_level L Q, hsum]
          subst hm
          have hPQ : P = Q := ih Q (eq_of_heq hp)
          have hee : e = e' := coverProjArrow_inj_fixed L (eq_of_heq he)
          rw [hPQ, hee]

end Work.ORLocInd.Howie
