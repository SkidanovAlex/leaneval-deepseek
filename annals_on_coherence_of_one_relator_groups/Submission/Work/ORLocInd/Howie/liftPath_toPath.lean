import Mathlib
import Submission.Work.ORLocInd.Howie.LiftPathComp

open Quiver

namespace Work.ORLocInd.Howie

/-- The lift of a single arrow (viewed as a path of length one) is the path of length one
consisting of the lifted arrow, re-indexed by the equality of the endpoint levels. -/
theorem liftPath_toPath {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) {a b : V} (e : a ⟶ b) (n : ℤ) :
    Work.ORLocInd.Howie.liftPath L e.toPath n =
      Quiver.Path.cast rfl
        (Work.ORLocInd.Howie.coverVertex_level_eq L (by rw [Work.ORLocInd.Howie.pathSum_toPath]))
        ((Work.ORLocInd.Howie.coverLiftArrow L e n).toPath) := by
  -- The two endpoint (level) equalities that occur below.
  have hm : (⟨a, n + pathSum L.toFun (Quiver.Path.nil : Quiver.Path a a)⟩ : CoverVertex L)
      = ⟨a, n⟩ :=
    coverVertex_level_eq L (by rw [pathSum_nil, add_zero])
  have hv : (⟨b, (n + pathSum L.toFun (Quiver.Path.nil : Quiver.Path a a))
        + L.toFun (Quiver.Total.mk a b e)⟩ : CoverVertex L)
      = ⟨b, n + L.toFun (Quiver.Total.mk a b e)⟩ :=
    coverVertex_level_eq L (by rw [pathSum_nil, add_zero])
  -- Reduce the goal to a heterogeneous equality of paths.
  refine (Quiver.Path.eq_cast_iff_heq (rfl : (⟨a, n⟩ : CoverVertex L) = ⟨a, n⟩) _ _ _).2 ?_
  simp only [Quiver.Hom.toPath]
  rw [liftPath_cons_cast']
  refine (Quiver.Path.cast_heq _ _ _).trans ?_
  -- Now compare the lifts of the empty path and of the single arrow.
  refine (Quiver.Path.cast_eq_iff_heq (rfl : (⟨a, n⟩ : CoverVertex L) = ⟨a, n⟩) hv _ _).1 ?_
  rw [Quiver.Path.cast_cons, Quiver.Path.cast_rfl_rfl]
  rw [Quiver.Path.cons.injEq]
  exact ⟨hm, by rw [liftPath_nil_cast']; exact Quiver.Path.cast_heq _ _ _,
    (Quiver.Hom.cast_heq (rfl : (⟨a, n + pathSum L.toFun (Quiver.Path.nil : Quiver.Path a a)⟩
        : CoverVertex L) = ⟨a, n + pathSum L.toFun (Quiver.Path.nil : Quiver.Path a a)⟩) hv _).trans
      (heq_coverLiftArrow L e hm)⟩

end Work.ORLocInd.Howie
