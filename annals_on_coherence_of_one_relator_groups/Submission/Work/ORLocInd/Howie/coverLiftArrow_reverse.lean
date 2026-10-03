import Mathlib
import Submission.Work.ORLocInd.Howie.LiftPathComp

namespace Work.ORLocInd.Howie

theorem coverLiftArrow_reverse {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) {b c : V} (e : b ⟶ c) (m : ℤ) :
    Quiver.reverse (Work.ORLocInd.Howie.coverLiftArrow L e m) =
      (Work.ORLocInd.Howie.coverLiftArrow L (Quiver.reverse e) (m + L.toFun (Quiver.Total.mk b c e))).cast rfl
        (Work.ORLocInd.Howie.coverVertex_level_eq L (by
          have h := L.balanced (Quiver.Total.mk b c e)
          rw [Quiver.totalReverse_mk] at h
          rw [h]; ring)) := by
  rw [Quiver.Hom.eq_cast_iff_heq]
  refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
  · intro x
    have hX : (m + L.toFun (Quiver.Total.mk b c e)) +
        L.toFun (Quiver.Total.mk c b (Quiver.reverse e)) = m := by
      have h := L.balanced (Quiver.Total.mk b c e)
      rw [Quiver.totalReverse_mk] at h
      rw [h]; ring
    simp only [hX]
  · rfl

end Work.ORLocInd.Howie
