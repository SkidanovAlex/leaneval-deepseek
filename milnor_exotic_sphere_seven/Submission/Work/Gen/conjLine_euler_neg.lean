import Mathlib
import Submission.Work.Gen.ConjLine
import Submission.Work.Gen.ConjIso
import Submission.Work.Gen.eulerClass_neg_of_realIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency true

open Work.Projective Work.TangentClasses Work.Thom

namespace Work.Gen

/-- **The fibrewise map of `conjIso` has determinant `-1`**, so `conjIso` is orientation reversing. -/
theorem conjIso_det_neg (n : ℕ) (b : CP n) :
    LinearMap.det ((conjIso n).hom b) < 0 := by
  have h1 : (conjIso n).hom b = conjLM := by
    ext v
    exact conjIso_hom_fiber n b v
  rw [h1]
  change LinearMap.det (conjLM : EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1)) < 0
  rw [det_conjLM]
  norm_num

theorem conjLine_euler_neg (n : ℕ) :
    (Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) (Work.Gen.conjLine n)).eulerClass
      = - (Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0))
          (Work.Gen.tautLine n)).eulerClass := by
  have h := Work.Gen.eulerClass_neg_of_realIso (m := 1) (le_refl 1) (Work.Gen.conjLine n)
    (Work.Gen.tautLine n) (Work.Gen.conjIso n) (fun b => conjIso_det_neg n b)
  have h' : - (Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0))
        (Work.Gen.tautLine n)).eulerClass
      = (Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0))
        (Work.Gen.conjLine n)).eulerClass := by
    rw [h, neg_neg]
  rw [← h']

end Work.Gen
