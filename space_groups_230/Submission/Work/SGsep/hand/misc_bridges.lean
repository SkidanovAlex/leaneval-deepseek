import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-- Two small bridges: `invMat` is the ring inverse of a unimodular integer matrix, and congruence
modulo a positive `m` makes `Int.emod` agree. -/
theorem misc_bridges :
    (∀ {U : IMat}, IsUnit U.det → invMat U = U⁻¹) ∧
    (∀ {a b : Int} {m : Nat}, 0 < m → (m : Int) ∣ b - a → a % (m : Int) = b % (m : Int)) := by
  constructor
  · intro U hU
    calc invMat U = 1 * invMat U := (one_mul _).symm
      _ = (U⁻¹ * U) * invMat U := by rw [Matrix.nonsing_inv_mul U hU]
      _ = U⁻¹ * (U * invMat U) := by rw [Matrix.mul_assoc]
      _ = U⁻¹ * 1 := by rw [mul_invMat hU]
      _ = U⁻¹ := mul_one _
  · intro a b m _ h
    exact Int.modEq_iff_dvd.mpr h

end Work.SGsep.hand
