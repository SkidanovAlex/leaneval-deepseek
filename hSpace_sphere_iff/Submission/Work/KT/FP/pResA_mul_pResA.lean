import Mathlib
import Submission.Work.KT.FP.PencilDefs

namespace Work.KT.FP

/-- **Resolvent identity for the linear pencil `z ↦ z • A + B`.**  If `w ≠ z` and both `z • A + B`
and `w • A + B` are units, then for `F z = pResA A B z = (z • A + B)⁻¹ * A` we have
`F z * F w = (w - z)⁻¹ • (F z - F w)`.

Proof: `(w - z) • (pRes z * A * pRes w) = pRes z - pRes w`, obtained from
`pRes z * ((w • A + B) - (z • A + B)) * pRes w = pRes z * ((w - z) • A) * pRes w` together with
`pRes z * (w • A + B) = 1` and `(z • A + B) * pRes w = 1` (`Ring.mul_inverse_cancel`,
`Ring.inverse_mul_cancel`); then multiply on the right by `A` and use `w - z ≠ 0`. -/
theorem pResA_mul_pResA {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {z w : ℂ} (hzw : w ≠ z)
    (hz : IsUnit (z • A + B)) (hw : IsUnit (w • A + B)) :
    pResA A B z * pResA A B w = (w - z)⁻¹ • (pResA A B z - pResA A B w) := by
  -- `pRes` is a two-sided inverse of the pencil on the unit locus.
  have hzi : pRes A B z * (z • A + B) = 1 := Ring.inverse_mul_cancel _ hz
  have hwi : (w • A + B) * pRes A B w = 1 := Ring.mul_inverse_cancel _ hw
  -- the difference of the two pencil values is the scalar `w - z` times `A`.
  have hdiff : (w • A + B) - (z • A + B) = (w - z) • A := by
    rw [sub_smul]; abel
  have hv : pRes A B z * (w • A + B) * pRes A B w = pRes A B z := by
    rw [mul_assoc, hwi, mul_one]
  have hu : pRes A B z * (z • A + B) * pRes A B w = pRes A B w := by
    rw [hzi, one_mul]
  -- `(w - z) • (pRes z * A * pRes w) = pRes z - pRes w`.
  have h2 : pRes A B z * ((w - z) • A) * pRes A B w = pRes A B z - pRes A B w := by
    rw [← hdiff, mul_sub, sub_mul, hv, hu]
  have h3 : (w - z) • (pRes A B z * A * pRes A B w) = pRes A B z - pRes A B w := by
    rw [← h2, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw
  have h4 : pRes A B z * A * pRes A B w = (w - z)⁻¹ • (pRes A B z - pRes A B w) := by
    calc pRes A B z * A * pRes A B w
        = (w - z)⁻¹ • ((w - z) • (pRes A B z * A * pRes A B w)) := by
            rw [smul_smul, inv_mul_cancel₀ hwz, one_smul]
      _ = (w - z)⁻¹ • (pRes A B z - pRes A B w) := by rw [h3]
  -- multiply the identity on the right by `A` and unfold `pResA`.
  simp only [pResA]
  rw [← mul_assoc (pRes A B z * A) (pRes A B w) A, h4, Algebra.smul_mul_assoc, sub_mul]

end Work.KT.FP
