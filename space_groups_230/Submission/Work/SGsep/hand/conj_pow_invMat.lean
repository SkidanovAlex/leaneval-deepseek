import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep.hand

open Work.SG

/-- Conjugation by a unimodular integer matrix `U` preserves powers: `(U A U⁻¹)^m = U A^m U⁻¹`
for every `m`, and hence `(U A U⁻¹)^m = 1 ↔ A^m = 1`.  Here `U⁻¹` is `invMat U`,
the integer matrix `(det U) • adjugate U`; `IsUnit U.det` forces `det U = ±1`, so that
`U * invMat U = 1` and `invMat U * U = 1` (lemmas `mul_invMat`, `invMat_mul` of
`Submission.Work.SG.SGsepDefs`). -/
theorem conj_pow_invMat {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    (∀ m : ℕ, (U * A * invMat U) ^ m = U * A ^ m * invMat U) ∧
      (∀ m : ℕ, (U * A * invMat U) ^ m = 1 ↔ A ^ m = 1) := by
  have hvu : invMat U * U = 1 := invMat_mul hU
  have huv : U * invMat U = 1 := mul_invMat hU
  -- `U` and `invMat U` are mutually inverse, so `U * A * invMat U` is the conjugate of `A`
  -- by the unit `U`, i.e. `U` and `U * A * invMat U` are semiconjugate.
  have hsem : SemiconjBy U A (U * A * invMat U) := by
    unfold SemiconjBy
    simp only [mul_assoc, hvu, mul_one]
  have hconj : IsConj A (U * A * invMat U) :=
    ⟨⟨U, invMat U, huv, hvu⟩, hsem⟩
  have hpow : ∀ m : ℕ, (U * A * invMat U) ^ m = U * A ^ m * invMat U := by
    intro m
    have h := (hsem.pow_right m).eq
    rw [h]
    simp only [mul_assoc, huv, mul_one]
  refine ⟨hpow, fun m => ?_⟩
  -- `IsConj` is insensitive to multiplication by `1`, so it transports `A ^ m = 1`.
  have hc : IsConj (A ^ m) ((U * A * invMat U) ^ m) := hconj.pow m
  constructor
  · intro h
    exact isConj_one_left.mp (hc.trans (isConj_one_left.mpr h))
  · intro h
    exact isConj_one_left.mp (hc.symm.trans (isConj_one_left.mpr h))

end Work.SGsep.hand
