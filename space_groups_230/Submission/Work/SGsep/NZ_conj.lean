import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-- Conjugation by `U` (inverse `invMat U`, given `IsUnit U.det`) is an endomorphism of the
monoid of integer matrices; hence it commutes with powers. -/
theorem conjEndo_pow {U : IMat} (hU : IsUnit U.det) (A : IMat) (n : ℕ) :
    (U * A * invMat U)^n = U * A^n * invMat U := by
  let φ : IMat →* IMat :=
    { toFun := fun B => U * B * invMat U
      map_one' := by simp [mul_invMat hU]
      map_mul' := by
        intro x y
        simp only [mul_assoc]
        rw [← mul_assoc (invMat U) U (y * invMat U), invMat_mul hU, one_mul] }
  have h : φ A = U * A * invMat U := rfl
  have := map_pow φ A n
  rw [h] at this
  exact this.symm

/-- Conjugation by a unimodular integer matrix preserves the multiplicative order of a matrix. -/
theorem mOrd_conj {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    mOrd (U * A * invMat U) = mOrd A := by
  have hpow := conjEndo_pow hU A
  have hiff : ∀ m, 1 ≤ m → (A^m = 1 ↔ (U * A * invMat U)^m = 1) := by
    intro m _hm
    constructor
    · intro h
      rw [hpow m, h]
      simp [mul_invMat hU]
    · intro h
      have key : invMat U * (U * A * invMat U)^m * U = A^m := by
        rw [hpow m]
        simp only [mul_assoc, invMat_mul hU, mul_one]
        rw [← mul_assoc, invMat_mul hU, one_mul]
      rw [← key, h]
      simp [invMat_mul hU]
  by_cases hA : ∃ m, 1 ≤ m ∧ A^m = 1
  · obtain ⟨h1, h2⟩ := mOrd_spec hA
    have hB : ∃ m, 1 ≤ m ∧ (U * A * invMat U)^m = 1 :=
      ⟨mOrd A, h1, (hiff (mOrd A) h1).mp h2⟩
    obtain ⟨g1, g2⟩ := mOrd_spec hB
    exact le_antisymm (mOrd_min hB h1 ((hiff _ h1).mp h2))
      (mOrd_min hA g1 ((hiff _ g1).mpr g2))
  · have hB : ¬ ∃ m, 1 ≤ m ∧ (U * A * invMat U)^m = 1 := by
      rintro ⟨m, hm, hBm⟩
      exact hA ⟨m, hm, (hiff m hm).mpr hBm⟩
    rw [mOrd, mOrd, dite_eq_right hA, dite_eq_right hB]

/-- `N_{U A U⁻¹} = U N_A U⁻¹` for unimodular `U`, where `N_A = ∑_{i < ord A} A^i`.  Prove
`(U A U⁻¹)^n = U A^n U⁻¹`, `mOrd (U A U⁻¹) = mOrd A`, then push the finite sum through. -/
theorem NZ_conj {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    NZ (U * A * invMat U) = U * NZ A * invMat U := by
  rw [NZ, NZ, mOrd_conj hU A]
  unfold Nsum
  have hsum : ∑ i ∈ Finset.range (mOrd A), (U * A * invMat U)^i
      = ∑ i ∈ Finset.range (mOrd A), U * A^i * invMat U := by
    apply Finset.sum_congr rfl
    intro i _
    rw [conjEndo_pow hU A i]
  rw [hsum, ← Finset.sum_mul, ← Finset.mul_sum]

end Work.SGsep
