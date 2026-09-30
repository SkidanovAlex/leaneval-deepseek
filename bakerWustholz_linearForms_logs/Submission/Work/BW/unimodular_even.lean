import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If every coordinate of `y` is even, then every coordinate of `A.mulVec y` is even,
for any integral matrix `A`. -/
private lemma two_dvd_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ)
    (hy : ∀ i, (2 : ℤ) ∣ y i) : ∀ i, (2 : ℤ) ∣ (A.mulVec y) i := by
  intro i
  change (2 : ℤ) ∣ ∑ j, A i j * y j
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right (hy j) (A i j)

/-- An integral matrix with unit determinant is invertible modulo `2`: if every coordinate of `U.mulVec x` is even, then every coordinate of `x` is even. -/
theorem unimodular_even {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    (x : Fin n → ℤ) (hx : ∀ i, (2 : ℤ) ∣ (U.mulVec x) i) : ∀ i, (2 : ℤ) ∣ x i := by
  intro i
  -- A unit of `ℤ` is `±1`.
  have hdet : U.det = 1 ∨ U.det = -1 := Int.isUnit_iff.mp hU
  -- Cramer's rule, in vector form: `adjugate U *ᵥ (U *ᵥ x) = det U • x`.
  have key : U.adjugate.mulVec (U.mulVec x) = U.det • x := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.mulVec x) (Matrix.adjugate_mul U)
    simpa [Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using h
  -- The left-hand side is even entrywise, by the auxiliary lemma.
  have h2 : (2 : ℤ) ∣ U.det * x i := by
    have hthis : (2 : ℤ) ∣ (U.adjugate.mulVec (U.mulVec x)) i := by
      change (2 : ℤ) ∣ ∑ j, U.adjugate i j * (U.mulVec x) j
      apply Finset.dvd_sum
      intro j _
      exact dvd_mul_of_dvd_right (hx j) (U.adjugate i j)
    rw [key] at hthis
    simpa [Pi.smul_apply] using hthis
  -- Conclude, since `det U = ±1`.
  rcases hdet with h | h
  · rw [h, one_mul] at h2; exact h2
  · rw [h, neg_one_mul] at h2
    exact Int.dvd_neg.mp h2

end Work.BW
