import Mathlib
import Submission.Work.BW.gramHadamard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a real vector, the sum of squares of its entries is at most the square of the sum of the
absolute values of its entries. -/
lemma sum_sq_le_sq_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ i, x i ^ 2 ≤ (∑ i, |x i|) ^ 2 := by
  simpa [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => |x i|) (fun i _ => abs_nonneg (x i))

/-- Hadamard bound for the Gram determinant of an integer matrix: the absolute value of the
determinant of `A = L · Lᵀ` is at most `r! · ∏_a (∑_i |L_a i|)²`. -/
lemma gramDet_natAbs_le {n r : ℕ} (L : Fin r → Fin n → ℤ) :
    (((Matrix.of (fun a a' : Fin r => ∑ i, L a i * L a' i)).det).natAbs : ℝ) ≤
      (r.factorial : ℝ) * ∏ a, (∑ i, |(L a i : ℝ)|) ^ 2 := by
  classical
  -- The real matrix of the rows of `L`, and the integer Gram matrix `M`.
  set B : Matrix (Fin r) (Fin n) ℝ := Matrix.of (fun a i => (L a i : ℝ)) with hB
  set M : Matrix (Fin r) (Fin r) ℤ := Matrix.of (fun a a' => ∑ i, L a i * L a' i) with hM
  -- Casting `M` to `ℝ` gives the Gram matrix `B * Bᵀ` of the rows of `B`.
  have hmap : M.map (fun x => (x : ℝ)) = B * B.transpose := by
    ext a a'
    simp [hM, hB, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Int.cast_sum]
  have hdet : (M.det : ℝ) = (B * B.transpose).det := by
    rw [Int.cast_det, hmap]
  -- `B * Bᵀ` is positive semidefinite, hence has nonnegative determinant.
  have hpsd : (B * B.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose B
  have hnn : 0 ≤ (B * B.transpose).det := hpsd.det_nonneg
  -- Transport the goal to the determinant of the real Gram matrix.
  rw [Nat.cast_natAbs, Int.cast_abs, hdet, abs_of_nonneg hnn]
  calc (B * B.transpose).det
      ≤ ∏ a, ∑ i, (B a i) ^ 2 := gramHadamard B
    _ ≤ ∏ a, (∑ i, |B a i|) ^ 2 := by
        apply Finset.prod_le_prod₀
        · intro a _; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        · intro a _; exact sum_sq_le_sq_sum_abs _
    _ ≤ (r.factorial : ℝ) * ∏ a, (∑ i, |B a i|) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (r.factorial : ℝ) := by
          have : (1 : ℕ) ≤ r.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
          exact_mod_cast this
        have h2 : 0 ≤ ∏ a, (∑ i, |B a i|) ^ 2 :=
          Finset.prod_nonneg (fun a _ => sq_nonneg _)
        calc ∏ a, (∑ i, |B a i|) ^ 2 = 1 * ∏ a, (∑ i, |B a i|) ^ 2 := by rw [one_mul]
          _ ≤ (r.factorial : ℝ) * ∏ a, (∑ i, |B a i|) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 h2
    _ = (r.factorial : ℝ) * ∏ a, (∑ i, |(L a i : ℝ)|) ^ 2 := by simp [hB]

end Work.BW
