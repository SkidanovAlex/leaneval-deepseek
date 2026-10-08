import Mathlib
import Submission.Work.Clifford.reverse_eq_C_mul_prod_roots_inv
import Submission.Work.Clifford.charpoly_roots_pow_eq_one
import Submission.Work.Coherence.inv_eq_conj_of_pow_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.charpoly_pow_sub_one_roots`

For an endomorphism `T` of a finite-dimensional complex vector space with `T ^ n = 1`
(`0 < n`), the roots of the characteristic polynomial of `T ^ (n - 1) = T⁻¹` are the complex
conjugates of the roots of the characteristic polynomial of `T`.

The mathematical content: `T` is invertible with inverse `T ^ (n - 1)`; the eigenvalues of `T` are
`n`-th roots of unity, hence `λ⁻¹ = conj λ` for every eigenvalue `λ`.  The characteristic
polynomial of the inverse is the reversed characteristic polynomial up to a unit scalar, whose
roots are the inverses of the roots of `charpoly T`.

Concretely, in a basis `T` becomes a matrix `M` with `M ^ n = 1`.  With
`p = M.charpoly`, `Matrix.charpoly_inv` gives `(M⁻¹).charpoly = (-1)^d · C (det M)⁻¹ · p.reverse`,
while `p.reverse = C (p.coeff 0) · ∏ (X - C a⁻¹)` over the roots `a` of `p`
(`reverse_eq_C_mul_prod_roots_inv`), and `(-1)^d · (det M)⁻¹ · p.coeff 0 = 1` because
`p.coeff 0 = (-1)^d · det M`.  Finally `a⁻¹ = conj a` by `charpoly_roots_pow_eq_one`.
-/

namespace Work.Clifford

open Polynomial Matrix LinearMap Module

theorem charpoly_pow_sub_one_roots {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : W →ₗ[ℂ] W) (n : ℕ) (hn : 0 < n) (hT : T ^ n = 1) :
    ((T ^ (n - 1)).charpoly).roots = (T.charpoly).roots.map (starRingEnd ℂ) := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let M := LinearMap.toMatrix b b T
  have hM : M ^ n = 1 := by
    change (LinearMap.toMatrix b b T) ^ n = 1
    rw [LinearMap.toMatrix_pow, hT, LinearMap.toMatrix_one]
  have hchar : M.charpoly = T.charpoly := LinearMap.charpoly_toMatrix T b
  have hMmul : M * M ^ (n - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ n by omega), hM]
  have hMmul' : M ^ (n - 1) * M = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega), hM]
  have hmatpow : M ^ (n - 1) = M⁻¹ := (Matrix.inv_eq_right_inv hMmul).symm
  have hunit : IsUnit M := isUnit_iff_exists.mpr ⟨M ^ (n - 1), hMmul, hMmul'⟩
  have hdetunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hdetne : M.det ≠ 0 := hdetunit.ne_zero
  have hkey : (M⁻¹).charpoly = M.charpoly.map (starRingEnd ℂ) := by
    have hpm : M.charpoly.Monic := Matrix.charpoly_monic M
    have hps : M.charpoly.Splits := IsAlgClosed.splits _
    have hroot : ∀ a ∈ M.charpoly.roots, a ^ n = 1 := by
      intro a ha
      exact charpoly_roots_pow_eq_one T n hT (by rw [hchar] at ha; exact ha)
    have hinv : ∀ a ∈ M.charpoly.roots, a⁻¹ = starRingEnd ℂ a := fun a ha =>
      Work.Coherence.inv_eq_conj_of_pow_eq_one hn.ne' (hroot a ha)
    have hc0 : M.charpoly.coeff 0
        = (-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W) * M.det := by
      rw [coeff_zero_eq_eval_zero, Matrix.eval_charpoly M 0]
      rw [Matrix.scalar_apply, Matrix.diagonal_zero, zero_sub, Matrix.det_neg]
    have hpc0ne : M.charpoly.coeff 0 ≠ 0 := by
      rw [hc0]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdetne
    have hsign : ((-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W))
        * ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W)) = 1 := by
      rw [← pow_add, show Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
            + Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
            = 2 * Fintype.card (Module.Free.ChooseBasisIndex ℂ W) by ring, pow_mul]
      norm_num
    have hinvdet : Ring.inverse M.det * M.det = 1 := Ring.inverse_mul_cancel _ hdetunit
    have hcc0c : (-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
        * Ring.inverse M.det * M.charpoly.coeff 0 = 1 := by
      rw [hc0]
      calc (-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
              * Ring.inverse M.det
              * ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W) * M.det)
          = ((-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
              * (-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W))
            * (Ring.inverse M.det * M.det) := by ring
        _ = 1 := by rw [hsign, hinvdet, one_mul]
    have hcc0poly : (-1 : ℂ[X]) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
        * C (Ring.inverse M.det) * C (M.charpoly.coeff 0) = 1 := by
      rw [show (-1 : ℂ[X]) = C (-1 : ℂ) by simp, ← map_pow]
      rw [← map_mul, ← map_mul, hcc0c, map_one]
    have hrev := reverse_eq_C_mul_prod_roots_inv M.charpoly hpm hps hpc0ne
    have hsplit := hps.eq_prod_roots_of_monic hpm
    have hmapeq : M.charpoly.map (starRingEnd ℂ)
        = (M.charpoly.roots.map (fun a => X - C a⁻¹)).prod := by
      conv_lhs => rw [hsplit]
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl ?_
      intro a ha
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [← hinv a ha]
    have hcvi : (M⁻¹).charpoly
        = (-1 : ℂ[X]) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ W)
          * C (Ring.inverse M.det) * M.charpoly.reverse := by
      rw [Matrix.charpoly_inv M hunit, ← Matrix.reverse_charpoly M]
    rw [hcvi, hrev]
    rw [← mul_assoc, hcc0poly, one_mul]
    exact hmapeq.symm
  have hL : (T ^ (n - 1)).charpoly = M.charpoly.map (starRingEnd ℂ) := by
    rw [← LinearMap.charpoly_toMatrix (T ^ (n - 1)) b, ← LinearMap.toMatrix_pow]
    change (M ^ (n - 1)).charpoly = M.charpoly.map (starRingEnd ℂ)
    rw [hmatpow, hkey]
  rw [hL, ← hchar]
  exact Polynomial.Splits.roots_map (IsAlgClosed.splits M.charpoly) (starRingEnd ℂ)

end Work.Clifford
