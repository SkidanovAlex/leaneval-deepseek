import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq
import Submission.Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent

open scoped BigOperators
open scoped RealInnerProductSpace

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Commons.Analysis.InnerProductSpace

/-- A linearly independent family of vectors in `ℝᵈ` whose coordinates are all integers
has exterior-power (wedge) norm at least `1`: the coordinates of `ιMulti ℝ j v` in the
standard exterior basis are the `j × j` minors of the integer coordinate matrix, one of
which is a nonzero integer (linear independence), and the Gram determinant — equal to the
squared wedge norm — dominates the square of any single minor. -/
theorem intWedge_norm_ge_one {d j : ℕ} (hj1 : 1 ≤ j)
    (v : Fin j → EuclideanSpace ℝ (Fin d))
    (hvz : ∀ r : Fin j, ∀ t : Fin d, ∃ z : ℤ, v r t = z)
    (hvli : LinearIndependent ℝ v) :
    (1 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ j v‖ := by
  classical
  -- `A` : the integer coordinate matrix; rows = coordinates, columns = vectors.
  let A : Matrix (Fin d) (Fin j) ℤ := fun t r => Classical.choose (hvz r t)
  have hA : ∀ r t, v r t = (A t r : ℝ) := by
    intro r t
    exact Classical.choose_spec (hvz r t)
  -- `M` : the same matrix over ℝ.
  let M : Matrix (Fin d) (Fin j) ℝ := A.map (fun z : ℤ => (z : ℝ))
  have hM : ∀ t r, M t r = v r t := by
    intro t r
    simpa [M] using (hA r t).symm
  -- Linear independence of `v` in `EuclideanSpace` gives linear independence of the
  -- coordinate functions over ℝ.
  have hfunc : LinearIndependent ℝ (fun r : Fin j => fun t : Fin d => v r t) := by
    let L : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
      WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
    have hker : L.toLinearMap.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact L.injective
    have hcomp : (fun r : Fin j => fun t : Fin d => v r t) =
        (fun r : Fin j => L.toLinearMap (v r)) := by
      funext r t
      rfl
    rw [hcomp]
    exact LinearIndependent.map' hvli L.toLinearMap hker
  have hMli : LinearIndependent ℝ (fun r : Fin j => fun t : Fin d => M t r) := by
    have hfun : (fun r : Fin j => fun t : Fin d => M t r) =
        (fun r : Fin j => fun t : Fin d => v r t) := by
      funext r t
      exact hM t r
    rw [hfun]
    exact hfunc
  -- ... and (since the coordinates are integers) ℤ-linear independence of the integer
  -- columns of `A`.
  have hzli : LinearIndependent ℤ (fun r : Fin j => fun t : Fin d => A t r) := by
    have hc : LinearIndependent ℝ (fun r : Fin j => fun t : Fin d => (A t r : ℝ)) := by
      simpa [M] using hMli
    exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)
      (v := fun r : Fin j => fun t : Fin d => A t r)).mp hc
  -- A nonzero `j × j` integer minor exists (pick `j` independent rows).
  obtain ⟨e, he⟩ := Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent
    (A := A) hzli
  let Bz : Matrix (Fin j) (Fin j) ℤ := A.submatrix e (fun c : Fin j => c)
  have hBz : Bz.det ≠ 0 := by
    simpa [Bz] using he
  have hBzge : (1 : ℝ) ≤ ((Bz.det : ℤ) : ℝ) ^ 2 := by
    have hz : (1 : ℤ) ≤ Bz.det ^ 2 := by
      have hpos : 0 < Bz.det ^ 2 := sq_pos_of_ne_zero hBz
      omega
    exact_mod_cast hz
  -- Gram-determinant bound: det (MᵀM) ≥ (nonzero integer minor)² ≥ 1.
  have hcomm := Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq (A := A) (e := e)
  have hBzReal : (Bz.map (fun z : ℤ => (z : ℝ))).det = (Bz.det : ℝ) := by
    exact (by
      rw [show Bz.map (fun z : ℤ => (z : ℝ)) = ((Int.castRingHom ℝ).mapMatrix Bz) by rfl]
      exact ((Int.castRingHom ℝ).map_det Bz).symm)
  have hminor : 1 ≤ (Bz.map (fun z : ℤ => (z : ℝ))).det ^ 2 := by
    simpa [hBzReal] using hBzge
  have hgramineq : (M.transpose * M).det ≥
      (Bz.map (fun z : ℤ => (z : ℝ))).det ^ 2 := by
    simpa [M, Bz] using hcomm
  -- The Gram matrix of `v` equals `MᵀM`.
  have hgram_entry : ∀ r s : Fin j, (Matrix.gram ℝ v) r s = (M.transpose * M) r s := by
    intro r s
    calc
      (Matrix.gram ℝ v) r s = ⟪v r, v s⟫ := by rw [Matrix.gram_apply]
      _ = ∑ t : Fin d, (v r) t * (v s) t := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro t ht
        simp [RCLike.inner_apply]
        ring
      _ = (M.transpose * M) r s := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro t ht
        simp [hM]
  have hgramM : Matrix.gram ℝ v = M.transpose * M := by
    ext r s
    exact hgram_entry r s
  -- ‖ιMulti ℝ j v‖² = det (gram v) = det (MᵀM) ≥ 1, and norms are nonnegative.
  let W := exteriorPower.ιMulti ℝ j v
  have hWsq : ‖W‖ ^ 2 = (M.transpose * M).det := by
    calc
      ‖W‖ ^ 2 = ⟪W, W⟫ := (real_inner_self_eq_norm_sq W).symm
      _ = (Matrix.gram ℝ v).det := by
        simpa [W] using exteriorPower.inner_ιMulti_self (x := v)
      _ = (M.transpose * M).det := by rw [hgramM]
  have hWsq_ge : 1 ≤ ‖W‖ ^ 2 := by
    rw [hWsq]
    exact le_trans hminor hgramineq
  have hnonneg : 0 ≤ ‖W‖ := norm_nonneg W
  have hW : 1 ≤ ‖W‖ := by nlinarith
  simpa [W]

end Commons.Analysis.InnerProductSpace
