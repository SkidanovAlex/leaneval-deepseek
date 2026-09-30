import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2AdjDefs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.gramHadamard
import Submission.Work.BW.cardIndexEqFinrank
import Submission.Work.BW.PhiMat_diag
import Submission.Work.BW.prod_index_eq_prod_mult
import Submission.Work.BW.sum_sq_le_card_mul_sup_sq


/-!
# The Gram-determinant bound `√det (A Aᵀ) ≤ N^{M·[F:ℚ]/2} ∏ᵢ ∏_w (sup_j w(aᵢⱼ))^{mult w}`

For a number field `F` and a matrix `a : Fin M → Fin N → F`, let
`A = PhiE a : ℝ^{N·d} → ℝ^{M·d}` be the matrix of the `ℝ`-linear map `Φ a` in the orthonormal
basis of the Euclidean mixed space (`d = [F : ℚ]`, so `A = PhiMat a`).  This file shows

`√det (A Aᵀ) ≤ N^{M·d/2} ∏ᵢ ∏_w (⨆ⱼ w (aᵢⱼ))^{w.mult}`,

the archimedean factor in Bombieri–Vaaler type kernel-lattice estimates.

The proof is Hadamard's inequality for the positive semidefinite matrix `A Aᵀ` together with the
computation of its diagonal entries: in the mixed space, multiplication by `aᵢⱼ` acts
componentwise on the coordinates of the infinite places, so the `(i,c)`-row of `A` has squared
norm `∑ⱼ (w (aᵢⱼ))²` where `w` is the place of the coordinate `c`.  Each such row norm is at most
`N · (⨆ⱼ w (aᵢⱼ))²`, and the product over `Fin M × index F` of `⨆ⱼ w (aᵢⱼ)` is the product over
the places weighted by `w.mult`.
-/

open scoped Classical
open NumberField

namespace Work.BW

/-- For a real matrix `A`, the determinant of the endomorphism `A Aᵀ` of `ℝ^m` (computed as
`A.toEuclideanLin ∘ (A.toEuclideanLin)†`) equals the determinant of the matrix `A * Aᵀ`. -/
theorem toEuclideanLin_det_comp_adjoint {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    LinearMap.det (((A.toEuclideanLin).toContinuousLinearMap.comp
        (A.toEuclideanLin).toContinuousLinearMap.adjoint) :
        EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ m) = (A * A.transpose).det := by
  have hcomp : (((A.toEuclideanLin).toContinuousLinearMap.comp
        (A.toEuclideanLin).toContinuousLinearMap.adjoint) :
        EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ m)
      = A.toEuclideanLin ∘ₗ LinearMap.adjoint A.toEuclideanLin := by
    rw [ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.adjoint_toLinearMap]
    rfl
  rw [hcomp]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.toLpLin_mul 2 2 2 A A.transpose]
  change LinearMap.det (Matrix.toEuclideanLin (A * A.transpose)) = (A * A.transpose).det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.det_toLin _ _

theorem sieg2_det_adjoint_le {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) :
    Real.sqrt (LinearMap.det (((PhiE a).toContinuousLinearMap.comp
        (PhiE a).toContinuousLinearMap.adjoint) :
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))) ≤
      (N : ℝ) ^ ((M : ℝ) * (Module.finrank ℚ F : ℝ) / 2) *
        ∏ i : Fin M, ∏ w : NumberField.InfinitePlace F,
          (⨆ j : Fin N, w (a i j)) ^ w.mult := by
  -- Reduce the left-hand side to the determinant of the matrix `PhiMat a * (PhiMat a)ᵀ`.
  rw [show PhiE a = Matrix.toEuclideanLin (PhiMat a) from rfl]
  rw [toEuclideanLin_det_comp_adjoint (PhiMat a)]
  have hpsd : (PhiMat a * (PhiMat a).transpose).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose (PhiMat a)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- Hadamard's inequality for the positive semidefinite matrix `A Aᵀ`.
  have hhad : (PhiMat a * (PhiMat a).transpose).det ≤
      ∏ p, (PhiMat a * (PhiMat a).transpose) p p :=
    gramHadamard_posSemidef _ hpsd
  refine le_trans (Real.sqrt_le_sqrt hhad) ?_
  rw [Real.sqrt_prod Finset.univ (fun p _ => hpsd.diag_nonneg (i := p))]
  -- The arithmetic of the exponents.
  have hsqrtpow : (Real.sqrt (N : ℝ)) ^
        (M * Fintype.card (NumberField.mixedEmbedding.index F))
      = (N : ℝ) ^ ((M : ℝ) * (Module.finrank ℚ F : ℝ) / 2) := by
    rw [cardIndexEqFinrank]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    push_cast
    ring
  -- The product over `Fin M × index F` grouped by place.
  have hprodidx : (∏ p : Fin M × NumberField.mixedEmbedding.index F,
        ⨆ j : Fin N, stdPlace p.2 (a p.1 j))
      = ∏ i : Fin M, ∏ w : NumberField.InfinitePlace F,
          (⨆ j : Fin N, w (a i j)) ^ w.mult :=
    prod_index_eq_prod_mult (fun z : Fin M × NumberField.InfinitePlace F =>
      ⨆ j : Fin N, z.2 (a z.1 j))
  -- Row norm bound.
  have hstep : (∏ p : Fin M × NumberField.mixedEmbedding.index F,
        Real.sqrt ((PhiMat a * (PhiMat a).transpose) p p))
      ≤ ∏ p : Fin M × NumberField.mixedEmbedding.index F,
          (Real.sqrt (N : ℝ) * (⨆ j : Fin N, stdPlace p.2 (a p.1 j))) := by
    refine Finset.prod_le_prod₀ (fun p _ => Real.sqrt_nonneg _) (fun p _ => ?_)
    rw [PhiMat_diag a p]
    refine le_trans (Real.sqrt_le_sqrt
      (sum_sq_le_card_mul_sup_sq (stdPlace p.2) (fun j => a p.1 j))) ?_
    rw [Real.sqrt_mul (Nat.cast_nonneg N),
      Real.sqrt_sq (Real.iSup_nonneg (fun j => apply_nonneg _ _))]
  refine le_trans hstep ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, hsqrtpow, hprodidx]

end Work.BW
