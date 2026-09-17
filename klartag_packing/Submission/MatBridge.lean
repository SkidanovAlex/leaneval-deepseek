import Mathlib
import Submission.MatSpace

/-!
# The bridge between `MatV d` and `Matrix (Fin d) (Fin d) ℝ`

`Submission.MatSpace` models the space of matrices as the Euclidean space `MatV d` (which has
the norm and inner-product instances needed for Gaussian analysis), and relates it to
`Matrix (Fin d) (Fin d) ℝ` through the linear equivalence `matOf d`.  This file records the
facts needed by the drift estimate:

* the Euclidean inner product of `MatV d` is the Frobenius inner product
  `⟪u, v⟫ = (u * vᵀ).trace` of the corresponding matrices;
* equivalently, `inner ℝ u v = ∑ p : Fin d × Fin d, u p * v p`, and
  `(M * Mᵀ).trace = ∑ p, M p.1 p.2 ^ 2`.
-/

namespace Submission.MatBridge

open Matrix
open Submission.MatSpace

noncomputable section

variable {d : ℕ}

/-- The trace of `M * Nᵀ` is the sum of the entrywise products. -/
theorem trace_mul_transpose_eq_sum (M N : Matrix (Fin d) (Fin d) ℝ) :
    (M * Nᵀ).trace = ∑ i, ∑ j, M i j * N i j := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply]

/-- The Euclidean inner product on `MatV d` is the Frobenius inner product of the corresponding
matrices. -/
theorem inner_eq_trace_mul_transpose (u v : MatV d) :
    inner ℝ u v = (matOf d u * (matOf d v)ᵀ).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, trace_mul_transpose_eq_sum]
  simp only [RCLike.inner_apply, conj_trivial, matOf_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Same, for a symmetric second factor. -/
theorem inner_eq_trace_mul (u v : MatV d) (hv : (matOf d v).IsSymm) :
    inner ℝ u v = (matOf d u * matOf d v).trace := by
  rw [inner_eq_trace_mul_transpose, hv.eq]

/-- The Frobenius square of a matrix, in terms of `MatV d`. -/
theorem sum_sq_eq_trace_mul_transpose (u : MatV d) :
    ∑ p : Fin d × Fin d, u p ^ 2 = (matOf d u * (matOf d u)ᵀ).trace := by
  rw [trace_mul_transpose_eq_sum, Fintype.sum_prod_type]
  simp only [matOf_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Orthogonal projection as an orthonormal-basis expansion -/

/-- The orthogonal projection onto `F` is the expansion in an orthonormal basis of `F`. -/
theorem starProjection_eq_sum (F : Submodule ℝ (MatV d)) (ξ : MatV d) :
    F.starProjection ξ
      = ∑ i, inner ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) ξ •
          (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) := by
  have hmem : F.starProjection ξ ∈ F := Submodule.starProjection_apply_mem F ξ
  have h1 := (stdOrthonormalBasis ℝ ↥F).sum_repr' (⟨F.starProjection ξ, hmem⟩ : ↥F)
  have h2 : ∀ i, inner ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) (F.starProjection ξ)
      = inner ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) ξ := by
    intro i
    rw [← Submodule.inner_starProjection_left_eq_right F
      (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) ξ,
      Submodule.starProjection_eq_self_iff.mpr ((stdOrthonormalBasis ℝ ↥F) i).2]
  symm
  have hco : F.subtype (∑ i, inner ℝ ((stdOrthonormalBasis ℝ ↥F) i)
        (⟨F.starProjection ξ, hmem⟩ : ↥F) • (stdOrthonormalBasis ℝ ↥F) i) = F.starProjection ξ := by
    rw [h1]; rfl
  rw [← hco, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Submodule.coe_inner, ← h2 i]
  rfl

/-- Same, read in the `Matrix` world. -/
theorem matOf_starProjection_eq_sum (F : Submodule ℝ (MatV d)) (ξ : MatV d) :
    matOf d (F.starProjection ξ)
      = ∑ i, inner ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) ξ •
          matOf d (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) := by
  rw [starProjection_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

/-- The elements of an orthonormal basis of a submodule of the symmetric matrices are
symmetric. -/
theorem isSymm_orthonormalBasis (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d)
    (i : Fin (Module.finrank ℝ ↥F)) :
    (matOf d (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d)).IsSymm :=
  hF ((stdOrthonormalBasis ℝ ↥F) i).2

/-- An orthonormal basis of `F ≤ symV d` is orthonormal for the Frobenius inner product of the
corresponding matrices. -/
theorem orthonormalBasis_trace_mul (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d)
    (i j : Fin (Module.finrank ℝ ↥F)) :
    (matOf d (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) *
      matOf d (((stdOrthonormalBasis ℝ ↥F) j : ↥F) : MatV d)).trace
      = if i = j then 1 else 0 := by
  have h := (stdOrthonormalBasis ℝ ↥F).orthonormal
  rw [← inner_eq_trace_mul _ _ (isSymm_orthonormalBasis F hF j)]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, real_inner_self_eq_norm_sq, ← Submodule.coe_norm, h.1 i]
    norm_num
  · rw [if_neg hij, ← Submodule.coe_inner F ((stdOrthonormalBasis ℝ ↥F) i)
      ((stdOrthonormalBasis ℝ ↥F) j)]
    exact h.2 hij

end

end Submission.MatBridge
