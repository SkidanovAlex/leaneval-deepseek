import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.DimFoundation
import Submission.Work.ORHughesFree.NaturalExtension.exists_mul_weak_inverse_matrix

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

universe u

/-- The `i`-th row of a matrix product `E * A` is the vector-`A`-product of the `i`-th row
of `E`. -/
lemma vecMul_row_eq_row_mul {R : Type*} [NonUnitalNonAssocSemiring R] {n q m : ℕ}
    (E : Matrix (Fin n) (Fin q) R) (A : Matrix (Fin q) (Fin m) R) (i : Fin n) :
    (fun j => E i j) ᵥ* A = fun j => (E * A) i j := by
  ext j
  simp [Matrix.vecMul_apply, Matrix.mul_apply, dotProduct]

/-- Rank–nullity for `x ↦ x ᵥ* Bmat p k`.  Route: `rdim (rowSpanBmat p k) = rk (Bmat p k)`
(`rdim_eq_rk_rows`); take a weak inverse `U` of `Bmat p k` from
`Work.ORHughesFree.NaturalExtension.exists_mul_weak_inverse_matrix` and apply
`Work.ORHughesFree.NaturalExtension.rk_add_rk_one_sub_mul`
(`DimFoundation.lean`), noting that the range of the idempotent `1 - Bmat p k * U` is the row
kernel `{x | x ᵥ* Bmat p k = 0} = kerBmat p k`, whose dimension is again given by
`rdim_eq_rk_rows`. -/
theorem rdim_rowSpanBmat_add_kerBmat {R : Type u} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R)
    (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (k : ℕ) :
    rdim rk (rowSpanBmat p k) + rdim rk (kerBmat p k) = (k : ℝ) + 1 := by
  obtain ⟨U, hU⟩ := exists_mul_weak_inverse_matrix (k + 1) (k + upDeg p + 1) (Bmat p k)
  -- `E := 1 - Bmat p k * U` is the projection onto the row kernel of `Bmat p k`.
  -- Its rows are killed by `Bmat p k`, since `E * Bmat p k = 0`.
  have hEA : ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U) * Bmat p k = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hU, sub_self]
  -- Every row of `E` lies in the row kernel.
  have hrow_mem : ∀ i : Fin (k + 1),
      (fun j : Fin (k + 1) =>
        ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U) i j) ∈ kerBmat p k := by
    intro i
    change (fun j : Fin (k + 1) =>
      ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U) i j)
      ∈ LinearMap.ker (Bmat p k).vecMulLinear
    rw [LinearMap.mem_ker, Matrix.vecMulLinear_apply, vecMul_row_eq_row_mul]
    funext j
    have h := congrFun (congrFun hEA i) j
    simpa using h
  -- Conversely the row kernel is spanned by the rows of `E`.
  have hker : kerBmat p k =
      Submodule.span R (Set.range (fun i : Fin (k + 1) =>
        (fun j : Fin (k + 1) =>
          ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U) i j))) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Submodule.mem_span_range_iff_exists_fun R]
      refine ⟨x, ?_⟩
      have hxE : x ᵥ* ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U) = x := by
        have hxA : x ᵥ* Bmat p k = 0 := by
          have h := LinearMap.mem_ker.mp
            (show x ∈ LinearMap.ker (Bmat p k).vecMulLinear from hx)
          rwa [Matrix.vecMulLinear_apply] at h
        calc x ᵥ* ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U)
            = x ᵥ* (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - x ᵥ* (Bmat p k * U) :=
              Matrix.vecMul_sub _ _ _
          _ = x - x ᵥ* (Bmat p k * U) := by rw [Matrix.vecMul_one]
          _ = x - (x ᵥ* Bmat p k) ᵥ* U := by rw [Matrix.vecMul_vecMul]
          _ = x - 0 := by rw [hxA]; simp
          _ = x := sub_zero x
      exact (Matrix.vecMul_eq_sum x
        ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U)).symm.trans hxE
    · rw [Submodule.span_le]
      rintro v ⟨i, rfl⟩
      exact hrow_mem i
  -- Rank–nullity in the row convention.
  have hrow1 : rdim rk (rowSpanBmat p k) = rk.rk (k + 1) (k + upDeg p + 1) (Bmat p k) :=
    rdim_eq_rk_rows rk (Bmat p k)
  have hrow2 : rdim rk (kerBmat p k) =
      rk.rk (k + 1) (k + 1) ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U) := by
    rw [hker]
    exact rdim_eq_rk_rows rk ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) R) - Bmat p k * U)
  have hsum := rk_add_rk_one_sub_mul rk (Bmat p k) U hU
  rw [hrow1, hrow2, hsum]
  rw [Nat.cast_add, Nat.cast_one]

end Work.ORHughesFree.NaturalExtension
