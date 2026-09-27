import Mathlib
import Submission.Work.Drive.ker_eq_span_cofactorVec

/-!
# The cofactor vector of a surjective `T : ℝ^{m+1} → ℝ^m` is nonzero

For a *surjective* linear map `T : ℝ^{m+1} → ℝ^m` the cofactor vector `cofactorVec T` — the vector
whose `j`-th component is the signed maximal minor of the matrix of `T` with the `j`-th row deleted —
does not vanish.

This is the "spans the kernel" half of the classical fact that, for a surjective `T`, the cofactor
vector is a nonzero vector spanning `ker T`.  The spanning statement is
`Work.Drive.ker_eq_span_cofactorVec`; here we only need non-vanishing, which follows by dimension
count: if `cofactorVec T = 0`, then `ker T = span {0} = ⊥`, so `T` would be injective, forcing
`m + 1 = finrank ℝ (ℝ^{m+1}) ≤ finrank ℝ (ℝ^m) = m`, which is absurd.

(Equivalently: the cofactor vector is orthogonal to the `m` linearly independent columns of the
matrix of `T` in `ℝ^{m+1}`, so its orthogonal complement has dimension `m < m + 1`; a nonzero vector
alone cannot account for a complement of dimension `m`, whence the cofactor vector is nonzero.)
-/

namespace Work.Drive

theorem cofactorVec_ne_zero_of_surjective {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m)
    (hT : Function.Surjective T) : Work.Drive.cofactorVec T ≠ 0 := by
  intro h0
  -- A vanishing cofactor vector leaves a trivial kernel.
  have hker : LinearMap.ker (T : Work.Drive.Amb m →ₗ[ℝ] Work.Drive.Tgt m) = ⊥ := by
    rw [ker_eq_span_cofactorVec T hT, h0]
    simp
  have hinj : Function.Injective (T : Work.Drive.Amb m →ₗ[ℝ] Work.Drive.Tgt m) :=
    LinearMap.ker_eq_bot.mp hker
  -- Injectivity contradicts the dimension count `dim ℝ^{m+1} = m + 1 > m = dim ℝ^m`.
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hle
  omega

end Work.Drive
