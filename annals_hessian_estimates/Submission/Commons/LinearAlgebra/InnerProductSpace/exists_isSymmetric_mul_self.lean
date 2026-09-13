import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Commons.LinearAlgebra.InnerProductSpace

/-- Every self-adjoint positive semi-definite operator `T` on a finite-dimensional real inner
product space has a self-adjoint square root `S` (i.e. `S * S = T`).

This is obtained from the spectral theorem: in an orthonormal eigenbasis of `T` the eigenvalues
`λ i` are nonnegative, and `S` is given by taking the square roots of the `λ i`. -/
theorem exists_isSymmetric_mul_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (hTnn : ∀ v : E, 0 ≤ inner ℝ (T v) v) :
    ∃ S : E →L[ℝ] E, S.IsSymmetric ∧ S * S = T := by
  classical
  let b := hT.eigenvectorBasis (𝕜 := ℝ) (E := E) rfl
  let lam := hT.eigenvalues (𝕜 := ℝ) (E := E) rfl
  -- `T` acts diagonally on the orthonormal eigenbasis `b`.
  have hTb : ∀ j, T (b j) = lam j • b j := by
    intro j
    exact hT.apply_eigenvectorBasis (𝕜 := ℝ) (E := E) rfl j
  have hbb : ∀ i, inner ℝ (b i) (b i) = 1 := by
    intro i
    rw [orthonormal_iff_ite.mp b.orthonormal i i]; simp
  -- positive semi-definiteness says the eigenvalues are nonnegative.
  have hnn : ∀ i, 0 ≤ lam i := by
    intro i
    have h1 : inner ℝ (T (b i)) (b i) = lam i := by
      rw [hTb i, inner_smul_left, hbb i]; simp
    rw [← h1]; exact hTnn (b i)
  -- the candidate square root, written as a sum of rank-one operators.
  let L : E →ₗ[ℝ] E := ∑ i, Real.sqrt (lam i) •
      (InnerProductSpace.rankOne ℝ (b i) (b i) : E →ₗ[ℝ] E)
  have hrank : ∀ i, (InnerProductSpace.rankOne ℝ (b i) (b i) : E →ₗ[ℝ] E).IsSymmetric := by
    intro i y z
    simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, mul_comm]
  have hLsym : L.IsSymmetric := by
    refine LinearMap.isSymmetric_sum _ (fun i _ => ?_)
    exact (hrank i).smul (by simp)
  have hLb : ∀ j, L (b j) = Real.sqrt (lam j) • b j := by
    intro j
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  refine ⟨L.toContinuousLinearMap, ?_, ?_⟩
  · rw [LinearMap.coe_toContinuousLinearMap]
    exact hLsym
  · apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext (fun j => ?_)
    have h1 : (L.toContinuousLinearMap) (b j) = Real.sqrt (lam j) • b j := hLb j
    change (L.toContinuousLinearMap * L.toContinuousLinearMap) (b j) = T (b j)
    rw [mul_apply_eq_comp, h1, map_smul, h1, hTb j]
    rw [smul_smul, Real.mul_self_sqrt (hnn j)]

end Commons.LinearAlgebra.InnerProductSpace