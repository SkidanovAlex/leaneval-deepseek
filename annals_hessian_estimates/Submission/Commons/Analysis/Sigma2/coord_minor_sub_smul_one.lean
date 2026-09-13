import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Trace

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem coord_minor_sub_smul_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : OrthonormalBasis (Fin 4) ℝ E) (a : ℝ) (N : E →L[ℝ] E) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪(N - a • 1) (b i), b i⟫ * ⟪(N - a • 1) (b j), b j⟫
          - ⟪(N - a • 1) (b i), b j⟫ ^ 2) else 0)
      = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          (⟪N (b i), b i⟫ * ⟪N (b j), b j⟫ - ⟪N (b i), b j⟫ ^ 2) else 0)
        - 3 * a * LinearMap.trace ℝ E (N : E →ₗ[ℝ] E) + 6 * a ^ 2 := by
  -- The entries of `N - a • 1` in the orthonormal basis `b`: the diagonal entries are shifted
  -- by `a`, the off-diagonal ones are unchanged.
  have hinner : ∀ i j : Fin 4,
      ⟪(N - a • 1) (b i), b j⟫ = ⟪N (b i), b j⟫ - a * (if i = j then 1 else 0) := by
    intro i j
    have h1 : (N - a • 1) (b i) = N (b i) - a • b i := by simp
    rw [h1, inner_sub_left, inner_smul_left, OrthonormalBasis.inner_eq_ite]
    simp
  -- The trace is the sum of the diagonal entries of `N`.
  have htrace : LinearMap.trace ℝ E (N : E →ₗ[ℝ] E) = ∑ i : Fin 4, ⟪N (b i), b i⟫ := by
    rw [LinearMap.trace_eq_sum_inner (N : E →ₗ[ℝ] E) b]
    apply Finset.sum_congr rfl; intro i _
    simp only [real_inner_comm]; rfl
  rw [htrace]
  -- Expand the four-fold sums and substitute the entries of `N - a • 1`.
  simp only [Fin.sum_univ_four, hinner]
  simp
  ring

end Commons.Analysis.Sigma2