import Mathlib
import Submission.Commons.Probability.RandomMatrix.opNorm_le_of_net_quadratic_nonneg

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace BigOperators
open Matrix

/-- A quadratic form `x ↦ ∑ᵢ ∑ⱼ M i j * x i * x j` given by a symmetric matrix `M` which is
bounded by `θ` on a `1/4`-net `S` of the unit sphere is bounded by `2θ‖x‖²` everywhere.

The proof converts `M` into the continuous linear operator `T` on `EuclideanSpace ℝ (Fin d)`
associated with it (via `Matrix.toEuclideanLin`), observes that `T` is self-adjoint (because
`M` is symmetric) and that `⟪T x, x⟫` is exactly the quadratic form, and then applies the
Vershynin-style net bound `opNorm_le_of_net_quadratic_nonneg` from the commons with
`δ = 1/4`: `‖T‖ ≤ θ / (1 - 2 * 1/4) = 2θ`. -/
theorem quadform_le_of_sphere_net {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hMsym : M.IsSymm)
    {θ : ℝ} (hθ : 0 ≤ θ) (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    (hnet : ∀ x ∈ S, |∑ i, ∑ j, M i j * x i * x j| ≤ θ) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      |∑ i, ∑ j, M i j * x i * x j| ≤ 2 * θ * ‖x‖ ^ 2 := by
  classical
  let T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (Matrix.toEuclideanLin M).toContinuousLinearMap
  -- `⟪T u, v⟫ = u ⬝ (M *ᵥ v)`
  have hleft : ∀ u v : EuclideanSpace ℝ (Fin d), inner ℝ (T u) v = u ⬝ᵥ (M *ᵥ v) := by
    intro u v
    have h1 : inner ℝ (T u) v = (M *ᵥ u) ⬝ᵥ v := by
      change inner ℝ (((Matrix.toEuclideanLin M).toContinuousLinearMap) u) v
        = (M *ᵥ u) ⬝ᵥ v
      rw [Commons.Probability.RandomMatrix.inner_clm_apply]
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mulVec_apply_eq_sum]
    calc inner ℝ (T u) v = (M *ᵥ u) ⬝ᵥ v := h1
      _ = v ⬝ᵥ (M *ᵥ u) := dotProduct_comm _ _
      _ = u ⬝ᵥ (Mᵀ *ᵥ v) := (Matrix.dotProduct_transpose_mulVec M u v).symm
      _ = u ⬝ᵥ (M *ᵥ v) := by rw [hMsym.eq]
  -- `⟪u, T v⟫ = u ⬝ (M *ᵥ v)`
  have hright : ∀ u v : EuclideanSpace ℝ (Fin d), inner ℝ u (T v) = u ⬝ᵥ (M *ᵥ v) := by
    intro u v
    have h1 : inner ℝ (T v) u = (M *ᵥ v) ⬝ᵥ u := by
      change inner ℝ (((Matrix.toEuclideanLin M).toContinuousLinearMap) v) u
        = (M *ᵥ v) ⬝ᵥ u
      rw [Commons.Probability.RandomMatrix.inner_clm_apply]
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mulVec_apply_eq_sum]
    rw [real_inner_comm, h1, dotProduct_comm]
  -- the quadratic form is the diagonal of the bilinear form of `T`
  have hdiag : ∀ x : EuclideanSpace ℝ (Fin d),
      inner ℝ (T x) x = ∑ i, ∑ j, M i j * x i * x j := by
    intro x
    rw [hleft x x, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnetT : ∀ x ∈ S, |inner ℝ (T x) x| ≤ θ := by
    intro x hx
    rw [hdiag x]
    exact hnet x hx
  -- net bound on the operator norm
  have hop : ‖T‖ ≤ 2 * θ := by
    have h := Commons.Probability.RandomMatrix.opNorm_le_of_net_quadratic_nonneg T
      (fun u v => (hleft u v).trans (hright u v).symm)
      (δ := 1 / 4) (θ := θ) (by norm_num) (by norm_num) hθ S hSun hcover hnetT
    have hden : (1 : ℝ) - 2 * (1 / 4) = 1 / 2 := by norm_num
    rw [hden] at h
    have hdiv : θ / (1 / 2 : ℝ) = 2 * θ := by ring
    rw [hdiv] at h
    exact h
  intro x
  rw [← hdiag x]
  calc |inner ℝ (T x) x| ≤ ‖T x‖ * ‖x‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (T x) x
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm T x
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring
    _ ≤ (2 * θ) * ‖x‖ ^ 2 := by
        gcongr
    _ = 2 * θ * ‖x‖ ^ 2 := by ring

end Commons.Analysis.InnerProductSpace
