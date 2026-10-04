import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **The quadratic form of the Gram matrix is the bilinear form on the expanded vector.**
For a continuous bilinear form `B` on a real normed space, vectors `σ i` and coefficients `v i`,
`∑ᵢ ∑ⱼ vᵢ vⱼ B (σᵢ) (σⱼ) = B (∑ᵢ vᵢ • σᵢ) (∑ⱼ vⱼ • σⱼ)`. -/
lemma sum_mul_inner_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (B : V →L[ℝ] V →L[ℝ] ℝ) (σ : Fin n → V) (v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * (B (σ i) (σ j)) = B (∑ i, v i • σ i) (∑ j, v j • σ j) := by
  -- Linearity in the first argument: `B (∑ᵢ vᵢ • σᵢ) = ∑ᵢ vᵢ • B (σᵢ)`.
  have hA : B (∑ i, v i • σ i) = ∑ i, v i • B (σ i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul B (v i) (σ i)
  -- Evaluation of that sum: `(∑ᵢ vᵢ • B (σᵢ)) x = ∑ᵢ vᵢ * B (σᵢ) x`.
  have hC : ∀ x : V, (∑ i, v i • B (σ i)) x = ∑ i, v i * (B (σ i) x) := by
    intro x
    rw [_root_.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]
  -- Linearity in the second argument: `B w (∑ⱼ vⱼ • σⱼ) = ∑ⱼ vⱼ * B w (σⱼ)`.
  have hB : ∀ w : V, B w (∑ j, v j • σ j) = ∑ j, v j * (B w (σ j)) := by
    intro w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  rw [hA, hC]
  apply Finset.sum_congr rfl
  intro i _
  rw [hB (σ i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Work.Diff.EXT
