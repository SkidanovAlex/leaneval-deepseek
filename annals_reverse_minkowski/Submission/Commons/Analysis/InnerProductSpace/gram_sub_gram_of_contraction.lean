import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- For a real inner product space, the double sum `∑∑ c x * ⟪u x, u y⟫ * c y` equals the
squared norm of the weighted sum `∑ c x • u x`. -/
private lemma sum2_inner_sq_real {ι : Type*} {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (s : Finset ι) (c : ι → ℝ) (u : ι → F) :
    (∑ x ∈ s, ∑ y ∈ s, c x * inner ℝ (u x) (u y) * c y) = (‖∑ x ∈ s, c x • u x‖ : ℝ) ^ 2 := by
  calc
    (∑ x ∈ s, ∑ y ∈ s, c x * inner ℝ (u x) (u y) * c y)
        = inner ℝ (∑ x ∈ s, c x • u x) (∑ y ∈ s, c y • u y) := by
            rw [sum_inner s (fun x => c x • u x)]
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [inner_sum s (fun y => c y • u y) (c x • u x)]
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [real_inner_smul_left, real_inner_smul_right]
            ring
    _ = (‖∑ x ∈ s, c x • u x‖ : ℝ) ^ 2 := by
            rw [real_inner_self_eq_norm_sq]

open Matrix

/-- Applying a linear contraction `T` to a family of vectors can only decrease the Gram
matrix in the positive semidefinite order: `gram v - gram (T ∘ v)` is positive semidefinite. -/
theorem gram_sub_gram_of_contraction {n m : ℕ}
    (v : Fin m → EuclideanSpace ℝ (Fin n))
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : ∀ x : EuclideanSpace ℝ (Fin n), ‖T x‖ ≤ ‖x‖) :
    ((Matrix.gram ℝ v) - (Matrix.gram ℝ (fun j => T (v j)))).PosSemidef := by
  classical
  refine ⟨?_, ?_⟩
  · exact (isHermitian_gram ℝ v).sub (isHermitian_gram ℝ (fun j => T (v j)))
  · intro c
    have hleft : (∑ i ∈ c.support, ∑ j ∈ c.support, star (c i) * gram ℝ v i j * c j)
        = (‖∑ i ∈ c.support, c i • v i‖ : ℝ) ^ 2 := by
      rw [← sum2_inner_sq_real c.support c v]
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp
    have hright : (∑ i ∈ c.support, ∑ j ∈ c.support,
        star (c i) * gram ℝ (fun j => T (v j)) i j * c j)
        = (‖∑ i ∈ c.support, c i • T (v i)‖ : ℝ) ^ 2 := by
      rw [← sum2_inner_sq_real c.support c (fun i => T (v i))]
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp
    have hnorm : (‖∑ i ∈ c.support, c i • T (v i)‖ : ℝ) ^ 2 ≤
        (‖∑ i ∈ c.support, c i • v i‖ : ℝ) ^ 2 := by
      have hw : (∑ i ∈ c.support, c i • T (v i)) = T (∑ i ∈ c.support, c i • v i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp
      rw [hw]
      exact pow_le_pow_left₀ (norm_nonneg _) (hT _) 2
    have hcalc :
        c.sum (fun i xi => c.sum (fun j xj =>
          star xi * (gram ℝ v - gram ℝ (fun j => T (v j))) i j * xj))
        = (‖∑ i ∈ c.support, c i • v i‖ : ℝ) ^ 2 - (‖∑ i ∈ c.support, c i • T (v i)‖ : ℝ) ^ 2 := by
      simp_rw [Finsupp.sum, Matrix.sub_apply]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      rw [hleft, hright]
    rw [hcalc, sub_nonneg]
    exact hnorm

end Commons.Analysis.InnerProductSpace
