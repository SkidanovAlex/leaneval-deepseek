import Mathlib
import Submission.Subspace.Index

/-!
# Rescaling the weights of the index

`index α r P = k · index α (k • r) P`: rescaling all weights by a positive integer `k` divides the
index by `k`.  This is used in Roth's lemma to pass between the Wronskian of a polynomial (whose
degrees are `k · r`) and the weight vector `k • r`, which is the vector for which the induction
hypothesis is applied.
-/

open scoped BigOperators

namespace Submission.Subspace

open Commons.Algebra.MvPolynomial (indexWt indexSet indexTay pderivIter)

variable {σ : Type*} [Fintype σ]

/-- The weighted value rescales inversely under `r ↦ k • r`. -/
lemma indexWt_nsmul (k : ℕ) (hk : 1 ≤ k) (r : σ → ℕ) (m : σ →₀ ℕ) :
    indexWt (k • r) m = (k : ℝ)⁻¹ * indexWt r m := by
  rw [indexWt, indexWt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, Nat.cast_id]
  have hkne : ((k : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Rescaling the weights.**  Multiplication of all weights by `k ≥ 1` divides the index by
`k`. -/
theorem index_eq_mul_index_nsmul {K : Type*} [Field K] (k : ℕ) (hk : 1 ≤ k) (α : σ → K)
    (r : σ → ℕ) (P : MvPolynomial σ K) :
    index α r P = (k : ℝ) * index α (k • r) P := by
  have hkne : ((k : ℕ) : ℝ) ≠ 0 := by positivity
  rcases eq_or_ne P 0 with rfl | hP
  · rw [index_zero, index_zero, mul_zero]
  · obtain ⟨m, hm, hmin, hle⟩ := index_eq_indexWt_of_min α r P hP
    obtain ⟨m', hm', hmin', hle'⟩ := index_eq_indexWt_of_min α (k • r) P hP
    have h1 : indexWt (k • r) m ≤ indexWt (k • r) m' := by
      rw [indexWt_nsmul k hk, indexWt_nsmul k hk]
      exact mul_le_mul_of_nonneg_left (hle m' hm') (by positivity)
    have h2 : indexWt (k • r) m' ≤ indexWt (k • r) m := hle' m hm
    have hm2 : indexWt (k • r) m' = indexWt (k • r) m := le_antisymm h2 h1
    rw [hmin, hmin', hm2, indexWt_nsmul k hk]
    field_simp

end Submission.Subspace
