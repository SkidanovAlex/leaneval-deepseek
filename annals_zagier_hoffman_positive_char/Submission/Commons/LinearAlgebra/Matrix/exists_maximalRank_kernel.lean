import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace Commons.LinearAlgebra.Matrix

/-- For a nonzero row vector `ρ` over a field there is a matrix `ϑ : Matrix (Fin ℓ) (Fin (ℓ-1)) K`
with linearly independent columns and `Matrix.vecMul ρ ϑ = 0` (a basis of the kernel of `ρ`). -/
theorem exists_maximalRank_kernel {K : Type*} [Field K] {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {ρ : Fin ℓ → K}
    (hρ : ρ ≠ 0) :
    ∃ ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) K,
      LinearIndependent K (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i) ∧
      Matrix.vecMul ρ ϑ = 0 := by
  -- Write `ℓ = m + 1` so that `Fin (ℓ - 1)` is definitionally `Fin m`.
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  -- Pick an index `k` at which `ρ` does not vanish.
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hρ
  simp only [Pi.zero_apply] at hk
  -- `e i` is the `i`-th index skipping `k`; it enumerates the complement of `{k}`.
  let e : Fin (m + 1 - 1) → Fin (m + 1) := fun i => Fin.succAbove k i
  -- `A` selects the coordinate `e i` in column `i`, `B` corrects it so that `ρ ⬝ (A + B) = 0`.
  let A : Matrix (Fin (m + 1)) (Fin (m + 1 - 1)) K :=
    fun j i => (Pi.single (e i) (1 : K) : Fin (m + 1) → K) j
  let B : Matrix (Fin (m + 1)) (Fin (m + 1 - 1)) K :=
    fun j i => (Pi.single k (-(ρ (e i) / ρ k)) : Fin (m + 1) → K) j
  refine ⟨A + B, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i0
    have h := congrFun hg (e i0)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
    -- Evaluating a linear combination of the columns at `e i0` isolates `g i0`.
    have hval : ∀ i : Fin (m + 1 - 1), (A + B) (e i0) i = if i0 = i then (1 : K) else 0 := by
      intro i
      rw [Matrix.add_apply]
      simp only [A, B, Pi.single_apply]
      rw [if_neg (Fin.succAbove_ne k i0), add_zero]
      by_cases hii : i0 = i
      · subst hii; simp
      · rw [if_neg hii, if_neg]
        intro hc
        exact hii (Fin.succAbove_right_injective hc)
    rw [Finset.sum_congr rfl (fun i _ => by rw [hval i])] at h
    have hsum : ∑ i : Fin (m + 1 - 1), g i * (if i0 = i then (1 : K) else 0) = g i0 := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    exact hsum ▸ h
  · rw [Matrix.vecMul_add]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
    have hA : ∑ j : Fin (m + 1), ρ j * A j i = ρ (e i) := by
      simp only [A, Pi.single_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    have hB : ∑ j : Fin (m + 1), ρ j * B j i = -ρ (e i) := by
      simp only [B, Pi.single_apply, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, reduceIte]
      rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hk]
    rw [hA, hB]
    simp

end Commons.LinearAlgebra.Matrix