import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Mul

namespace Commons.LinearAlgebra.Matrix

/-- Over `𝔽₂`, the outer product of two non-zero vectors determines the vectors. -/
theorem vecMulVec_injective_zmod_two {m n : ℕ} {b b' : Fin m → ZMod 2} {φ φ' : Fin n → ZMod 2}
    (hb : b ≠ 0) (hφ : φ ≠ 0) (hb' : b' ≠ 0) (hφ' : φ' ≠ 0)
    (h : Matrix.vecMulVec b φ = Matrix.vecMulVec b' φ') : b = b' ∧ φ = φ' := by
  -- In `ZMod 2` every non-zero element equals `1`.
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x hx
    have hlt : x.val < 2 := ZMod.val_lt x
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with h0 | h1
    · exact absurd ((ZMod.val_eq_zero x).mp h0) hx
    · rw [← ZMod.natCast_zmod_val x, h1]
      norm_num
  -- A non-zero function on a finite type has a non-zero value.
  have hb_ne : ∃ i, b i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (funext fun i => hcon i)
  have hφ_ne : ∃ j, φ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (funext fun j => hcon j)
  obtain ⟨i₀, hi₀⟩ := hb_ne
  obtain ⟨j₀, hj₀⟩ := hφ_ne
  have hi₀' : b i₀ = 1 := hz _ hi₀
  have hj₀' : φ j₀ = 1 := hz _ hj₀
  have hentry : b' i₀ * φ' j₀ = 1 := by
    have h1 := congrFun (congrFun h i₀) j₀
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hi₀', hj₀', one_mul] at h1
    exact h1.symm
  have hb'1 : b' i₀ = 1 := by
    refine hz _ ?_
    intro h0
    rw [h0, zero_mul] at hentry
    exact zero_ne_one hentry
  have hφ'1 : φ' j₀ = 1 := by
    refine hz _ ?_
    intro h0
    rw [h0, mul_zero] at hentry
    exact zero_ne_one hentry
  refine ⟨?_, ?_⟩
  · funext i
    have h1 := congrFun (congrFun h i) j₀
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hj₀', hφ'1, mul_one, mul_one] at h1
    exact h1
  · funext j
    have h1 := congrFun (congrFun h i₀) j
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hi₀', hb'1, one_mul, one_mul] at h1
    exact h1

end Commons.LinearAlgebra.Matrix