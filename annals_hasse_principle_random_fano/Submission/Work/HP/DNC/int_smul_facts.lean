import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MobScaleVec

namespace Work.HP.DNC

theorem int_smul_facts {ι : Type*} [Fintype ι] :
    (∀ (k : ℕ) (b : ι → ℤ), Work.HP.eNorm ((k : ℤ) • b) = (k : ℝ) * Work.HP.eNorm b) ∧
    (∀ (k : ℕ) (b : ι → ℤ), Work.HP.toR ((k : ℤ) • b) = (k : ℝ) • Work.HP.toR b) ∧
    (∀ (k : ℕ) (b₁ b₂ : ι → ℤ), 1 ≤ k → (k : ℤ) • b₁ = (k : ℤ) • b₂ → b₁ = b₂) ∧
    (∀ (k : ℕ) (b : ι → ℤ), 1 ≤ k → ((k : ℤ) • b = 0 ↔ b = 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k b
    have h1 : ∑ i, ((((k : ℤ) • b) i : ℝ)) ^ 2 = ((k : ℝ)) ^ 2 * ∑ i, ((b i : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
      ring
    rw [Work.HP.eNorm, Work.HP.eNorm, h1, Real.sqrt_mul (sq_nonneg (k : ℝ)),
      Real.sqrt_sq (Nat.cast_nonneg k)]
  · intro k b
    funext i
    simp only [Work.HP.toR, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  · intro k b₁ b₂ hk h
    funext i
    have hk0 : (k : ℤ) ≠ 0 := by
      have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      omega
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hk0 hi
  · intro k b hk
    constructor
    · intro h
      funext i
      have hk0 : (k : ℤ) ≠ 0 := by
        have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
        omega
      have hi := congrFun h i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left hk0
    · intro h
      rw [h]
      simp

end Work.HP.DNC
