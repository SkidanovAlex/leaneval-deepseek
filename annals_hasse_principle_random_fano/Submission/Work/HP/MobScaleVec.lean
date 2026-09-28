import Mathlib
import Submission.Work.HP.MobDefs

namespace Work.HP

theorem MobScaleVec {ι : Type*} [Fintype ι] :
    (∀ (ℓ : ℕ) (a : ι → ℤ), eNorm (scaleVec ℓ a) = (ℓ : ℝ) * eNorm a) ∧
    (∀ (ℓ : ℕ) (a : ι → ℤ), toR (scaleVec ℓ a) = (ℓ : ℝ) • toR a) ∧
    (∀ (v t : ι → ℝ) (α c : ℝ), 0 < c → (c • t ∈ Cgam v α ↔ t ∈ Cgam v α)) ∧
    (∀ (ℓ : ℕ) (a : ι → ℤ), scaleVec ℓ a = 0 ↔ ℓ = 0 ∨ a = 0) ∧
    (∀ (ℓ : ℕ) (a b : ι → ℤ), 1 ≤ ℓ → scaleVec ℓ a = scaleVec ℓ b → a = b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ a
    have h1 : ∑ i, (((scaleVec ℓ a) i : ℝ)) ^ 2 = ((ℓ : ℝ)) ^ 2 * ∑ i, ((a i : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [scaleVec, Int.cast_mul, Int.cast_natCast]
      ring
    rw [eNorm, eNorm, h1, Real.sqrt_mul (sq_nonneg (ℓ : ℝ)),
      Real.sqrt_sq (Nat.cast_nonneg ℓ)]
  · intro ℓ a
    funext i
    simp only [toR, scaleVec, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  · intro v t α c hc
    have hdot : dotR v (c • t) = c * dotR v t := by
      simp only [dotR, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hrn : rNorm (c • t) = c * rNorm t := by
      have h2 : ∑ i, ((c • t) i) ^ 2 = c ^ 2 * ∑ i, (t i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [rNorm, rNorm, h2, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq (le_of_lt hc)]
    simp only [Cgam, Set.mem_ofPred_eq]
    rw [hdot, hrn, abs_mul, abs_of_pos hc]
    have heq : rNorm v * (c * rNorm t) / (2 * α) = c * (rNorm v * rNorm t / (2 * α)) := by
      ring
    rw [heq]
    exact mul_le_mul_iff_of_pos_left hc
  · intro ℓ a
    constructor
    · intro h
      by_cases hℓ : ℓ = 0
      · exact Or.inl hℓ
      · right
        funext i
        have hi := congr_fun h i
        simp only [scaleVec, Pi.zero_apply] at hi
        have hc : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hℓ
        exact (mul_eq_zero.mp hi).resolve_left hc
    · rintro (rfl | rfl)
      · funext i; simp [scaleVec]
      · funext i; simp [scaleVec]
  · intro ℓ a b hℓ h
    funext i
    have hi := congr_fun h i
    simp only [scaleVec] at hi
    have hc : (ℓ : ℤ) ≠ 0 := by
      have h1 : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
      omega
    exact mul_left_cancel₀ hc hi

end Work.HP
