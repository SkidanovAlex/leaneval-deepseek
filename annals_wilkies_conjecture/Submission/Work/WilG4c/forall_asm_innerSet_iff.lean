import Mathlib
import Submission.Work.WilG4c.EpsSetDefs

namespace Work.WilG4c

/-- Unfolding `asm N x c ε δ y u w ∈ innerSet N φ` into the four disjuncts
(negated hypothesis, the two graph equations, and the inequality). -/
theorem asm_mem_innerSet_iff {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (x c : Fin N → ℝ) (ε δ : ℝ)
    (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w ∈ innerSet N φ ↔
      ¬ (∑ i : Fin N, (y i - x i) ^ 2 < δ ^ 2) ∨ ¬ (u = φ y) ∨ ¬ (w = φ x) ∨
        (u - w - ∑ i : Fin N, c i * (y i - x i)) ^ 2 ≤ ε ^ 2 * ∑ i : Fin N, (y i - x i) ^ 2 := by
  rw [mem_innerSet]
  simp only [asm_xIdx, asm_yIdx, asm_cIdx, asm_eIdx, asm_dIdx, asm_uIdx, asm_wIdx]

theorem forall_asm_innerSet_iff {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (x c : Fin N → ℝ) (ε δ : ℝ) :
    (∀ (y : Fin N → ℝ) (u w : ℝ), Work.WilG4c.asm N x c ε δ y u w ∈ Work.WilG4c.innerSet N φ) ↔
      (∀ y : Fin N → ℝ, (∑ i, (y i - x i) ^ 2 < δ ^ 2) →
        (φ y - φ x - ∑ i, c i * (y i - x i)) ^ 2 ≤ ε ^ 2 * ∑ i, (y i - x i) ^ 2) := by
  constructor
  · intro H y hy
    rcases (asm_mem_innerSet_iff φ x c ε δ y (φ y) (φ x)).mp (H y (φ y) (φ x)) with h | h | h | h
    · exact absurd hy h
    · exact absurd rfl h
    · exact absurd rfl h
    · exact h
  · intro H y u w
    rw [asm_mem_innerSet_iff]
    by_cases hy : (∑ i : Fin N, (y i - x i) ^ 2 < δ ^ 2)
    · by_cases hu : u = φ y
      · by_cases hw : w = φ x
        · subst hu; subst hw
          exact Or.inr (Or.inr (Or.inr (H y hy)))
        · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inl hu)
    · exact Or.inl hy

end Work.WilG4c
