import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Cauchy–Schwarz for sums of square roots: only the nonnegativity of `a`, `b`
on the index set `s` is needed (Mathlib's `Real.sum_sqrt_mul_sqrt_le` asks for it
globally, so we restrict the functions to `s`). -/
theorem sum_sqrt_mul_sqrt_le {α : Type} (s : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i) ≤
      Real.sqrt (∑ i ∈ s, a i) * Real.sqrt (∑ i ∈ s, b i) := by
  classical
  have h1 : ∀ i : α, 0 ≤ (if i ∈ s then a i else 0) := by
    intro i
    by_cases h : i ∈ s
    · simp [h, ha i h]
    · simp [h]
  have h2 : ∀ i : α, 0 ≤ (if i ∈ s then b i else 0) := by
    intro i
    by_cases h : i ∈ s
    · simp [h, hb i h]
    · simp [h]
  have key := Real.sum_sqrt_mul_sqrt_le (f := fun i => if i ∈ s then a i else 0)
    (g := fun i => if i ∈ s then b i else 0) s h1 h2
  have e1 : ∑ i ∈ s, Real.sqrt (if i ∈ s then a i else 0) * Real.sqrt (if i ∈ s then b i else 0)
          = ∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i) := by
    apply Finset.sum_congr rfl
    intro i hi; simp [hi]
  have e2 : ∑ i ∈ s, (if i ∈ s then a i else 0) = ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl
    intro i hi; simp [hi]
  have e3 : ∑ i ∈ s, (if i ∈ s then b i else 0) = ∑ i ∈ s, b i := by
    apply Finset.sum_congr rfl
    intro i hi; simp [hi]
  rw [e1, e2, e3] at key
  exact key

end Work.N8
