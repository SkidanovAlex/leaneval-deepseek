import Mathlib
import Submission.Work.LinnikContract.Defs

open scoped BigOperators

namespace Work.LinnikContract.API

/-- Elementary API for the box predicates and box sums: `InBox` is monotone in the radius `R`,
`Ncount` is monotone in `lam`, and `boxAbs` is a sum of non-negative terms.
`InBox q R ρ = (lamOf q ρ ≤ R ∧ |ρ.im| * log q ≤ R)`, `Ncount` is a cardinality of a
`Finset.filter`, and `boxAbs` is a `∑ᶠ` of `(zeroMult : ℝ) * ‖F2 …‖` over the box.
No `native_decide`. -/
theorem box_api :
    (∀ (q : ℕ) {R R' : ℝ}, R ≤ R' → ∀ ρ : ℂ,
      Work.LinnikContract.InBox q R ρ → Work.LinnikContract.InBox q R' ρ) ∧
    (∀ (q : ℕ) [NeZero q] {lam lam' : ℝ}, lam ≤ lam' →
      Work.LinnikContract.Ncount q lam ≤ Work.LinnikContract.Ncount q lam') ∧
    (∀ (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q),
      0 ≤ Work.LinnikContract.boxAbs q K R χ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `InBox` is monotone in the radius `R`, componentwise.
    intro q R R' hR ρ hρ
    exact ⟨le_trans hρ.1 hR, le_trans hρ.2 hR⟩
  · -- `Ncount` is a cardinality of an upward-closed `Finset.filter`.
    intro q _ lam lam' h
    unfold Work.LinnikContract.Ncount
    exact Finset.card_le_card (by
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
      obtain ⟨ρ, hZ, hle⟩ := hχ
      exact ⟨ρ, hZ, le_trans hle h⟩)
  · -- `boxAbs` is a `∑ᶠ` of non-negative terms.
    intro q _ K R χ
    unfold Work.LinnikContract.boxAbs
    apply finsum_nonneg
    intro ρ
    split_ifs with h
    · exact mul_nonneg (by positivity) (norm_nonneg _)
    · exact le_refl 0

end Work.LinnikContract.API
