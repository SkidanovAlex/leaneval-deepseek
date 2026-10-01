import Mathlib
import Submission.Work.ZeroDensity.Defs

namespace Work.ZeroDensity.Deuring

/-- If every zero `ρ` (of any character mod `q`), other than the exceptional pair `(χ₁,β₁)`, has
`λ(ρ) ≥ c_r·log(1/λ(β₁))`, then there is no pair counted by `restCount χ₁ β₁ t` as soon as
`t < c_r·log(1/λ(β₁))`.  Indeed every summand of the (multiplicity weighted) count is either zero or
satisfies the repulsion hypothesis, whose conclusion contradicts the bound `λ(ρ) ≤ t`. -/
theorem restCount_eq_zero_of_lt_repulsion {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q}
    {β₁ : ℂ} {c_r : ℝ}
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      |ρ.im| ≤ 1 → ¬(χ = χ₁ ∧ ρ = β₁) →
        c_r * Real.log (1 / Work.LinnikContract.lamOf q β₁) ≤ Work.LinnikContract.lamOf q ρ)
    {t : ℝ} (ht : t < c_r * Real.log (1 / Work.LinnikContract.lamOf q β₁)) :
    Work.ZeroDensity.restCount χ₁ β₁ t = 0 := by
  rw [Work.ZeroDensity.restCount, Work.LinnikAreas.Siegel.pairCount]
  refine Finset.sum_eq_zero fun χ _ => ?_
  refine finsum_eq_zero_of_forall_eq_zero fun ρ => ?_
  rw [if_neg]
  rintro ⟨hz, hlam, him, hne⟩
  have h := hrep χ ρ hz him hne
  linarith

end Work.ZeroDensity.Deuring
