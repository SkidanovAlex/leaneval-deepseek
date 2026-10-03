/-
# The fibre form of the arithmetic kernel of the twisted bilinear multiplier

This module records the `form-1`/`form-2` factorisation of Krause--Mirek--Tao, *Pointwise ergodic
theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022), in the shape in
which the large-scale (`§8`) analysis consumes it: the full kernel of `Btwist`,
`arithKernel ρ P q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`, is the average over the residues `n` of the
modulus `q` of the products of the two one-variable arithmetic factors

  `arithChar ρ l₁ (n - j₁) · cw m₁ j₁ · h (x - j₁)` and
  `arithChar ρ l₂ (P(n) - j₂) · cw m₂ j₂ · k (x - j₂)`.

The content is `Work.KMTAreas.A7.arithKernel_eq_arithChar` (in `Large/ArithFactor.lean`)
specialised to `q = arithQ ρ (max l₁ l₂)`, together with the distribution of the remaining
constants over the finite sum.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.ArithFactor

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- **Fibre form of the kernel of `Btwist`.**  Writing `q = arithQ ρ (max l₁ l₂)` for the common
period of the arithmetic frequencies of height `≤ max l₁ l₂`, the kernel of the twisted bilinear
multiplier is the average over the fibres `n ∈ ℤ/qℤ` of the product of the two arithmetic factors
attached to `(j₁,j₂)`:

`arithKernel ρ P q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂ · h (x-j₁) · k (x-j₂)
  = q⁻¹ ∑_{n < q} (arithChar ρ l₁ (n-j₁) · cw m₁ j₁ · h (x-j₁))
                · (arithChar ρ l₂ (P(n)-j₂) · cw m₂ j₂ · k (x-j₂))`.

This is `arithKernel_eq_arithChar` at `q = arithQ ρ (max l₁ l₂)`, with the constants `cw mᵢ jᵢ`,
`h (x-j₁)`, `k (x-j₂)` distributed over the finite sum. -/
theorem arithKernel_fiberTerm (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) (x j₁ j₂ : ℤ) :
    arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂
        * h (x - j₁) * k (x - j₂)
      = (arithQ ρ (max l₁ l₂) : ℂ)⁻¹ *
          ∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            (arithChar ρ l₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
              * (arithChar ρ l₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)) := by
  rw [arithKernel_eq_arithChar]
  rw [show (∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            (arithChar ρ l₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
              * (arithChar ρ l₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)))
        = (∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            (arithChar ρ l₁ ((n : ℤ) - j₁) * arithChar ρ l₂ (P.eval (n : ℤ) - j₂)))
            * (cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring]
  ring

end

end Work.KMTAreas.A7
