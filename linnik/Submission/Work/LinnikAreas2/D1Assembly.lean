/-
# LinnikAreas2 — a second (assembly) route to `D1`, built on the §11 ingredients

This module contains the §11 assembly of HB Lemma 11.1 (`Di` in the contract) written by the
`area4_r2` agent, as a fallback/complement to the dedicated `d1_of_area1` worker: it reuses the
*proved* ingredients (`Density4.zero_detector`, `Density4.psi_weighted_eval`,
`Density4.theta_diag_eval`, `LinnikAreas2.hb11_offdiag_pair_bound`, the coefficient calculus
`acoef`/`bcoef`/`tsum_acoef_mul_bcoef` and the closing step `d1_of_weighted` of
`LinnikAreas2.d1_of_area1`), plus the three interface lemmas
`LinnikAreas2.theta_diag_sharp` (HB (11.17) *with* the subtraction),
`LinnikAreas2.hb15_operator_bound` (HB (11.15)) and `LinnikAreas2.duality_tsum`
(the `ℓ²(ℕ)` duality principle).

`NOTE_area4_r2_D1_plan.md` records the overall plan and, in particular, why the *subtracted*
diagonal estimate is needed for the constant `67/6`.
-/
import Mathlib
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas.Density4.zero_detector
import Submission.Work.LinnikAreas.Density4.theta_diag_eval
import Submission.Work.LinnikAreas.Density4.duality_principle
import Submission.Work.LinnikAreas.Density4.Parent
import Submission.Work.A7.lamChar_api
import Submission.Work.LinnikAreas2.D2Aux

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedVariables false

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-! ## 1. The set `S` of characters with a box zero, and its enumeration by minimising zeros -/

/-- The characters mod `q` carrying a zero in the working region with `λ ≤ lamMax q` — the index
set of HB's `N(λ₀)` (round-2 `D1`'s sum). -/
def hbSet (q : ℕ) [NeZero q] : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun χ => ∃ ρ, Work.LinnikContract2.IsZ χ ρ ∧
    Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q)

theorem mem_hbSet {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} :
    χ ∈ hbSet q ↔ ∃ ρ, Work.LinnikContract2.IsZ χ ρ ∧
      Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q := by
  simp [hbSet]

/-- HB's weighted count in the shape consumed by `d1_of_weighted`:
`Σ_{χ ∈ S} 2w·λ(χ)/(e^{73λ(χ)/30} - e^{16λ(χ)/15})`, `S` = the characters with a box zero. -/
def wSum (q : ℕ) [NeZero q] (w : ℝ) : ℝ :=
  ∑ χ ∈ hbSet q,
    2 * w * Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ)

/-- The HB weight of the contract, in the `lamChar` form used by `d1_of_weighted`. -/
theorem wHB_lamChar_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (w : ℝ) :
    2 * w * Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ)
      = 2 * Work.LinnikContract2.lamChar χ * w
          / (Real.exp (73/30 * Work.LinnikContract2.lamChar χ)
              - Real.exp (16/15 * Work.LinnikContract2.lamChar χ)) := by
  rw [Work.LinnikContract2.wHB]
  ring

/-- `wSum` in the explicit rational shape of the contract's `d1_of_weighted` hypothesis. -/
theorem wSum_eq (q : ℕ) [NeZero q] (w : ℝ) :
    wSum q w = ∑ χ ∈ hbSet q,
      2 * Work.LinnikContract2.lamChar χ * w
        / (Real.exp (73/30 * Work.LinnikContract2.lamChar χ)
            - Real.exp (16/15 * Work.LinnikContract2.lamChar χ)) := by
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  exact wHB_lamChar_eq q χ w

end Work.LinnikAreas2
