import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjCut_multiplier_gain
import Submission.Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3 / Symbol calculus, step 7: the *cross-chart pair* operator

The target `Work.Diff.STE.B3.ENormB_pair_J_commutator_v2` reduces (see its `SESSION 14` header
block) to the two-chart pair operators

  `X = M_{a}(Λ^k M_b V − S_ε M_b L̂) + M_c(L̂ M_d S_ε − V M_d Λ^k)`,

where

* `Λ^k = lapPow k` is the flat Laplacian power in the *chart-1* variable,
* `V = conjCut ρ ε T T'` is the chart-2 Friedrichs cutoff `S_ε` read in chart-1 variables,
* `L̂ = conjLapPow k T T'` is the chart-2 Laplacian power read in chart-1 variables,
* `S_ε = flatCut ρ ε` is the chart-1 cutoff,
* `T : chart-1 coordinates → chart-2 coordinates` is the chart transition, `T' = T⁻¹`,
* `a, b, c, d` are the smooth weights produced by the transfers and the partition of unity; in the
  application they satisfy `a * b = c * d` (both products equal the square `ψ_m²` of the *other*
  chart's localised weight).

The operator `X` is of order `2k` term by term; the estimate needs it to be of order `2k − 1`,
which holds exactly because the four leading symbols cancel pairwise once `a * b = c * d`.

This file only *defines* `pairOp`; its order reduction is the theorem
`Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_le` (delegated).
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep7

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **two-chart transfer pair operator** of the `[Qk, J]` commutator estimate: the pairing
`⟨x, X v⟩` against it is the contribution of a single chart pair `{l, m}` to
`Ξ = ENormB_pair k (J f) u − ENormB_pair k f (J u)`, after transporting everything to the
chart-`l` variable.  Its four terms are of order `2k` individually; its order is `2k − 1`. -/
def pairOp (k : ℕ) (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (a b c d : (ι → ℝ) → ℂ) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => a x * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)
    + c x * (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
        (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
      - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x)

end Work.Diff.STE.B3.SymCalcStep7
