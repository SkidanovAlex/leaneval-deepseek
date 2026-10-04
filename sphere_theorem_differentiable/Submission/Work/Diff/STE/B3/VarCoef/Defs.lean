import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Variable-coefficient second-order operators on the flat torus (lead definitions, 2026-10-03)

`varLap A B g = -(Σ_{a,b} A a b · ∂_a ∂_b g + Σ_a B a · ∂_a g)`: the flat Laplacian `-Δ_z` of a chart `z`,
rewritten in another chart `y` (with `z = τ y`, `y = σ z`), has exactly this form, with
`A a b y = Σ_r ∂_r σ_a (τ y) · ∂_r σ_b (τ y)` and `B a y = Σ_r ∂_r ∂_r σ_a (τ y)`.  The sign makes
`varLap` the conjugate of `lapPow 1 = -lapC`.  `varLapPow k` is the `k`-fold iterate.

Route (lead, 2026-10-03): the commutator `[Q, J_l]` is computed in the chart `l` of the mollifier `J_l`.
The cutoff `S = flatCut` is never transported. Only the differential operator `Q_i = R_i^* Λ R_i` is
transported into chart `l`, where it becomes `c' · varLapPow k A B (c · ·)` (the lemma `lapPow_comp_eq_varLapPow`).
-/

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The variable-coefficient second-order operator `-(Σ A_ab ∂_a∂_b + Σ B_a ∂_a)`. -/
noncomputable def varLap (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => -((∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) x)
      + ∑ a, ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a g x)

/-- The `k`-fold iterate of `varLap A B`. -/
noncomputable def varLapPow (k : ℕ) (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) :
    ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ) :=
  (varLap A B)^[k]

end Work.Diff.STE.B3.VarCoef
