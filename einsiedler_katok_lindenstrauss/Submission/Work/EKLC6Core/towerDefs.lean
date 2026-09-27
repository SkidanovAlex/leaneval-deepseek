import Mathlib
import Submission.Work.EKLC6Core.Basic

/-!
# `Work.EKLC6Core.towerDefs` — vocabulary of the return-time tower (Pisa 7.49)

For an open set `Ω ⊆ X₃` and the map `x ↦ aDiag t • x`, the *first-return set* of level `i ≥ 1`
is the set of points of `Ω` whose first return to `Ω` happens at time `i`, and the
*never-returning set* is the set of points of `Ω` whose forward orbit never meets `Ω` again.
`Ω` is the disjoint union of the `firstReturnSet t Ω i` (`i ≥ 1`) and `neverReturnSet t Ω`
(this is the partition `Q̃` of Pisa 7.49: `Q_i = firstReturnSet t Ω i` and `Q_∞` is the
never-returning part, which is `μ`-null by Poincaré recurrence).

These are the cells of the tower from which the coding partition of Pisa 7.51 is built by
smearing in the `G⁻(t)`-direction and splitting transversally.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The `i`-th **first-return set** of `Ω` (`i ≥ 1`): points of `Ω` that come back to `Ω` at time
`i` but at no earlier positive time. -/
def firstReturnSet (t : Fin 3 → ℝ) (Ω : Set X3) (i : ℕ) : Set X3 :=
  Ω ∩ ((fun y : X3 => aDiag t • y)^[i]) ⁻¹' Ω ∩
    ⋂ j ∈ Finset.Icc 1 (i - 1), (((fun y : X3 => aDiag t • y)^[j]) ⁻¹' Ω)ᶜ

/-- The **never-returning set** of `Ω`: points of `Ω` no positive iterate of which lies in `Ω`. -/
def neverReturnSet (t : Fin 3 → ℝ) (Ω : Set X3) : Set X3 :=
  Ω ∩ ⋂ j ∈ {j : ℕ | 1 ≤ j}, (((fun y : X3 => aDiag t • y)^[j]) ⁻¹' Ω)ᶜ

end Work.EKLC6Core
