import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R2.Clauses
import Submission.Work.FTS.RegPkgGal.R2.Repair
import Submission.Work.FTS.RegPkgGal.R2.angIntegral_le
import Submission.Work.FTS.RegPkgGal.R2.integrableOn_pth_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The repaired Taylor packages, unconditional

The two unconditional versions of the repaired statement, obtained by discharging the analytic
inputs of `Repair.lean`:

* `tay_clauses_nbhd` — the shape adopted by the repaired interface (`R2b`): `hsm` is taken on a
  neighbourhood of the closed angular range, `z ∈ (-1, ∞)`, `θ ∈ (-1, π/2+1)`;
* `tay_clauses_of_continuous` — the version with the *minimal* extra hypothesis, namely
  continuity of the angular slices `θ ↦ g z θ τ` on `Iθ` (for `0 < z ≤ 2`).

Both are proved with no `PLACEHOLDER` and with no axiom beyond `propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-- **The repaired Taylor clauses, in the shape of the repaired interface (`R2b`).**

This is the statement of `tay_clauses` with the *single* change that the joint `C¹` hypothesis
is assumed on a neighbourhood of the closed angular range (`θ ∈ (-1, π/2+1)` and `z > -1`)
instead of only on the open quadrant.  That extra smoothness makes the angular slices `C¹`
across the two angular endpoints, which is exactly what the counterexample
(`Work.FTS.RegPkgGal.R2.tay_clauses_refuted`) shows to be necessary. -/
theorem tay_clauses_nbhd {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) :=
  tay_clauses_nbhd_aux hα hα1 hS hCθ hK hQ hsm hd hvt hquad hlinz (angIntegral_le hα hα1)

/-- **The repaired Taylor clauses with the minimal extra hypothesis.**

The hypotheses of `tay_clauses` are kept verbatim (the joint `C¹` hypothesis is still taken on
the open quadrant) and one hypothesis is *added*: each angular slice `θ ↦ g z θ τ` is continuous
on `Iθ` (for `0 < z ≤ 2`).  This is precisely the information that the counterexample of
`Work.FTS.RegPkgGal.R2.tay_clauses_refuted` violates, and it is physically necessary (a jump of
the slice at `θ = 0` would be a discontinuity of the vorticity across the plane `x₃ = 0`). -/
theorem tay_clauses_of_continuous {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z)
    (hcontθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 < z → z ≤ 2 →
      ContinuousOn (fun θ => g z θ τ) Work.Spaces.Iθ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) :=
  tay_clauses_of_continuous_aux hα hα1 hS hCθ hK hQ hsm hd hvt hquad hlinz hcontθ
    (angIntegral_le hα hα1)
    (fun τ hτ z hz => integrableOn_pth_slice (g := fun z θ => g z θ τ) hα hα1 hCθ hz
      (hsm τ hτ) (fun θ hθ => hd τ hτ z θ (le_of_lt hz) hθ))

end Work.FTS.RegPkgGal.R2
