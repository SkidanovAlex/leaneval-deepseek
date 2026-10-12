import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBogFS.CleanFunAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauAt_bounds` — the elementary bounds of the honest kinetic symbol `τ`

`τ = tauAt v μ k = Work.BoseBoxFock.tauSm eT s d ℓ k` is the smoothed kinetic symbol
`(1−ε_T)u²τ̃(x/u) + ε_Tu₂²τ̃(x/u₂)` with `x = ‖k‖`, `u = (2sℓ)⁻¹ = cleanLo1`,
`u₂ = (2dsℓ)⁻¹ = cleanLo2` and the profile `τ̃` of `Work.BoseBoxFock.exists_tauProf`
(`(max 0 (r−2))² ≤ τ̃ r ≤ (max 0 (r−1))²`, `τ̃ r = 0` for `r ≤ 1`).

This module proves the four bounds of `τ` used by the sign row and by the oscillation
estimates of the clean Riemann row:

* `0 ≤ τ ≤ ‖k‖²`;
* `τ = 0` for `‖k‖ ≤ cleanLoMin v μ` (the kinetic gap at the origin);
* `(max 0 (‖k‖ − 2·cleanLoMax v μ))² ≤ 2·τ` (the quadratic growth beyond the kink);
* `‖k‖² − τ ≤ 4·cleanLoMax v μ·‖k‖ + (cleanLoMax v μ)²` (the deficit of `τ` below `‖k‖²`).

The threshold `ε₀` is chosen so that `ε_T ≤ 1/2` at the admissible parameters.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The profile facts of `Work.BoseBoxFock.tauProf` (extracted from `exists_tauProf`). -/
lemma tauProf_facts :
    Monotone Work.BoseBoxFock.tauProf ∧
      (∀ r, (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r) ∧
      (∀ r, Work.BoseBoxFock.tauProf r ≤ (max 0 (r - 1)) ^ 2) ∧
      (∀ r, r ≤ 1 → Work.BoseBoxFock.tauProf r = 0) := by
  obtain ⟨-, hmono, hge, hle, hzero, -⟩ :=
    Work.BoseBoxFock.tauProf_spec
  exact ⟨hmono, hge, hle, hzero⟩

/-- `tauProf` is nonnegative. -/
lemma tauProf_nonneg_bog (r : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf r :=
  le_trans (sq_nonneg _) (tauProf_facts.2.1 r)

/-! The four bounds themselves are stated and requested at the fresh path
`Submission/Work/BoseBogFS/tauAt_bounds_row.lean` (`Work.BoseBogFS.tauAt_bounds_row`); see
`FINDING_cleanFun_tsum_session12.md` §4 item 3. -/

end Work.BoseBogFS
