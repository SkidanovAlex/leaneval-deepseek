import ChallengeDeps
import Submission.Work.BoseBogFS.close_rho_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Arith` — the §11 arithmetic of `BogOpBoundFS`

`bogOpBound_at` consumes one arithmetic hypothesis (`hArith`): the §7–§11 error display
fits into the free constant `Capp` of the §11 bracket.  This module supplies it from the
pieces:

* the `(ρ−μ)²` slot of the `𝒞`-sum — `close_rho_sq_le` (the `1/(2¹⁴π)` of `F9`);
* the `Ezero` slot (the `10¹⁰ε(μ,ρ_z)` and lattice-mesh errors of
  `Work.BoseB6Est.fsZeroPoint_le`) — bounded by `Work.BoseFixR.errAbs`, hence by
  `errBracket` through `errAbs_le_errBracket`;
* the reserve slot `Res` (`½Kbar + ½S + 3G` of `qw_dNumOpR_le`).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The §11 arithmetic `hArith` of `bogOpBound_at`**, from the three slots. -/
theorem hArith_of_pieces (v : ℝ³ → ℝ) (R μ ρ δ Ezero Res C₄ C₅ C₀ gHat0 : ℝ)
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (ht : dil v μ ≤ 1)
    (hg : gHat0 = 8 * π * _root_.BoseGases.a v)
    (hclose : |ρ - μ| ≤ closeThresholdFS v μ)
    (hδ : δ ≤ C₀ * dil v μ * (R / _root_.BoseGases.a v) ^ 2) (hC₀ : 0 ≤ C₀)
    (hEzero : Ezero ≤ C₄ * errBracket v R μ) (hRes : Res ≤ C₅ * errBracket v R μ)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅) :
    Ezero + Res + (ρ - μ) ^ 2 * (gHat0 / 2) * ell3 v μ * δ
      ≤ (C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1) * errBracket v R μ := by
  have h3 := close_rho_sq_le v R μ ρ δ C₀ gHat0 hav hμ ht hg hclose hδ hC₀
  nlinarith [h3, hEzero, hRes]

end Work.BoseBogFS
