import ChallengeDeps
import Submission.Work.BoseBoxFock.AllDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ZPLatticeDefs` — the `N`-free zero-point row (`ZPLatticeRow`)

Verbatim from `Submission/Work/BOSE_ALL_STATEMENTS.lean.txt` (item 8): FS `lem:BogIntegral`
on the **full** dual lattice `ℤ³`, with no cut-off and no cube, in finite-subset form.  It is
the `N`-free replacement for the cube/cut-off zero-point route, which is dead because the
gate forces `N ≳ ℓ/R` while the mesh route needs `N ≲ K_ℓ²`.

`Work.BoseBogFS.hZP_of_lattice` reduces the honest cube/cut-off zero-point sum to this row
(the summands are `≥ 0` and `ZP` is increasing in `|ℬ|` on `|ℬ| ≤ 𝒜`), and
`Work.BoseBoxFock.BogOpBoundFSAll` is then reached with `ZPLatticeRow` as the only analytic
input.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS `lem:BogIntegral` on the **full** dual lattice, no cut-off, no cube: `N`-free.
(Finite-subset form; the `ZP` summands are `≥ 0`.) -/
def ZPLatticeRow (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C₄ : ℝ, 0 < ε₀ ∧ 0 ≤ C₄ ∧ ∀ μ : ℝ, Adm v ε₀ μ → ∀ ρ : ℝ,
    Work.BoseBoxFock.CloseCondFS v μ ρ → ∀ S : Finset (Fin 3 → ℤ),
      ∑ n ∈ S, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          (Work.BoseBoxFock.tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s (paramsAt μ (a v)).d
              (ell v μ) ((ell v μ)⁻¹ • Work.BoseB4.vec n)
            + ρ * chat (W1fun v h (ell v μ)) ((ell v μ)⁻¹ • Work.BoseB4.vec n))
          (ρ * chat (W1fun v h (ell v μ)) ((ell v μ)⁻¹ • Work.BoseB4.vec n))
        ≤ -(4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2 * chat (W1omegaFun v h (ell v μ)) 0
          + C₄ * errBracket v R μ

end Work.BoseBogFS
