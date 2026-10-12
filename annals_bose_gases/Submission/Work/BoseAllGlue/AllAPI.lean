import Mathlib.Order.Filter.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.AllDefs
import Submission.Work.BoseBoxFock.RB67FS_of_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseAllGlue.AllAPI` — the `All` instruments for the D3 glue

`Submission.Work.BoseBoxFock.AllDefs` (frozen) carries the `All` vocabulary of design
item 5: `Q3KernelFSAll`, `RViewFSAll`, `KzDatum.viewFSAll`, `valFSAll`
(`BoseBoxFock/KzAll.lean`), `RB4boxDomAtAll`/`RB4boxDomFSAll`, `RB5FSAll(K)`,
`RB67FSAll`, `BogOpBoundFSAll`, `controlWordHiAll`, `Control3QFSAll`,
`HonestGateAt(FS)All`.  What was missing is the *analytic* instrument bundle that the
four glue ports consume, namely the `All` forms of

* FS `eq:SimplifyKz` (`KzOpFS_decomp`, `BoseBoxFock/RB67FS_of_pieces.lean`) — the
  decomposition of the substituted Hamiltonian `KzOpFSAll` into the `c`-number, the
  Bogoliubov quadratic, the χ-mode number term, the Control3Q word and the gap reserve;
* the quadratic-form (`qw`) form of that decomposition;
* the `KzValFS`-API `KzValFS_le_of_bound` (`BoseFixR/NodeRestrictedBFS.lean`) — the
  reduction of an operator form bound to a lower bound on the window infimum.

They are exactly the three instruments that the ports of `RB67FS_of_pieces` and
`NodeRestrictedBFS` replace.  `KzOpFSAll` and `controlWordHiAll` differ from
`KzOpFS`/`controlWordHi` by the *same* operator
`Q₂^ex`-label-`0` row `Q2exAll - Q2ex` (`Work.BoseRowQ2.KzBridge`:
`KzOpFSAll_eq_KzOpFS_add_sub`), so the decomposition is *derived* from the frozen
one rather than re-proved: add the row to both sides, and recognise
`controlWordHi + (Q2exAll - Q2ex) = controlWordHiAll`.

Everything here is sorry-free and axiom-clean.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseAllGlue

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The Control3Q words -/

/-- **`controlWordHiAll` is `controlWordHi` plus the label-`0` row of `Q₂^ex`.** -/
theorem controlWordHiAll_eq (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) :
    controlWordHiAll T E = controlWordHi T E + (F.Q2exAll E - F.Q2ex E) := by
  simp only [controlWordHiAll, controlWordHi]
  abel

/-- The same with the environment re-pointed at `KzEnvAt E ρ` (`KzEnvAt` does not change
`F.Q2ex`, so the replacement is *not* definitionally the first lemma). -/
theorem controlWordHiAll_KzEnvAt_eq (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    controlWordHiAll T (KzEnvAt E ρ)
      = controlWordHi T (KzEnvAt E ρ) + (F.Q2exAll (KzEnvAt E ρ) - F.Q2ex (KzEnvAt E ρ)) := by
  simp only [controlWordHiAll, controlWordHi]
  abel

/-! ## 2. FS `eq:SimplifyKz` in the `All` vocabulary -/

/-- **FS `eq:SimplifyKz`, `All` form**: `KzOpFSAll` is the `c`-number plus the Bogoliubov
quadratic `KzBogFS`, the χ-mode number term, the `All` Control3Q word
`controlWordHiAll`, minus the `RHi`-restricted diagonal word and the remaining gap
reserve `(b/2 − b/50)·gapOpT`.

Derived from the frozen `KzOpFS_decomp` by adding the label-`0` row
`Q2exAll − Q2ex` (`Work.BoseRowQ2.KzOpFSAll_eq_KzOpFS_add_sub`) to both sides: the row
is *also* the difference between `controlWordHiAll` and `controlWordHi`. -/
theorem KzOpFSAll_decomp (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (hℓ : E.ell ≠ 0) (hd : E.d ≠ 0) :
    KzOpFSAll F T E gHat0 ρ
      = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) • (1 : F.H →ₗ[ℝ] F.H)
        + KzBogFS F E ρ
        + (((ρ - E.mu) * E.W1 0) • (∑ k : Mode, F.nOp k))
        + controlWordHiAll T (KzEnvAt E ρ)
        - F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ))
        + (E.b / 2 - E.b / 50) • T.gapOpT (KzEnvAt E ρ) := by
  rw [Work.BoseRowQ2.KzOpFSAll_eq_KzOpFS_add_sub,
    Work.BoseBoxFock.KzOpFS_decomp F T E gHat0 ρ hℓ hd,
    controlWordHiAll_KzEnvAt_eq]
  abel

/-- The `qw`-form of `KzOpFSAll_decomp`. -/
theorem qw_KzOpFSAll_eq (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (hℓ : E.ell ≠ 0) (hd : E.d ≠ 0) (f : F.H) :
    F.qw f (KzOpFSAll F T E gHat0 ρ)
      = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) * F.normSq f
        + F.qw f (KzBogFS F E ρ)
        + ((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k)
        + F.qw f (controlWordHiAll T (KzEnvAt E ρ))
        - F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        + (E.b / 2 - E.b / 50) * F.qw f (T.gapOpT (KzEnvAt E ρ)) := by
  rw [KzOpFSAll_decomp F T E gHat0 ρ hℓ hd]
  simp only [Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_sub,
    Work.BoseB7.FockData.qw_smul, Work.BoseBoxFock.qw_one]

/-! ## 3. The `valFSAll` API -/

/-- **`KzValFSAll_le_of_bound`**: a lower bound valid for every (nonzero) window state
bounds the window infimum of `KzOpFSAll` — the `All` form of
`Work.BoseFixR.KzValFS_le_of_bound` (`BoseFixR/NodeRestrictedBFS.lean`). -/
theorem KzValFSAll_le_of_bound (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ)
    (hne : Nonempty {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0}) {B : ℝ}
    (h : ∀ f : F.H, T.NWindow E.bigM f → f ≠ 0 →
      B * F.normSq f ≤ F.qw f (KzOpFSAll F T E gHat0 ρ)) :
    B ≤ KzValFSAll F T E gHat0 ρ := by
  letI := hne
  refine le_ciInf fun f => ?_
  rw [le_div_iff₀ (normSq_pos F f.2.2)]
  exact h f.1 f.2.1 f.2.2

/-- The `KzDatum` form of `KzValFSAll_le_of_bound` (the shape `NodeRestrictedBFS`
consumes). -/
theorem valFSAll_ge_of_bound (D : KzDatum) {ρ B : ℝ}
    (hne : Nonempty {f : D.F.H // D.T.NWindow D.E.bigM f ∧ f ≠ 0})
    (h : ∀ f : D.F.H, D.T.NWindow D.E.bigM f → f ≠ 0 →
      B * D.F.normSq f ≤ D.F.qw f (KzOpFSAll D.F D.T D.E D.gHat0 ρ)) :
    B ≤ D.valFSAll ρ :=
  KzValFSAll_le_of_bound D.F D.T D.E D.gHat0 ρ hne h

end Work.BoseAllGlue
