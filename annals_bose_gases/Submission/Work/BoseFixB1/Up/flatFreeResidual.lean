import ChallengeDeps
import Submission.Work.BoseFixB1.Up.flatFreeResidual_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB1.Up.flatFreeResidual` — the flat branch of FS `thm:smallbox`

The single residual of the `Up/` chapter: the *flat (condensed)* branch of FS
`thm:smallbox` at the sliding box `B(u)`, with a **free** threshold `γ` — i.e. there is
`γ > 0` such that every non-thin box, low state satisfies `PerBoxF` whenever the box's
excited count is at most `γ·(n‖Φ‖²)`.

Everything else of the per-box target is already proved and axiom-clean in this cone:
the gap branch at every threshold (`Up.gapAtAll`), the thin (degenerate-box) case
(`Up.perBoxF_thin_holds`), the three-way assembly (`Up.perBoxFWeight_of_flatFree`), the
fixed-threshold conversion (`Up.flatFreeResidual_of_flatAtomShape`), and the corpus's
sharp flat ledger `Work.BoseFixB1S.perBoxF_of_ledger_sharp`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The flat-branch residual** (free threshold, free constants): there is *some* positive
threshold `γ` at which the flat (condensed) branch of FS `thm:smallbox` at the sliding box
holds, with *some* positive coefficient `c₁` and *some* error constant `C`. -/
theorem flatFreeResidual {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    FlatFreeResidual v h R :=
  flatFreeResidual_holds h hv hv1 hvrad hR hv_supp hav

end Work.BoseFixB1.Up
