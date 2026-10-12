import ChallengeDeps
import Submission.Work.BoseB1Cube.psiWeight_integral_four_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomRouteCubeFree` — the loop-free FS route, **closed**

Holder of `Submission/Work/BoseB1Cube/cubeCrudeBand_holds.lean`.  Read `FINDING_nomRouteCube.md`
(§1 the route, §2 the `eq:appTB` exponent typo, §3 the residual chain) and
`NOTE_appTB_exponent_typo.md`.

`nomRouteCube.lean` assembled FS's own route to the assigned node `Work.BoseB1Cube.CubeCrudeBand v h`
but left the slot-doubling conditional on the abstract analytic input `PsiWeightFourIntegral`
(the integral form of `ψ(1,4μ,t) ≤ 4ψ(1,μ,t) + 12μ²`).  This module supplies that input from the
PROVED `Work.BoseB1Cube.psiWeight_integral_four_le` and therefore closes the chain:

    CubeCrudeBand v h
      ⟸ PerBoxFNomSlots v h R          (`cubeCrudeBand_of_perBoxFNomSlots`, PROVED, sorry-free)
      ⟸ PerBoxFNomMu v h R             (`perBoxFNomSlots_of_perBoxFNomMu`, below)

with everything between the last line and the node itself either a theorem of the corpus
(`slidingGoodCube`, `countWindowOfNominal`) or arithmetic proved in `nomRouteCube.lean`.  So the
assigned node is reduced to the **single** statement `PerBoxFNomMu v h R` — FS `thm:smallbox`
(`final_v2.tex:3907`) at the sliding box, in FS's own *nominal* (indicator-count) spelling, at the
single chemical-potential slot `μ` — which per `FINDING_nomRouteCube.md` §2–§3 *is* FS's published
row (same word, same demand), the outer band and the count-window loop not appearing at all.

The reason this needs its own module: `psiWeight_integral_four_le.lean` imports `nomRouteCube.lean`,
so the wiring cannot live in the latter.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`PsiWeightFourIntegral`** — the sole analytic input of the slot doubling — from the PROVED
`Work.BoseB1Cube.psiWeight_integral_four_le`. -/
theorem psiWeightFourIntegral_holds : PsiWeightFourIntegral :=
  fun ℓ d μ u n Φ hℓ hd hμ hV hΦ => psiWeight_integral_four_le hℓ hd hμ u Φ hV hΦ

/-- **`PerBoxFNomSlots` from the one-slot nominal row.**  The two chemical-potential slots that FS
use (`μ` on `I₋` and `4μ` on the boundary layer) are one statement: the doubled slot costs only a
quarter of `c₁` and a `max · 1` on the error constant. -/
theorem perBoxFNomSlots_of_perBoxFNomMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hMu : PerBoxFNomMu v h R) :
    PerBoxFNomSlots v h R :=
  perBoxFNomSlots_of_slotMu h hv hvrad hR hv_supp psiWeightFourIntegral_holds hMu

/-- **THE ASSIGNED NODE FROM FS's ONE-SLOT NOMINAL ROW ALONE.**

`Work.BoseB1Cube.CubeCrudeBand v h` from `Work.BoseB1Cube.PerBoxFNomMu v h R` (FS `thm:smallbox` at
the sliding box, nominal spelling, slot `μ`) — the whole chain of `nomRouteCube.lean` plus the
`ψ`-arithmetic, with no count window, no outer band and no loop. -/
theorem cubeCrudeBand_of_slotMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hMu : PerBoxFNomMu v h R) : CubeCrudeBand v h :=
  cubeCrudeBand_of_perBoxFNomSlots h hv hv1 hvrad hR hv_supp hav
    (perBoxFNomSlots_of_perBoxFNomMu h hv hvrad hR hv_supp hMu)

end Work.BoseB1Cube
