import Mathlib
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.pairRegLinBase
import Submission.Work.Drive.linShearIncidence
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.rowB_linTrans_pairReg_openDense

/-!
# Row B (R1) of the `refParityFamily` lane: the pair row of the two transported linear models

`Work.Drive.RefParityFamily` needs, among its seven class-level rows, the *pair* row

> `PairReg (model (linBase A 0) ⟨blk 0 t⟩) (model (linBase A 1) ⟨blk 1 t⟩)`

where `model Φ ⟨τ⟩ = linTransClass Φ τ cl hcl` is the class map of the transported linear disk model.
This module states it for the design's parameter space `ℝ¹² = (ℝ⁴)³`, as an open set `R` of parameters
dense at every point of the closed unit ball.

The row is the `hpairL0L1` row (`R1`) of `Submission/Work/Drive/REFPARITY_PLAN.md` §9; its producer is
the twin lemma `Work.Drive.rowB_linTrans_pairReg_openDense` of the design lane
(`Submission/Work/Drive/rowB_linTrans_pairReg_openDense.lean`), which proves it by reducing `PairReg`
to the six incidence conditions of `Work.Drive.pairReg_linPlaneCharts_of_incidence` on the transported
planes, checking them at the diagonal `t = 0` (`Work.Drive.linIncidence_linBase`) and propagating them
by the identity principle for analytic functions (`Work.Drive.isOpen_denseAtBall_ne_zero`) — the
witnesses at the diagonal are exactly the design lane's `linIncidence_linBase`.
-/

namespace Work.Drive

/-- **Row B / R1.** `PairReg` of the two per-block transported linear models holds on an open set of
parameters dense at every point of the closed unit ball. -/
theorem refRowB_pairReg_openDense (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧ Work.Drive.DenseAtBall R ∧
      ∀ t ∈ R, Work.Drive.PairReg
        (Work.Drive.linTransClass (Work.Drive.linBase A 0) (Work.Drive.blk 0 t) cl hcl)
        (Work.Drive.linTransClass (Work.Drive.linBase A 1) (Work.Drive.blk 1 t) cl hcl) :=
  rowB_linTrans_pairReg_openDense A cl hcl

end Work.Drive
