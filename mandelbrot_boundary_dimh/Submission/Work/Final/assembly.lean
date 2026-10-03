import Submission.Work.Wiring
import Submission.Work.Mset.mset
import Submission.Work.Param.param
import Submission.Work.Transfer.transfer
import Submission.Work.Motion.motion
import Submission.Work.Dim.dim
import Submission.Work.Fatou.fatouU
import Submission.Lib.UnifWrapper
import Submission.Work.Parab.parab
import Submission.Work.Pert.pert2_v2
import Submission.Work.Horn.horn
import Submission.Work.L61.l61
import Submission.Work.L62.l62c
import Submission.Work.F0Facts.f0facts
import Submission.Work.Repel.repel3

/-! Lead staging: the final assembly of the challenge from the area theorems (pert2_v2 still WIP). -/

open LeanEval.Dynamics.MandelbrotBoundary MeasureTheory

namespace Work.Final

theorem mandelbrot_boundary_dimh_assembled :
    dimH (frontier Mandelbrot) = 2 :=
  MandelDim.main_of_all Work.Mset.mset (Work.Param.param Work.Mset.mset)
    (Work.Transfer.transfer Work.Mset.mset Work.Motion.motion Work.Dim.dim)
    (Work.Fatou.fatouU MandelDim.uniformizationHyp) Work.Parab.parab Work.Pert.pert2_v2
    Work.Horn.horn Work.L61.l61 Work.L62.l62c Work.F0Facts.f0facts Work.Repel.repel3

end Work.Final
