import ChallengeDeps
import Submission.Helpers
import Submission.Work.Final.assembly

open LeanEval.Dynamics.MandelbrotBoundary
open Function MeasureTheory

namespace Submission

theorem mandelbrot_boundary_dimh :
    dimH (frontier Mandelbrot) = 2 :=
  Work.Final.mandelbrot_boundary_dimh_assembled

end Submission
