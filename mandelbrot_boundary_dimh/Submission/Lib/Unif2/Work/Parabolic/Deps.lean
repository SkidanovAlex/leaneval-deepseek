import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.GreenInterface
import Submission.Lib.Unif2.BoundedHolomorphic
import Submission.Lib.Unif2.Work.Potential.removable_singularity_of_bounded_near
import Submission.Lib.Unif2.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Lib.Unif2.Work.Potential.Defs
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Holomorphic
import Submission.Lib.Unif2.HolomorphicLog
import Submission.Lib.Unif2.Conjugate
import Submission.Lib.Unif2.Extremal
import Submission.Lib.Unif2.ExtremalExist
import Submission.Lib.Unif2.ExtremalInj
import Submission.Lib.Unif2.ExtremalOnto
import Submission.Lib.Unif2.Packaging
import Submission.Lib.Unif2.PackagingOpen
import Submission.Lib.Unif2.Endgame
import Submission.Lib.Unif2.Endgame2
import Submission.Lib.Unif2.GreenData
import Submission.Lib.Unif2.GreenModulus
import Submission.Lib.Unif2.GreenFunctionX
import Submission.Lib.Unif2.Sweep
import Submission.Lib.Unif2.SweepMember
import Submission.Lib.Unif2.GreenConditional
import Submission.Lib.Unif2.ChartLogClamp
import Submission.Lib.Unif2.MaxPrincipleX
import Submission.Lib.Unif2.MaxPrincipleRegion
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero
import Submission.Lib.Unif2.Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
import Submission.Lib.Unif2.Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
import Submission.Lib.Unif2.Work.Parabolic.Basic
import Submission.Lib.Unif2.Work.Parabolic.Model

/-!
# Imports for the parabolic subproject

A single import giving all the library modules the parabolic chapter (`Submission/Work/Parabolic/`)
builds on: the holomorphic/harmonic layer of the Riemann-surface development, the extremal-function
machinery, the packaging of bijective holomorphic maps as complex diffeomorphisms, the Riemann
mapping theorem (first half), and this subproject's own `Basic`/`Model` modules.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

namespace Work.Parabolic

end Work.Parabolic
