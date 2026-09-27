import Submission.UnifDeps
import Submission.GreenInterface
import Submission.BoundedHolomorphic
import Submission.Work.Potential.removable_singularity_of_bounded_near
import Submission.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Work.Potential.Defs
import Submission.RiemannSurface
import Submission.Holomorphic
import Submission.HolomorphicLog
import Submission.Conjugate
import Submission.Extremal
import Submission.ExtremalExist
import Submission.ExtremalInj
import Submission.ExtremalOnto
import Submission.Packaging
import Submission.PackagingOpen
import Submission.Endgame
import Submission.Endgame2
import Submission.GreenData
import Submission.GreenModulus
import Submission.GreenFunctionX
import Submission.Sweep
import Submission.SweepMember
import Submission.GreenConditional
import Submission.ChartLogClamp
import Submission.MaxPrincipleX
import Submission.MaxPrincipleRegion
import Submission.Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero
import Submission.Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
import Submission.Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
import Submission.Work.Parabolic.Basic
import Submission.Work.Parabolic.Model

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
