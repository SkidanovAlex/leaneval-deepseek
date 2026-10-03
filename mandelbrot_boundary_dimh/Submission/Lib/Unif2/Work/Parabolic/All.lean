import Submission.Lib.Unif2.Work.Parabolic.Basic
import Submission.Lib.Unif2.Work.Parabolic.Model
import Submission.Lib.Unif2.Work.Parabolic.Deps
import Submission.Lib.Unif2.Work.Parabolic.harmonicOnX_comp_biholomorph
import Submission.Lib.Unif2.Work.Parabolic.holomorphicOnX_comp_biholomorph
import Submission.Lib.Unif2.Work.Parabolic.isOpenMap_of_injective_holomorphic
import Submission.Lib.Unif2.Work.Parabolic.injFamily_nonempty_of_isOpenEmbedding_of_not_surjective
import Submission.Lib.Unif2.Work.Parabolic.isCompact_closure_superlevel_greenUpperHalfPlane
import Submission.Lib.Unif2.Work.Parabolic.hasGreenFunctionAt_iUHP
import Submission.Lib.Unif2.Work.Parabolic.Transport
import Submission.Lib.Unif2.Work.Parabolic.isParabolic_complex
import Submission.Lib.Unif2.Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact
import Submission.Lib.Unif2.Work.Parabolic.unbounded_near_pole_of_isGreenFunctionAt
import Submission.Lib.Unif2.Work.Parabolic.uniformization_of_greenFunctionAt
import Submission.Lib.Unif2.Work.Parabolic.Reduction
import Submission.Lib.Unif2.Work.Parabolic.Main

/-!
# `Work.Parabolic`: the parabolic case, one import

A single import for the whole parabolic subproject.  The main entry points are (namespace
`Work.Parabolic`):

* `IsGreenFunctionAt`, `HasGreenFunctionAt`, `HasGreenFunction`, `IsParabolic`, `IsHyperbolic`
  (`Basic.lean`) — the Green-function notion with *relative* compactness of the superlevel sets;
* `plane_of_no_greenFunction`, `plane_of_no_greenFunction_of_dichotomy` (`Main.lean`) — the
  parabolic branch of uniformization, conditional on the two classical inputs;
* `not_exists_hasGreenFunctionWeak_of_not_compact` — the reason the raw (compact superlevel set)
  formulation of `Submission.HasGreenFunctionWeak` cannot be used;
* `raw_shape_hypothesis_holds_and_conclusion_fails`, `not_plane_of_no_greenFunction_raw`
  (`Main.lean`) — the certificate that the originally requested shape of the statement is false;
* `uniformization_of_greenFunctionAt` — the hyperbolic endgame with the corrected hypothesis;
* `hasGreenFunctionAt_iUHP`, `isParabolic_complex`, `Transport.lean`, `Reduction.lean` — the model
  cases, conformal invariance and the reduction lemmas.
-/
