/-
  Subproject WilE9G — import hub (everything proved in this directory, except the deliverable).

  The deliverable `Work.WilE9G.EffStratAE_of_frozen` lives in
  `Submission/Work/WilE9G/EffStratAE_of_frozen.lean`; it is NOT imported here, because its own
  auxiliary modules (`WilE9G/Assembly/*`) import THIS module.  To get everything, import

      Submission.Work.WilE9G.EffStratAE_of_frozen

  which pulls in `All` transitively.
-/
import Submission.Work.WilE9G.Defs
import Submission.Work.WilE9G.Basic
import Submission.Work.WilE9G.Collapse
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Reduce
import Submission.Work.WilE9G.Jac
import Submission.Work.WilE9G.Cover.stratProj_eq_of_isPreconnected
import Submission.Work.WilE9G.Sard.volume_image_univ_eq_zero_of_lt
import Submission.Work.WilE9G.Sard.morseSard
import Submission.Work.WilE9G.Sard.exists_null_of_Good
import Submission.Work.WilE9G.G1
import Submission.Work.WilE9G.Mult.exists_multiplier_of_ambStratum_fibre
import Submission.Work.WilE9G.Cover
import Submission.Work.WilE9G.Mat.det_ne_zero_iff_rank_eq_card
import Submission.Work.WilE9G.Fubini.ae_null_slice_of_null
import Submission.Work.WilE9G.Lagrange.Defs
import Submission.Work.WilE9G.Lagrange.exists_lagrange_stratum
import Submission.Work.WilE9G.Lagrange.exists_null_of_degenerate
import Submission.Work.WilE9G.Frozen
import Submission.Work.WilE9G.Amb.stratum_zero_to_amb
