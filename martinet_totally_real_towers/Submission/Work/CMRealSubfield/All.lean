import Submission.Work.CMRealSubfield.Defs
import Submission.Work.CMRealSubfield.Archimedean
import Submission.Work.CMRealSubfield.CMBasic
import Submission.Work.CMRealSubfield.Walls
import Submission.Work.CMRealSubfield.Reduction
import Submission.Work.CMRealSubfield.Bridge
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le
import Submission.Work.CMRealSubfield.RootDiscr.pow_rootDiscr_eq_abs_discr
import Submission.Work.CMRealSubfield.RootDiscr.pow_discr_dvd_discr
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_algebra
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr
import Submission.Work.CMRealSubfield.RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield
import Submission.Work.CMRealSubfield.RealSubfield.le_finrank_maximalRealSubfield_of_two_mul_le
import Submission.Work.CMRealSubfield.RealSubfield.finrank_maximalRealSubfield_eq_finrank_of_isTotallyReal
import Submission.Work.CMRealSubfield.RealSubfield.natAbs_discr_maximalRealSubfield_sq_dvd
import Submission.Work.CMRealSubfield.RealSubfield.discr_maximalRealSubfield_sq_dvd
import Submission.Work.CMRealSubfield.RealSubfield.abs_discr_maximalRealSubfield_sq_le
import Submission.Work.CMRealSubfield.RealSubfield.rootDiscr_maximalRealSubfield_le_of_isCMField
import Submission.Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank

/-!
# `Submission.Work.CMRealSubfield`: the whole chapter in one import

Imports every module of the maximal-real-subfield reduction, so that a consumer can
`import Submission.Work.CMRealSubfield.All` and see the complete interface.  See
`Submission/Work/CMRealSubfield/README.md` for the map of the area and the entry points.
-/
