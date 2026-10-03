import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass
import Submission.Work.FIArea5.S16Hecke.existsPrimarySplit
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne

namespace Work.FIArea6Hecke

theorem heckeStripNearOne (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    Work.FIArea6Hecke.StripNearOne ε :=
  Work.FIArea6Hecke.R.heckeStripNearOne ε hε hε4

end Work.FIArea6Hecke
