import Mathlib
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea6.TauPieces.CleanSumEqTsum

namespace Work.FIArea6

theorem S16CleanSum_eq_Tsum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    (∑ z ∈ Work.FITop.boxN Pa, Work.FIArea6.S16CleanSummand Pa chi m p z)
      = Work.FIArea6Hecke.Tsum Pa chi m p :=
  Work.FIArea6.TauPieces.CleanSumEqTsum Pa chi m p hpsupp

end Work.FIArea6
