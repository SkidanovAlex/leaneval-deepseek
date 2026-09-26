import ChallengeDeps
import Submission.Work.CKFinal.ckmrv_of_satisfiesThm31_smooth
import Submission.Work.CKFinal.exists_thm31_pair

open LeanEval.Analysis.CKMRVInterpolation
open Filter Topology
open scoped FourierTransform SchwartzMap

namespace Submission

theorem ckmrv_fourier_interpolation :
    CKMRV 8 1 ∧ CKMRV 24 2 := by
  obtain ⟨F8, Ft8, h8, hs8, hst8, he8, het8, -⟩ := Work.CKFinal.exists_thm31_pair 8 1 (Or.inl rfl)
  obtain ⟨F24, Ft24, h24, hs24, hst24, he24, het24, hdec⟩ :=
    Work.CKFinal.exists_thm31_pair 24 2 (Or.inr rfl)
  exact Work.CKFinal.ckmrv_of_satisfiesThm31_smooth F8 Ft8 h8 hs8 hst8 he8 het8
    F24 Ft24 h24 hs24 hst24 he24 het24 (hdec rfl).1 (hdec rfl).2

end Submission

