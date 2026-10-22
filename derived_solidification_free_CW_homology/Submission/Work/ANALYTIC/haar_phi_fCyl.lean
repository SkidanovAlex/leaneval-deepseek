import Mathlib
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ANALYTIC.HaarBasisDefs
import Submission.Work.ANALYTIC.haar_biorth

namespace Work.ANALYTIC

/-- Biorthogonality of the Haar/Schauder basis of `C(T,ℤ)`, specialised to the `ℕ`-indexed
functionals `phi T i` and basis elements `fCyl T j`: `phi T i (fCyl T j) = δ_{ij}`.
This is the diagonal case `Haar.phi_fCyl_self` together with the off-diagonal case
`haar_offdiag` (both in `Submission/Work/ANALYTIC/`). -/
theorem haar_phi_fCyl (T : LightProfinite.{0}) [Infinite T] (i j : ℕ) :
    Work.ANALYTIC.Haar.phi T i (Work.ANALYTIC.Haar.fCyl T j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact Haar.phi_fCyl_self T i
  · rw [if_neg h]
    exact haar_offdiag T i j h

end Work.ANALYTIC
