import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.DomainTiling
import Submission.Work.Asymptotics.Mp_smul_mem_closure_DomainD
import Submission.Work.Asymptotics.closure_DomainD_subset_iUnion_Mp
import Submission.Work.Asymptotics.fd_subset_DomainD
import Submission.Work.Asymptotics.reduction_bound
import Submission.Work.Asymptotics.carry_bound
import Submission.Work.Asymptotics.sigma_entry_bound
import Submission.Work.Asymptotics.PropagateCarries
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.CarryDefs
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.PropagateBounds.EvenBound
import Submission.Work.Asymptotics.PropagateBounds.OddBound

namespace Work.Asymptotics

/-- CKMRV Proposition 3.2(2) with the linear dependence on the constants (declare in namespace
`Work.Asymptotics`).  A holomorphic function `f` on `ℍ` satisfying the two transformation laws
`(T-I)²f = h₁` and `S(T-I)²f = h₂` on all of `ℍ` (the predicate
`Work.Asymptotics.Propagates k Set.univ f h₁ h₂`), whose defects obey a moderate-growth bound
with the same exponent `Nf`, and which has moderate growth on `𝒟`, has moderate growth on `ℍ`
with constants depending only on `Nf` and `k`, not on `Cf`, `C₁`, `C₂`. -/
theorem bound_of_propagates {k : ℤ} {f h₁ h₂ : UpperHalfPlane → ℂ}
    (h : Work.Asymptotics.Propagates k Set.univ f h₁ h₂) {Nf Cf C₁ C₂ : ℝ}
    (hCf : 0 ≤ Cf) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ τ ∈ Work.Asymptotics.DomainD, ‖f τ‖ ≤ Cf * (Work.Kernels.scale τ) ^ Nf)
    (hh₁ : ∀ τ : UpperHalfPlane, ‖h₁ τ‖ ≤ C₁ * (Work.Kernels.scale τ) ^ Nf)
    (hh₂ : ∀ τ : UpperHalfPlane, ‖h₂ τ‖ ≤ C₂ * (Work.Kernels.scale τ) ^ Nf) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Cf + C₁ + C₂) * (Work.Kernels.scale τ) ^ N := by
  rcases k.even_or_odd with hk | hk
  · exact Work.Asymptotics.bound_of_propagates_even hk h hCf hC₁ hC₂ hf hh₁ hh₂
  · exact Work.Asymptotics.bound_of_propagates_odd hk h hCf hC₁ hC₂ hf hh₁ hh₂

end Work.Asymptotics
