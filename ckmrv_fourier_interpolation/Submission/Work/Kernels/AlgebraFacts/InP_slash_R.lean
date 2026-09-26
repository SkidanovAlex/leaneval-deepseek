import Mathlib
import Submission.Work.Kernels.GroupAlgebra
import Submission.Work.Kernels.Slash

namespace Work.Kernels.AlgebraFacts

lemma InP_slash_R {F : UpperHalfPlane → ℂ} (hF : Work.Kernels.InP F) (k : ℤ)
    (r : Work.Kernels.R) : Work.Kernels.InP (Work.Kernels.slash k r F) := by
  rw [Work.Kernels.slash]
  have hsum : r.coeff.sum (fun γ c => c • SlashAction.map k γ F)
      = ∑ γ ∈ r.coeff.support, (r.coeff γ) • SlashAction.map k γ F :=
    Finsupp.sum_of_support_subset r.coeff (subset_refl _)
      (fun γ c => c • SlashAction.map k γ F) (fun i _ => by simp)
  rw [hsum]
  refine InP.sum r.coeff.support (fun γ _ => ?_)
  simpa only [Pi.smul_def, smul_eq_mul] using
    InP.const_mul (r.coeff γ) (InP.slash hF k γ)

end Work.Kernels.AlgebraFacts
