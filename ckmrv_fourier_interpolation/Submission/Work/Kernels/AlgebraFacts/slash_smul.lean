/-
# `slash` is `ℂ`-linear in the group-algebra variable

The weight-`k` action `slash k r F = ∑_γ c_γ · (F ∣[k] γ)` of the group algebra
`R = ℂ[SL(2,ℤ)]` on functions `ℍ → ℂ` is `ℂ`-linear in `r`: scaling the coefficients of
`r` scales the resulting function. This is the elementary algebra fact behind the
`ℂ`-module structure on the spaces `Ann_k(J, 𝒫)` of CKMRV Section 4.2.
-/
import Mathlib
import Submission.Work.Kernels.GroupAlgebra

namespace Work.Kernels.AlgebraFacts

/-- The action `slash k · F` is `ℂ`-linear in the group-algebra element. -/
lemma slash_smul (k : ℤ) (c : ℂ) (r : Work.Kernels.R) (F : UpperHalfPlane → ℂ) :
    Work.Kernels.slash k (c • r) F = c • Work.Kernels.slash k r F := by
  -- Unfold the definition and push the scalar `c` through the coefficients of `r`.
  have h1 : (c • r).coeff.sum (fun γ a => a • SlashAction.map k γ F)
      = r.coeff.sum (fun γ a => (c * a) • SlashAction.map k γ F) := by
    rw [MonoidAlgebra.coeff_smul]
    exact Finsupp.sum_smul_index (h := fun γ a => a • SlashAction.map k γ F)
      (fun _ => zero_smul ℂ _)
  have h2 : c • r.coeff.sum (fun γ a => a • SlashAction.map k γ F)
      = r.coeff.sum (fun γ a => c • (a • SlashAction.map k γ F)) := Finsupp.smul_sum
  rw [Work.Kernels.slash, Work.Kernels.slash, h1, h2]
  refine Finsupp.sum_congr (fun γ _ => ?_)
  exact mul_smul c (r.coeff γ) _

end Work.Kernels.AlgebraFacts
