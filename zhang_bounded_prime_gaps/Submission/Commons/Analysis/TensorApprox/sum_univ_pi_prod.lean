import Mathlib
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_box

namespace Commons.Analysis.TensorApprox

/-- Factorization of a sum of tensor products over the whole function space: summing
`∏ i, g i (f i)` over all functions `f : ∀ i, κ i` equals the product of the one-variable sums.
This is the additive form of `Finset.prod_univ_sum`. -/
theorem sum_univ_pi_prod {ι : Type*} {κ : ι → Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (κ i)] [CommSemiring R] (g : ∀ i, κ i → R) :
    ∑ f : (∀ i, κ i), ∏ i, g i (f i) = ∏ i, ∑ j, g i j :=
  (Fintype.prod_sum g).symm

end Commons.Analysis.TensorApprox
