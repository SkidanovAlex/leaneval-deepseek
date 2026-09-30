import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.ebound_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Merging equal frequencies in the range-extension error `ebound`

`ebound b c K P Q X t` is a double sum over the pairs `(p, m)` in `pSetB K P Q X`.  Every pair
contributes the *same* frequency `log (p * m)` of the Dirichlet polynomial
`Σ γ i · (nn i)^{-(1+it)}`, so the pairs with equal product `p * m` may be merged and `ebound`
written as a Dirichlet polynomial indexed by the merged frequencies:

`ebound b c K P Q X t = Σ_n ebD b c K P Q X n · n^{-(1+it)}`,

where `ebD` is the merged coefficient.  The lemma below states this with the sum taken over an
arbitrary finset `N` containing the support `ebnn '' pSetB` (frequencies outside the support
contribute the empty fibre, hence `0`).
-/

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- `ebound` written as a single sum over the index set `pSetB`, each pair `(p,m)` carrying the
coefficient `ebγ ⟨p,m⟩ = c p · b m · (ω(m;P,Q)+1)⁻¹` and the frequency `p * m`. -/
theorem ebound_eq_sigma_sum (b c : ℕ → ℂ) (K P Q X t : ℝ) :
    Work.BMF.mrDirect.ebound b c K P Q X t
      = ∑ i ∈ Work.BMF.mrDirect.pSetB K P Q X,
          Work.BMF.mr_direct.ebγ b c P Q i * (Work.BMF.mr_direct.ebnn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  have key : ∀ (p m : ℕ),
      c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) *
        (b m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = Work.BMF.mr_direct.ebγ b c P Q ⟨p, m⟩ * (Work.BMF.mr_direct.ebnn ⟨p, m⟩ : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    intro p m
    simp only [Work.BMF.mr_direct.ebγ, Work.BMF.mr_direct.ebnn]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  rw [Work.BMF.mrDirect.ebound, Work.BMF.mrDirect.pSetB, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => key p m

theorem ebound_eq_fiber_sum (b c : ℕ → ℂ) (K P Q X t : ℝ) (N : Finset ℕ)
    (hN : ∀ i ∈ Work.BMF.mrDirect.pSetB K P Q X, Work.BMF.mr_direct.ebnn i ∈ N) :
    Work.BMF.mrDirect.ebound b c K P Q X t
      = ∑ n ∈ N, Work.BMF.mr_direct.ebD b c K P Q X n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  rw [ebound_eq_sigma_sum]
  -- Merge the pairs with equal product; the outer sum runs over `N ⊇ ebnn '' pSetB`.
  rw [← Finset.sum_fiberwise_of_maps_to hN
    (fun i => Work.BMF.mr_direct.ebγ b c P Q i *
      (Work.BMF.mr_direct.ebnn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
  refine Finset.sum_congr rfl fun n _ => ?_
  -- On each fibre the frequency `ebnn i` is constantly `n`, so it factors out of the sum.
  simp only [Work.BMF.mr_direct.ebD, Work.BMF.mr_direct.ebFiber]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

end

end Work.BMF.mr_direct
