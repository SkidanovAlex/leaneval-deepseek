import Mathlib
import Submission.Work.BMF.mr_direct.dupExtraR_defs
import Submission.Work.BMF.mr_direct.dupExtra_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators

/-- The primes of `primeImgDR K P Q A B` are second components of elements of `pairSetD K P Q`. -/
lemma primeImgDR_subset_image (K P Q A B : ℝ) :
    primeImgDR K P Q A B ⊆ (pairSetD K P Q).image (fun y => y.2) := by
  intro p hp
  rw [primeImgDR, Finset.mem_image] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hx1 : x.1 ∈ pairSetD K P Q := by
    rw [pSetDR_eq_sigma] at hx
    exact (Finset.mem_sigma.mp hx).1
  rw [← hxp]
  exact Finset.mem_image.mpr ⟨x.1, hx1, rfl⟩

/-- The reciprocal sum over the primes of `primeImgDR` is at most the reciprocal sum over the
second components of `pairSetD`. -/
lemma primeImgDR_inv_sum_le (K P Q A B : ℝ) :
    ∑ p ∈ Work.BMF.mr_direct.primeImgDR K P Q A B, (1 : ℝ) / (p : ℝ)
      ≤ ∑ y ∈ Work.BMF.mr_direct.pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ) := by
  calc ∑ p ∈ primeImgDR K P Q A B, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ ((pairSetD K P Q).image (fun y => y.2) : Finset ℕ), (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
          (primeImgDR_subset_image K P Q A B)
          (fun i _ _ => div_nonneg zero_le_one (Nat.cast_nonneg i))
    _ ≤ ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ) :=
        sum_image_le_of_nonneg (pairSetD K P Q) (fun y => y.2) (fun n => (1 : ℝ) / (n : ℝ))
          (fun n => by positivity)

end Work.BMF.mr_direct
