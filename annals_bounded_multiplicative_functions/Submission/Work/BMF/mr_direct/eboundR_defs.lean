import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.ebound_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Merged-frequency vocabulary for the range-extension error `eboundR`

This is the range analogue of `Submission/Work/BMF/mr_direct/ebound_defs.lean`.

`eboundR b c K P Q A B t` is a double sum over the pairs `(p, m)` with
`p ∈ primeSet P Q`, `m ∈ winIdxR K A B (jdex K p)` and `m ∉ natIcc (A/p) (B/p)`.
To apply the Montgomery--Vaughan mean value theorem we merge the pairs with equal product
`p * m`: they all contribute the same frequency `log (p*m)`.

* `ebnn ⟨p,m⟩ = p * m` is the merged frequency (as in the dyadic case);
* `ebγ` is the coefficient attached to a pair (as in the dyadic case);
* `pSetBR K P Q A B` is the index set of `eboundR`;
* `ebFiberR K P Q A B n` is the set of pairs in `pSetBR K P Q A B` with product `n`;
* `ebDR b c K P Q A B n` is the merged coefficient `Σ_{ebnn i = n} ebγ i`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- The range index set of `eboundR`, as a `sigma`-type. -/
def pSetBR (K P Q A B : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Work.BMF.mrDirect.primeSet P Q).sigma (fun (p : ℕ) =>
    (Work.BMF.mrDirect.winIdxR K A B (Work.BMF.mrDirect.jdex K p)).filter
      (fun (m : ℕ) => m ∉ Work.BMF.natIcc (A / p) (B / p)))

/-- The fibre of `ebnn` over `n` inside `pSetBR K P Q A B`. -/
def ebFiberR (K P Q A B : ℝ) (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (pSetBR K P Q A B).filter (fun i => ebnn i = n)

/-- The merged range coefficient `d n = Σ_{ebnn i = n} ebγ i`. -/
def ebDR (b c : ℕ → ℂ) (K P Q A B : ℝ) (n : ℕ) : ℂ :=
  ∑ i ∈ ebFiberR K P Q A B n, ebγ b c P Q i

/-- `eboundR` written as a single sum over the index set `pSetBR`, each pair `(p,m)` carrying
the coefficient `ebγ ⟨p,m⟩ = c p · b m · (ω(m;P,Q)+1)⁻¹` and the frequency `p * m`. -/
theorem eboundR_eq_sigma_sum (b c : ℕ → ℂ) (K P Q A B t : ℝ) :
    Work.BMF.mrDirect.eboundR b c K P Q A B t
      = ∑ i ∈ pSetBR K P Q A B,
          ebγ b c P Q i * (ebnn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  have key : ∀ (p m : ℕ),
      c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) *
        (b m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ebγ b c P Q ⟨p, m⟩ * (ebnn ⟨p, m⟩ : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    intro p m
    simp only [ebγ, ebnn]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  rw [Work.BMF.mrDirect.eboundR, pSetBR, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => key p m

/-- `eboundR` written as a single sum over the merged frequencies: for any finset `N` containing
the support `ebnn '' pSetBR` one has
`eboundR b c K P Q A B t = Σ_{n ∈ N} ebDR b c K P Q A B n · n^{-(1+it)}`. -/
theorem eboundR_eq_fiber_sum (b c : ℕ → ℂ) (K P Q A B t : ℝ) (N : Finset ℕ)
    (hN : ∀ i ∈ pSetBR K P Q A B, ebnn i ∈ N) :
    Work.BMF.mrDirect.eboundR b c K P Q A B t
      = ∑ n ∈ N, ebDR b c K P Q A B n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  rw [eboundR_eq_sigma_sum]
  rw [← Finset.sum_fiberwise_of_maps_to hN
    (fun i => ebγ b c P Q i * (ebnn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [ebDR, ebFiberR]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

end

end Work.BMF.mr_direct
