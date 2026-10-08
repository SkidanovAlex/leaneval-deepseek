import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.commutator_subgroupOf_eq_commutator
import Submission.Work.NormalComplement.exists_ppow_notMem_of_dvd_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement

namespace Work.NormalComplement

/-- For a nontrivial finite solvable subgroup `E` and every prime `p | [E : E']` there is a
`p`-element of `E` outside `E'`.  Route: `E ≠ ⊥` plus solvability forces `E' ≠ E` (else the derived
series is constantly `⊤`), so `E/E'` is a nontrivial finite abelian group and Cauchy in the quotient
(`Work.NPC.Frobenius.pResidual` machinery not needed: use `exists_prime_orderOf_dvd_card'` on the
quotient group `↥E ⧸ (⁅E,E⁆).subgroupOf E`) gives `a ∈ E` whose image has order `p`; replacing `a`
by its `p`-part `a ^ m` (`orderOf a = p ^ k * m`, `p ∤ m`) gives the required `p`-element: it lies
outside `E'` because its image is `(aE')^m ≠ 1`. -/
theorem primes_of_abelianization : Work.NormalComplement.PrimesOfAbelianizationProp := by
  intro G _ _ E _hEne _hsol p hp hdiv
  -- `⁅E,E⁆`, viewed inside `↥E`, is the derived subgroup `commutator ↥E`.
  have hsub : (⁅E, E⁆).subgroupOf E = commutator ↥E := commutator_subgroupOf_eq_commutator E
  -- hence `p` divides the index of `commutator ↥E` in `↥E`.
  have hdiv' : p ∣ (commutator ↥E).index := by
    have h1 : p ∣ ((⁅E,E⁆).subgroupOf E).index := hdiv
    rwa [hsub] at h1
  -- Cauchy's theorem in the abelianisation, together with the `p`-part of a lift.
  obtain ⟨y₀, hy₀, k, hk⟩ :=
    exists_ppow_notMem_of_dvd_index (H := ↥E) (N := commutator ↥E) hp hdiv'
  refine ⟨(y₀ : G), y₀.2, ?_, k, ?_⟩
  · rw [← hsub] at hy₀
    simpa [Subgroup.mem_subgroupOf] using hy₀
  · rw [Subgroup.orderOf_coe]
    exact hk

end Work.NormalComplement
