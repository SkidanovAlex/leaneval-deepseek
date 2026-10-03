import Mathlib
import Submission.Work.ORReductions.Coherent.AssembleSemiring

/-!
# Injectivity of the semiring-level assembly map

`assembleS H K c = ∑ q, single (Quotient.out q) 1 * subgroupAlgMap H K (c q)` assembles an element
`c` of `(G ⧸ H) →₀ K[H]` into `K[G]`, for an arbitrary (not necessarily commutative) semiring `K`.

Here we prove that this assembly is injective.  The proof is by coefficient extraction: for
`q : G ⧸ H` and `h : H`, the coefficient of `Quotient.out q * h` in `assembleS H K c` is exactly
the coefficient of `h` in `c q`, because each summand
`single (Quotient.out q') 1 * subgroupAlgMap H K (c q')` is supported on the coset `q'`, and the
cosets are disjoint.  Applied to `assembleS H K c = 0` this gives `c q = 0` for every `q`.

This is the semiring-level counterpart of `SubgroupAlg.sum_coset_eq_zero`, which is stated only for
commutative semirings.
-/

namespace Work.ORReductions.Coherent

open MonoidAlgebra

/-- The coefficient of `assembleS H K c` at `Quotient.out q * h` is the coefficient of `c q` at
`h`: the summands of the assembly are supported on pairwise disjoint cosets. -/
lemma coeff_assembleS {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H) (q : G ⧸ H) (h : H) :
    (assembleS H K c).coeff (Quotient.out q * (h : G)) = (c q).coeff h := by
  classical
  rw [assembleS]
  rw [show c.sum (fun q' r => MonoidAlgebra.single (Quotient.out q') (1 : K) *
        Work.ORReductions.subgroupAlgMap H K r) =
      ∑ q' ∈ c.support, MonoidAlgebra.single (Quotient.out q') (1 : K) *
        Work.ORReductions.subgroupAlgMap H K (c q') from rfl]
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  trans ∑ q' ∈ c.support, (if q' = q then (c q').coeff h else 0)
  · refine Finset.sum_congr rfl fun q' _ => ?_
    by_cases hqq : q' = q
    · rw [if_pos hqq, hqq]
      exact Work.ORReductions.SubgroupAlg.coeff_single_mul_subgroupAlgMap_same H K q (c q) h
    · rw [if_neg hqq]
      exact Work.ORReductions.SubgroupAlg.coeff_single_mul_subgroupAlgMap_ne H K q' q h
        (c q') (fun hq => hqq hq.symm)
  · rw [Finset.sum_ite_eq']
    by_cases hq : q ∈ c.support
    · rw [if_pos hq]
    · rw [if_neg hq, Finsupp.notMem_support_iff.mp hq]
      rfl

theorem assembleS_injective {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H)
    (hc : Work.ORReductions.Coherent.assembleS H K c = 0) : c = 0 := by
  classical
  refine Finsupp.ext fun q => MonoidAlgebra.coeff_injective ?_
  refine Finsupp.ext fun h => ?_
  have hh := coeff_assembleS H K c q h
  rw [hc] at hh
  simpa using hh.symm

end Work.ORReductions.Coherent
