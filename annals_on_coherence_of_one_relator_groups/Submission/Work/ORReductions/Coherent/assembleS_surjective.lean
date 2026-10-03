import Mathlib
import Submission.Work.ORReductions.Coherent.AssembleSemiring

/-!
# Surjectivity of the assembly map `(G ⧸ H) →₀ K[H] → K[G]` over a semiring

`assembleS H K c = ∑ q, single (Quotient.out q) 1 * subgroupAlgMap H K (c q)` assembles a
finitely supported family of elements of `K[H]`, one for each left coset of `H`, into an element
of `K[G]`.  Here we show that this map is surjective for an arbitrary *semiring* `K`: every
`x : K[G]` is the sum of its coset components, each of which is placed on its coset using the
chosen representative `Quotient.out`.

The proof requires no commutativity of `K`, only the additive lemmas for `Finsupp.sum` and the
multiplication rule `single a r * single b s = single (a * b) (r * s)` for the monoid algebra.
-/

namespace Work.ORReductions.Coherent

open MonoidAlgebra

/-- The assembly map is additive in its argument. -/
lemma assembleS_add {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    (c c' : (G ⧸ H) →₀ MonoidAlgebra K H) :
    assembleS H K (c + c') = assembleS H K c + assembleS H K c' := by
  classical
  rw [assembleS, assembleS, assembleS]
  exact Finsupp.sum_add_index (by intro q _; simp)
    (by intro q _ a b; rw [map_add, mul_add])

/-- The assembly map commutes with finite sums. -/
lemma assembleS_finset_sum {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    {ι : Type*} (s : Finset ι) (F : ι → (G ⧸ H) →₀ MonoidAlgebra K H) :
    assembleS H K (∑ i ∈ s, F i) = ∑ i ∈ s, assembleS H K (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [assembleS]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, assembleS_add, ih]

/-- The assembly map on a single coset component. -/
lemma assembleS_single {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    (q : G ⧸ H) (r : MonoidAlgebra K H) :
    assembleS H K (Finsupp.single q r) =
      MonoidAlgebra.single (Quotient.out q) (1 : K) * subgroupAlgMap H K r := by
  rw [assembleS, Finsupp.sum_single_index (by simp)]

theorem assembleS_surjective {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    (x : MonoidAlgebra K G) :
    ∃ c : (G ⧸ H) →₀ MonoidAlgebra K H,
      Work.ORReductions.Coherent.assembleS H K c = x := by
  classical
  refine ⟨∑ g ∈ x.coeff.support, Finsupp.single (SubgroupAlg.cosetOf H g)
      (MonoidAlgebra.single (SubgroupAlg.cosetLog H (SubgroupAlg.cosetOf H g) g)
        (x.coeff g)), ?_⟩
  rw [assembleS_finset_sum]
  rw [show (∑ g ∈ x.coeff.support, assembleS H K (Finsupp.single (SubgroupAlg.cosetOf H g)
        (MonoidAlgebra.single (SubgroupAlg.cosetLog H (SubgroupAlg.cosetOf H g) g)
          (x.coeff g)))) =
      ∑ g ∈ x.coeff.support, MonoidAlgebra.single g (x.coeff g) from
    Finset.sum_congr rfl fun g _ => by
      rw [assembleS_single, SubgroupAlg.subgroupAlgMap_single,
        MonoidAlgebra.single_mul_single, one_mul, SubgroupAlg.out_mul_cosetLog H rfl]]
  exact MonoidAlgebra.sum_coeff_single x

end Work.ORReductions.Coherent
