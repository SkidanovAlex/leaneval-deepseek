import Mathlib
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORFP2.CosetProj
import Submission.Work.ORFP2.sum_coset_comp_eq_self
import Submission.Work.ORFP2.projH_mul_transferHom
import Submission.Work.ORReductions.Coherent.ker_le_span_mapRange_alt
import Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup

/-!
# Injectivity of a relation matrix over `K[H]` lifts to `K[G]`

Let `H ≤ G` be a subgroup and `K` a commutative semiring.  The group algebra `K[G]` is free as a
left `K[H]`-module, with basis given by the coset representatives `Quotient.out q` indexed by the
left cosets `q ∈ G ⧸ H`; equivalently
`K[G] = ⨁_{q ∈ G ⧸ H} single (out q) 1 * K[H]`.  The identification of `K[G]` with the direct sum
`(G ⧸ H) →₀ K[H]` is the `K`-linear map `assemble` of
`Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup`, whose basic properties are that
it is injective, that it is compatible with right multiplication by elements of `K[H]`
(`assemble_mapRange_mul`), and that the coefficient of `assemble c` on the `q`-th coset is the
coefficient of `c q` (`coeff_sum_coset`).

The main theorem below is the algebraic core of the flatness of `K[G]` over `K[H]`: if the
`K[H]`-linear relation matrix `Finsupp.linearCombination K[H] y` is injective, then so is the
`K[G]`-linear relation matrix `Finsupp.linearCombination K[G] (subgroupAlgMap H K ∘ y)`.

The proof decomposes a finitely supported family `c : ι →₀ K[G]` into its `K[H]`-valued coset
components `rc j : (G ⧸ H) →₀ K[H]` (so that `assemble (rc j) = c j`).  Since `assemble` converts
multiplication by `subgroupAlgMap H K (y j)` into multiplication of the components by `y j`, the
value `Finsupp.linearCombination K[G] (φ ∘ y) c` is the assembly of the family
`q ↦ ∑ j, (rc j) q * y j`.  Comparing two families with the same image and extracting the `q`-th
coset component produces two `K[H]`-valued coefficient vectors with the same image under
`Finsupp.linearCombination K[H] y`; injectivity of the latter forces `(rc j) q = (rd j) q` for all
`j` and `q`, whence `c = d`.
-/

namespace Work.ORReductions.SubgroupAlg

open MonoidAlgebra

variable {G : Type*} [Group G] {K : Type*} [CommSemiring K]

/-- `assemble` is injective: the decomposition of `K[G]` into its `K[H]`-components along the left
cosets of `H` is faithful.  Read off the coefficient of `assemble c` at `Quotient.out q * h`, which
by `coeff_sum_coset` is the coefficient of `c q` at `h`. -/
lemma assemble_injective (H : Subgroup G) : Function.Injective (assemble H K) := by
  intro c c' h
  refine Finsupp.ext fun q => MonoidAlgebra.ext (Finsupp.ext fun hh => ?_)
  have h2 := congrArg (fun z : MonoidAlgebra K G => z.coeff (Quotient.out q * ((hh : H) : G))) h
  rw [assemble_apply, assemble_apply, coeff_sum_coset H K c q hh,
      coeff_sum_coset H K c' q hh] at h2
  exact h2

/-- The value at `j` of a finite sum of `Finsupp.single`s is the `j`-th coefficient, and `0` when
`j` is not an index of the sum. -/
lemma finset_sum_single_apply {α : Type*} {M : Type*} [AddCommMonoid M] [DecidableEq α]
    (s : Finset α) (f : α → M) (j : α) :
    (∑ i ∈ s, (Finsupp.single i (f i) : α →₀ M)) j = if j ∈ s then f j else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  exact Finset.sum_ite_eq' s j f

/-- The value of `Finsupp.linearCombination` on a coefficient vector which is a finite sum of
singletons. -/
lemma linearCombination_single_sum_eq {H : Subgroup G} {ι : Type*}
    (y : ι → MonoidAlgebra K H) (s : Finset ι) (f : ι → MonoidAlgebra K H) :
    Finsupp.linearCombination (MonoidAlgebra K H) y (∑ j ∈ s, Finsupp.single j (f j))
      = ∑ j ∈ s, f j * y j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.linearCombination_single, smul_eq_mul]

/-- The `q`-th coset component of the assembled family `∑ j, (r j).mapRange (· * y j)`: it is
`∑ j, (r j) q * y j`. -/
lemma mapRange_sum_apply {ι : Type*} (H : Subgroup G) (y : ι → MonoidAlgebra K H)
    (c : ι →₀ MonoidAlgebra K G) (r : ι → (G ⧸ H) →₀ MonoidAlgebra K H) (q : G ⧸ H) :
    (∑ j ∈ c.support, (r j).mapRange (fun a => a * y j) (by simp)) q
      = ∑ j ∈ c.support, (r j) q * y j := by
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.mapRange_apply]

/-- The fundamental computation: assembling the family of coset components
`q ↦ ∑ j, (rc j) q * y j` of a coefficient vector `c : ι →₀ K[G]` computes
`Finsupp.linearCombination K[G] (subgroupAlgMap H K ∘ y) c`. -/
lemma assemble_decomposition {ι : Type*} (H : Subgroup G) (y : ι → MonoidAlgebra K H)
    (c : ι →₀ MonoidAlgebra K G) (r : ι → (G ⧸ H) →₀ MonoidAlgebra K H)
    (hr : ∀ j, assemble H K (r j) = c j) :
    assemble H K (∑ j ∈ c.support, (r j).mapRange (fun a => a * y j) (by simp))
      = Finsupp.linearCombination (MonoidAlgebra K G)
          (fun j : ι => Work.ORReductions.subgroupAlgMap H K (y j)) c := by
  rw [assemble_finset_sum]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [assemble_mapRange_mul, hr j, smul_eq_mul]

theorem linearCombination_injective_subgroup {G : Type*} [Group G] (H : Subgroup G)
    (K : Type*) [CommSemiring K] {ι : Type*} (y : ι → MonoidAlgebra K H)
    (hy : Function.Injective (Finsupp.linearCombination (MonoidAlgebra K H) y)) :
    Function.Injective (Finsupp.linearCombination (MonoidAlgebra K G)
      (fun j : ι => Work.ORReductions.subgroupAlgMap H K (y j))) := by
  classical
  intro c d hcd
  choose rc hrc using fun j : ι => exists_assemble_eq H K (c j)
  choose rd hrd using fun j : ι => exists_assemble_eq H K (d j)
  -- Both coefficient vectors assemble to the same `K[H]`-valued family over the cosets.
  have hW : (∑ j ∈ c.support, (rc j).mapRange (fun a => a * y j) (by simp))
      = (∑ j ∈ d.support, (rd j).mapRange (fun a => a * y j) (by simp)) := by
    apply assemble_injective (K := K) H
    rw [assemble_decomposition H y c rc hrc, assemble_decomposition H y d rd hrd, hcd]
  -- Components of a coefficient vector supported off `c.support` vanish.
  have hrc0 : ∀ j ∉ c.support, rc j = 0 := by
    intro j hj
    refine assemble_injective (K := K) H ?_
    rw [hrc j, Finsupp.notMem_support_iff.mp hj, map_zero]
  have hrd0 : ∀ j ∉ d.support, rd j = 0 := by
    intro j hj
    refine assemble_injective (K := K) H ?_
    rw [hrd j, Finsupp.notMem_support_iff.mp hj, map_zero]
  -- Compare the `q`-th coset components.
  have hrcq : ∀ (j : ι) (q : G ⧸ H), (rc j) q = (rd j) q := by
    intro j q
    have hq := congrArg (fun z : (G ⧸ H) →₀ MonoidAlgebra K H => z q) hW
    rw [mapRange_sum_apply, mapRange_sum_apply] at hq
    -- The two `K[H]`-valued coefficient vectors with the same image under
    -- `Finsupp.linearCombination K[H] y`.
    have hkey : Finsupp.linearCombination (MonoidAlgebra K H) y
          (∑ j' ∈ c.support, Finsupp.single j' ((rc j') q))
        = Finsupp.linearCombination (MonoidAlgebra K H) y
          (∑ j' ∈ d.support, Finsupp.single j' ((rd j') q)) := by
      rw [linearCombination_single_sum_eq, linearCombination_single_sum_eq]
      exact hq
    have h2 := hy hkey
    have h3 : (∑ j' ∈ c.support, Finsupp.single j' ((rc j') q) : ι →₀ MonoidAlgebra K H) j
        = (rc j) q := by
      rw [finset_sum_single_apply]
      by_cases hj : j ∈ c.support
      · rw [if_pos hj]
      · rw [if_neg hj, hrc0 j hj, Finsupp.zero_apply]
    have h4 : (∑ j' ∈ d.support, Finsupp.single j' ((rd j') q) : ι →₀ MonoidAlgebra K H) j
        = (rd j) q := by
      rw [finset_sum_single_apply]
      by_cases hj : j ∈ d.support
      · rw [if_pos hj]
      · rw [if_neg hj, hrd0 j hj, Finsupp.zero_apply]
    rw [← h3, h2, h4]
  -- Hence the two components agree, and so do `c` and `d`.
  refine Finsupp.ext fun j => ?_
  rw [← hrc j, ← hrd j]
  exact congrArg (assemble H K) (Finsupp.ext fun q => hrcq j q)

end Work.ORReductions.SubgroupAlg
