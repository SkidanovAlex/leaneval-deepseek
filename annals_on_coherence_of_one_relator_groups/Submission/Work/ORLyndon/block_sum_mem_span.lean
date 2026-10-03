import Mathlib
import Submission.Work.ORLyndon.cosetFinsetDefs

namespace Work.ORLyndon

/-- Let `w : G` and `l : ℕ`.  For any element `h` of the right coset finset `cosetFinset w l t`
(written as `h = t * w ^ k`, `k < l`) the difference `of h - of t` lies in the left ideal generated
by `of w - 1`: indeed `of (t * w ^ k) - of t = of t * (of w ^ k - 1)` and
`of w ^ k - 1 = (∑ i < k, of w ^ i) * (of w - 1)`. -/
theorem of_sub_of_mem_span_coset {G : Type*} [Group G] [DecidableEq G] {K : Type*} [Field K]
    (w : G) (l : ℕ) (t : G) {h : G} (hh : h ∈ cosetFinset w l t) :
    MonoidAlgebra.of K G h - MonoidAlgebra.of K G t ∈
      Ideal.span ({MonoidAlgebra.of K G w - 1} : Set (MonoidAlgebra K G)) := by
  classical
  set I : Ideal (MonoidAlgebra K G) :=
    Ideal.span ({MonoidAlgebra.of K G w - 1} : Set (MonoidAlgebra K G)) with hI
  have hw1 : MonoidAlgebra.of K G w - 1 ∈ I := Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨k, _, rfl⟩ := mem_cosetFinset.mp hh
  have h2 : MonoidAlgebra.of K G (t * w ^ k) - MonoidAlgebra.of K G t
      = MonoidAlgebra.of K G t * (MonoidAlgebra.of K G w ^ k - 1) := by
    rw [map_mul, map_pow, mul_sub, mul_one]
  rw [h2]
  refine Ideal.mul_mem_left I _ ?_
  rw [← geom_sum_mul (MonoidAlgebra.of K G w) k]
  exact Ideal.mul_mem_left I _ hw1

theorem block_sum_mem_span {G : Type*} [Group G] [DecidableEq G] {K : Type*} [Field K]
    (w : G) (l : ℕ) (a : MonoidAlgebra K G) (t : G) {s : Finset G}
    (hsub : ∀ h ∈ s, h ∈ cosetFinset w l t) :
    (∑ h ∈ s, a.coeff h • MonoidAlgebra.of K G h) -
        (∑ h ∈ s, a.coeff h) • MonoidAlgebra.of K G t ∈
      Ideal.span ({MonoidAlgebra.of K G w - 1} : Set (MonoidAlgebra K G)) := by
  classical
  set I : Ideal (MonoidAlgebra K G) :=
    Ideal.span ({MonoidAlgebra.of K G w - 1} : Set (MonoidAlgebra K G)) with hI
  have key : ∀ h ∈ s, MonoidAlgebra.of K G h - MonoidAlgebra.of K G t ∈ I :=
    fun h hs => of_sub_of_mem_span_coset w l t (hsub h hs)
  have hX : (∑ h ∈ s, a.coeff h • MonoidAlgebra.of K G h) -
        (∑ h ∈ s, a.coeff h) • MonoidAlgebra.of K G t
      = ∑ h ∈ s, a.coeff h • (MonoidAlgebra.of K G h - MonoidAlgebra.of K G t) := by
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun h _ => (smul_sub _ _ _).symm)
  rw [hX]
  refine Ideal.sum_mem I (fun h hs => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left I _ (key h hs)

end Work.ORLyndon
