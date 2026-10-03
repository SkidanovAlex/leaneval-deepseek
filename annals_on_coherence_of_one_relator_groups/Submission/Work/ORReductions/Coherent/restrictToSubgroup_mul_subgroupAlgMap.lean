import Mathlib
import Submission.Work.ORReductions.Coherent.SubgroupRestriction
import Submission.Work.ORReductions.Coherent.restrictToSubgroup_subgroupAlgMap
import Submission.Work.ORReductions.SubgroupAlg

namespace Work.ORReductions.Coherent

open MonoidAlgebra

variable {G : Type*} [Group G]

/-- Right `K[H]`-linearity of `restrictToSubgroup` on a single basis element of `K[G]`. -/
theorem restrictToSubgroup_single_mul_subgroupAlgMap (H : Subgroup G) (K : Type*) [Semiring K]
    (g : G) (d : K) (t : MonoidAlgebra K H) :
    Work.ORReductions.Coherent.restrictToSubgroup H K
        (MonoidAlgebra.single g d * Work.ORReductions.subgroupAlgMap H K t) =
      Work.ORReductions.Coherent.restrictToSubgroup H K (MonoidAlgebra.single g d) * t := by
  classical
  refine Finsupp.induction (motive := fun c : H →₀ K =>
    Work.ORReductions.Coherent.restrictToSubgroup H K
        (MonoidAlgebra.single g d *
          Work.ORReductions.subgroupAlgMap H K (MonoidAlgebra.ofCoeff c)) =
      Work.ORReductions.Coherent.restrictToSubgroup H K (MonoidAlgebra.single g d) *
        MonoidAlgebra.ofCoeff c) t.coeff ?_ ?_
  · simp
  · intro h e f _ _ ih
    have h1 : MonoidAlgebra.ofCoeff (Finsupp.single h e + f) =
        MonoidAlgebra.single h e + MonoidAlgebra.ofCoeff f := by
      rw [MonoidAlgebra.ofCoeff_add, MonoidAlgebra.ofCoeff_single]
    have h2 : Work.ORReductions.subgroupAlgMap H K (MonoidAlgebra.single h e) =
        MonoidAlgebra.single (h : G) e :=
      Work.ORReductions.SubgroupAlg.subgroupAlgMap_single H K h e
    rw [h1, map_add, mul_add, map_add, mul_add, ih, h2]
    rw [MonoidAlgebra.single_mul_single]
    by_cases hg : g ∈ H
    · rw [Work.ORReductions.Coherent.restrictToSubgroup_single_of_mem H K (g * (h : G)) (d * e)
          (H.mul_mem hg h.2),
        Work.ORReductions.Coherent.restrictToSubgroup_single_of_mem H K g d hg,
        MonoidAlgebra.single_mul_single]
      congr 1
    · have hnot : g * (h : G) ∉ H := fun hmem => hg (by simpa using H.mul_mem hmem (H.inv_mem h.2))
      rw [Work.ORReductions.Coherent.restrictToSubgroup_single_of_notMem H K (g * (h : G)) (d * e)
          hnot,
        Work.ORReductions.Coherent.restrictToSubgroup_single_of_notMem H K g d hg]
      simp

theorem restrictToSubgroup_mul_subgroupAlgMap {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] (b : MonoidAlgebra K G) (t : MonoidAlgebra K H) :
    Work.ORReductions.Coherent.restrictToSubgroup H K
        (b * Work.ORReductions.subgroupAlgMap H K t) =
      Work.ORReductions.Coherent.restrictToSubgroup H K b * t := by
  classical
  refine Finsupp.induction (motive := fun c : G →₀ K =>
    Work.ORReductions.Coherent.restrictToSubgroup H K
        (MonoidAlgebra.ofCoeff c * Work.ORReductions.subgroupAlgMap H K t) =
      Work.ORReductions.Coherent.restrictToSubgroup H K (MonoidAlgebra.ofCoeff c) * t) b.coeff ?_ ?_
  · simp
  · intro g d f _ _ ih
    have h1 : MonoidAlgebra.ofCoeff (Finsupp.single g d + f) =
        MonoidAlgebra.single g d + MonoidAlgebra.ofCoeff f := by
      rw [MonoidAlgebra.ofCoeff_add, MonoidAlgebra.ofCoeff_single]
    rw [h1, add_mul, map_add, ih, map_add, add_mul,
      restrictToSubgroup_single_mul_subgroupAlgMap H K g d t]

end Work.ORReductions.Coherent
