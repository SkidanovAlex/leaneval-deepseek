import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SmallSES

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
open Work.Cohomology

/-- A singular simplex of `X` whose image is contained in a subset `A ⊆ X` factors through the
inclusion `A ↪ X`: it is the image of a simplex of `A`. -/
lemma exists_map_inclUX_of_range_subset {X : TopCat} (A : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n)
    (h : Set.range (fun z : stdSimplex ℝ (Fin (n.unop.len + 1)) =>
        TopCat.toSSetObjEquivT X n σ z) ⊆ A) :
    ∃ a : (TopCat.toSSet.obj (TopCat.of A)).obj n,
      (TopCat.toSSet.map (inclUX A)).app n a = σ := by
  refine ⟨(TopCat.toSSetObjEquivT (TopCat.of A) n).symm
    ⟨fun z => ⟨TopCat.toSSetObjEquivT X n σ z, h ⟨z, rfl⟩⟩, ?_⟩, ?_⟩
  · exact (TopCat.toSSetObjEquivT X n σ).continuous.subtype_mk _
  · apply (TopCat.toSSetObjEquivT X n).injective
    ext z
    rw [toSSetObjEquiv_map_apply, Equiv.apply_symm_apply]
    rfl

/-- Every simplex of the small simplicial set `smallSSet U V` (i.e. every singular simplex of `X`
whose image lies in `U` or in `V`) is the image of a simplex of `U` or of `V` under the maps
`smallLiftU`, `smallLiftV` induced by the inclusions. -/
theorem smallLift_cov {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (s : (smallSSet U V).obj n) :
    (∃ a : (TopCat.toSSet.obj (TopCat.of U)).obj n, (smallLiftU U V).app n a = s) ∨
    (∃ b : (TopCat.toSSet.obj (TopCat.of V)).obj n, (smallLiftV U V).app n b = s) := by
  rcases s.2 with h | h
  · left
    obtain ⟨a, ha⟩ := exists_map_inclUX_of_range_subset U n s.1 h
    exact ⟨a, by apply Subtype.ext; rw [smallLiftU, SSet.Subcomplex.lift_app_coe]; exact ha⟩
  · right
    obtain ⟨b, hb⟩ := exists_map_inclUX_of_range_subset V n s.1 h
    exact ⟨b, by apply Subtype.ext; rw [smallLiftV, SSet.Subcomplex.lift_app_coe]; exact hb⟩

end Work.Cohomology
