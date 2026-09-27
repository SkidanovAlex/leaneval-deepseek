import Mathlib
import Submission.Work.Cohomology.Chains

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- The range of the underlying map on simplices of the inclusion of a subcomplex is the set of
simplices of that subcomplex. -/
lemma range_ι_subcomplex (S : SSet.{0}) (C : S.Subcomplex) (n : ℕ) :
    Set.range (C.ι.app (op ⦋n⦌)) = C.obj (op ⦋n⦌) := by
  rw [Subfunctor.ι_app]
  exact Subtype.range_coe

/-- The inclusion of a subcomplex is injective on `n`-simplices. -/
lemma injective_ι_subcomplex (S : SSet.{0}) (C : S.Subcomplex) (n : ℕ) :
    Function.Injective (C.ι.app (op ⦋n⦌)) := by
  intro x y h
  exact Subtype.ext h

/-- The range of the chain map induced by an injective-on-`n`-simplices morphism `f` is the
submodule of chains supported on the image of `f` in degree `n`. -/
lemma range_chainMap_of_injective {S T : SSet.{0}} (R : Type) [CommRing R]
    (f : S ⟶ T) (n : ℕ) (hf : Function.Injective (f.app (op ⦋n⦌))) :
    (Submission.Cohomology.chainMap R f n).range
      = Finsupp.supported R R (Set.range (f.app (op ⦋n⦌))) := by
  ext x
  rw [LinearMap.mem_range, Finsupp.mem_supported']
  rw [show (∃ y, Submission.Cohomology.chainMap R f n y = x) ↔
      x ∈ Set.range (Finsupp.mapDomain (f.app (op ⦋n⦌))) from by
    simp only [Submission.Cohomology.chainMap, Finsupp.lmapDomain_apply, Set.mem_range]]
  exact Finsupp.mem_range_mapDomain_iff (f.app (op ⦋n⦌)) hf x

/-- The range of the chain map induced by the inclusion of a subcomplex `C` is the submodule of
chains supported on the `n`-simplices of `C`. -/
lemma range_chainMap_subcomplex (S : SSet.{0}) (C : S.Subcomplex) (n : ℕ) :
    (Submission.Cohomology.chainMap ℚ C.ι n).range
      = Finsupp.supported ℚ ℚ (C.obj (op ⦋n⦌)) := by
  rw [range_chainMap_of_injective ℚ C.ι n (injective_ι_subcomplex S C n),
    range_ι_subcomplex S C n]

theorem chainMap_sup (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    (Submission.Cohomology.chainMap ℚ (A ⊔ B).ι n).range
        = (Submission.Cohomology.chainMap ℚ A.ι n).range ⊔
          (Submission.Cohomology.chainMap ℚ B.ι n).range ∧
      Function.Injective (Submission.Cohomology.chainMap ℚ (A ⊔ B).ι n) := by
  constructor
  · rw [range_chainMap_subcomplex S (A ⊔ B) n, range_chainMap_subcomplex S A n,
        range_chainMap_subcomplex S B n, Subfunctor.max_obj, Finsupp.supported_union]
  · intro x y h
    exact Finsupp.mapDomain_injective (injective_ι_subcomplex S (A ⊔ B) n)
      (by simpa only [Submission.Cohomology.chainMap, Finsupp.lmapDomain_apply] using h)

end Work.Cohomology
