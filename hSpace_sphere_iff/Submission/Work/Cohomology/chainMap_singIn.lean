import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SingIn
import Submission.Work.Cohomology.Chains

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- Pushing singular chains forward along the inclusion `singIn X W ⟶ Sing X` identifies the
`n`-chains of the subcomplex `singIn X W` with exactly the `n`-chains of `X` that lie in `W`,
and it is injective because the inclusion is. -/
theorem chainMap_singIn (X : TopCat.{0}) (W : Set X) (n : ℕ) :
    (Submission.Cohomology.chainMap ℚ (Submission.Cohomology.singIn X W).ι n).range
        = Submission.Cohomology.chainIn X W n ∧
      Function.Injective (Submission.Cohomology.chainMap ℚ (Submission.Cohomology.singIn X W).ι n) := by
  have hset : Set.range (fun x : ((Submission.Cohomology.singIn X W) : SSet).obj (op ⦋n⦌) =>
        Finsupp.single
          (ConcreteCategory.hom ((Submission.Cohomology.singIn X W).ι.app (op ⦋n⦌)) x) (1 : ℚ))
      = {c | ∃ σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌),
          (∀ t, TopCat.toSSetObjEquivT X (op ⦋n⦌) σ t ∈ W) ∧ c = Finsupp.single σ 1} := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, (Submission.Cohomology.mem_singIn_iff x.1).mp x.2, by simp⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, (Submission.Cohomology.mem_singIn_iff σ).mpr hσ⟩, by simp⟩
  constructor
  · change (Finsupp.lmapDomain ℚ ℚ
        ((Submission.Cohomology.singIn X W).ι.app (op ⦋n⦌))).range
      = Submission.Cohomology.chainIn X W n
    rw [Finsupp.range_lmapDomain, Submission.Cohomology.chainIn, hset]
  · intro a b h
    let f := ConcreteCategory.hom ((Submission.Cohomology.singIn X W).ι.app (op ⦋n⦌))
    have hf : Function.Injective f := fun x y hxy => Subtype.ext hxy
    have h' : Finsupp.mapDomain f a = Finsupp.mapDomain f b := by
      simpa [Submission.Cohomology.chainMap, Finsupp.lmapDomain_apply, f] using h
    exact Finsupp.mapDomain_injective hf h'

end Work.Cohomology
