import Mathlib
import Submission.Work.GroupCohomology.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- Conjugation of `1`-cocycles of a normal subgroup is a left action of `G`:
`conjCocycle (g * h) = conjCocycle g ∘ conjCocycle h`. -/
theorem conjCocycle_comp {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] (g h : G)
    (f : Work.GroupCohomology.Z1 N A) :
    Work.GroupCohomology.conjCocycle (N := N) (g * h) f =
      Work.GroupCohomology.conjCocycle (N := N) g
        (Work.GroupCohomology.conjCocycle (N := N) h f) := by
  ext n
  simp only [Work.GroupCohomology.conjCocycle_apply]
  rw [show Work.GroupCohomology.conjAutN N (g * h) =
        Work.GroupCohomology.conjAutN N g * Work.GroupCohomology.conjAutN N h from
      map_mul _ g h]
  rw [mul_inv_rev, MulAut.mul_apply]
  rw [mul_smul]

end Work.GroupCohomology
