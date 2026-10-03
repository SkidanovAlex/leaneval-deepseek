import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceCore
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.OrbitF
import Submission.Work.ORHughesFree.Rat.mem_ofGroup_mul_A_iff

namespace Work.ORHughesFree.Rat

/-- **The orbit form of `Rat.FL`**: `V ∈ Rat.FL x` iff some *left* translate `φu · x` has its
`U ♮ X`-normal form supported in the `V`-part, equivalently iff shifting the support of `Psi x`
by the group letter `Ugen u` lands in `Orbit.NUV V`. -/
theorem mem_FL_iff_exists {U : Type} [Group U] (x : Work.ORHughesFree.RatU U) (V : Subgroup U) :
    V ∈ Work.ORHughesFree.Rat.FL x ↔
      ∃ u : U, ∀ p ∈ (Work.ORHughesFree.Rat.FreeProduct.Psi x).coeff.support,
        Work.ORHughesFree.Rat.FreeProduct.NU.Ugen u * p ∈ Work.ORHughesFree.Rat.Orbit.NUV V := by
  change x ∈ BL V ↔ _
  rw [mem_BL_iff_ofGroup_mul]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u, (mem_ofGroup_mul_A_iff V x u).mp h⟩
  · rintro ⟨u, h⟩
    exact ⟨u, (mem_ofGroup_mul_A_iff V x u).mpr h⟩

end Work.ORHughesFree.Rat
