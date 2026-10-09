import Mathlib
import Submission.Work.GroupCohomology.Basic
import Submission.Work.AbsoluteGalois.Obstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

/-- The pullback of a `2`-cocycle along a group homomorphism `ρ : H →* Q` is a `2`-cocycle: the
`H`-action on `A` is the one obtained from the `Q`-action by composition with `ρ`. -/
theorem pullbackCocycle_mem_Z2 {Q H A : Type*} [Group Q] [Group H] [AddCommGroup A]
    [DistribMulAction Q A] (ρ : H →* Q) (c : Q × Q → A)
    (hc : c ∈ Work.GroupCohomology.Z2 Q A) :
    letI := DistribMulAction.compHom A ρ
    Work.AbsoluteGalois.pullbackCocycle ρ c ∈ Work.GroupCohomology.Z2 H A := by
  rw [Work.GroupCohomology.mem_Z2_iff] at hc ⊢
  intro g h k
  have h := hc (ρ g) (ρ h) (ρ k)
  simpa only [Work.AbsoluteGalois.pullbackCocycle_apply, map_mul,
    MulAction.compHom_smul_def] using h

end Work.AbsoluteGalois
