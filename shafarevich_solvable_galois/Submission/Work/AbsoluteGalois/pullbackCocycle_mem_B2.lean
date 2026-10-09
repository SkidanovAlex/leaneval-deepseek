import Mathlib
import Submission.Work.GroupCohomology.Basic
import Submission.Work.AbsoluteGalois.Obstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

/-- The pullback of a `2`-coboundary along a group homomorphism is a `2`-coboundary.

Explicitly, if `c = d¹ f` for some `1`-cochain `f : Q → A`, then
`pullbackCocycle ρ c = d¹ (f ∘ ρ)` with respect to the pulled-back action
`DistribMulAction.compHom A ρ`, so it lies in `B²(H, A)`. -/
theorem pullbackCocycle_mem_B2 {Q H A : Type*} [Group Q] [Group H] [AddCommGroup A]
    [DistribMulAction Q A] (ρ : H →* Q) (c : Q × Q → A)
    (hc : c ∈ Work.GroupCohomology.B2 Q A) :
    letI := DistribMulAction.compHom A ρ
    Work.AbsoluteGalois.pullbackCocycle ρ c ∈ Work.GroupCohomology.B2 H A := by
  letI := DistribMulAction.compHom A ρ
  obtain ⟨f, hf⟩ :=
    (Work.GroupCohomology.mem_B2_iff (G := Q) (A := A) c).mp hc
  refine (Work.GroupCohomology.mem_B2_iff (G := H) (A := A)
    (Work.AbsoluteGalois.pullbackCocycle ρ c)).mpr ⟨fun h => f (ρ h), ?_⟩
  subst hf
  funext p
  obtain ⟨g, h⟩ := p
  simp only [Work.GroupCohomology.d1_apply, Work.AbsoluteGalois.pullbackCocycle_apply, map_mul]
  rfl

end Work.AbsoluteGalois
