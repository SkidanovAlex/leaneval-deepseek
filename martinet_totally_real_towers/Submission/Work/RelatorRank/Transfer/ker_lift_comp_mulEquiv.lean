import Mathlib
import Submission.Work.RelatorRank.Bridge

namespace Work.RelatorRank.Transfer

/-- **The presentation kernel does not change under a group isomorphism.**  For any multiplicative
equivalence `e : G ≃* H` and any family `gen : ι → G`, the kernels of `FreeGroup.lift gen` and of
`FreeGroup.lift (e ∘ gen)` coincide (as subgroups of the free group on `ι`).  This is the plain-group
counterpart of `Work.RelatorRank.ker_lift_comp_continuousMulEquiv`; the two lifts are related by
`FreeGroup.lift (e ∘ gen) = e.toMonoidHom.comp (FreeGroup.lift gen)`, and composition with an
injective map does not change the kernel. -/
theorem ker_lift_comp_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {ι : Type*}
    (gen : ι → G) :
    MonoidHom.ker (FreeGroup.lift fun i => e (gen i)) = MonoidHom.ker (FreeGroup.lift gen) := by
  have hcomp : FreeGroup.lift (fun i => e (gen i))
      = (e : G →* H).comp (FreeGroup.lift gen) := by
    refine MonoidHom.ext fun x => ?_
    exact (FreeGroup.lift_unique ((e : G →* H).comp (FreeGroup.lift gen))
      (fun i => by simp) (x := x)).symm
  rw [hcomp, MonoidHom.ker_comp_of_injective _ _ e.injective]

end Work.RelatorRank.Transfer
