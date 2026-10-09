import Mathlib
import Submission.Work.Properness.BridgeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

/-- **The obstruction calculus in the abstract setting of a closure model.**

`(closureToSetup M hcomm).HasLift` is, by definition, the existence of a lift of `M.pi` along the
restriction map `restrictHom M.L`, i.e. of a homomorphism `ψ : G_ℚ →* E.G` with
`M.pi.comp ψ = restrictHom M.L` (`Setup.HasLift` is `Nonempty Setup.Lift`, and `Setup.Lift` is the
subtype of such `ψ`).  By `Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2`, such a
lift exists exactly when the extension class of `E`, pulled back along the restriction map, is a
coboundary in `H²(G_ℚ, ker M.pi)`.  This lemma is the bookkeeping that identifies the two
formulations. -/
theorem hasLift_iff_pullbackCocycle_mem_B2 {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel) (hcomm : ∀ a b : M.pi.ker, a * b = b * a) : letI : CommGroup M.pi.ker := { (inferInstance : Group M.pi.ker) with mul_comm := hcomm }; letI := Work.AbsoluteGalois.kernelModule M hcomm; letI := DistribMulAction.compHom (Additive M.pi.ker) (Work.AbsoluteGalois.restrictHom M.L); ((Work.Properness.closureToSetup M hcomm).HasLift ↔ Work.AbsoluteGalois.pullbackCocycle (Work.AbsoluteGalois.restrictHom M.L) (Work.AbsoluteGalois.sectionCocycle M.pi M.normalizedSection M.normalizedSection_spec) ∈ Work.GroupCohomology.B2 (Field.absoluteGaloisGroup ℚ) (Additive M.pi.ker)) := by
  -- `Setup.HasLift` unfolds to `Nonempty Setup.Lift`, and `Setup.Lift` is the subtype of lifts;
  -- for the closure-model setup this is literally `∃ ψ, M.pi.comp ψ = restrictHom M.L`.
  have key : (closureToSetup M hcomm).HasLift ↔
      ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
        M.pi.comp ψ = Work.AbsoluteGalois.restrictHom M.L := by
    simp only [Setup.HasLift, Setup.Lift, Setup.IsLift]
    exact nonempty_subtype
  rw [key]
  exact Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2 M hcomm

end Work.Properness
