/-
Copyright (c) 2025. All rights reserved.

# A surjective lift of `G_ℚ →* E.G` is a proper lift of the associated abstract setup

`Submission.EmbeddingProblem.ClosureModel.HasSurjectiveLift M` says that there is a surjection
`ψ : G_ℚ →* E.G` with open kernel whose composite with the projection `M.pi` of the embedding
problem is the restriction map `restrictHom M.L`.  The abstract setting
`Work.Properness.closureToSetup M` attached to `M` has, by construction, `H = G_ℚ`, `E = E.G`,
`π = M.pi` and `ρ = restrictHom M.L`; hence `ψ` is *literally* a lift in the sense of
`Work.Properness.Setup`, and it is a lift in the strong (proper) sense because it is surjective.

This is the trivial half of the equivalence between `M.HasSurjectiveLift` and the existence of a
proper lift of `closureToSetup M`; it does not use the openness of `ker ψ` nor the commutativity
of the kernel, and it is stated with the latter hypothesis only so that `closureToSetup M hcomm`
typechecks.
-/
import Mathlib
import Submission.Work.Properness.BridgeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

theorem hasSurjectiveLift_imp_hasProperLift {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel) (hcomm : ∀ a b : M.pi.ker, a * b = b * a) (h : M.HasSurjectiveLift) : (Work.Properness.closureToSetup M hcomm).HasProperLift := by
  obtain ⟨ψ, -, hsurj, hcomp⟩ := h
  refine ⟨⟨ψ, ?_⟩, hsurj⟩
  refine MonoidHom.ext fun σ => ?_
  exact hcomp σ

end Work.Properness
