import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.fifthPowAtPoles_of_asPoint
import Submission.Work.MotC2.aut_functionField
import Submission.Work.MotV5.Alpha.Reduction
import Submission.Work.MotV5.Nodes.lam_AS

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

/-- **Node LAM_AS in `α`-semilinear form — the version consumed by the rigidity of the link.**
This is the form of `Work.MotV5.Nodes.lam_AS` in which the isomorphism is only `𝕜`-linear, with the
automorphism `α` of the base `RatFunc 𝕜` that it induces supplied as the hypothesis `hθ`
(`θ (algebraMap c) = algebraMap (α c)`); the `RatFunc 𝕜`-linear case `lam_AS` is the special case
`α = id`.  The passage from a `𝕜`-linear isomorphism to one with an explicit `α` is the *proved*
`Work.MotV5.basePreserved_of_X` (`base_preserved_AS.lean`) together with
`Work.MotV.restrict_algEquiv`, which needs the bridge — hence `α` appears here as a hypothesis
rather than being manufactured inside this node.

Let `f₁, f₂ : RatFunc 𝕜` carry admissible twisting data (`Work.MotV5.ASTwistData`, sharing the
projective fifth-torsion shift `σS`), let `α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜`, and let
`θ : F₁ ≃ₐ[𝕜] F₂` with `θ (algebraMap c) = algebraMap (α c)` for all `c`.  Then there are `ε = ±1`
and a nonzero tuple `y : Fin 5 → RatFunc 𝕜` whose Galois coordinates for the parameter
`f₁ - ε · α⁻¹ f₂` satisfy the Klein equations: the twisted Klein curve `C^AS_{f₁ - ε · α⁻¹ f₂}` has a
`K`-rational point.

**Why `α⁻¹` and not `α`.**  With the hypothesis above, `θ` is a `K`-algebra isomorphism from `F₁`
onto `F₂` endowed with the `K`-structure pulled back along `α`; the regraded field is the twist of
the class `α⁻¹ f₂`, because `asRoot f₂` satisfies `℘(asRoot f₂) = algebraMap_{F₂} f₂ =
algebraMap_{F₂^α} (α⁻¹ f₂)`.  This is exactly the convention of the *proved* characteristic-`≠ 5`
sibling `Work.MotV.twist_natural` (which establishes `twistFieldT D h₁ ≃ₐ[K] twistFieldT D (φ⁻¹ h₂)`
from `θ (algebraMap c) = algebraMap (φ c)`, `α := φ⁻¹` being the automorphism of the design's
convention, `MOTIVIC_S45_LEAD.md` §C5 NAT) followed by `Work.MotV.twist_iso_point`.

With `f₁ = fAS 𝕜`, `f₂ = 2 • fAS 𝕜` the parameter is `fAS 𝕜 - 2ε · α⁻¹ (fAS 𝕜)` with
`2ε ∈ {±2}`; `Work.MotV5.fifthPowAtPoles_of_asPoint` (proved) then gives
`FifthPowAtPoles 𝕜 (RatFunc 𝕜) (fAS 𝕜 - 2ε · α⁻¹ (fAS 𝕜))`, and `exponent_rigidity_AS`
(proved, quantified over *all* `α`) with `α' := α⁻¹` and `m := 2ε ∈ {±2}` is its negation. -/
theorem lam_AS_alpha (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ₁ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D f₁ τ₁ σS σ₁)
    (h2 : Work.MotV5.ASTwistData 𝕜 D f₂ τ₂ σS σ₂)
    (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (θ : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS))
    (hθ : ∀ c : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) c)
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) (α c)) :
    ∃ (ε : ℤ) (_ : ε = 1 ∨ ε = -1) (y : Fin 5 → RatFunc 𝕜), y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (Work.MotV.asCoord
          (Work.MotV5.asRoot (f₁ - algebraMap 𝕜 (RatFunc 𝕜) ((ε : ℤ) : 𝕜) * α.symm f₂))
          (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0 := by
  refine Work.MotV5.Alpha.lam_AS_alpha_of 𝕜 D hD ?_ f₁ f₂ τ₁ τ₂ σS σ₁ σ₂ h1 h2 α θ hθ
  intro g₁ g₂ τ₁' τ₂' σS' σ₁' σ₂' h1' h2' θ'
  exact lam_AS 𝕜 D hD g₁ g₂ τ₁' τ₂' σS' σ₁' σ₂' h1' h2' θ'

end Work.MotV5.Nodes
