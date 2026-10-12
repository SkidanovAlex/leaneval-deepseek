import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Bargmann_inner
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BargmannLift` — the Bargmann isometry with a spectator operator

The resolution of the identity in coherent states (`Work.BoseB4.Bargmann_inner`)

    `⟪Ψ, Ψ'⟫ = ∫_ℂ ⟪Φ Ψ z, Φ Ψ' z⟫ dν(z)`

immediately upgrades to the form FS use, with one spectator operator `B`
inserted on the second vector: since `Φ (lift B Ψ') z = B (Φ Ψ' z)`
(`Work.BoseB4.Phi_lift`),

    `⟪Ψ, (lift B) Ψ'⟫ = ∫_ℂ ⟪Φ Ψ z, B (Φ Ψ' z)⟫ dν(z)`.

This is the `p = q = 0` case of the `c`-number substitution
(`Work.BoseB4.Kafz_monomial`), i.e. the bare `∑_j a_k† a_k`-type terms of FS
`eq:HLambdaSecond`.
-/

noncomputable section

open scoped lp NNReal ENNReal
open MeasureTheory Filter

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem bargmann_lift (B : E →ₗ[ℂ] E) (Ψ Ψ' : FockCore E) :
    inner ℂ (Embed E Ψ) (Embed E (lift B Ψ'))
      = ∫ z : ℂ, inner ℂ (Phi Ψ z) (B (Phi Ψ' z)) ∂gauss := by
  rw [← coreInner, Bargmann_inner]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Phi_lift]

end Work.BoseB4
