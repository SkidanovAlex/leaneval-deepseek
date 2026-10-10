import Mathlib
import Submission.Work.Genus.CharP.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

/-- The `p`-th root twist of a curve with non-zero discriminant has non-zero discriminant.  Route:
`Δ` is the explicit polynomial `-b₂² b₈ - 8 b₄³ - 27 b₆² + 9 b₂ b₄ b₆` in the `aᵢ`, and the `bᵢ`
are themselves polynomial expressions in the `aᵢ` with integer coefficients.  Hence
`(Δ (rootTwist E)) ^ p` equals `Δ` evaluated at the `p`-th powers of the coefficients of
`rootTwist E`, which by `Work.Genus.rootTwist_a₁` etc. are the `aᵢ` of `E`; since `x ↦ x ^ p` is a
ring homomorphism on `F` (Frobenius) fixing the integer coefficients (`map_intCast`), this equals
`Δ E`.  (`ring`-style unfolding of `WeierstrassCurve.Δ`, `b₂`, `b₄`, `b₆`, `b₈` together with
`add_pow_char`/`mul_pow`.) -/
theorem rootTwist_discriminant {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (E : WeierstrassCurve F) :
    (Work.Genus.rootTwist (p := p) E).Δ ^ p = E.Δ := by
  -- `E` is the base change of its own root twist along the Frobenius, since the coefficients of
  -- the twist are `p`-th roots of the coefficients of `E`.
  have h : E = (Work.Genus.rootTwist (p := p) E).map (frobenius F p) := by
    ext <;> simp [frobenius_def]
  -- `Δ` commutes with base change, so `E.Δ` is the `p`-th power of `(rootTwist E).Δ`.
  have h2 : E.Δ = (Work.Genus.rootTwist (p := p) E).Δ ^ p := by
    conv_lhs => rw [h]
    rw [WeierstrassCurve.map_Δ, frobenius_def]
  exact h2.symm

end Work.Genus.CharP
