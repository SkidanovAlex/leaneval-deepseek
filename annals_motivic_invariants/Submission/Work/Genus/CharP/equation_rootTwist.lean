import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.CharP.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

open Work.Genus

/-- **The Frobenius descent of the Weierstrass equation.**  If `(X ^ p, Y ^ p)` satisfies the
Weierstrass equation of `E` then `(X, Y)` satisfies the Weierstrass equation of the `p`-th root
twist `E^{(1/p)}`.

Route: raise both sides of the target equation to the `p`-th power; in characteristic `p`,
`(u + v) ^ p = u ^ p + v ^ p` (`add_pow_char`) and `(u * v) ^ p = u ^ p * v ^ p`, so the left-hand
side becomes `(Y ^ p) ^ 2 + (E.a₁) * X ^ p * Y ^ p + (E.a₃) * Y ^ p` (using
`Work.Genus.rootTwist_a₁`, `rootTwist_a₃`, `rootTwist_a₂`, `rootTwist_a₄`, `rootTwist_a₆`) and the
right-hand side likewise, which is exactly the hypothesis; conclude by injectivity of `x ↦ x ^ p`
(`frobenius_inj`). -/
theorem equation_rootTwist {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (E : WeierstrassCurve F) {X Y : RatFunc F}
    (h : (Y ^ p) ^ 2 + algebraMap F (RatFunc F) E.a₁ * X ^ p * Y ^ p
        + algebraMap F (RatFunc F) E.a₃ * Y ^ p
      = (X ^ p) ^ 3 + algebraMap F (RatFunc F) E.a₂ * (X ^ p) ^ 2
        + algebraMap F (RatFunc F) E.a₄ * X ^ p + algebraMap F (RatFunc F) E.a₆) :
    Y ^ 2 + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₁ * X * Y
        + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₃ * Y
      = X ^ 3 + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₂ * X ^ 2
        + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₄ * X
        + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₆ := by
  -- The `p`-th power of the left-hand side of the target equation is the left-hand side of `h`.
  have hL : (Y ^ 2 + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₁ * X * Y
        + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₃ * Y) ^ p
      = (Y ^ p) ^ 2 + algebraMap F (RatFunc F) E.a₁ * X ^ p * Y ^ p
        + algebraMap F (RatFunc F) E.a₃ * Y ^ p := by
    simp only [add_pow_char, mul_pow, ← map_pow, Work.Genus.rootTwist_a₁,
      Work.Genus.rootTwist_a₃]
    rw [pow_right_comm Y 2 p]
  -- The `p`-th power of the right-hand side of the target equation is the right-hand side of `h`.
  have hR : (X ^ 3 + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₂ * X ^ 2
        + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₄ * X
        + algebraMap F (RatFunc F) (Work.Genus.rootTwist (p := p) E).a₆) ^ p
      = (X ^ p) ^ 3 + algebraMap F (RatFunc F) E.a₂ * (X ^ p) ^ 2
        + algebraMap F (RatFunc F) E.a₄ * X ^ p + algebraMap F (RatFunc F) E.a₆ := by
    simp only [add_pow_char, mul_pow, ← map_pow, Work.Genus.rootTwist_a₂,
      Work.Genus.rootTwist_a₄, Work.Genus.rootTwist_a₆]
    rw [pow_right_comm X 3 p, pow_right_comm X 2 p]
  -- Frobenius is injective on `𝔽(t)`, so equality of `p`-th powers gives the equation.
  exact frobenius_inj (RatFunc F) p
    (by rw [frobenius_def, frobenius_def, hL, hR]; exact h)

end Work.Genus.CharP
