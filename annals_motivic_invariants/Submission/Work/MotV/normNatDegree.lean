import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Polynomial.Bivariate

namespace Work.MotV

/-- The degree of the norm of `p + qY` in the affine coordinate ring `F[W]`, read off in terms of
the degrees of `p` and `q`.  This is Mathlib's
`WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` transported from `degree` to
`natDegree` (via `Polynomial.natDegree = WithBot.unbotD 0 ∘ degree`). -/
theorem normNatDegree {L : Type*} [Field L] (W : WeierstrassCurve L)
    {x : WeierstrassCurve.Affine.CoordinateRing W} {p q : Polynomial L}
    (h : p • (1 : WeierstrassCurve.Affine.CoordinateRing W) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk W Polynomial.X = x) :
    (Algebra.norm (Polynomial L) x).natDegree =
      (max (2 • p.degree) (2 • q.degree + 3)).unbotD 0 := by
  rw [← h]
  rw [Polynomial.natDegree,
    WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis p q]

end Work.MotV
