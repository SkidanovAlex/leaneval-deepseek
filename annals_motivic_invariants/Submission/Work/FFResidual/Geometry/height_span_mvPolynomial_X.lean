import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.FFResidual.Geometry

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- In `𝔽[X₀,…,Xₙ]` over a field `𝔽`, the principal ideal `(X₀)` has height one: `X₀` is a
non-zero-divisor (the polynomial ring is a domain) and not a unit, and the ring is Noetherian
(Krull's principal ideal theorem,
`Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors`). -/
theorem height_span_mvPolynomial_X (𝔽 : Type) [Field 𝔽] (n : ℕ) :
    (Ideal.span {MvPolynomial.X (0 : Fin (n+1))} : Ideal (MvPolynomial (Fin (n+1)) 𝔽)).height = 1 := by
  haveI : IsNoetherianRing (MvPolynomial (Fin (n+1)) 𝔽) := MvPolynomial.isNoetherianRing
  have hX0prime : Prime (MvPolynomial.X (0 : Fin (n+1)) : MvPolynomial (Fin (n+1)) 𝔽) :=
    MvPolynomial.X_prime
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hX0prime.ne_zero)
    (fun hunit => hX0prime.not_isUnit hunit)

end Work.FFResidual.Geometry
