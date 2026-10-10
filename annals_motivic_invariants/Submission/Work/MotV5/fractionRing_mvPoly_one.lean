import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- **One polynomial variable.**  `Frac F[x] = RatFunc F`.  The canonical `𝕜`-algebra equivalence
`MvPolynomial (Fin 1) F ≃ₐ[F] Polynomial F` (equivalently `MvPolynomial.uniqueAlgEquiv`, restricted
to `𝕜`) induces it (`IsFractionRing.algEquivOfAlgEquiv`), composed with
`RatFunc.toFractionRingAlgEquiv`.  This is the base-extended version of the sibling result
`Work.Wire123.IsSquare.fractionRing_mvPolynomial_succ_ratFunc` at `n = 0`. -/
theorem fractionRing_mvPoly_one {𝕜 F : Type} [Field 𝕜] [Field F] [Algebra 𝕜 F] :
    Nonempty (FractionRing (MvPolynomial (Fin 1) F) ≃ₐ[𝕜] RatFunc F) :=
  -- `MvPolynomial (Fin 1) F ≃ₐ[F] F[X]` (`MvPolynomial.uniqueAlgEquiv`), restricted to `𝕜`,
  -- transports fraction rings (`IsFractionRing.algEquivOfAlgEquiv`), and `RatFunc F` is the
  -- fraction field of `F[X]` (`RatFunc.toFractionRingAlgEquiv`).
  ⟨(IsFractionRing.algEquivOfAlgEquiv
      ((MvPolynomial.uniqueAlgEquiv F (Fin 1)).restrictScalars 𝕜)).trans
    (RatFunc.toFractionRingAlgEquiv (K := F) (R := 𝕜)).symm⟩

end Work.MotV5
