import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwCensus.SdualTScale` — scaling the chart of the target ruling divisor

The target ruling divisor of the T-twisted Crauder–Katz link is

  `sdualT a b h = kleinTwSDualV (C a) (C b) (C h) (chart3 K)`,

i.e. the Kummer-inverse twist of the dual secant quintic of the Klein model, read on the affine
chart `chart3 = ![0, X 0, X 1, X 2, 1]`.

The polynomial `kleinTwSDualV` is quasi-homogeneous on that chart: a monomial carrying the
`h`-power `γ` and the `z`-exponents `(e₀,…,e₄)` satisfies `3 e₁ + 2 e₂ + e₃ + 5 = 5 γ` whenever
`e₀ = 0` (the only monomials surviving `z₀ = 0`).  Consequently the *weighted* chart scaling
`X i ↦ t^(3-i) X i` (`i = 0,1,2`, weights `3,2,1`), combined with the Kummer substitution
`h ↦ t⁵ h`, is an identity up to the factor `t⁵`:

  `t⁵ · sdualT a b h (t³ x₀, t² x₁, t x₂) = sdualT a b (t⁵ h) (x₀, x₁, x₂)`.

This is the homogeneity used to normalise the target ruling divisor along the `𝔾_m`-scaling of
the chart.  The proof is a direct computation (the two `simp only`s distribute `aeval` through
`kleinTwSDualV` and evaluate the chart vector, and `ring` closes the resulting polynomial
identity, which is `kleinTwSDualV_scale`).
-/

set_option maxHeartbeats 800000

namespace Work.MotK.TwCensus

/-- **The general commutative-ring form of the chart scaling.**  On the chart
`z = (0, t³ z₁, t² z₂, t z₃, 1)` the twist `kleinTwSDualV a b h` agrees with
`t⁵ · kleinTwSDualV a b (t⁵ h)` on the unscaled chart `z = (0, z₁, z₂, z₃, 1)`. -/
theorem kleinTwSDualV_scale {R : Type*} [CommRing R] (a b h t z1 z2 z3 : R) :
    t ^ 5 * Work.MotK.kleinTwSDualV a b h
        (fun j => ![0, t ^ 3 * z1, t ^ 2 * z2, t * z3, (1 : R)] j)
      = Work.MotK.kleinTwSDualV a b (t ^ 5 * h)
        (fun j => ![0, z1, z2, z3, (1 : R)] j) := by
  simp only [Work.MotK.kleinTwSDualV, Matrix.cons_val]
  first | refl_ring1 | ring

/-- **Chart scaling of the target ruling divisor.**  Substituting the weighted chart scaling
`X i ↦ t^(3-i) X i` into `sdualT a b h` and multiplying by `t⁵` replaces the Kummer parameter
`h` by `t⁵ h`. -/
theorem SdualTScale {K : Type} [Field K] (a b h t : K) :
    (MvPolynomial.C t) ^ 5 *
        MvPolynomial.aeval
          (fun i : Fin 3 => ![(MvPolynomial.C (t ^ 3)) * MvPolynomial.X 0,
            (MvPolynomial.C (t ^ 2)) * MvPolynomial.X 1, (MvPolynomial.C t) * MvPolynomial.X 2] i)
          (Work.MotK.TGen.sdualT a b h)
      = Work.MotK.TGen.sdualT a b (t ^ 5 * h) := by
  simp only [Work.MotK.TGen.sdualT, Work.MotK.kleinTwSDualV, Work.MotK.chart3,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    MvPolynomial.algebraMap_eq, Matrix.cons_val]
  first | refl_ring1 | ring

end Work.MotK.TwCensus
