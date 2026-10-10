import Mathlib
import Submission.Work.MotK.TGen.ZpgI4W4NonZeroDiv
import Submission.Work.MotK.TGen.ZpgI4StdIndependent
import Submission.Work.MotK.K6WDet

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgI4W4NonZeroDiv` — `zpgW4` is a non-zero-divisor modulo the chart ideal

This is the *unconditional* companion of `Work.MotK.TGen.ZpgI4W4NonZeroDiv_of`: the quotient
`K[y₁,y₂,y₃,y₄]/zpgI4` of the affine chart of the twisted Klein curve is a free `K[X₃]`-module on
the five standard monomials `1, X₀, X₁, X₂, X₀X₂`, and multiplication by
`zpgW4 = b⁴X₀ − a⁴h²X₂²` has non-zero determinant on it (`ZpgWMatDetMain`), hence is injective.

The four hypotheses of `ZpgI4W4NonZeroDiv_of` are supplied by
* `ZpgI4SpanMain` (spans) — via the Finset-sum rewrite `zpgSum_eq`,
* `ZpgI4StdIndependent` (independence) — likewise,
* `ZpgWMatMulMain` (the multiplication matrix),
* `ZpgWMatDetMain` (its determinant is non-zero).

The result is the `hkey` input of `Work.MotK.TGen.ZpgI4NormalForm`, hence the input of
`Work.MotK.TGen.ZpgI4SatW`.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Work.MotK.TGen

theorem ZpgI4W4NonZeroDiv (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (u : MvPolynomial (Fin 4) K)
    (hu : zpgW4 a b h * u ∈ zpgI4 a b h) : u ∈ zpgI4 a b h :=
  Work.MotK.K6WDet.zpgI4W4NonZeroDiv K a b h ha hb hh u hu
-- The statement is unchanged; the proof moved to `Submission/Work/MotK/K6WDet.lean`, which
-- supplies the four inputs of `ZpgI4W4NonZeroDiv_of`: `ZpgI4SpanMain`, `ZpgI4StdIndependent`,
-- `ZpgWMatMulMain` and the determinant `Work.MotK.K6WDet.WDetNeZero` (the placeholder
-- `ZpgWMatDetMain` is still a `sorry`, hence unused).

end Work.MotK.TGen
