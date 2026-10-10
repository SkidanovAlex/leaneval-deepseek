import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASResidual

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Definitions for the K6 identification of the AS (characteristic-`5`) link

This file isolates the two *explicit* algebraic objects that the AS analogue of node **K6**
(`Work.MotAS.ASZTwistDiv`) needs, in exact mirror of the T-route's
`Work.MotK.TwCensus.Qideal`/`Work.MotK.TGen.ZTwistDivPlaneGeom`:

* `asQideal a b g`: the radical of the five transported AS Pfaffians `kleinPAS a b g`, read in the
  affine variables `X 0, …, X 4` (the chart `y₀ = 1` is imposed separately by
  `Ideal.span {X 0 - 1}`).  Its variety is the AS twisted Klein curve
  `C_g = V(kleinPAS a b g)`, whose function field is `Work.MotAS.twistFieldAS D g`.

* `ZIAS a b g`: (from `ASResidual`) the ideal of the five cubics `kleinRAS a b g` at the chart
  `(1, X 0, X 1, X 2, 0)` of the AS target hyperplane slice `{ẑ₄ = 0}`; its variety is the chart
  part of the *residual curve* `C'` of the AS link.

The identification `C' ≅ Jac²(C_g) = C_{2g}` (the paper's Crauder–Katz `C' = Jac²C`) is the content
of the two leaves stated in `Submission/Work/MotAS/ASZTwistGeom.lean` and
`Submission/Work/MotAS/ASZTwistChart.lean`; this file only holds the definitions.
-/

set_option autoImplicit false

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [CommRing K]

/-- **The radical of the transported AS Pfaffians** in the affine chart `y₀ = 1` of `ℙ⁴` (i.e. in
the variables `X 0, …, X 4`, with the chart condition imposed by adjoining `X 0 - 1`).  Its variety
is the AS twisted Klein curve `C_g = V(kleinPAS a b g)`, so that
`FractionRing (MvPolynomial (Fin 5) K ⧸ (asQideal a b g ⊔ ⟨X 0 - 1⟩))` is the function field of the
chart of `C_g`. -/
noncomputable def asQideal (a b g : K) : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.radical (Ideal.span (Set.range (fun k : Fin 5 =>
    kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i) k)))

/-- The chart ideal of the AS twisted Klein curve: the AS Pfaffian radical together with the chart
condition `y₀ = 1`. -/
noncomputable def asChartIdeal (a b g : K) : Ideal (MvPolynomial (Fin 5) K) :=
  asQideal a b g ⊔ Ideal.span {MvPolynomial.X (0 : Fin 5) - 1}

end Work.MotAS
