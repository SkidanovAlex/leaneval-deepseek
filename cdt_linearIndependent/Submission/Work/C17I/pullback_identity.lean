import Mathlib
import Submission.Work.C17I.defs

namespace Work.C17I

/-- The purely algebraic core of the pullback identity.  With `D = z - 1`, `A2, A1, A0` the
pulled-back operator coefficients at `y = sw z`, `Rh = ρ(y)`, and `U, U1, U2` the values
`P(y), P'(y), P''(y)`, the chain rule gives the normalised pullback coefficients
`odP = 2/D - A1/(A2 D²)`, `odQ = A0/(A2 D⁴)`, `odR = Rh/(A2 D⁴)`. -/
lemma pullback_alg {A2 A1 A0 Rh U U1 U2 D : ℂ} (hD : D ≠ 0) (hA2 : A2 ≠ 0)
    (hM : A2 * U2 + A1 * U1 + A0 * U = Rh) :
    U2 / D ^ 4 + 2 * U1 / D ^ 3
      + (2 / D - A1 / (A2 * D ^ 2)) * (U1 * (-(1 / D ^ 2)))
      + (A0 / (A2 * D ^ 4)) * U
    = Rh / (A2 * D ^ 4) := by
  field_simp
  linear_combination hM

theorem pullback_identity (a b : ℚ) (ra rb rab r0 : ℤ) (z : ℂ) (hz1 : z ≠ 1)
    (hw : Work.C17I.pp2 a b z ≠ 0)
    (hd1 : deriv (Work.C17I.PhiC a b ra rb rab r0) z
      = deriv (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw z) * (-(1 / (z - 1) ^ 2)))
    (hd2 : deriv (deriv (Work.C17I.PhiC a b ra rb rab r0)) z
      = deriv (deriv (Work.C17.Pfun a b ra rb rab r0)) (Work.C17I.sw z) / (z - 1) ^ 4
        + 2 * deriv (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw z) / (z - 1) ^ 3)
    (hM : (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) (Work.C17I.sw z)
            * deriv (deriv (Work.C17.Pfun a b ra rb rab r0)) (Work.C17I.sw z)
          + (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) (Work.C17I.sw z)
            * deriv (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw z)
          + (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) (Work.C17I.sw z)
            * Work.C17.Pfun a b ra rb rab r0 (Work.C17I.sw z)
          = (Work.C17.rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) (Work.C17I.sw z)) :
    deriv (deriv (Work.C17I.PhiC a b ra rb rab r0)) z
      + Work.C17I.odP a b z * deriv (Work.C17I.PhiC a b ra rb rab r0) z
      + Work.C17I.odQ a b z * Work.C17I.PhiC a b ra rb rab r0 z
      = Work.C17I.odR a b ra rb rab z := by
  have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [hd1, hd2, odP, odQ, odR, pp1, pp2, pp0, prh, PhiC]
  exact pullback_alg hD hw hM

end Work.C17I
