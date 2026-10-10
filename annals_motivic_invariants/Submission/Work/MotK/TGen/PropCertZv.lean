import Mathlib
import Submission.Work.MotK.TGen.ThetaSTDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.PropCertZv` — the certificate for the kernel defect of the ruling matrix

The kernel defect of the ruling matrix is `WL a b h = T·Pt1 + Pt2`
(`Submission/Work/MotK/TGen/ThetaSTDefs.lean`), and the two projections of the ruling line onto the
source ruling divisor are governed by the "coordinate certificate"

* `PmL a b h i - PmL a b h 4 · (chartPt i)`,  `i = 1,2,3`,

where `PmL a b h = kleinTwP a b h (ZvL)` is the twisted quadro map evaluated at the ruling line
`ZvL(T) = T·rv + rw` of the fibre over the chart point `chartPt = (0, x₀, x₁, x₂, 1)`, and

* `WZL a b h = T·(Zcub 4) - (Zcub 3)`

is the kernel defect written in the generators of the residual-curve ideal `ZI a b h`
(`Work.MotK.TwCensus.Zcub` is `kleinTwR` evaluated at the affine chart `chart3`).

The three identities say that, modulo `ZvL ∈ ker (AmatP ·)`, the twisted Pfaffians at the ruling
line differ from `PmL 4` proportionally to `WZL`, with the explicit proportionality constants
`-h/b³ · (T·a·x₁ + b·x₂)`, `h/(a·b)`, `-h/b² · T`.  They are the polynomial identities that make
`theta (sT) = 0` (`Work.MotK.TGen.ThetaST`) reduce to the single function `WZL`.

## Proof technique

Each identity is an explicit polynomial identity in `a, b, h` and the chart coordinates
`x₀, x₁, x₂`, in which the constants `a/b`, `a²/b²`, … occur *inside* `MvPolynomial.C`.  Since
`MvPolynomial` (and `Polynomial` over it) is not a division ring, `field_simp` cannot be applied
there.  As in `Submission/Work/MotK/TGen/AmatPChartPtData.lean`, the device used is the standard
one: embed `Polynomial (MvPolynomial (Fin 3) K)` into its fraction field `F`, which is injective,
push the algebra map through the polynomial expressions with `map_mul, map_add, map_sub, map_pow,
map_neg, map_zero, map_one, map_div₀`, turn `Polynomial.C` and `MvPolynomial.C` into the
corresponding `algebraMap`s, clear denominators with `field_simp` and close with `ring` in the
field `F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TGen

open MvPolynomial Polynomial Matrix

/-- A non-zero element of `K` stays non-zero in the fraction field of `K[x₀,x₁,x₂][T]`. -/
private lemma algebraMap_pfrac_ne_zero {K : Type} [Field K] (x : K) (hx : x ≠ 0) :
    algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K))) x ≠ 0 := by
  intro h0
  exact hx ((algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))).injective
    (by rw [h0, map_zero]))

set_option maxHeartbeats 8000000 in
theorem PropCertZv (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (PmL a b h 1 - PmL a b h 4 * Polynomial.C (Work.MotK.TwCensus.chartPt (K := K) 1)
        = -(Polynomial.C (MvPolynomial.C (h / b ^ 3)))
            * (Polynomial.X * Polynomial.C (MvPolynomial.C a * MvPolynomial.X 1)
                + Polynomial.C (MvPolynomial.C b * MvPolynomial.X 2)) * WZL a b h)
    ∧ (PmL a b h 2 - PmL a b h 4 * Polynomial.C (Work.MotK.TwCensus.chartPt (K := K) 2)
        = Polynomial.C (MvPolynomial.C (h / (a * b))) * WZL a b h)
    ∧ (PmL a b h 3 - PmL a b h 4 * Polynomial.C (Work.MotK.TwCensus.chartPt (K := K) 3)
        = -(Polynomial.C (MvPolynomial.C (h / b ^ 2))) * Polynomial.X * WZL a b h) := by
  have ha' := algebraMap_pfrac_ne_zero (K := K) a ha
  have hb' := algebraMap_pfrac_ne_zero (K := K) b hb
  refine ⟨?_, ?_, ?_⟩
  · apply IsFractionRing.injective (Polynomial (MvPolynomial (Fin 3) K))
      (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))
    simp only [PmL, WZL, ZvL, Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1,
      Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4,
      Work.MotK.TwCensus.chartPt, Work.MotK.TwCensus.Zcub, Work.MotK.kleinTwR,
      Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2, Work.MotK.kleinTwR3,
      Work.MotK.kleinTwR4, Work.MotK.chart3, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      map_mul, map_add, map_sub, map_pow, map_neg, map_zero, map_one, map_div₀,
      Polynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    field_simp [hb', ha']
    first | refl_ring1 | ring
  · apply IsFractionRing.injective (Polynomial (MvPolynomial (Fin 3) K))
      (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))
    simp only [PmL, WZL, ZvL, Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1,
      Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4,
      Work.MotK.TwCensus.chartPt, Work.MotK.TwCensus.Zcub, Work.MotK.kleinTwR,
      Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2, Work.MotK.kleinTwR3,
      Work.MotK.kleinTwR4, Work.MotK.chart3, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      map_mul, map_add, map_sub, map_pow, map_neg, map_zero, map_one, map_div₀,
      Polynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    field_simp [hb', ha']
    first | refl_ring1 | ring
  · apply IsFractionRing.injective (Polynomial (MvPolynomial (Fin 3) K))
      (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))
    simp only [PmL, WZL, ZvL, Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1,
      Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4,
      Work.MotK.TwCensus.chartPt, Work.MotK.TwCensus.Zcub, Work.MotK.kleinTwR,
      Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2, Work.MotK.kleinTwR3,
      Work.MotK.kleinTwR4, Work.MotK.chart3, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      map_mul, map_add, map_sub, map_pow, map_neg, map_zero, map_one, map_div₀,
      Polynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    field_simp [hb', ha']
    first | refl_ring1 | ring

end Work.MotK.TGen
