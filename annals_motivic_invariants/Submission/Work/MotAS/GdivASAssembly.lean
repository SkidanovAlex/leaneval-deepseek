import Mathlib
import Submission.Work.MotAS.FdivASGen3
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `GdivAS` — the target divisor of the AS census, factorised

Item 3 of the repair plan (`Submission/Work/MotAS/Guide_AS.lean`), second half.  The target divisor
of the census is

  `GdivAS a b g = cubAS a b g * sdualAS a b g * bwVecAS a b g 4`,

and the *second polar factor* `cubAS` is not an independent polynomial: the polar form of the AS
quadric at `pAS = 288 • e₀` sees only the fourth coordinate (`MotAS.kleinBilinAS_pAS`), so

* `MotAS.linAS_eq_const` : `linAS a b = -576 (C a ^ 2 - C a * C b - C b ^ 2)`,
* `MotAS.bwVecAS_four_eq` : `bwVecAS a b g 4 = (kleinRAS (C a) (C b) (C g) (chart3 K)) 4`, because
  `π_p x = x - x 0 • p` (`Work.MotK.kleinTwPi`) and `pAS` is supported in coordinate `0`,
* `MotAS.cubAS_eq_linAS_mul` : `cubAS a b g = linAS a b * bwVecAS a b g 4`,
* `MotAS.GdivAS_eq` : `GdivAS a b g = linAS a b * (bwVecAS a b g 4) ^ 2 * sdualAS a b g`.

Hence the non-vanishing clause `GdivAS ≠ 0` of the census reduces to its three factors:
`linAS` is a unit (`MotAS.isUnit_linAS`), and the remaining two are the two ingredients
`bwVecAS · 4 ≠ 0` and `sdualAS ≠ 0`.  `MotAS.GdivAS_ne_zero_of` assembles that reduction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The linear polar factor is the constant `-576 (a² − ab − b²)` (the `(chart3) 4 = 1` case of
`MotAS.kleinBilinAS_pAS`). -/
theorem linAS_eq_const {K : Type*} [Field K] (a b : K) :
    linAS a b = -(576 : MvPolynomial (Fin 3) K) * (C a ^ 2 - C a * C b - C b ^ 2) := by
  have h := kleinBilinAS_pAS (K := K) a b (Work.MotK.chart3 K)
  rw [show linAS a b = kleinBilinAS (C a) (C b) (pAS K) (Work.MotK.chart3 K) from rfl, h,
    show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 4 = 1 from rfl, mul_one]

/-- The chart denominator `bwVecAS · 4` is the fourth component of the inverse chart map:
`π_p x = x - x 0 • p` and `pAS` is supported in coordinate `0`. -/
theorem bwVecAS_four_eq {K : Type*} [Field K] (a b g : K) :
    bwVecAS a b g 4 = kleinRAS (C a) (C b) (C g) (Work.MotK.chart3 K) 4 := by
  simp [bwVecAS, Work.MotK.kleinTwPi, pAS_apply]

/-- The second polar factor is the first one times the chart denominator:
`cubAS a b g = linAS a b * bwVecAS a b g 4`. -/
theorem cubAS_eq_linAS_mul {K : Type*} [Field K] (a b g : K) :
    cubAS a b g = linAS a b * bwVecAS a b g 4 := by
  have hX := kleinBilinAS_pAS (K := K) a b
    (kleinRAS (C a) (C b) (C g) (Work.MotK.chart3 K))
  rw [show cubAS a b g = kleinBilinAS (C a) (C b) (pAS K)
        (kleinRAS (C a) (C b) (C g) (Work.MotK.chart3 K)) from rfl,
      hX, linAS_eq_const a b, bwVecAS_four_eq a b g]

/-- **The target divisor, factorised**: `GdivAS = linAS · (bwVecAS · 4)² · sdualAS`. -/
theorem GdivAS_eq {K : Type*} [Field K] (a b g : K) :
    GdivAS a b g = linAS a b * bwVecAS a b g 4 * bwVecAS a b g 4 * sdualAS a b g := by
  rw [show GdivAS a b g = cubAS a b g * sdualAS a b g * bwVecAS a b g 4 from rfl,
    cubAS_eq_linAS_mul a b g]
  first | refl_ring1 | ring

/-- **`GdivAS ≠ 0` modulo its two non-unit factors.**  The `linAS` factor is the unit
`-576 (aK² − aK bK − bK²)` (`MotAS.isUnit_linAS`), so what remains is `bwVecAS · 4 ≠ 0` (the
non-vanishing of the inverse chart denominator) and `sdualAS ≠ 0` (which follows from the class
clause `MotAS.censusAS_class_sdual`). -/
theorem GdivAS_ne_zero_of (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hbw : bwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ≠ 0)
    (hsd : sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0) :
    GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 := by
  have hlin : linAS (aK D) (bK D) ≠ 0 := (isUnit_linAS D hD).ne_zero
  rw [GdivAS_eq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hlin hbw) hbw) hsd

end Work.MotAS
