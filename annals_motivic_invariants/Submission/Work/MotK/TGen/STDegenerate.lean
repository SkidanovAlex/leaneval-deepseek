import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.KleinTwQ_stereo
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The degenerate locus of the source ruling divisor `sT`

The source ruling divisor `sT a b h = kleinTwS (kleinTwStereo p chart3)` of the T-twisted
Crauder--Katz link vanishes identically as soon as one of the parameters `a`, `b`, `h` is zero.

The reason is visible term by term in the explicit form of the twisted secant quintic: every
monomial of `kleinTwS a b h y` contains either a positive power of `a` or a positive power of `b`
or a positive power of `h`, and in each of the three degenerate cases the *argument* `y` of `sT`
also acquires a vanishing coordinate:

* `a = 0`: only `b^10 h^2 · y₀y₁y₂y₃y₄` survives, and `y₁ = 0` (the polar form `kleinTwBilin`
  degenerates to `-b²h (u₁v₄ + u₄v₁)` and `kleinPointT` has `p₁ = p₄ = 0`);
* `b = 0`: only `-a^10 h^2 · y₀y₁y₂y₃y₄` survives, and `y₂ = 0` (now `kleinTwBilin` is
  `a²h (u₂v₃ + u₃v₂)` and `p₂ = 1`, `p₃ = 0`);
* `h = 0`: only `-a^5 b^5 · y₀^5` survives, and `y₀ = 0` (the quadric becomes `-ab x₀²` and
  `chart3 0 = 0`).

Division by zero makes `kleinPointT` collapse to `(1,0,1,0,0)` in all three cases, which is what
makes the elementary coordinate computations above go through.
-/

namespace Work.MotK.TGen

open MvPolynomial

/-! ## The degenerate forms of the twisted secant quintic `kleinTwS` -/

section GeneralRing

variable {R : Type*} [CommRing R]

/-- `kleinTwS 0 b h y` is the single pure-`b` term `b^10 h^2 y₀y₁y₂y₃y₄`. -/
lemma kleinTwS_of_a_eq_zero (b h : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwS (0 : R) b h y = b ^ 10 * h ^ 2 * (y 0 * y 1 * y 2 * y 3 * y 4) := by
  simp only [Work.MotK.kleinTwS]; ring

/-- `kleinTwS a 0 h y` is the single pure-`a` term `-a^10 h^2 y₀y₁y₂y₃y₄`. -/
lemma kleinTwS_of_b_eq_zero (a h : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwS a (0 : R) h y = -(a ^ 10) * h ^ 2 * (y 0 * y 1 * y 2 * y 3 * y 4) := by
  simp only [Work.MotK.kleinTwS]; ring

/-- `kleinTwS a b 0 y` is the single `h`-free term `-a^5 b^5 y₀^5`. -/
lemma kleinTwS_of_h_eq_zero (a b : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwS a b (0 : R) y = -(a ^ 5 * b ^ 5) * (y 0) ^ 5 := by
  simp only [Work.MotK.kleinTwS]; ring

end GeneralRing

/-! ## The vanishing coordinate of the stereographic argument -/

/-- With `a = 0` the first coordinate of `kleinTwStereo p chart3` vanishes. -/
lemma kleinTwStereo_zero_a (K : Type) [Field K] (b h : K) :
    Work.MotK.kleinTwStereo (0 : MvPolynomial (Fin 3) K) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.pRa 0 b h) (Work.MotK.chart3 K) 1 = 0 := by
  simp only [Work.MotK.kleinTwStereo, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
    Work.MotK.kleinTwP0, Work.MotK.pRa_apply, Work.MotK.chart3, Work.MotK.kleinPointT,
    Pi.add_apply, MvPolynomial.C_0, MvPolynomial.C_1]
  try ring

/-- With `b = 0` the second coordinate of `kleinTwStereo p chart3` vanishes. -/
lemma kleinTwStereo_zero_b (K : Type) [Field K] (a h : K) :
    Work.MotK.kleinTwStereo (MvPolynomial.C a) (0 : MvPolynomial (Fin 3) K) (MvPolynomial.C h)
      (Work.MotK.pRa a 0 h) (Work.MotK.chart3 K) 2 = 0 := by
  simp only [Work.MotK.kleinTwStereo, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
    Work.MotK.kleinTwP0, Work.MotK.pRa_apply, Work.MotK.chart3, Work.MotK.kleinPointT,
    Pi.add_apply]
  simp
  try ring

/-- With `h = 0` the zeroth coordinate of `kleinTwStereo p chart3` vanishes. -/
lemma kleinTwStereo_zero_h (K : Type) [Field K] (a b : K) :
    Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (0 : MvPolynomial (Fin 3) K)
      (Work.MotK.pRa a b 0) (Work.MotK.chart3 K) 0 = 0 := by
  simp only [Work.MotK.kleinTwStereo, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
    Work.MotK.kleinTwP0, Work.MotK.pRa_apply, Work.MotK.chart3, Work.MotK.kleinPointT,
    Pi.add_apply]
  simp
  try ring

/-! ## The theorem -/

theorem STDegenerate (K : Type) [Field K] (a b h : K) (h0 : a = 0 ∨ b = 0 ∨ h = 0) :
    Work.MotK.TGen.sT a b h = 0 := by
  rcases h0 with ha | hb | hh
  · rw [ha]
    rw [Work.MotK.TGen.sT, MvPolynomial.C_0, kleinTwS_of_a_eq_zero, kleinTwStereo_zero_a]
    first | refl_ring1 | ring
  · rw [hb]
    rw [Work.MotK.TGen.sT, MvPolynomial.C_0, kleinTwS_of_b_eq_zero, kleinTwStereo_zero_b]
    first | refl_ring1 | ring
  · rw [hh]
    rw [Work.MotK.TGen.sT, MvPolynomial.C_0, kleinTwS_of_h_eq_zero, kleinTwStereo_zero_h]
    first | refl_ring1 | ring

end Work.MotK.TGen
