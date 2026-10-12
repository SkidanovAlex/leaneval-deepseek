import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.GCBoxBound
import Submission.LhyIntegral
import Submission.LocPotential
import Submission.Work.ModeLatticeR3
import Submission.Work.SmallBoxTBWord.Defs
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Bogoliubov model integral, dimensionful form

This file evaluates the (improperly convergent) 3-dimensional Bogoliubov
model integral

    ∫_{ℝ³} [ (‖k‖² + c) − √((‖k‖² + c)² − c²) − c²/(2‖k‖²) ] dk
      = − c^{5/2} · 64π/(15√2)          (c > 0),

in exact form.  The `c^{5/2}`-homogeneity comes from the scaling
`k = √c · x`, and the dimensionless radius integral that is left is the one
already delivered by the corpus as
`Submission.BoseGases.lhy_model_integral_scaled`:

    ∫₀^∞ (x⁴ + x² − 1/2 − x³√(x²+2)) dx = −16/(15√2).

The reduction to that identity is:

* `Submission.BoseGases.integral_fun_norm_r3` (unconditional polar/radial
  integration on `ℝ³`, which needs no integrability hypothesis),
* the one-dimensional scaling `r = √c · x` (`integral_comp_mul_left_Ioi`),
* the algebraic rewriting `√((cx²+c)² − c²) = cx√(x²+2)` for `x > 0`,
* the elementary real power identity `√c · c² = c^{5/2}`.

All the elementary algebra is kept local and private; the two corpus lemmas
are used as black boxes.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseBox

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The radial integrand `r ↦ (r²+c) − √((r²+c)² − c²) − c²/(2r²)`. -/
private def gfun (c r : ℝ) : ℝ :=
  (r ^ 2 + c) - Real.sqrt ((r ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * r ^ 2)

/-- `gfun`, multiplied by the polar Jacobian `r²` and simplified off `r = 0`. -/
private def hfun (c r : ℝ) : ℝ :=
  r ^ 2 * ((r ^ 2 + c) - Real.sqrt ((r ^ 2 + c) ^ 2 - c ^ 2)) - c ^ 2 / 2

/-- The dimensionless integrand of `lhy_model_integral_scaled`. -/
private def ifun (x : ℝ) : ℝ :=
  x ^ 4 + x ^ 2 - (1 / 2 : ℝ) - x ^ 3 * Real.sqrt (x ^ 2 + 2)

/-- `r² · gfun c r = hfun c r` for `r ≠ 0`. -/
private lemma sq_mul_gfun {c r : ℝ} (hr : r ≠ 0) : r ^ 2 * gfun c r = hfun c r := by
  have h : (2 : ℝ) * r ^ 2 ≠ 0 := by positivity
  simp only [gfun, hfun]
  rw [mul_sub, mul_sub]
  field_simp

/-- **The change of scale `r = √c · x` on the radial integral.** -/
private lemma hfun_smul {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    hfun c (Real.sqrt c * x) = c ^ 2 * ifun x := by
  have hq2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
  have hr2 : (Real.sqrt c * x) ^ 2 = c * x ^ 2 := by rw [mul_pow, hq2]
  have hinner : ((Real.sqrt c * x) ^ 2 + c) ^ 2 - c ^ 2 = c ^ 2 * x ^ 2 * (x ^ 2 + 2) := by
    rw [hr2]; ring
  have hsqrt :
      Real.sqrt (((Real.sqrt c * x) ^ 2 + c) ^ 2 - c ^ 2) = c * x * Real.sqrt (x ^ 2 + 2) := by
    rw [hinner, show c ^ 2 * x ^ 2 * (x ^ 2 + 2) = (c * x) ^ 2 * (x ^ 2 + 2) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ (c * x) ^ 2), Real.sqrt_sq (by positivity : 0 ≤ c * x)]
  simp only [hfun, ifun]
  rw [hsqrt, hr2]
  ring

/-- `√c · c² = c^{5/2}`. -/
private lemma sqrt_mul_sq {c : ℝ} (hc : 0 < c) : Real.sqrt c * c ^ 2 = c ^ (5 / 2 : ℝ) := by
  rw [show (5 / 2 : ℝ) = (1 / 2 : ℝ) + 2 by norm_num, Real.rpow_add hc, Real.rpow_two,
    ← Real.sqrt_eq_rpow]

theorem bog_model_integral {c : ℝ} (hc : 0 < c) : (∫ k : EuclideanSpace ℝ (Fin 3), ((‖k‖ ^ 2 + c) - Real.sqrt ((‖k‖ ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * ‖k‖ ^ 2))) = -(c ^ (5 / 2 : ℝ)) * (64 * Real.pi / (15 * Real.sqrt 2)) := by
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  -- Step 1: polar coordinates on `ℝ³`.
  have h1 : (∫ k : ℝ³,
        ((‖k‖ ^ 2 + c) - Real.sqrt ((‖k‖ ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * ‖k‖ ^ 2)))
      = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * gfun c r :=
    Submission.BoseGases.integral_fun_norm_r3 (g := gfun c)
  -- Step 2: absorb the Jacobian `r²` into the integrand (off the origin).
  have h2 : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * gfun c r)
      = ∫ r in Set.Ioi (0 : ℝ), hfun c r := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact sq_mul_gfun (ne_of_gt hr)
  -- Step 3: the change of variables `r = √c · x`.
  have h3 : (∫ r in Set.Ioi (0 : ℝ), hfun c r)
      = Real.sqrt c * ∫ x in Set.Ioi (0 : ℝ), hfun c (Real.sqrt c * x) := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi (g := hfun c) (a := (0 : ℝ))
      (b := Real.sqrt c) hsqrtc
    rw [mul_zero] at h
    rw [smul_eq_mul] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqrtc), one_mul]
  -- Step 4: the scaled integrand is `c²` times the dimensionless one.
  have h4 : (∫ x in Set.Ioi (0 : ℝ), hfun c (Real.sqrt c * x))
      = c ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ifun x := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact hfun_smul hc hx
  -- Step 5: the corpus's dimensionless model integral.
  have h5 : (∫ x in Set.Ioi (0 : ℝ), ifun x) = -16 / (15 * Real.sqrt 2) := by
    simpa [ifun] using Submission.BoseGases.lhy_model_integral_scaled
  rw [h1, h2, h3, h4, h5]
  rw [show 4 * Real.pi * (Real.sqrt c * (c ^ 2 * (-16 / (15 * Real.sqrt 2))))
      = -(Real.sqrt c * c ^ 2) * (64 * Real.pi / (15 * Real.sqrt 2)) by ring,
    sqrt_mul_sq hc]

end Work.BoseBox
