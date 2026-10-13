/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted radial Hardy inequality `zHardy_weighted`: auxiliary definitions

This module collects the vocabulary of the proof of

  `Work.FTS.EllipticEst.zHardy_weighted`:
for every `n` there is a universal `C > 0` with

  `∫_0^∞ w(z)² (rDzIter n g z)² dz ≤ C ∫_0^∞ w(z)² (rDzIter (n+1) g z)² dz`

for every `g` smooth on `(0,∞)`, where `w(z) = (1+z)²/z²` is the radial weight of the
paper (`Work.Spaces.w`).

The proof is the one-dimensional weighted Hardy inequality for the operator `D = z ∂_z`
and the weight `w²`.  Writing `u = h·w·√z` one has the pointwise identity

  `4 w² (zh')² - w² h² = 4 z (u')² + (8/(1+z)²) w² h² - 4 (d/dz)(a h² w² z)`

with `a(z) = (z-3)/(2(1+z))`; both terms displayed on the right are non-negative, so the
total derivative contributes the *boundary* term `4(a h² w² z)`, which vanishes at `0` and
at `∞` along suitable sequences (because `w²h²` is integrable) — this is the content of
`zHardy_seq_bot`, `zHardy_seq_top` and `zHardy_tendsto_setIntegral_Ioc`.

## The gadgets

* `zA` (the `a` above), `zDw` (the derivative of `w`), `zDA` (the derivative of `zA`);
* `zFlux h z = zA z * (h z)² * (w z)² * z`, whose derivative is `zFluxD h (deriv h z) z`;
* `zHardy_alg`: the algebraic identity above (a pure rational identity in `z, p, q`);
* `hasDerivAt_zFlux` + `zHardy_pointwise`: the pointwise inequality
  `0 ≤ 4 w² (rDz h)² - w² h² + 4 (zFlux h)'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The auxiliary functions -/

/-- The function `a(z) = (z-3)/(2(1+z))` of the completion of squares. -/
def zA (z : ℝ) : ℝ := (z - 3) / (2 * (1 + z))

/-- The derivative of the radial weight `w(z) = (1+z)²/z²`. -/
def zDw (z : ℝ) : ℝ := 2 * (1 + z) / z ^ 2 - 2 * (1 + z) ^ 2 / z ^ 3

/-- The derivative of `zA`. -/
def zDA (z : ℝ) : ℝ := 2 / (1 + z) ^ 2

/-- The "flux" `zFlux h z = a(z) · h(z)² · w(z)² · z` of the completion of squares. -/
def zFlux (h : ℝ → ℝ) (z : ℝ) : ℝ := zA z * (h z) ^ 2 * (Work.Spaces.w z) ^ 2 * z

/-- The derivative of `zFlux h` at a point where `h` has derivative `p`. -/
def zFluxD (h : ℝ → ℝ) (p z : ℝ) : ℝ :=
  zDA z * (h z) ^ 2 * (Work.Spaces.w z) ^ 2 * z
    + zA z * (2 * h z * p) * (Work.Spaces.w z) ^ 2 * z
    + zA z * (h z) ^ 2 * (2 * Work.Spaces.w z * zDw z) * z
    + zA z * (h z) ^ 2 * (Work.Spaces.w z) ^ 2

/-! ## The derivatives of `zA` and of the weight `w` -/

theorem hasDerivAt_zA {z : ℝ} (hz : 0 < z) : HasDerivAt zA (zDA z) z := by
  have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have hnum : HasDerivAt (fun y : ℝ => y - 3) 1 z := hid.sub_const 3
  have hden : HasDerivAt (fun y : ℝ => 2 * (1 + y)) 2 z := by
    have h := (hid.const_add (1 : ℝ)).const_mul (2 : ℝ)
    exact h.congr_deriv (by ring)
  have h := hnum.div hden (by positivity)
  change HasDerivAt (fun y : ℝ => (y - 3) / (2 * (1 + y))) (zDA z) z
  refine h.congr_deriv ?_
  rw [zDA]
  have h2 : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  try ring

theorem hasDerivAt_w {z : ℝ} (hz : 0 < z) : HasDerivAt Work.Spaces.w (zDw z) z := by
  have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have hnum : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + z)) z := by
    have h := (hid.const_add (1 : ℝ)).pow 2
    exact h.congr_deriv (by ring)
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    have h := hid.pow 2
    exact h.congr_deriv (by ring)
  have h := hnum.div hden (by positivity)
  change HasDerivAt (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) (zDw z) z
  refine h.congr_deriv ?_
  rw [zDw]
  have h2 : z ≠ 0 := ne_of_gt hz
  field_simp
  try ring

/-! ## The algebraic identity of the completion of squares -/

/-- The pure rational identity behind the weighted Hardy inequality: for `z > 0` and
arbitrary reals `p, q`,

`4 w² (zp)² - w² q² + 4 (a' q² w² z + a·2qp·w²·z + a q² 2ww' z + a q² w²)
  = 4 (z p w + z q w' + q w/2)² + (8/(1+z)²) q² w²`,

with `w = w(z)`, `w' = zDw z`, `a = zA z`, `a' = zDA z`. -/
theorem zHardy_alg (z p q : ℝ) (hz : 0 < z) :
    4 * (Work.Spaces.w z) ^ 2 * (z * p) ^ 2 - (Work.Spaces.w z) ^ 2 * q ^ 2
      + 4 * (zDA z * q ^ 2 * (Work.Spaces.w z) ^ 2 * z
             + zA z * (2 * q * p) * (Work.Spaces.w z) ^ 2 * z
             + zA z * q ^ 2 * (2 * Work.Spaces.w z * zDw z) * z
             + zA z * q ^ 2 * (Work.Spaces.w z) ^ 2)
    = 4 * (z * p * Work.Spaces.w z + z * q * zDw z + q * Work.Spaces.w z / 2) ^ 2
      + (8 / (1 + z) ^ 2) * q ^ 2 * (Work.Spaces.w z) ^ 2 := by
  have h1 : z ≠ 0 := ne_of_gt hz
  have h2 : 1 + z ≠ 0 := by linarith
  simp only [Work.Spaces.w, zDw, zDA, zA]
  field_simp
  ring

/-! ## The pointwise inequality -/

theorem hasDerivAt_zFlux (h : ℝ → ℝ) {z p : ℝ} (hz : 0 < z) (hh : HasDerivAt h p z) :
    HasDerivAt (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y) (zFluxD h p z) z := by
  have ha := hasDerivAt_zA hz
  have hw := hasDerivAt_w hz
  have hq : HasDerivAt (fun y : ℝ => (h y) ^ 2) (2 * h z * p) z := by
    have h' := hh.pow 2
    refine h'.congr_deriv ?_
    ring
  have hw2 : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2)
      (2 * Work.Spaces.w z * zDw z) z := by
    have h' := hw.pow 2
    refine h'.congr_deriv ?_
    ring
  have hid : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
  have hmain : HasDerivAt (fun y : ℝ => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y)
      (((zDA z * (h z) ^ 2 + zA z * (2 * h z * p)) * (Work.Spaces.w z) ^ 2
        + zA z * (h z) ^ 2 * (2 * Work.Spaces.w z * zDw z)) * z
        + zA z * (h z) ^ 2 * (Work.Spaces.w z) ^ 2 * 1) z :=
    ((ha.mul hq).mul hw2).mul hid
  refine hmain.congr_deriv ?_
  simp only [zFluxD]
  ring

/-- The pointwise inequality of the weighted Hardy estimate: for `z > 0` and `h`
differentiable at `z`,

`0 ≤ 4 w(z)² (z h'(z))² - w(z)² h(z)² + 4 (d/dz)(a h² w² z)(z)`. -/
theorem zHardy_pointwise (h : ℝ → ℝ) {z p : ℝ} (hz : 0 < z) (hh : HasDerivAt h p z) :
    0 ≤ 4 * (Work.Spaces.w z) ^ 2 * (z * p) ^ 2 - (Work.Spaces.w z) ^ 2 * (h z) ^ 2
      + 4 * deriv (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y) z := by
  have hd : deriv (fun y => zA y * (h y) ^ 2 * (Work.Spaces.w y) ^ 2 * y) z = zFluxD h p z :=
    (hasDerivAt_zFlux h hz hh).deriv
  rw [hd]
  simp only [zFluxD]
  rw [zHardy_alg z p (h z) hz]
  have h1 : (0 : ℝ) ≤ 8 / (1 + z) ^ 2 := by
    have : (0 : ℝ) < 1 + z := by linarith
    positivity
  have h2 : (0 : ℝ) ≤ 4 * (z * p * Work.Spaces.w z + z * h z * zDw z
      + h z * Work.Spaces.w z / 2) ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ (h z) ^ 2 * (Work.Spaces.w z) ^ 2 := by positivity
  nlinarith [mul_nonneg h1 h3]

end Work.FTS.EllipticEst
