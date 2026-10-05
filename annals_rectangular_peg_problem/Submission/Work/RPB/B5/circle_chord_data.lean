import Mathlib
import Submission.Work.RPB.Defs

/-!
# `B5.circle_chord_data`: the chord data of the standard circle

For the standard parametrisation of the unit circle `t ↦ e^{it}` (i.e. for a curve family `c` whose
time `τ = 0` slice is `c 0 t = Complex.exp (t * I)`), the chord data of `Work.RPB` is completely
explicit.  With `E := Complex.exp ((t : ℂ) * I)`:

* the half chord is `halfChord c 0 t r = E * (↑(sin r / r) * I)`
  (this is the even difference quotient `(e^{i(t+r)} - e^{i(t-r)})/(2r)`
  `= e^{it} (2 i sin r)/(2r)`; note that at `r = 0` both sides are `0`, so the identity is
  uniform in `r` — it does not need `r ≠ 0`);
* consequently `‖halfChord c 0 t r‖ = |sin r| / |r|`, whence
  `r ^ 2 * ‖halfChord c 0 t r‖ ^ 2 = sin r ^ 2` (for `r ≠ 0` by cancellation; for `r = 0` both
  sides vanish);
* the chord sum is `halfChordSum c 0 t r = √2 cos r · E`, since
  `(e^{i(t+r)} + e^{i(t-r)})/√2 = e^{it} (2 cos r)/√2` and `2/√2 = √2`.

These are the values of the chord annulus of the round circle, which is the model used at the
`τ = 0` end of the isotopy in the proof of `exists_lagFamily` (`B5`).

## Contents

* `CircleChord.exp_ofReal_add_mul_I`, `…_sub_mul_I`: the addition formula for `e^{i x}`, in the
  real-parameter form used here;
* `CircleChord.exp_sub_exp_neg_mul_I`, `…_add_…`: `e^{ir} - e^{-ir} = 2i sin r` and
  `e^{ir} + e^{-ir} = 2 cos r`;
* `CircleChord.halfChord_circle`, `…Sum_circle`: the two explicit chord data;
* `CircleChord.sq_mul_abs_div_sq`: the elementary real cancellation
  `r² (|a|/|r|)² = a²` for `r ≠ 0`;
* `circle_chord_data`: the requested statement.
-/

open Complex Real

namespace Work.RPB.B5

namespace CircleChord

/-- `e^{i(a+b)} = e^{ia} e^{ib}` for real `a`, `b`, in the `↑(a + b) * I` shape. -/
lemma exp_ofReal_add_mul_I (a b : ℝ) :
    Complex.exp (((a + b : ℝ)) * Complex.I)
      = Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `e^{i(a-b)} = e^{ia} e^{-ib}` for real `a`, `b`. -/
lemma exp_ofReal_sub_mul_I (a b : ℝ) :
    Complex.exp (((a - b : ℝ)) * Complex.I)
      = Complex.exp ((a : ℂ) * Complex.I) * Complex.exp (-((b : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `e^{ir} - e^{-ir} = 2 i sin r`. -/
lemma exp_sub_exp_neg_mul_I (r : ℝ) :
    Complex.exp ((r : ℂ) * Complex.I) - Complex.exp (-((r : ℂ) * Complex.I))
      = ((2 * Real.sin r : ℝ) : ℂ) * Complex.I := by
  have h2 : Complex.exp (-((r : ℂ) * Complex.I))
      = (Real.cos r : ℂ) - (Real.sin r : ℂ) * Complex.I := by
    rw [show -((r : ℂ) * Complex.I) = (((-r : ℝ)) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [Complex.exp_ofReal_mul_I, h2]
  push_cast; ring

/-- `e^{ir} + e^{-ir} = 2 cos r`. -/
lemma exp_add_exp_neg_mul_I (r : ℝ) :
    Complex.exp ((r : ℂ) * Complex.I) + Complex.exp (-((r : ℂ) * Complex.I))
      = ((2 * Real.cos r : ℝ) : ℂ) := by
  have h : -((r : ℂ) * Complex.I) = starRingEnd ℂ ((r : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [h, Complex.exp_conj, Complex.add_conj, Complex.exp_ofReal_mul_I]
  simp

/-- **The half chord of the unit circle**:
`(e^{i(t+r)} - e^{i(t-r)})/(2r) = e^{it} · i · (sin r / r)`.

Valid for every `r ∈ ℝ`, including `r = 0` (where both sides are `0`, both divisions being the
junk value `0`). -/
lemma halfChord_circle (c : ℝ → ℝ → ℂ) (h0 : ∀ t, c 0 t = Complex.exp (t * Complex.I))
    (t r : ℝ) :
    Work.RPB.halfChord c 0 t r
      = Complex.exp ((t : ℂ) * Complex.I) * (((Real.sin r / r : ℝ) : ℂ) * Complex.I) := by
  -- the scalar reduction `2 sin r · i / (2r) = i · (sin r / r)`, valid for all `r`
  have key : ((2 * Real.sin r : ℝ) : ℂ) * Complex.I / (2 * (r : ℂ))
      = ((Real.sin r / r : ℝ) : ℂ) * Complex.I := by
    have h2s : ((2 * Real.sin r : ℝ) : ℂ) = (2 : ℂ) * (Real.sin r : ℂ) := by push_cast; ring
    have hkey : ∀ (a x b : ℂ), 2 * a * x / (2 * b) = a * x / b := by
      intro a x b; rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
    rw [h2s, hkey, ← div_mul_eq_mul_div, ← Complex.ofReal_div]
  unfold Work.RPB.halfChord
  rw [h0 (t + r), h0 (t - r), exp_ofReal_add_mul_I t r, exp_ofReal_sub_mul_I t r,
    ← mul_sub, exp_sub_exp_neg_mul_I r, mul_div_assoc, key]

/-- **The chord sum of the unit circle**: `(e^{i(t+r)} + e^{i(t-r)})/√2 = √2 cos r · e^{it}`. -/
lemma halfChordSum_circle (c : ℝ → ℝ → ℂ) (h0 : ∀ t, c 0 t = Complex.exp (t * Complex.I))
    (t r : ℝ) :
    Work.RPB.halfChordSum c 0 t r
      = ((Real.sqrt 2 * Real.cos r : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  -- `2 cos r / √2 = √2 cos r`
  have key : ((2 * Real.cos r : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)
      = ((Real.sqrt 2 * Real.cos r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div]
    congr 1
    have hs : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := Real.div_sqrt
    have h : 2 * Real.cos r / Real.sqrt 2 = (2 / Real.sqrt 2) * Real.cos r := by ring
    rw [h, hs]
  unfold Work.RPB.halfChordSum
  rw [h0 (t + r), h0 (t - r), exp_ofReal_add_mul_I t r, exp_ofReal_sub_mul_I t r,
    ← mul_add, exp_add_exp_neg_mul_I r, mul_div_assoc, key, mul_comm]

/-- The elementary cancellation `r ^ 2 * (|a| / |r|) ^ 2 = a ^ 2` for `r ≠ 0`. -/
lemma sq_mul_abs_div_sq (a r : ℝ) (hr : r ≠ 0) : r ^ 2 * (|a| / |r|) ^ 2 = a ^ 2 := by
  rw [div_pow, sq_abs, sq_abs]
  field_simp

end CircleChord

open CircleChord

/-- The chord data of the standard unit circle at time `τ = 0`: the squared chord level is
`sin ^ 2 r`, and the reduced chord coordinate is `√2 cos r` times the circle point `e^{it}`. -/
theorem circle_chord_data (c : ℝ → ℝ → ℂ) (h0 : ∀ t, c 0 t = Complex.exp (t * Complex.I))
    (t r : ℝ) :
    r ^ 2 * ‖Work.RPB.halfChord c 0 t r‖ ^ 2 = Real.sin r ^ 2 ∧
      Work.RPB.halfChordSum c 0 t r
        = ((Real.sqrt 2 * Real.cos r : ℝ) : ℂ) * Complex.exp (t * Complex.I) := by
  constructor
  · -- `‖halfChord‖ = |sin r| / |r|`, then cancel `r ^ 2`
    by_cases hr : r = 0
    · rw [hr]; simp [Work.RPB.halfChord]
    · rw [halfChord_circle c h0 t r, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
        Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_div, one_mul, mul_one]
      exact sq_mul_abs_div_sq (Real.sin r) r hr
  · exact halfChordSum_circle c h0 t r

end Work.RPB.B5
