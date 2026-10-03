import Mathlib

/-!
# Decay of `coth (π s) ∓ 1` in the half-planes `Re s ≥ 1/2` and `Re s ≤ -1/2`

This is the elementary `L¹`-tail estimate used in the Fatou-coordinate chapter of the
Shishikura development: on the right half-plane `Re ≥ 1/2` the kernel `coth (π s) - 1`
decays like `e^{-2π Re s}`, and symmetrically on the left half-plane for `coth (π s) + 1`.

The proof is the naive triangle-inequality bound.  With `z = π s` and `a = Re z`,

* `sinh z = (e^z - e^{-z})/2`, so `‖sinh z‖ ≥ (e^a - e^{-a})/2`;
* `coth z - 1 = (cosh z - sinh z)/sinh z = e^{-z}/sinh z`, so
  `‖coth z - 1‖ ≤ e^{-a} / ((e^a - e^{-a})/2) ≤ 4 e^{-2a}`,
  the last step being equivalent to `e^{2a} ≥ 2`, which holds because `2a ≥ π > log 2`.

The left half-plane case follows by the oddness `coth (-z) = -coth z`.
-/

namespace Work.FatouL1

/-- `2 ≤ exp (2 * a)` for `a ≥ π / 2`. -/
private lemma two_le_exp_two_mul (a : ℝ) (ha : Real.pi / 2 ≤ a) :
    (2 : ℝ) ≤ Real.exp (2 * a) := by
  have hpi : (2 : ℝ) < Real.exp Real.pi := by
    have := Real.add_one_lt_exp Real.pi_ne_zero
    linarith [Real.pi_gt_three]
  have h1 : Real.pi ≤ 2 * a := by linarith
  have h2 : Real.exp Real.pi ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr h1
  linarith

/-- The right half-plane bound: for `Re z ≥ π/2`, `‖coth z - 1‖ ≤ 4 exp (-2 Re z)`. -/
private lemma coth_sub_one_le (z : ℂ) (hz : Real.pi / 2 ≤ z.re) :
    ‖Complex.cosh z / Complex.sinh z - 1‖ ≤ 4 * Real.exp (-2 * z.re) := by
  -- `2 exp (-a) ≤ exp a`, where `a = Re z`.
  have h2exp : 2 * Real.exp (-z.re) ≤ Real.exp z.re := by
    have h := mul_le_mul_of_nonneg_right (two_le_exp_two_mul z.re hz)
      (le_of_lt (Real.exp_pos (-z.re)))
    have harg : 2 * z.re + -z.re = z.re := by ring
    rwa [← Real.exp_add, harg] at h
  -- hence `exp a / 4 ≤ (exp a - exp (-a)) / 2`
  have h4 : Real.exp z.re / 4 ≤ (Real.exp z.re - Real.exp (-z.re)) / 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by norm_num : (0:ℝ) < 2)]
    linarith
  -- and the reverse triangle inequality gives the lower bound for `‖sinh z‖`
  have hsinh_lb : Real.exp z.re / 4 ≤ ‖Complex.sinh z‖ := by
    have h1 : ‖Complex.sinh z‖ = ‖Complex.exp z - Complex.exp (-z)‖ / 2 := by
      rw [Complex.sinh, norm_div]; norm_num
    have h2 : Real.exp z.re - Real.exp (-z.re) ≤ ‖Complex.exp z - Complex.exp (-z)‖ := by
      have h := abs_norm_sub_norm_le (Complex.exp z) (Complex.exp (-z))
      rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
      have h3 : |Real.exp z.re - Real.exp (-z.re)| = Real.exp z.re - Real.exp (-z.re) := by
        rw [abs_of_nonneg]
        have : Real.exp (-z.re) ≤ Real.exp z.re := Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
        linarith
      rwa [h3] at h
    linarith
  have hsinh_pos : 0 < ‖Complex.sinh z‖ := by
    have := Real.exp_pos z.re
    linarith
  have hsinh_ne : Complex.sinh z ≠ 0 := norm_pos_iff.mp hsinh_pos
  -- `coth z - 1 = e^{-z} / sinh z`
  have hid : Complex.cosh z / Complex.sinh z - 1 = Complex.exp (-z) / Complex.sinh z := by
    field_simp
    simp only [Complex.cosh, Complex.sinh]
    ring
  rw [hid, norm_div, Complex.norm_exp, Complex.neg_re]
  rw [div_le_iff₀ hsinh_pos]
  have hident : 4 * Real.exp (-2 * z.re) * (Real.exp z.re / 4) = Real.exp (-z.re) := by
    have h : Real.exp (-2 * z.re) * Real.exp z.re = Real.exp (-z.re) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← h]; ring
  have hstep := mul_le_mul_of_nonneg_left hsinh_lb
    (by positivity : (0:ℝ) ≤ 4 * Real.exp (-2 * z.re))
  rw [hident] at hstep
  exact hstep

theorem cothDecay :
    (∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s) - 1‖ ≤ 4 * Real.exp (-2 * Real.pi * s.re)) ∧
    (∀ s : ℂ, s.re ≤ -(1 / 2) →
      ‖Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s) + 1‖ ≤ 4 * Real.exp (2 * Real.pi * s.re)) := by
  have hre : ∀ s : ℂ, (Real.pi * s).re = Real.pi * s.re := by
    intro s
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  constructor
  · -- right half-plane
    intro s hs
    have hz : Real.pi / 2 ≤ (Real.pi * s).re := by
      rw [hre]; nlinarith [Real.pi_pos]
    have h := coth_sub_one_le (Real.pi * s) hz
    have harg : -2 * (Real.pi * s).re = -2 * Real.pi * s.re := by
      rw [hre]; ring
    rwa [harg] at h
  · -- left half-plane: reflect through the origin using `coth (-z) = -coth z`
    intro s hs
    have hz : Real.pi / 2 ≤ (-(Real.pi * s)).re := by
      rw [Complex.neg_re, hre]; nlinarith [Real.pi_pos]
    have h := coth_sub_one_le (-(Real.pi * s)) hz
    have hodd : Complex.cosh (-(Real.pi * s)) / Complex.sinh (-(Real.pi * s)) - 1
        = -(Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s) + 1) := by
      rw [Complex.cosh_neg, Complex.sinh_neg, div_neg]
      ring
    have harg : -2 * (-(Real.pi * s)).re = 2 * Real.pi * s.re := by
      rw [Complex.neg_re, hre]; ring
    rw [hodd, norm_neg, harg] at h
    exact h

end Work.FatouL1
