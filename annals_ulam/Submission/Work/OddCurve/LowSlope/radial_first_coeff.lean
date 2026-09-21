import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs

/-!
# The first radial coefficient of the low-slope odd reconstruction

For `n ≥ 1`, `a, b ∈ [3/8, 15/8]`, writing `P = 2n+2`, `R = a^{1/P}` and `r = b^{1/P}`,
this file proves

  `(n+1) * ( R^2 / (P * a * (R+r)) + R^2 * r / ((P-1) * a * (R+r)) ) ≤ 3/2`.

This is the (first order) bound on the size of the radial correction that the
low-slope odd reconstruction needs; the constant `3/2` is loose, the true
supremum of the left-hand side over `P ≥ 4` and `a,b ∈ [3/8,15/8]` being `4/3`.

## Structure of the argument

Only the *lower* bounds `a ≥ 3/8`, `b ≥ 3/8` are used.  Writing `c = (3/8)^{1/P}`,
`P ≥ 4`, the proof reduces to the two numeric facts

* `1 ≤ 3 * c^(P-1) = 3 * (3/8)^{(P-1)/P}`, and
* `P/(P-1) ≤ 3 * c^(P-2) = 3 * (3/8)^{(P-2)/P}`.

The first is immediate from `(3/8)^x ≥ 3/8` for `x ≤ 1`.  The second, after
writing `(3/8)^{1-2/P} = (3/8) * (8/3)^{2/P}`, comes from the elementary lower
bound `(8/3)^t ≥ 1 + (5/8)t` (`t ≥ 0`), which follows from `exp u ≥ 1 + u` and
`log(8/3) ≥ 1 - 3/8 = 5/8`; what remains is the polynomial inequality
`4P^2 + 9P - 45 ≥ 0`, valid for `P ≥ 4`.
-/

namespace Work.OddCurve.LowSlope

/-- For `t ≥ 0`, `(8/3)^t ≥ 1 + (5/8) * t`.

This is the tangent-line bound at `0` for the convex function `t ↦ (8/3)^t`,
using `log (8/3) ≥ 1 - (8/3)⁻¹ = 5/8`. -/
lemma eight_thirds_rpow_lower (t : ℝ) (ht : 0 ≤ t) :
    1 + (5 / 8) * t ≤ ((8 : ℝ) / 3) ^ t := by
  have hpos : (0 : ℝ) < 8 / 3 := by norm_num
  have hlog : (5 : ℝ) / 8 ≤ Real.log (8 / 3) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : ((8 : ℝ) / 3)⁻¹ = 3 / 8 := by norm_num
    rw [hinv] at h
    linarith
  rw [Real.rpow_def_of_pos hpos]
  have h1 : Real.log (8 / 3) * t + 1 ≤ Real.exp (Real.log (8 / 3) * t) :=
    Real.add_one_le_exp _
  have h2 : (5 / 8) * t ≤ Real.log (8 / 3) * t := by nlinarith
  linarith

/-- `((3/8)^{1/P})^(P-1) = (3/8)^{1 - 1/P}`. -/
lemma three_eighths_rpow_inv_pow_sub_one (P : ℝ) (hP : 0 < P) :
    (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 1) = ((3 : ℝ) / 8) ^ (1 - P⁻¹) := by
  rw [← Real.rpow_mul (show (0 : ℝ) ≤ 3 / 8 by norm_num)]
  congr 1
  field_simp

/-- `((3/8)^{1/P})^(P-2) = (3/8)^{1 - 2/P}`. -/
lemma three_eighths_rpow_inv_pow_sub_two (P : ℝ) (hP : 0 < P) :
    (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 2) = ((3 : ℝ) / 8) ^ (1 - 2 / P) := by
  rw [← Real.rpow_mul (show (0 : ℝ) ≤ 3 / 8 by norm_num)]
  congr 1
  field_simp

/-- `1 ≤ 3 * ((3/8)^{1/P})^(P-1)` for `P > 0`. -/
lemma one_le_three_mul_three_eighths_pow (P : ℝ) (hP : 0 < P) :
    1 ≤ 3 * (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 1) := by
  rw [three_eighths_rpow_inv_pow_sub_one P hP]
  have hle : (3 : ℝ) / 8 ≤ ((3 : ℝ) / 8) ^ (1 - P⁻¹) := by
    have h : ((3 : ℝ) / 8) ^ (1 : ℝ) ≤ ((3 : ℝ) / 8) ^ (1 - P⁻¹) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by
        have : 0 ≤ P⁻¹ := inv_nonneg.mpr hP.le
        linarith)
    rwa [Real.rpow_one] at h
  linarith

/-- `P/(P-1) ≤ 3 * ((3/8)^{1/P})^(P-2)` for `P ≥ 4`. -/
lemma div_le_three_mul_three_eighths_pow (P : ℝ) (hP : 4 ≤ P) :
    P / (P - 1) ≤ 3 * (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 2) := by
  have hP0 : 0 < P := by linarith
  rw [three_eighths_rpow_inv_pow_sub_two P hP0]
  have hdecomp : ((3 : ℝ) / 8) ^ (1 - 2 / P) = (3 / 8) * ((8 : ℝ) / 3) ^ (2 / P) := by
    rw [show (1 : ℝ) - 2 / P = 1 + (-(2 / P)) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3 / 8), Real.rpow_one]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 8),
      ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3 / 8),
      show ((3 : ℝ) / 8)⁻¹ = 8 / 3 by norm_num]
  rw [hdecomp]
  have hlower : 1 + (5 / 8) * (2 / P) ≤ ((8 : ℝ) / 3) ^ (2 / P) :=
    eight_thirds_rpow_lower (2 / P) (by positivity)
  have hfin : P / (P - 1) ≤ (9 : ℝ) / 8 * (1 + (5 / 8) * (2 / P)) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < P - 1)]
    field_simp
    nlinarith
  have h3 : 3 * ((3 : ℝ) / 8 * ((8 : ℝ) / 3) ^ (2 / P))
      = (9 : ℝ) / 8 * ((8 : ℝ) / 3) ^ (2 / P) := by ring
  rw [h3]
  nlinarith [hlower, hfin]

/-- The core estimate: for `P ≥ 4`, `a ≥ 3/8`, `b ≥ 3/8`, with `R = a^{1/P}`, `r = b^{1/P}`,
  `R^2 * (1 + (P/(P-1)) * r) ≤ 3 * a * (R + r)`. -/
lemma radial_first_coeff_core (P : ℝ) (hP : 4 ≤ P) (a b : ℝ)
    (ha : 3 / 8 ≤ a) (hb : 3 / 8 ≤ b) :
    let R : ℝ := a ^ P⁻¹
    let r : ℝ := b ^ P⁻¹
    R ^ 2 * (1 + (P / (P - 1)) * r) ≤ 3 * a * (R + r) := by
  dsimp only
  have hP0 : 0 < P := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hR0 : 0 < a ^ P⁻¹ := Real.rpow_pos_of_pos ha0 _
  have hr0 : 0 < b ^ P⁻¹ := Real.rpow_pos_of_pos hb0 _
  have hc0 : 0 < ((3 : ℝ) / 8) ^ P⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hcR : ((3 : ℝ) / 8) ^ P⁻¹ ≤ a ^ P⁻¹ :=
    Real.rpow_le_rpow (by norm_num) ha (le_of_lt (inv_pos.mpr hP0))
  have hI : 1 ≤ 3 * (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 1) :=
    one_le_three_mul_three_eighths_pow P hP0
  have hII : P / (P - 1) ≤ 3 * (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 2) :=
    div_le_three_mul_three_eighths_pow P hP
  have hp1 : (0 : ℝ) ≤ P - 1 := by linarith
  have hp2 : (0 : ℝ) ≤ P - 2 := by linarith
  have hcR1 : (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 1) ≤ (a ^ P⁻¹) ^ (P - 1) :=
    Real.rpow_le_rpow (le_of_lt hc0) hcR hp1
  have hcR2 : (((3 : ℝ) / 8) ^ P⁻¹) ^ (P - 2) ≤ (a ^ P⁻¹) ^ (P - 2) :=
    Real.rpow_le_rpow (le_of_lt hc0) hcR hp2
  have h3 : (a ^ P⁻¹) ^ (P - 1) = (a ^ P⁻¹) ^ (P - 2) * a ^ P⁻¹ := by
    have h : (a ^ P⁻¹) ^ (P - 1) = (a ^ P⁻¹) ^ (P - 2) * (a ^ P⁻¹) ^ (1 : ℝ) := by
      rw [show P - 1 = (P - 2) + 1 by ring, Real.rpow_add hR0]
    rwa [Real.rpow_one] at h
  have hstep : 1 + (P / (P - 1)) * (b ^ P⁻¹)
      ≤ 3 * (a ^ P⁻¹) ^ (P - 2) * (a ^ P⁻¹ + b ^ P⁻¹) := by
    nlinarith [hI, hII, hcR1, hcR2, hr0.le, h3]
  have hRpow : (a ^ P⁻¹) ^ 2 * (a ^ P⁻¹) ^ (P - 2) = a := by
    rw [show ((a ^ P⁻¹) ^ 2 : ℝ) = (a ^ P⁻¹) ^ (2 : ℝ) from
      (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_add hR0, show (2 : ℝ) + (P - 2) = P by ring]
    rw [← Real.rpow_mul (le_of_lt ha0), inv_mul_cancel₀ (ne_of_gt hP0), Real.rpow_one]
  calc (a ^ P⁻¹) ^ 2 * (1 + (P / (P - 1)) * (b ^ P⁻¹))
      ≤ (a ^ P⁻¹) ^ 2 * (3 * (a ^ P⁻¹) ^ (P - 2) * (a ^ P⁻¹ + b ^ P⁻¹)) := by
        apply mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 3 * ((a ^ P⁻¹) ^ 2 * (a ^ P⁻¹) ^ (P - 2)) * (a ^ P⁻¹ + b ^ P⁻¹) := by ring
    _ = 3 * a * (a ^ P⁻¹ + b ^ P⁻¹) := by rw [hRpow]

theorem radial_first_coeff (n : ℕ) (hn : 1 ≤ n) {a b : ℝ}
    (ha : 3 / 8 ≤ a) (ha' : a ≤ 15 / 8) (hb : 3 / 8 ≤ b) (hb' : b ≤ 15 / 8) :
    let R : ℝ := a ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹)
    let r : ℝ := b ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹)
    (n + 1) * (R ^ 2 / ((2 * n + 2 : ℝ) * a * (R + r)) +
      R ^ 2 * r / ((2 * n + 1 : ℝ) * a * (R + r))) ≤ 3 / 2 := by
  have hP4 : (4 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
    have h : (4 : ℕ) ≤ 2 * n + 2 := by omega
    exact_mod_cast h
  have hcore := radial_first_coeff_core ((2 * n + 2 : ℕ) : ℝ) hP4 a b ha hb
  dsimp only at hcore ⊢
  set R : ℝ := a ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹) with hRdef
  set r : ℝ := b ^ (((2 * n + 2 : ℕ) : ℝ)⁻¹) with hrdef
  have hMcast : ((2 * n + 2 : ℕ) : ℝ) = 2 * (n : ℝ) + 2 := by push_cast; ring
  rw [hMcast] at hcore
  have hden : (2 * (n : ℝ) + 2) - 1 = 2 * (n : ℝ) + 1 := by ring
  rw [hden] at hcore
  have hid : ((n : ℝ) + 1) *
        (R ^ 2 / ((2 * (n : ℝ) + 2) * a * (R + r))
          + R ^ 2 * r / ((2 * (n : ℝ) + 1) * a * (R + r)))
      = R ^ 2 * (1 + ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) * r)
          / (2 * (a * (R + r))) := by
    have hA : (2 * (n : ℝ) + 2) = 2 * ((n : ℝ) + 1) := by ring
    rw [hA]
    field_simp
  rw [hid]
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hR0 : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos ha0 _
  have hr0 : 0 < r := by rw [hrdef]; exact Real.rpow_pos_of_pos hb0 _
  have hpos : (0 : ℝ) < 2 * (a * (R + r)) := by positivity
  rw [div_le_iff₀ hpos]
  linarith [hcore]

end Work.OddCurve.LowSlope
