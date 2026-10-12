import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseKinLoc.Assembly.tprR_branches_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Assembly

set_option maxHeartbeats 1600000

/-- Mixed-regime kinetic-energy budget.

In the "mixed" regime `q ∈ [5/(12 s), 5/(12 d s))` the kinetic-vs-interaction
budget closes using the slack hypothesis
`b/β + εT * (25/18) * C * d * s ≤ (1-εT) * (7/3)/(4s)²`.

Strategy: bound the first two terms by `εT q²` and `b/β` respectively, expand
`(q - 1/(4s))² = q² - q/(2s) + 1/(16s²)`, and reduce everything to the key
inequality
`b/β + (1-εT)/(16s²) + 8 εT C d³s³ q² ≤ (1-εT) q/(2s)`,
which after multiplication by `16 s²` becomes a polynomial inequality
`16 s² b/β + (1-εT) + 128 εT C d³s⁵q² ≤ 8 s (1-εT) q`.
The latter follows from the slack hypothesis (`16 s² b/β ≤ (7/3)(1-εT) - (200/9)εT C d s³`),
from `near` (`128 d²s²q² ≤ 200/9`) and from `far` (`8sq ≥ 10/3`). -/
theorem budget_mixed (β C q d s εT b : ℝ) (hβ : 0 < β) (hC : 0 ≤ C)
    (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hε : 0 ≤ εT) (hε1 : εT ≤ 1) (hb : 0 ≤ b)
    (hfar : (5 / 6) * (2 * s)⁻¹ ≤ q) (hnear : ¬ ((5 / 6) * (2 * (d * s))⁻¹ ≤ q))
    (hslack : b * β⁻¹ + εT * ((25 / 18) * C * d * s)
        ≤ (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2)) :
    εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * β⁻¹ * (q ^ 2 / (q ^ 2 + β))
      + (1 - εT) * (q - (2 * (2 * s))⁻¹) ^ 2 + εT * (C * (2 * (d * s)) ^ 3 * q ^ 2)
      ≤ q ^ 2 := by
  -- `q > 0` from `far`.
  have hq_pos : 0 < q := by
    have h5 : (0:ℝ) < (5/6) * (2*s)⁻¹ := by positivity
    linarith [hfar]
  have h16 : (0:ℝ) < 16 * s^2 := by positivity
  -- First term: drop the denominator (which is ≥ 1).
  have hA : εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ εT * q ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + d^2*q^2)]
    have hnn : (0:ℝ) ≤ εT * q^2 * (d^2*q^2) := by positivity
    nlinarith [hnn]
  -- Second term: `q²/(q²+β) ≤ 1`.
  have hB : b * β⁻¹ * (q ^ 2 / (q ^ 2 + β)) ≤ b * β⁻¹ := by
    apply mul_le_of_le_one_right (mul_nonneg hb (inv_nonneg.mpr hβ.le))
    rw [div_le_one (by positivity : (0:ℝ) < q^2 + β)]
    nlinarith [hβ, sq_nonneg q]
  -- Expansion of the third (quadratic) term.
  have hD : (q - (2 * (2 * s))⁻¹)^2 = q^2 - q*(2*s)⁻¹ + (16*s^2)⁻¹ := by
    field_simp
    ring
  -- The fourth term is a polynomial.
  have hE : εT * (C * (2 * (d * s)) ^ 3 * q ^ 2) = εT * C * 8 * d^3 * s^3 * q^2 := by ring
  -- `far`, cleared of denominators: `5 ≤ 12 s q`.
  have hP1 : 5 ≤ 12 * s * q := by
    have h := mul_le_mul_of_nonneg_left hfar (show (0:ℝ) ≤ 12 * s by positivity)
    have hL : 12 * s * ((5 / 6) * (2 * s)⁻¹) = 5 := by field_simp; ring
    linarith [h, hL]
  -- `near`, cleared of denominators and squared: `128 d²s²q² ≤ 200/9`.
  have hP2 : 128 * d^2 * s^2 * q^2 ≤ 200/9 := by
    have hq : q < (5 / 6) * (2 * (d * s))⁻¹ := not_le.mp hnear
    have h12 : (0:ℝ) < 12 * d * s := by positivity
    have h := mul_lt_mul_of_pos_right hq h12
    have hR : ((5 / 6) * (2 * (d * s))⁻¹) * (12 * d * s) = 5 := by field_simp; ring
    have h4 : 12 * d * s * q < 5 := by linarith [h, hR]
    have hnn : 0 ≤ 12 * d * s * q := by positivity
    have hsq : (12 * d * s * q)^2 = 144 * d^2 * s^2 * q^2 := by ring
    have h200 : 1152 * d^2 * s^2 * q^2 ≤ 200 := by nlinarith [h4, hnn, hsq]
    linarith [h200]
  -- `slack`, cleared of denominators (multiplied by `144 s²`).
  have hP3 : 144 * s^2 * (b * β⁻¹) + 200 * (εT * C * d * s^3) ≤ 21 * (1 - εT) := by
    have h := mul_le_mul_of_nonneg_left hslack (show (0:ℝ) ≤ 144 * s^2 by positivity)
    have hL : 144 * s^2 * (b * β⁻¹ + εT * ((25 / 18) * C * d * s))
        = 144 * s^2 * (b * β⁻¹) + 200 * (εT * C * d * s^3) := by ring
    have h4 : ((4 * s)⁻¹)^2 = (16*s^2)⁻¹ := by rw [inv_pow]; congr 1; ring
    have hR : 144 * s^2 * ((1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2)) = 21 * (1 - εT) := by
      rw [h4]; field_simp; ring
    linarith [h, hL, hR]
  -- Key polynomial inequality `16 s² b/β + (1-εT) + 128 εT C d³s⁵q² ≤ 8 s (1-εT) q`.
  have hA1 : 16*s^2*(b*β⁻¹) ≤ (7/3)*(1-εT) - (200/9)*(εT*C*d*s^3) := by linarith [hP3]
  have hmul : εT*C*d*s^3 * (128*d^2*s^2*q^2) ≤ εT*C*d*s^3 * (200/9) :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  have hEeq : εT*C*d*s^3 * (128*d^2*s^2*q^2) = 128 * (εT*C*d^3*s^5*q^2) := by ring
  have hA3 : 16*s^2*(b*β⁻¹) + 128*(εT*C*d^3*s^5*q^2) ≤ (7/3)*(1-εT) := by
    nlinarith [hA1, hmul, hEeq]
  have hA4 : (0:ℝ) ≤ 1 - εT := by linarith
  have hA5 : (1-εT)*(10/3 - 8*s*q) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hA4
    linarith [hP1]
  have hsum : 16*s^2*(b*β⁻¹) + (1-εT) + 128*(εT*C*d^3*s^5*q^2) ≤ 8*s*(1-εT)*q := by
    nlinarith [hA3, hA5]
  -- Divide the polynomial inequality by `16 s²` to obtain the key inequality.
  have hkey : b*β⁻¹ + (1-εT)*(16*s^2)⁻¹ + εT*C*8*d^3*s^3*q^2 ≤ (1-εT)*q*(2*s)⁻¹ := by
    have h1 : 16*s^2 * (b*β⁻¹ + (1-εT)*(16*s^2)⁻¹ + εT*C*8*d^3*s^3*q^2)
        = 16*s^2*(b*β⁻¹) + (1-εT) + 128*(εT*C*d^3*s^5*q^2) := by
      field_simp; ring
    have h2 : 16*s^2 * ((1-εT)*q*(2*s)⁻¹) = 8*s*(1-εT)*q := by field_simp; ring
    have hh : 16*s^2 * (b*β⁻¹ + (1-εT)*(16*s^2)⁻¹ + εT*C*8*d^3*s^3*q^2)
        ≤ 16*s^2 * ((1-εT)*q*(2*s)⁻¹) := by rw [h1, h2]; exact hsum
    exact (mul_le_mul_iff_of_pos_left h16).mp hh
  -- Assemble.
  rw [hD, hE]
  nlinarith [hA, hB, hkey]

end Work.BoseKinLoc.Assembly
