import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.kf_sub_le_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

/-- Pure real-variable arithmetic: if `0 < a ≤ b` then

`6 * a ^ 2 / b ^ 3 ≤ 10000 * a ^ (3/2) * b ^ (-(5/2))`.

The two sides differ by the factor `(a/b)^{1/2} ≤ 1`. -/
private lemma rpow_six_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    6 * a ^ (2:ℕ) / b ^ (3:ℕ) ≤ 10000 * a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by
  have ha2 : a ^ (2:ℕ) = a ^ ((3:ℝ)/2) * a ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_natCast a 2, show (((2:ℕ)):ℝ) = (3:ℝ)/2 + 1/2 by norm_num,
      Real.rpow_add ha]
  have hb3 : b ^ (3:ℕ) = b ^ ((5:ℝ)/2) * b ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_natCast b 3, show (((3:ℕ)):ℝ) = (5:ℝ)/2 + 1/2 by norm_num,
      Real.rpow_add hb]
  have hkey : a ^ ((1:ℝ)/2) * b ^ (-(1:ℝ)/2) ≤ 1 := by
    have h1 : b ^ (-(1:ℝ)/2) = (b ^ ((1:ℝ)/2))⁻¹ := by
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hb)]
    rw [h1, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hb _)]
    exact Real.rpow_le_rpow (le_of_lt ha) hab (by norm_num)
  have hmain : a ^ (2:ℕ) / b ^ (3:ℕ) ≤ a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by
    calc a ^ (2:ℕ) / b ^ (3:ℕ)
        = (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) * (a ^ ((1:ℝ)/2) * b ^ (-(1:ℝ)/2)) := by
          rw [ha2, hb3, show (-(5:ℝ)/2) = -((5:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hb),
              show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hb)]
          field_simp
      _ ≤ (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) * 1 :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by ring
  have h6 : 6 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2))
      ≤ 10000 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) :=
    by nlinarith [(by positivity : (0:ℝ) ≤ a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2))]
  calc 6 * a ^ (2:ℕ) / b ^ (3:ℕ) = 6 * (a ^ (2:ℕ) / b ^ (3:ℕ)) := by ring
    _ ≤ 6 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) := by linarith [hmain]
    _ ≤ 10000 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) := h6
    _ = 10000 * a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by ring

/-- **Second-order Taylor expansion of the Newtonian kernel `x ↦ ‖x‖⁻¹`.**

For `2 ‖h‖ ≤ ‖z‖` the remainder of the first-order expansion
`‖z + h‖⁻¹ = ‖z‖⁻¹ - ⟪kf z, h⟫ + O(‖h‖^{3/2} ‖z‖^{-5/2})` is bounded by
`10⁴ ‖h‖^{3/2} ‖z‖^{-5/2}`, where `kf z = ‖z‖⁻³ • z` is the gradient of `‖·‖⁻¹`
(`⟪kf z, h⟫ = ⟪z, h⟫ / ‖z‖³`).

The proof is the exact identity (`s = ‖z‖`, `w = ‖z + h‖`, `A = ⟪z, h⟫`, `T = s³ w (s+w)`)

`(w⁻¹ - s⁻¹ + A/s³) · T = A (w (s+w) - 2 s²) - s² ‖h‖²`,

following from `w² = s² + 2A + ‖h‖²`, together with the bounds
`|A| ≤ s ‖h‖`, `|w (s+w) - 2 s²| = |3 s (w-s) + (w-s)²| ≤ (7/2) s ‖h‖` (using
`|w - s| ≤ ‖h‖` and `‖h‖ ≤ s/2`) and `T ≥ (3/4) s⁵` (using `s/2 ≤ w ≤ 3s/2`).
This gives the bound `6 ‖h‖² / ‖z‖³`, which is at most
`6 ‖h‖^{3/2} ‖z‖^{-5/2} ≤ 10⁴ ‖h‖^{3/2} ‖z‖^{-5/2}` (`rpow_six_le`). -/
theorem abs_inv_norm_taylor_residual_le {z h : Work.FTS.BSSwirl.R3} (hz : 2 * ‖h‖ ≤ ‖z‖) :
    |(‖z + h‖)⁻¹ - (‖z‖)⁻¹ + inner ℝ (Work.StabilityFar.Decay.kf z) h|
      ≤ 10000 * ‖h‖ ^ ((3 : ℝ) / 2) * ‖z‖ ^ (-(5 : ℝ) / 2) := by
  rcases eq_or_lt_of_le (norm_nonneg h) with hh0 | hhpos
  · -- degenerate case `h = 0`
    have h0 : h = 0 := by rw [← norm_eq_zero]; exact hh0.symm
    rw [h0]
    simp [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0)]
  · -- main case
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) hz
    set s : ℝ := ‖z‖ with hsdef
    set w : ℝ := ‖z + h‖ with hwdef
    set A : ℝ := inner ℝ z h with hAdef
    have hs : 0 < s := by rw [hsdef]; exact hzpos
    have hhle : ‖h‖ ≤ s / 2 := by rw [hsdef]; linarith
    have hAle : |A| ≤ s * ‖h‖ := by
      rw [hAdef, hsdef]; exact abs_real_inner_le_norm z h
    have hwsub : |w - s| ≤ ‖h‖ := by
      have hd : (z + h) - z = h := by abel
      have h := abs_norm_sub_norm_le (z + h) z
      rw [hd] at h
      simpa [hwdef, hsdef] using h
    have hw : 0 < w := by
      have h1 : s - w ≤ ‖h‖ := by
        have := (abs_le.mp hwsub).1; linarith
      linarith [hhle, hs]
    have hwlow : s/2 ≤ w := by
      have h1 : s - w ≤ ‖h‖ := by
        have := (abs_le.mp hwsub).1; linarith
      linarith [hhle]
    -- the exact second-order identity
    have hR : (w)⁻¹ - (s)⁻¹ + (s^3)⁻¹ * A
        = (A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2) / (s^3 * w * (s+w)) := by
      rw [hsdef, hwdef, hAdef]
      have hw2 : ‖z + h‖^2 = ‖z‖^2 + 2 * (inner ℝ z h) + ‖h‖^2 := norm_add_sq_real z h
      have hzn : ‖z‖ ≠ 0 := by rw [← hsdef]; exact ne_of_gt hs
      have hwn : ‖z + h‖ ≠ 0 := by rw [← hwdef]; exact ne_of_gt hw
      have hsw : ‖z‖ + ‖z+h‖ ≠ 0 := by positivity
      field_simp
      ring_nf
      rw [hw2]
      ring
    -- the two elementary bounds on the numerator
    have hD : |w * (s + w) - 2 * s^2| ≤ 7/2 * s * ‖h‖ := by
      have hfac : w * (s + w) - 2 * s^2 = 3 * s * (w - s) + (w - s)^2 := by ring
      rw [hfac]
      have h1 : |3 * s * (w - s)| ≤ 3 * s * ‖h‖ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3), abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left hwsub (by positivity)
      have h2 : |(w - s)^2| ≤ (s/2) * ‖h‖ := by
        have h3 : |w - s| ≤ s/2 := le_trans hwsub hhle
        rw [abs_sq, ← sq_abs]
        nlinarith [abs_nonneg (w - s), h3, hwsub]
      calc |3 * s * (w - s) + (w - s)^2| ≤ |3 * s * (w - s)| + |(w - s)^2| :=
            abs_add_le _ _
        _ ≤ 3 * s * ‖h‖ + (s/2) * ‖h‖ := by linarith
        _ = 7/2 * s * ‖h‖ := by ring
    have hnum : |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2| ≤ 9/2 * s^2 * ‖h‖^2 := by
      have h1 : |A * (w*(s+w) - 2*s^2)| ≤ 7/2 * s^2 * ‖h‖^2 := by
        rw [abs_mul]
        calc |A| * |w*(s+w) - 2*s^2| ≤ (s * ‖h‖) * (7/2 * s * ‖h‖) :=
              mul_le_mul hAle hD (abs_nonneg _) (by positivity)
          _ = 7/2 * s^2 * ‖h‖^2 := by ring
      have htri : |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2|
          ≤ |A * (w*(s+w) - 2*s^2)| + |s^2 * ‖h‖^2| := by
        rw [sub_eq_add_neg, ← abs_neg (s^2 * ‖h‖^2)]
        exact abs_add_le _ _
      have h2 : |s^2 * ‖h‖^2| = s^2 * ‖h‖^2 := abs_of_nonneg (by positivity)
      calc |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2|
          ≤ |A * (w*(s+w) - 2*s^2)| + |s^2 * ‖h‖^2| := htri
        _ = |A * (w*(s+w) - 2*s^2)| + s^2 * ‖h‖^2 := by rw [h2]
        _ ≤ 7/2 * s^2 * ‖h‖^2 + s^2 * ‖h‖^2 := by linarith [h1]
        _ = 9/2 * s^2 * ‖h‖^2 := by ring
    -- the lower bound for the denominator
    have hT : 0 < s^3 * w * (s+w) := by positivity
    have hTlow : 3/4 * s^5 ≤ s^3 * w * (s+w) := by
      have h2 : 3*s/2 ≤ s + w := by linarith
      calc 3/4 * s^5 = s^3 * (s/2) * (3*s/2) := by ring
        _ ≤ s^3 * w * (s+w) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hwlow (by positivity)) h2
              (by positivity) (by positivity)
    have hRbound : |(w)⁻¹ - (s)⁻¹ + (s^3)⁻¹ * A| ≤ 6 * ‖h‖^2 / s^3 := by
      rw [hR, abs_div, abs_of_pos hT]
      have h1 : |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2| / (s^3 * w * (s+w))
          ≤ (9/2 * s^2 * ‖h‖^2) / (s^3 * w * (s+w)) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hT)
      have h2 : (9/2 * s^2 * ‖h‖^2) / (s^3 * w * (s+w))
          ≤ (9/2 * s^2 * ‖h‖^2) / (3/4 * s^5) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hTlow
      have h3 : (9/2 * s^2 * ‖h‖^2) / (3/4 * s^5) = 6 * ‖h‖^2 / s^3 := by
        field_simp
        ring
      linarith [h1, h2, h3.le, h3.ge]
    -- turn `inner ℝ (kf z) h` into `(s^3)⁻¹ * A`
    have hinner : inner ℝ (Work.StabilityFar.Decay.kf z) h = (s^3)⁻¹ * A := by
      rw [hsdef, hAdef, Work.StabilityFar.Decay.kf, inner_smul_left]
      simp
    rw [hinner]
    exact hRbound.trans (rpow_six_le ‖h‖ s hhpos hs (by linarith [hhle]))

end Work.FTS.BSSwirl
