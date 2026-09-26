import Mathlib
import Submission.Work.SphereJordan.halfAnnulusSetup

/-!
# The boundary-vector map determines the direction

`Work.SphereJordan.bdVec z` is the point of the boundary `∂upRect` of the rectangle
`upRect = [1/2,1] × [0,π]` of radial coordinates associated with the direction of `z`; it is
constant on the positive rays (`bdVec_smul_pos`) and, as shown here, injective on the set of
directions.  Equivalently: equality of the boundary vectors forces the two complex numbers to be
positive real multiples of each other.

The proof exhibits an explicit left inverse `dirOfUpRect` of `bdVec` on the unit circle: `dirOfUpRect`
reads off the complex direction `e^{iθ}` from a point of `∂upRect` by inverting the linear
parametrisation of each of the four sides of the rectangle.  The only analytic input is the
elementary relation between `arcsin`, `sin`, `cos` and `sqrt`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

/-- Reconstruction of the direction `e^{iθ}` of the unit circle from a point `p` of `∂upRect`: the
four branches invert the four sides of the rectangle (`p.1 = 1`, `p.2 = π`, `p.1 = 1/2`, `p.2 = 0`).
The branches are listed so that the points of the boundary are matched, in order, with
`θ ∈ [0, π/2]`, `θ ∈ [π/2, π]`, `θ ∈ [π, 3π/2]` and `θ ∈ [3π/2, 2π]`. -/
def dirOfUpRect (p : ℝ × ℝ) : ℂ :=
  if p.1 = 1 then Complex.exp ((p.2 / 2 : ℝ) * Complex.I)
  else if p.2 = Real.pi then Complex.exp (((Real.pi * (3/2 - p.1)) : ℝ) * Complex.I)
  else if p.1 = 1/2 then Complex.exp (((3*Real.pi - p.2)/2 : ℝ) * Complex.I)
  else Complex.exp (((Real.pi * (p.1 + 1)) : ℝ) * Complex.I)

/-! ## Evaluation of the four branches of `dirOfUpRect` -/

lemma dirOfUpRect_side1 (b : ℝ) :
    dirOfUpRect (1, b) = Complex.exp ((b / 2 : ℝ) * Complex.I) := by
  simp [dirOfUpRect]

lemma dirOfUpRect_side2 (a : ℝ) (ha : a ≠ 1) :
    dirOfUpRect (a, Real.pi) = Complex.exp (((Real.pi * (3/2 - a)) : ℝ) * Complex.I) := by
  simp only [dirOfUpRect]
  rw [if_neg ha]
  simp

lemma dirOfUpRect_side3 (b : ℝ) (hb : b ≠ Real.pi) :
    dirOfUpRect (1/2, b) = Complex.exp (((3*Real.pi - b)/2 : ℝ) * Complex.I) := by
  simp only [dirOfUpRect]
  rw [if_neg (by norm_num : (1/2:ℝ) ≠ 1), if_neg (fun h => hb h)]
  simp

lemma dirOfUpRect_side4 (a : ℝ) (ha1 : a ≠ 1) (ha2 : a ≠ 1/2) :
    dirOfUpRect (a, 0) = Complex.exp (((Real.pi * (a + 1)) : ℝ) * Complex.I) := by
  simp only [dirOfUpRect]
  rw [if_neg ha1, if_neg (fun h => Real.pi_ne_zero h.symm), if_neg ha2]

lemma sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi, Real.sin_pi_div_two]

lemma cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_two,
    neg_zero]

/-! ## `dirOfUpRect` inverts `bdVec` on the unit circle -/

theorem dirOfUpRect_bdVec (w : ℂ) (hw : ‖w‖ = 1) : dirOfUpRect (bdVec w) = w := by
  have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h := Complex.sq_norm w
    rw [hw] at h
    rw [Complex.normSq_apply] at h
    nlinarith
  have hy_le : w.im ≤ 1 := by nlinarith [sq_nonneg w.re]
  have hy_ge : -1 ≤ w.im := by nlinarith [sq_nonneg w.re]
  have hy'_le : -w.im ≤ 1 := by nlinarith [sq_nonneg w.re]
  have hy'_ge : -1 ≤ -w.im := by nlinarith [sq_nonneg w.re]
  have hnorm : w.im / ‖w‖ = w.im := by rw [hw, div_one]
  have hnorm' : -w.im / ‖w‖ = -w.im := by rw [hw, div_one]
  by_cases h1 : 0 ≤ w.im
  · by_cases h2 : 0 ≤ w.re
    · -- `Im w ≥ 0`, `Re w ≥ 0`: the right side `p.1 = 1`
      rw [bdVec, if_pos h1, if_pos h2, hnorm, dirOfUpRect_side1]
      rw [show (2 * Real.arcsin w.im) / 2 = Real.arcsin w.im by ring]
      apply Complex.ext
      · rw [Complex.exp_ofReal_mul_I_re, Real.cos_arcsin]
        have h1' : 1 - w.im ^ 2 = w.re ^ 2 := by linarith
        rw [h1', Real.sqrt_sq_eq_abs, abs_of_nonneg h2]
      · rw [Complex.exp_ofReal_mul_I_im]
        exact Real.sin_arcsin hy_ge hy_le
    · -- `Im w ≥ 0`, `Re w < 0`: the top side `p.2 = π`
      rw [bdVec, if_pos h1, if_neg h2]
      have hre_neg : w.re < 0 := lt_of_not_ge h2
      have hp1 : (1/2 + Real.arcsin w.im / Real.pi) ≠ 1 := by
        intro h
        have h' : Real.arcsin w.im = Real.pi / 2 := by
          have h2' : Real.arcsin w.im / Real.pi = 1/2 := by linarith
          rw [div_eq_iff Real.pi_ne_zero] at h2'
          linarith
        have hy1 : w.im = 1 := by
          have hs := Real.sin_arcsin hy_ge hy_le
          rw [h', Real.sin_pi_div_two] at hs
          exact hs.symm
        have hre0 : w.re = 0 := by
          have : w.re ^ 2 = 0 := by nlinarith [hsq]
          exact sq_eq_zero_iff.mp this
        linarith
      rw [hnorm, dirOfUpRect_side2 _ hp1]
      rw [show Real.pi * (3/2 - (1/2 + Real.arcsin w.im / Real.pi)) = Real.pi - Real.arcsin w.im by
        field_simp; ring]
      apply Complex.ext
      · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_sub, Real.cos_arcsin]
        have h1' : 1 - w.im ^ 2 = w.re ^ 2 := by linarith
        rw [h1', Real.sqrt_sq_eq_abs, abs_of_neg hre_neg]
        ring
      · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub]
        exact Real.sin_arcsin hy_ge hy_le
  · by_cases h2 : 0 ≤ w.re
    · -- `Im w < 0`, `Re w ≥ 0`: the bottom side `p.2 = 0`
      rw [bdVec, if_neg h1, if_pos h2, hnorm']
      have him_neg : w.im < 0 := lt_of_not_ge h1
      have hp1 : (1 - Real.arcsin (-w.im) / Real.pi) ≠ 1 := by
        intro h
        have h2' : Real.arcsin (-w.im) / Real.pi = 0 := by linarith
        have h3 : Real.arcsin (-w.im) = 0 := by
          rcases div_eq_zero_iff.mp h2' with hh | hh
          · exact hh
          · exact absurd hh Real.pi_ne_zero
        have : -w.im = 0 := Real.arcsin_eq_zero_iff.mp h3
        linarith
      by_cases hcase : (1 - Real.arcsin (-w.im) / Real.pi) = 1/2
      · -- the corner `w = -I`
        have ha : Real.arcsin (-w.im) = Real.pi / 2 := by
          have h2' : Real.arcsin (-w.im) / Real.pi = 1/2 := by linarith
          rw [div_eq_iff Real.pi_ne_zero] at h2'
          linarith
        have hy1 : w.im = -1 := by
          have hs := Real.sin_arcsin hy'_ge hy'_le
          rw [ha, Real.sin_pi_div_two] at hs
          linarith
        have hre0 : w.re = 0 := by
          have : w.re ^ 2 = 0 := by nlinarith [hsq]
          exact sq_eq_zero_iff.mp this
        rw [hcase, dirOfUpRect_side3 0 (fun h => Real.pi_ne_zero h.symm)]
        rw [show (3 * Real.pi - 0) / 2 = 3 * Real.pi / 2 by ring]
        apply Complex.ext
        · rw [Complex.exp_ofReal_mul_I_re, cos_three_pi_div_two]; exact hre0.symm
        · rw [Complex.exp_ofReal_mul_I_im, sin_three_pi_div_two]; exact hy1.symm
      · rw [dirOfUpRect_side4 _ hp1 hcase]
        rw [show Real.pi * ((1 - Real.arcsin (-w.im) / Real.pi) + 1)
            = 2 * Real.pi - Real.arcsin (-w.im) by field_simp; ring]
        apply Complex.ext
        · rw [Complex.exp_ofReal_mul_I_re, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi,
            one_mul, zero_mul, add_zero, Real.cos_arcsin]
          have h1' : 1 - (-w.im) ^ 2 = w.re ^ 2 := by nlinarith [hsq]
          rw [h1', Real.sqrt_sq_eq_abs, abs_of_nonneg h2]
        · rw [Complex.exp_ofReal_mul_I_im, Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi,
            one_mul, zero_mul, zero_sub]
          rw [Real.sin_arcsin hy'_ge hy'_le]
          ring
    · -- `Im w < 0`, `Re w < 0`: the left side `p.1 = 1/2`
      rw [bdVec, if_neg h1, if_neg h2, hnorm']
      have him_neg : w.im < 0 := lt_of_not_ge h1
      have hre_neg : w.re < 0 := lt_of_not_ge h2
      have hp2 : Real.pi - 2 * Real.arcsin (-w.im) ≠ Real.pi := by
        intro h
        have h' : Real.arcsin (-w.im) = 0 := by linarith
        have : -w.im = 0 := Real.arcsin_eq_zero_iff.mp h'
        linarith
      rw [dirOfUpRect_side3 _ hp2]
      rw [show (3 * Real.pi - (Real.pi - 2 * Real.arcsin (-w.im))) / 2
          = Real.pi + Real.arcsin (-w.im) by ring]
      apply Complex.ext
      · rw [Complex.exp_ofReal_mul_I_re,
          show Real.pi + Real.arcsin (-w.im) = Real.arcsin (-w.im) + Real.pi by ring,
          Real.cos_add_pi, Real.cos_arcsin]
        have h1' : 1 - (-w.im) ^ 2 = w.re ^ 2 := by nlinarith [hsq]
        rw [h1', Real.sqrt_sq_eq_abs, abs_of_neg hre_neg]
        ring
      · rw [Complex.exp_ofReal_mul_I_im,
          show Real.pi + Real.arcsin (-w.im) = Real.arcsin (-w.im) + Real.pi by ring,
          Real.sin_add_pi]
        rw [Real.sin_arcsin hy'_ge hy'_le]
        ring

/-- On nonzero inputs, `dirOfUpRect (bdVec z)` recovers the unit vector in the direction of `z`. -/
lemma dirOfUpRect_bdVec_smul_inv (z : ℂ) (hz : z ≠ 0) :
    dirOfUpRect (bdVec z) = ‖z‖⁻¹ • z := by
  have hnorm : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  rw [← bdVec_smul_pos z (inv_pos.mpr (norm_pos_iff.mpr hz))]
  exact dirOfUpRect_bdVec _ hnorm

theorem bdVec_eq_imp_smul (z z' : ℂ) (hz : z ≠ 0) (hz' : z' ≠ 0) (h : Work.SphereJordan.bdVec z = Work.SphereJordan.bdVec z') : ∃ c : ℝ, 0 < c ∧ z' = c • z := by
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnz' : ‖z'‖ ≠ 0 := norm_ne_zero_iff.mpr hz'
  have key : ‖z‖⁻¹ • z = ‖z'‖⁻¹ • z' := by
    rw [← dirOfUpRect_bdVec_smul_inv z hz, ← dirOfUpRect_bdVec_smul_inv z' hz', h]
  refine ⟨‖z'‖ * ‖z‖⁻¹, mul_pos (norm_pos_iff.mpr hz') (inv_pos.mpr (norm_pos_iff.mpr hz)), ?_⟩
  rw [mul_smul, key, smul_smul, mul_inv_cancel₀ hnz', one_smul]

end

end Work.SphereJordan
