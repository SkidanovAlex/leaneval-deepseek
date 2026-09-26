import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.CuspDecay.j_annulus_lower
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E4Fun_upper_half
import Submission.Work.Asymptotics.divisor_qdiff_lower
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.CKFinal.LineDecay.orbit_classification
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.qParamFun_line_half
import Submission.Work.CKFinal.LineDecay.Delta_first_order_lin
import Submission.Work.CKFinal.LineDecay.E4_two_term_explicit
import Submission.Work.CKFinal.LineDecay.DenomLower_lines

/-!
# Growth of `K` on the vertical lines `Re z ∈ {-1,0,1}` and above the pole

For `τ` on one of the two critical lines `Re τ = ±1/2` with `Im τ ≥ 12`, and for
`z = ofComplex (x + i r)` either with `x ∈ {-1,0,1}`, `r ≥ 1` or with `|x| ≤ 1`,
`r ≥ Im τ + 1`, the CKMRV kernel `K = (K₊ + K₋)/2` satisfies

  `‖K(τ,z)‖ ≤ C (1+r)^N exp (2π r)`.

This is the "top edge" growth bound used in the contour shift of CKMRV §5.3: together with
`λ > 2π` it makes `K(τ,x+iR) e^{iλ(x+iR)} → 0` as `R → ∞`.

The proof is the *cleared kernel* route: off the coincidence set
`K = K^{clear}/(Δ(τ)Δ(z)^e (j τ - j z))` (`Work.Kernels.ClearLink.KPlusClear_eq_smul`),
`K^{clear}` has moderate growth in `z` (`Work.Kernels.KernelClear_growth_z`), and the CKMRV
divisor is bounded below by `(1/8) exp(-2π min (Im z) (Im τ))` on the region (proved here as
`divisor_lower_strip`, from the two first-order cusp expansions `Δ = q + O(q/20)` and
`E₄ = 1 + 240q + O(q²)`, following the sign-alignment argument of
`Submission/Work/CKFinal/LineDecay/DenomLower_lines.lean`).  Since `Δ(z) → 0` like `q(z)`,
the single power of `Δ(z)` in the divisor is exactly what produces the factor `e^{2π Im z}`.
-/

set_option maxHeartbeats 2000000

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-! ## The nome at integer real parts -/

/-- `q(z) = e^{-2π Im z}` is a *positive real* number when `Re z ∈ ℤ`. -/
private lemma qParamFun_of_re_int (z : ℍ) (hz : z.re = -1 ∨ z.re = 0 ∨ z.re = 1) :
    Work.Kernels.qParamFun z = ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, z.re = (n : ℝ) := by
    rcases hz with h | h | h
    · exact ⟨-1, by rw [h]; norm_num⟩
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  have hcoe : (z : ℂ) = (n : ℂ) + (z.im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im (z : ℂ)]
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hn]
    push_cast
    ring
  show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)) = _
  rw [hcoe]
  have h1 : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  have h2 : 2 * (Real.pi : ℂ) * Complex.I * ((z.im : ℂ) * Complex.I)
      = ((-(2 * Real.pi * z.im) : ℝ) : ℂ) := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((z.im : ℂ) * Complex.I)
        = (2 * (Real.pi : ℂ) * (z.im : ℂ)) * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]
    push_cast
    ring
  rw [mul_add, h1, h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
    Complex.ofReal_exp]

/-! ## Elementary exponential bounds -/

/-- `e^{-2πt} ≤ 1/512` for `t ≥ 1`. -/
private lemma exp_neg_two_pi_im_le_inv512 {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-(2 * Real.pi * t)) ≤ 1 / 512 := by
  have h1 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
  exact le_trans h1 Work.Asymptotics.exp_neg_two_pi_le_inv512

/-- `e^{-2πt} ≤ 1/40000` for `t ≥ 12`. -/
private lemma exp_neg_two_pi_im_le_small {t : ℝ} (ht : 12 ≤ t) :
    Real.exp (-(2 * Real.pi * t)) ≤ 1 / 40000 := by
  have h1 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(24 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
  have h2 : Real.exp (-(24 * Real.pi)) = (Real.exp (-(2 * Real.pi))) ^ 12 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 : Real.exp (-(2 * Real.pi)) ≤ 1 / 512 := Work.Asymptotics.exp_neg_two_pi_le_inv512
  have h4 : (Real.exp (-(2 * Real.pi))) ^ 12 ≤ ((1 : ℝ) / 512) ^ 12 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h3 12
  have h5 : ((1 : ℝ) / 512) ^ 12 ≤ 1 / 40000 := by norm_num
  calc Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(24 * Real.pi)) := h1
    _ = (Real.exp (-(2 * Real.pi))) ^ 12 := h2
    _ ≤ ((1 : ℝ) / 512) ^ 12 := h4
    _ ≤ 1 / 40000 := h5

/-- `e^{-2π Im z} ≤ ‖z‖`-type control: for `-1 ≤ Re z ≤ 1` the point `z` is bounded by
`1 + Im z`. -/
private lemma coe_norm_le_one_add_im (z : ℍ) (h1 : -1 ≤ z.re) (h2 : z.re ≤ 1) :
    ‖(z : ℂ)‖ ≤ 1 + z.im := by
  have hcoe : (z : ℂ) = ((z.re : ℂ)) + ((z.im : ℂ)) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im (z : ℂ)]
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  calc ‖(z : ℂ)‖ ≤ ‖((z.re : ℂ))‖ + ‖((z.im : ℂ)) * Complex.I‖ := by
        rw [hcoe]; exact norm_add_le _ _
    _ = |z.re| + |z.im| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 + z.im := by
        rw [abs_of_pos z.im_pos]; linarith [abs_le.mpr ⟨h1, h2⟩]

/-! ## Two explicit bounds for `E₄³` -/

/-- If `E = 1 + 240a + ξ` with `a ≥ 0`, `a ≤ 1/512` and `‖ξ‖ ≤ 79a`, then `E³` has real part
at least `1/2` and norm at most `5`. -/
private lemma cube_bounds_real {E : ℂ} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 512)
    (hξ : ‖E - 1 - 240 * (a : ℂ)‖ ≤ 79 * a) :
    (1 / 2 : ℝ) ≤ (E ^ 3).re ∧ ‖E ^ 3‖ ≤ 5 := by
  set ξ : ℂ := E - 1 - 240 * (a : ℂ) with hξdef
  have hE : E = 1 + 240 * (a : ℂ) + ξ := by rw [hξdef]; ring
  rw [hξdef] at hξ
  have h79a0 : (0 : ℝ) ≤ 79 * a := by linarith
  -- numerical constants
  have hA : (79 : ℝ) * a ≤ 1 / 4 := by
    have h : (79 : ℝ) * a ≤ 79 * (1 / 512) := by nlinarith [ha, ha0]
    linarith [h, (by norm_num : (79 : ℝ) * (1 / 512) ≤ 1 / 4)]
  have hB : (319 : ℝ) * a ≤ 2 / 3 := by
    have h : (319 : ℝ) * a ≤ 319 * (1 / 512) := by nlinarith [ha, ha0]
    linarith [h, (by norm_num : (319 : ℝ) * (1 / 512) ≤ 2 / 3)]
  have hξre_lo : -(79 * a) ≤ ξ.re := by
    have h1 : -(‖ξ‖) ≤ ξ.re := neg_norm_le_re ξ
    linarith
  have hξre_hi : ξ.re ≤ 79 * a := le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm ξ) hξ)
  have hξim : |ξ.im| ≤ 79 * a := le_trans (Complex.abs_im_le_norm ξ) hξ
  have hEre : E.re = 1 + 240 * a + ξ.re := by rw [hE]; simp [Complex.add_re, Complex.mul_re]
  have hEim : E.im = ξ.im := by rw [hE]; simp [Complex.add_im, Complex.mul_im]
  have hEnorm : ‖E‖ ≤ 1 + 319 * a := by
    rw [hE]
    have h1 : ‖(1 : ℂ) + 240 * (a : ℂ)‖ = 1 + 240 * a := by
      rw [show (1 : ℂ) + 240 * (a : ℂ) = (((1 + 240 * a : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    calc ‖1 + 240 * (a : ℂ) + ξ‖ ≤ ‖1 + 240 * (a : ℂ)‖ + ‖ξ‖ := norm_add_le _ _
      _ ≤ (1 + 240 * a) + 79 * a := by
          rw [h1]; linarith
      _ = 1 + 319 * a := by ring
  constructor
  · have h1 : (1 : ℝ) ≤ E.re := by rw [hEre]; linarith
    have h2 : E.re ≤ 5 / 3 := by rw [hEre]; linarith
    have h3 : |E.im| ≤ 79 * a := by rw [hEim]; exact hξim
    have h5 := re_cube_lower (w := E) (xl := 1) (xh := 5 / 3) (d := 79 * a) h1 h2 h3
      (by norm_num) h79a0
    have h6 : (1 / 2 : ℝ) ≤ 1 - 3 * (5 / 3) * (79 * a) ^ 2 := by
      have h7 : (79 * a) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        apply pow_le_pow_left₀ h79a0 hA
      linarith
    linarith
  · calc ‖E ^ 3‖ = ‖E‖ ^ 3 := norm_pow E 3
      _ ≤ (5 / 3) ^ 3 := by
          apply pow_le_pow_left₀ (norm_nonneg E)
          linarith
      _ ≤ 5 := by norm_num

/-- If `E = 1 + ξ` with `a ≥ 0`, `a ≤ 1/40000` and `‖ξ‖ ≤ 241a`, then `E³` has real part at
least `1/2` and norm at most `2`. -/
private lemma cube_bounds_small {E : ℂ} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 40000)
    (hξ : ‖E - 1‖ ≤ 241 * a) :
    (1 / 2 : ℝ) ≤ (E ^ 3).re ∧ ‖E ^ 3‖ ≤ 2 := by
  set ξ : ℂ := E - 1 with hξdef
  have hE : E = 1 + ξ := by rw [hξdef]; ring
  rw [hξdef] at hξ
  have h241 : (241 : ℝ) * a ≤ 1 / 100 := by
    have h : (241 : ℝ) * a ≤ 241 * (1 / 40000) := by nlinarith [ha, ha0]
    linarith [h, (by norm_num : (241 : ℝ) * (1 / 40000) ≤ 1 / 100)]
  have hξ' : ‖ξ‖ ≤ 1 / 100 := le_trans hξ h241
  have hξre_lo : -(1 / 100 : ℝ) ≤ ξ.re := by
    have h1 : -(‖ξ‖) ≤ ξ.re := neg_norm_le_re ξ
    linarith
  have hξre_hi : ξ.re ≤ 1 / 100 := le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm ξ) hξ')
  have hξim : |ξ.im| ≤ 1 / 100 := le_trans (Complex.abs_im_le_norm ξ) hξ'
  have hEre : E.re = 1 + ξ.re := by rw [hE]; simp
  have hEim : E.im = ξ.im := by rw [hE]; simp
  have hEnorm : ‖E‖ ≤ 101 / 100 := by
    rw [hE]
    have h1 : ‖(1 : ℂ) + ξ‖ ≤ 1 + ‖ξ‖ := by simpa using norm_add_le (1 : ℂ) ξ
    linarith
  constructor
  · have h1 : (99 / 100 : ℝ) ≤ E.re := by rw [hEre]; linarith
    have h2 : E.re ≤ 101 / 100 := by rw [hEre]; linarith
    have h3 : |E.im| ≤ 1 / 100 := by rw [hEim]; linarith
    have h4 := re_cube_lower (w := E) (xl := 99 / 100) (xh := 101 / 100) (d := 1 / 100) h1 h2 h3
      (by norm_num) (by norm_num)
    have h5 : (1 / 2 : ℝ) ≤ (99 / 100 : ℝ) ^ 3 - 3 * (101 / 100) * (1 / 100) ^ 2 := by norm_num
    linarith
  · calc ‖E ^ 3‖ = ‖E‖ ^ 3 := norm_pow E 3
      _ ≤ (101 / 100) ^ 3 := pow_le_pow_left₀ (norm_nonneg E) hEnorm 3
      _ ≤ 2 := by norm_num


/-! ## First-order bounds for `Δ` and `E₄` -/

/-- The two-term expansion of `E₄` controls `‖E₄ - 1‖` on `{Im ≥ 12}` by `241 e^{-2π Im}`. -/
private lemma E4_sub_one_le (z : ℍ) (hz : 12 ≤ z.im) :
    ‖Work.Kernels.E4Fun z - 1‖ ≤ 241 * Real.exp (-(2 * Real.pi * z.im)) := by
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have h := E4_two_term_explicit z hz1
  have hq := Work.Asymptotics.norm_qParamFun z
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 / 40000 := by
    rw [hq]; exact exp_neg_two_pi_im_le_small hz
  have h3 : ‖Work.Kernels.E4Fun z - 1‖
      ≤ ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
        + 240 * ‖Work.Kernels.qParamFun z‖ := by
    have h4 : ‖Work.Kernels.E4Fun z - 1‖
        = ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
            + 240 * Work.Kernels.qParamFun z‖ := by congr 1; ring
    rw [h4]
    calc ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
            + 240 * Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
          + ‖(240 : ℂ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
      _ = ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
          + 240 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_mul]; norm_num
  have h5 : 40000 * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ := by
    have h6 : 40000 * ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      nlinarith [hq1, norm_nonneg (Work.Kernels.qParamFun z)]
    calc 40000 * ‖Work.Kernels.qParamFun z‖ ^ 2
        = (40000 * ‖Work.Kernels.qParamFun z‖) * ‖Work.Kernels.qParamFun z‖ := by ring
      _ ≤ 1 * ‖Work.Kernels.qParamFun z‖ := mul_le_mul_of_nonneg_right h6 (norm_nonneg _)
      _ = ‖Work.Kernels.qParamFun z‖ := one_mul _
  calc ‖Work.Kernels.E4Fun z - 1‖
      ≤ ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
        + 240 * ‖Work.Kernels.qParamFun z‖ := h3
    _ ≤ 40000 * ‖Work.Kernels.qParamFun z‖ ^ 2 + 240 * ‖Work.Kernels.qParamFun z‖ := by linarith
    _ ≤ ‖Work.Kernels.qParamFun z‖ + 240 * ‖Work.Kernels.qParamFun z‖ := by linarith
    _ = 241 * ‖Work.Kernels.qParamFun z‖ := by ring
    _ = 241 * Real.exp (-(2 * Real.pi * z.im)) := by rw [hq]

/-- If `q(z) = a` is a real number with `a = e^{-2π Im z}`, then the real part of `Δ(z)` is at
least `(19/20)a` in absolute value and its imaginary part is at most `a/20`. -/
private lemma Delta_re_bounds {z : ℍ} (hz : 1 ≤ z.im)
    (hq : Work.Kernels.qParamFun z = ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ)) :
    (19 / 20) * Real.exp (-(2 * Real.pi * z.im)) ≤ (Work.Kernels.DeltaFun z).re ∧
      |(Work.Kernels.DeltaFun z).im| ≤ (1 / 20) * Real.exp (-(2 * Real.pi * z.im)) := by
  have h := Delta_first_order_lin z hz
  have hq' : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [hq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hq', hq] at h
  constructor
  · have h1 : -(‖Work.Kernels.DeltaFun z - ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ)‖)
        ≤ (Work.Kernels.DeltaFun z - ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ)).re :=
      neg_norm_le_re _
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    linarith
  · have h2 : (Work.Kernels.DeltaFun z - ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ)).im
        = (Work.Kernels.DeltaFun z).im := by
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    have h3 : |(Work.Kernels.DeltaFun z - ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ)).im|
        ≤ ‖Work.Kernels.DeltaFun z - ((Real.exp (-(2 * Real.pi * z.im)) : ℝ) : ℂ)‖ :=
      Complex.abs_im_le_norm _
    rw [h2] at h3
    linarith

/-- If `q(w) = -b` is a negative real then `Re(-Δ(w)) ≥ (19/20)b` and `|Im(-Δ(w))| ≤ b/20`. -/
private lemma Delta_neg_re_bounds {w : ℍ} (hw : 1 ≤ w.im) {b : ℝ}
    (hq : Work.Kernels.qParamFun w = -(b : ℂ)) (hb0 : 0 ≤ b) :
    (19 / 20) * b ≤ (-(Work.Kernels.DeltaFun w)).re ∧
      |(-(Work.Kernels.DeltaFun w)).im| ≤ (1 / 20) * b := by
  have h := Delta_first_order_lin w hw
  have hq' : ‖Work.Kernels.qParamFun w‖ = b := by rw [hq, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hb0]
  rw [hq', hq] at h
  have h' : ‖Work.Kernels.DeltaFun w + (b : ℂ)‖ ≤ (1 / 20) * b := by simpa using h
  constructor
  · have h1 : (Work.Kernels.DeltaFun w + (b : ℂ)).re
        ≤ ‖Work.Kernels.DeltaFun w + (b : ℂ)‖ := Complex.re_le_norm _
    have h2 : (-(Work.Kernels.DeltaFun w)).re
        = b - (Work.Kernels.DeltaFun w + (b : ℂ)).re := by
      rw [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; ring
    rw [h2]; linarith
  · have h2 : (-(Work.Kernels.DeltaFun w)).im
        = -((Work.Kernels.DeltaFun w + (b : ℂ)).im) := by
      rw [Complex.neg_im, Complex.add_im, Complex.ofReal_im, add_zero]
    have h3 : |(Work.Kernels.DeltaFun w + (b : ℂ)).im|
        ≤ ‖Work.Kernels.DeltaFun w + (b : ℂ)‖ := Complex.abs_im_le_norm _
    rw [h2, abs_neg]
    linarith

/-- `‖Δ(w)‖ ≤ (21/20) e^{-2π Im w}` for `Im w ≥ 1`. -/
private lemma Delta_norm_le (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.DeltaFun w‖ ≤ (21 / 20) * Real.exp (-(2 * Real.pi * w.im)) := by
  have h := Delta_first_order_lin w hw
  have hq := Work.Asymptotics.norm_qParamFun w
  have h3 : ‖Work.Kernels.DeltaFun w‖
      ≤ ‖Work.Kernels.DeltaFun w - Work.Kernels.qParamFun w‖
        + ‖Work.Kernels.qParamFun w‖ := by
    have h4 : ‖Work.Kernels.DeltaFun w‖
        = ‖(Work.Kernels.DeltaFun w - Work.Kernels.qParamFun w)
            + Work.Kernels.qParamFun w‖ := by congr 1; ring
    rw [h4]; exact norm_add_le _ _
  rw [hq] at h h3
  linarith

/-- `‖Δ(w)‖ ≥ (19/20) e^{-2π Im w}` for `Im w ≥ 1`. -/
private lemma Delta_norm_ge (w : ℍ) (hw : 1 ≤ w.im) :
    (19 / 20) * Real.exp (-(2 * Real.pi * w.im)) ≤ ‖Work.Kernels.DeltaFun w‖ := by
  have h := Delta_first_order_lin w hw
  have hq := Work.Asymptotics.norm_qParamFun w
  have h3 : ‖Work.Kernels.qParamFun w‖ - ‖Work.Kernels.DeltaFun w - Work.Kernels.qParamFun w‖
      ≤ ‖Work.Kernels.DeltaFun w‖ := by
    have h4 := norm_sub_norm_le (Work.Kernels.qParamFun w)
      (Work.Kernels.qParamFun w - Work.Kernels.DeltaFun w)
    have h5 : Work.Kernels.qParamFun w - (Work.Kernels.qParamFun w - Work.Kernels.DeltaFun w)
        = Work.Kernels.DeltaFun w := by ring
    rw [h5] at h4
    have h6 : ‖Work.Kernels.qParamFun w - Work.Kernels.DeltaFun w‖
        = ‖Work.Kernels.DeltaFun w - Work.Kernels.qParamFun w‖ := norm_sub_rev _ _
    linarith [h4, le_of_eq h6]
  rw [hq] at h h3
  linarith

/-- **The CKMRV divisor is bounded away from zero on the two-clause region.**

For `τ` on one of the two lines `Re τ = ±1/2` with `Im τ ≥ 12` and for `z` with
`-1 ≤ Re z ≤ 1`, `Im z ≥ 1`, either `Re z ∈ {-1,0,1}` or `Im z ≥ Im τ + 1`, the divisor
`Δ(τ)Δ(z)(j τ - j z)` is at least `(1/8) exp(-2π min (Im z) (Im τ))`.

The two clauses are exactly the two situations in which the two leading terms of
`Δ(z)E₄(τ)³ - Δ(τ)E₄(z)³ = Δ(τ)Δ(z)(jτ - jz)` have *aligned* real parts: for `Re z ∈ ℤ` the
nome `q(z) = e^{-2π Im z}` is a positive real, while `q(τ) = -e^{-2π Im τ}` is a negative real;
and for `Im z ≥ Im τ + 1` the term `Δ(τ)E₄(z)³` dominates the (smaller) term `Δ(z)E₄(τ)³`. -/
private theorem divisor_lower_strip (τ z : ℍ) (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2)
    (him : 12 ≤ τ.im) (hz1 : -1 ≤ z.re) (hz2 : z.re ≤ 1) (hz3 : 1 ≤ z.im)
    (hz4 : z.re = -1 ∨ z.re = 0 ∨ z.re = 1 ∨ τ.im + 1 ≤ z.im) :
    (1 / 8) * Real.exp (-(2 * Real.pi * min z.im τ.im)) ≤
      ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  have him1 : (1 : ℝ) ≤ τ.im := by linarith
  rw [delta_mul_j_sub τ z]
  refine le_trans ?_ (Complex.re_le_norm _)
  set b : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hb
  have hb0 : 0 < b := Real.exp_pos _
  have hb40000 : b ≤ 1 / 40000 := by rw [hb]; exact exp_neg_two_pi_im_le_small him
  have hqτR : Work.Kernels.qParamFun τ = -(b : ℂ) := by
    rw [qParamFun_line_half τ hre, hb]
  have hτR := Delta_neg_re_bounds him1 hqτR hb0.le
  have hEτb := cube_bounds_small (E := Work.Kernels.E4Fun τ) (a := b) hb0.le hb40000
    (E4_sub_one_le τ him)
  have hEτre : (0 : ℝ) ≤ (Work.Kernels.E4Fun τ ^ 3).re := by linarith [hEτb.1]
  have hsplit : (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3
        - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3).re
      = (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3).re
        + ((-(Work.Kernels.DeltaFun τ)) * Work.Kernels.E4Fun z ^ 3).re := by
    have h1 : Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3
          - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3
        = Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3
          + (-(Work.Kernels.DeltaFun τ)) * Work.Kernels.E4Fun z ^ 3 := by ring
    rw [h1, Complex.add_re]
  have hcaseA : (z.re = -1 ∨ z.re = 0 ∨ z.re = 1) →
      (1 / 8) * Real.exp (-(2 * Real.pi * min z.im τ.im))
        ≤ (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3
            - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3).re := by
    intro hx
    set a : ℝ := Real.exp (-(2 * Real.pi * z.im)) with ha
    have ha0 : 0 < a := Real.exp_pos _
    have ha512 : a ≤ 1 / 512 := by rw [ha]; exact exp_neg_two_pi_im_le_inv512 hz3
    have hqzR : Work.Kernels.qParamFun z = (a : ℂ) := by
      rw [qParamFun_of_re_int z hx, ha]
    have hzR := Delta_re_bounds hz3 hqzR
    have hEzξ : ‖Work.Kernels.E4Fun z - 1 - 240 * (a : ℂ)‖ ≤ 79 * a := by
      have h := E4_two_term_explicit z hz3
      have hq := Work.Asymptotics.norm_qParamFun z
      have hq' : ‖Work.Kernels.qParamFun z‖ = a := by rw [hq, ha]
      rw [hq', hqzR] at h
      have h3 : 40000 * a ^ 2 ≤ 79 * a := by
        have h4 : a ^ 2 ≤ (1 / 512) * a := by
          calc a ^ 2 = a * a := by ring
            _ ≤ (1 / 512) * a := mul_le_mul_of_nonneg_right ha512 ha0.le
        calc 40000 * a ^ 2 ≤ 40000 * ((1 / 512) * a) := mul_le_mul_of_nonneg_left h4 (by norm_num)
          _ = (40000 / 512) * a := by ring
          _ ≤ 79 * a := by nlinarith
      linarith
    have hEzb := cube_bounds_real (E := Work.Kernels.E4Fun z) (a := a) ha0.le ha512 hEzξ
    have hEzre : (0 : ℝ) ≤ (Work.Kernels.E4Fun z ^ 3).re := by linarith [hEzb.1]
    have ht1 : (19 / 20) * a * (1 / 2) - (1 / 20) * a * 2
        ≤ (19 / 20) * a * (Work.Kernels.E4Fun τ ^ 3).re
          - (1 / 20) * a * ‖Work.Kernels.E4Fun τ ^ 3‖ := by
      have h1 : (19 / 20) * a * (1 / 2) ≤ (19 / 20) * a * (Work.Kernels.E4Fun τ ^ 3).re :=
        mul_le_mul_of_nonneg_left hEτb.1 (by positivity)
      have h2 : (1 / 20) * a * ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ (1 / 20) * a * 2 :=
        mul_le_mul_of_nonneg_left hEτb.2 (by positivity)
      linarith
    have hterm1 := re_mul_lower (u := Work.Kernels.DeltaFun z) (w := Work.Kernels.E4Fun τ ^ 3)
      (r := (19 / 20) * a) (t := (1 / 20) * a) hzR.1 hzR.2 hEτre (by linarith [ha0])
    have h1 : (3 / 8) * a ≤ (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3).re := by
      linarith [hterm1, ht1]
    have ht2 : (19 / 20) * b * (1 / 2) - (1 / 20) * b * 5
        ≤ (19 / 20) * b * (Work.Kernels.E4Fun z ^ 3).re
          - (1 / 20) * b * ‖Work.Kernels.E4Fun z ^ 3‖ := by
      have h1 : (19 / 20) * b * (1 / 2) ≤ (19 / 20) * b * (Work.Kernels.E4Fun z ^ 3).re :=
        mul_le_mul_of_nonneg_left hEzb.1 (by positivity)
      have h2 : (1 / 20) * b * ‖Work.Kernels.E4Fun z ^ 3‖ ≤ (1 / 20) * b * 5 :=
        mul_le_mul_of_nonneg_left hEzb.2 (by positivity)
      linarith
    have hterm2 := re_mul_lower (u := -(Work.Kernels.DeltaFun τ))
      (w := Work.Kernels.E4Fun z ^ 3) (r := (19 / 20) * b) (t := (1 / 20) * b)
      hτR.1 hτR.2 hEzre (by linarith [hb0])
    have h2 : (9 / 40) * b ≤ ((-(Work.Kernels.DeltaFun τ)) * Work.Kernels.E4Fun z ^ 3).re := by
      linarith [hterm2, ht2]
    have hmin : Real.exp (-(2 * Real.pi * min z.im τ.im)) ≤ a + b := by
      rcases le_total z.im τ.im with h | h
      · rw [min_eq_left h]; linarith [hb0.le]
      · rw [min_eq_right h]; linarith [ha0.le]
    have hmin8 : (1 / 8) * Real.exp (-(2 * Real.pi * min z.im τ.im)) ≤ (1 / 8) * (a + b) :=
      mul_le_mul_of_nonneg_left hmin (by norm_num)
    rw [hsplit]
    linarith [h1, h2, hmin8]
  have hcaseB : (τ.im + 1 ≤ z.im) →
      (1 / 8) * Real.exp (-(2 * Real.pi * min z.im τ.im))
        ≤ (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3
            - Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun z ^ 3).re := by
    intro ht
    set a : ℝ := Real.exp (-(2 * Real.pi * z.im)) with ha
    have ha0 : 0 < a := Real.exp_pos _
    have hz12 : (12 : ℝ) ≤ z.im := by linarith
    have ha40000 : a ≤ 1 / 40000 := by rw [ha]; exact exp_neg_two_pi_im_le_small hz12
    have ha_leb : a ≤ Real.exp (-(2 * Real.pi)) * b := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(2 * Real.pi * (τ.im + 1))) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
      have h2 : Real.exp (-(2 * Real.pi * (τ.im + 1)))
          = Real.exp (-(2 * Real.pi)) * b := by
        rw [hb, ← Real.exp_add]; ring_nf
      rw [← ha, h2] at h1
      exact h1
    have hΔzn : ‖Work.Kernels.DeltaFun z‖ ≤ (21 / 20) * a := by
      have h := Delta_norm_le z hz3
      rw [← ha] at h
      exact h
    have hEzb := cube_bounds_small (E := Work.Kernels.E4Fun z) (a := a) ha0.le ha40000
      (by rw [ha]; exact E4_sub_one_le z hz12)
    have hEzre : (0 : ℝ) ≤ (Work.Kernels.E4Fun z ^ 3).re := by linarith [hEzb.1]
    have ht2 : (19 / 20) * b * (1 / 2) - (1 / 20) * b * 2
        ≤ (19 / 20) * b * (Work.Kernels.E4Fun z ^ 3).re
          - (1 / 20) * b * ‖Work.Kernels.E4Fun z ^ 3‖ := by
      have h1 : (19 / 20) * b * (1 / 2) ≤ (19 / 20) * b * (Work.Kernels.E4Fun z ^ 3).re :=
        mul_le_mul_of_nonneg_left hEzb.1 (by positivity)
      have h2 : (1 / 20) * b * ‖Work.Kernels.E4Fun z ^ 3‖ ≤ (1 / 20) * b * 2 :=
        mul_le_mul_of_nonneg_left hEzb.2 (by positivity)
      linarith
    have hterm2 := re_mul_lower (u := -(Work.Kernels.DeltaFun τ))
      (w := Work.Kernels.E4Fun z ^ 3) (r := (19 / 20) * b) (t := (1 / 20) * b)
      hτR.1 hτR.2 hEzre (by linarith [hb0])
    have h2 : (3 / 8) * b ≤ ((-(Work.Kernels.DeltaFun τ)) * Work.Kernels.E4Fun z ^ 3).re := by
      linarith [hterm2, ht2]
    have h1 : -((21 / 10) * a) ≤ (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3).re := by
      have h3 : ‖Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3‖ ≤ (21 / 10) * a := by
        rw [norm_mul]
        have h5 : ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ ((21 / 20) * a) * 2 :=
          mul_le_mul hΔzn hEτb.2 (norm_nonneg _) (by linarith [ha0])
        linarith
      have h4 := neg_norm_le_re (Work.Kernels.DeltaFun z * Work.Kernels.E4Fun τ ^ 3)
      linarith
    have hsmall : (21 / 10) * a ≤ (1 / 4) * b := by
      have h6 : (21 / 10) * Real.exp (-(2 * Real.pi)) ≤ 1 / 4 := by
        have h5 : Real.exp (-(2 * Real.pi)) ≤ 1 / 512 := Work.Asymptotics.exp_neg_two_pi_le_inv512
        linarith
      calc (21 / 10) * a ≤ (21 / 10) * (Real.exp (-(2 * Real.pi)) * b) :=
            mul_le_mul_of_nonneg_left ha_leb (by norm_num)
        _ = ((21 / 10) * Real.exp (-(2 * Real.pi))) * b := by ring
        _ ≤ (1 / 4) * b := mul_le_mul_of_nonneg_right h6 hb0.le
    have hmin : min z.im τ.im = τ.im := min_eq_right (by linarith)
    rw [hsplit, hmin]
    linarith [h1, h2, hsmall, hb]
  rcases hz4 with hx | hx | hx | ht
  · exact hcaseA (Or.inl hx)
  · exact hcaseA (Or.inr (Or.inl hx))
  · exact hcaseA (Or.inr (Or.inr hx))
  · exact hcaseB ht


/-! ## The kernel bound on the region -/

/-- The kernel bound on the two-clause region, obtained from the cleared kernel bound
(`InP` of `KfunClear`) and the divisor lower bound. -/
private theorem region_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (him : 12 ≤ τ.im) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ z : ℍ, -1 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im →
      (z.re = -1 ∨ z.re = 0 ∨ z.re = 1 ∨ τ.im + 1 ≤ z.im) →
      ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ C * (1 + z.im) ^ N * Real.exp (2 * Real.pi * z.im) := by
  have hsc₀ : ∃ α Nα : ℝ, 0 ≤ α ∧ 0 ≤ Nα ∧
      ∀ z : ℍ, ‖Work.Kernels.KfunClear ℓ d τ z‖ ≤ α * (Work.Kernels.scale z) ^ Nα := by
    have h := (Work.Kernels.moderateGrowthOn_iff_scale Set.univ
        (fun z : ℍ => Work.Kernels.KfunClear ℓ d τ z)).mp
      (Work.Kernels.KernelClear_growth_z ℓ d hd τ).1.2
    simpa using h
  obtain ⟨α, Nα, hα, hNα, hsc⟩ := hsc₀
  set X : ℝ := 8 * α * 4 ^ Nα * (20 / 19) * Real.exp (2 * Real.pi * τ.im) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  refine ⟨max 1 X, Nα, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hNα, ?_⟩
  intro z hz1 hz2 hz3 hz4
  have hdiv := divisor_lower_strip τ z hre him hz1 hz2 hz3 hz4
  have hdivpos : 0 < (1 / 8) * Real.exp (-(2 * Real.pi * min z.im τ.im)) := by positivity
  have hjne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro hJ
    have hz : Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) = 0 := by
      rw [hJ, sub_self, mul_zero]
    rw [hz, norm_zero] at hdiv
    linarith
  -- the cleared bound
  have hcz : ‖Work.Kernels.KfunClear ℓ d τ z‖ ≤ α * 4 ^ Nα * (1 + z.im) ^ Nα := by
    have h1 := hsc z
    have hnorm : ‖(z : ℂ)‖ ≤ 1 + z.im := coe_norm_le_one_add_im z hz1 hz2
    have hinv : (z.im)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ z.im_pos]; exact hz3
    have hscale : Work.Kernels.scale z ≤ 4 * (1 + z.im) := by
      rw [Work.Kernels.scale]; linarith
    calc ‖Work.Kernels.KfunClear ℓ d τ z‖ ≤ α * (Work.Kernels.scale z) ^ Nα := h1
      _ ≤ α * (4 * (1 + z.im)) ^ Nα :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Work.Kernels.scale_pos z).le hscale hNα) hα
      _ = α * 4 ^ Nα * (1 + z.im) ^ Nα := by
          rw [Real.mul_rpow (by norm_num) (by linarith : (0 : ℝ) ≤ 1 + z.im)]
          ring
  -- the cleared identity
  have hclear : ‖Work.Kernels.Kfun ℓ d τ z‖
      = ‖Work.Kernels.KfunClear ℓ d τ z‖ / ‖Work.Kernels.growthPrefactor d τ z‖ := by
    have h1 := Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z hjne
    have h2 := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z hjne
    have hK : Work.Kernels.KfunClear ℓ d τ z
        = Work.Kernels.growthPrefactor d τ z * Work.Kernels.Kfun ℓ d τ z := by
      simp only [Work.Kernels.KfunClear, h1, h2, Work.Kernels.Kfun]
      ring
    have hgpne : Work.Kernels.growthPrefactor d τ z ≠ 0 := by
      simp only [Work.Kernels.growthPrefactor]
      exact mul_ne_zero (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
        (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)))
        (sub_ne_zero.mpr hjne)
    have hnorm : ‖Work.Kernels.KfunClear ℓ d τ z‖
        = ‖Work.Kernels.growthPrefactor d τ z‖ * ‖Work.Kernels.Kfun ℓ d τ z‖ := by
      rw [hK, norm_mul]
    refine (eq_div_iff (norm_ne_zero_iff.mpr hgpne)).mpr ?_
    rw [hnorm, mul_comm]
  -- abbreviations
  set gm : ℝ := Real.exp (2 * Real.pi * min z.im τ.im) with hgm
  set B : ℝ := Real.exp (2 * Real.pi * z.im) with hB
  have hgm0 : 0 < gm := by rw [hgm]; exact Real.exp_pos _
  have hB0 : 0 < B := by rw [hB]; exact Real.exp_pos _
  have hgmB : gm ≤ B := by
    rw [hgm, hB]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, min_le_left z.im τ.im])
  have hBinv : Real.exp (-(2 * Real.pi * z.im)) = B⁻¹ := by rw [hB, Real.exp_neg]
  have hgminv : Real.exp (-(2 * Real.pi * min z.im τ.im)) = gm⁻¹ := by rw [hgm, Real.exp_neg]
  rw [hgminv] at hdiv hdivpos
  have hΔzge : (19 / 20) * B⁻¹ ≤ ‖Work.Kernels.DeltaFun z‖ := by
    have h := Delta_norm_ge z hz3
    rwa [hBinv] at h
  have h8le : 8 * α * 4 ^ Nα ≤ max 1 X := by
    rw [hX]
    have h0 : (0 : ℝ) ≤ 8 * α * 4 ^ Nα := by positivity
    have h1 : (1 : ℝ) ≤ (20 / 19) * Real.exp (2 * Real.pi * τ.im) := by
      have h2 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * τ.im) :=
        Real.one_le_exp (by nlinarith [Real.pi_pos, τ.im_pos])
      nlinarith
    calc 8 * α * 4 ^ Nα
        ≤ 8 * α * 4 ^ Nα * ((20 / 19) * Real.exp (2 * Real.pi * τ.im)) :=
          le_mul_of_one_le_right h0 h1
      _ = 8 * α * 4 ^ Nα * (20 / 19) * Real.exp (2 * Real.pi * τ.im) := by ring
      _ ≤ max 1 (8 * α * 4 ^ Nα * (20 / 19) * Real.exp (2 * Real.pi * τ.im)) := le_max_right _ _
  rcases hd with rfl | rfl
  · -- d = 8
    have hgp8 : Work.Kernels.growthPrefactor 8 τ z
        = Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
      simp only [Work.Kernels.growthPrefactor, if_true, pow_one]
    have hdiv8 : (1 / 8) * gm⁻¹ ≤ ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
      rw [hgp8]; exact hdiv
    have hpos : 0 < ‖Work.Kernels.growthPrefactor 8 τ z‖ := lt_of_lt_of_le hdivpos hdiv8
    rw [hclear, div_le_iff₀ hpos]
    refine le_trans hcz ?_
    have h1 : (8 * α * 4 ^ Nα * (1 + z.im) ^ Nα * gm) * ((1 / 8) * gm⁻¹)
        = α * 4 ^ Nα * (1 + z.im) ^ Nα := by
      field_simp
    have h2 : 8 * α * 4 ^ Nα * (1 + z.im) ^ Nα ≤ max 1 X * (1 + z.im) ^ Nα :=
      mul_le_mul_of_nonneg_right h8le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + z.im) Nα)
    calc α * 4 ^ Nα * (1 + z.im) ^ Nα
        = (8 * α * 4 ^ Nα * (1 + z.im) ^ Nα * gm) * ((1 / 8) * gm⁻¹) := h1.symm
      _ ≤ (8 * α * 4 ^ Nα * (1 + z.im) ^ Nα * gm)
            * ‖Work.Kernels.growthPrefactor 8 τ z‖ :=
          mul_le_mul_of_nonneg_left hdiv8 (by positivity)
      _ ≤ (8 * α * 4 ^ Nα * (1 + z.im) ^ Nα * B)
            * ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hgmB (by positivity)
      _ ≤ (max 1 X * (1 + z.im) ^ Nα * B) * ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine mul_le_mul_of_nonneg_right h2 (le_of_lt hB0)
  · -- d = 24
    have hgp24 : Work.Kernels.growthPrefactor 24 τ z
        = Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z ^ 2
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
      simp only [Work.Kernels.growthPrefactor]
      norm_num
    have hdiv24 : (1 / 8) * gm⁻¹ * ((19 / 20) * B⁻¹)
        ≤ ‖Work.Kernels.growthPrefactor 24 τ z‖ := by
      have hsplit : Work.Kernels.growthPrefactor 24 τ z
          = Work.Kernels.DeltaFun z * (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
        rw [hgp24]; ring
      rw [hsplit, norm_mul]
      have h1 : ((19 / 20) * B⁻¹) * ((1 / 8) * gm⁻¹) ≤ ‖Work.Kernels.DeltaFun z‖
          * ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
        mul_le_mul hΔzge hdiv hdivpos.le (norm_nonneg _)
      have h2 : (1 / 8) * gm⁻¹ * ((19 / 20) * B⁻¹)
          = ((19 / 20) * B⁻¹) * ((1 / 8) * gm⁻¹) := by ring
      rwa [h2]
    have hdiv24b : (1 / 8) * gm⁻¹ * (19 / 20) ≤ B * ‖Work.Kernels.growthPrefactor 24 τ z‖ := by
      have h := mul_le_mul_of_nonneg_left hdiv24 hB0.le
      have h' : B * ((1 / 8) * gm⁻¹ * ((19 / 20) * B⁻¹)) = (1 / 8) * gm⁻¹ * (19 / 20) := by
        rw [show B * ((1 / 8) * gm⁻¹ * ((19 / 20) * B⁻¹))
            = ((1 / 8) * gm⁻¹ * (19 / 20)) * (B * B⁻¹) by ring]
        rw [mul_inv_cancel₀ (ne_of_gt hB0), mul_one]
      rwa [h'] at h
    have hpos : 0 < ‖Work.Kernels.growthPrefactor 24 τ z‖ :=
      lt_of_lt_of_le (by positivity) hdiv24
    rw [hclear, div_le_iff₀ hpos]
    refine le_trans hcz ?_
    have hexp : Real.exp (2 * Real.pi * τ.im) * gm⁻¹
        = Real.exp (2 * Real.pi * (τ.im - min z.im τ.im)) := by
      rw [hgm, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    have hA : (1 : ℝ) ≤ Real.exp (2 * Real.pi * (τ.im - min z.im τ.im)) :=
      Real.one_le_exp (by nlinarith [Real.pi_pos, min_le_right z.im τ.im])
    have hkey : α * 4 ^ Nα * (1 + z.im) ^ Nα
        ≤ X * (1 + z.im) ^ Nα * ((1 / 8) * gm⁻¹ * (19 / 20)) := by
      have h1 : α * 4 ^ Nα * (1 + z.im) ^ Nα
          ≤ α * 4 ^ Nα * (1 + z.im) ^ Nα * (Real.exp (2 * Real.pi * τ.im) * gm⁻¹) :=
        le_mul_of_one_le_right (by positivity) (by rw [hexp]; exact hA)
      have h2 : α * 4 ^ Nα * (1 + z.im) ^ Nα * (Real.exp (2 * Real.pi * τ.im) * gm⁻¹)
          = 8 * α * 4 ^ Nα * (20 / 19) * Real.exp (2 * Real.pi * τ.im) * (1 + z.im) ^ Nα
            * ((1 / 8) * gm⁻¹ * (19 / 20)) := by ring
      rw [hX]
      exact h1.trans_eq h2
    calc α * 4 ^ Nα * (1 + z.im) ^ Nα
        ≤ X * (1 + z.im) ^ Nα * ((1 / 8) * gm⁻¹ * (19 / 20)) := hkey
      _ ≤ X * (1 + z.im) ^ Nα * (B * ‖Work.Kernels.growthPrefactor 24 τ z‖) :=
          mul_le_mul_of_nonneg_left hdiv24b (by positivity)
      _ ≤ (max 1 X * (1 + z.im) ^ Nα * B) * ‖Work.Kernels.growthPrefactor 24 τ z‖ := by
          have h3 : X * (1 + z.im) ^ Nα ≤ max 1 X * (1 + z.im) ^ Nα :=
            mul_le_mul_of_nonneg_right (le_max_right 1 X)
              (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + z.im) Nα)
          calc X * (1 + z.im) ^ Nα * (B * ‖Work.Kernels.growthPrefactor 24 τ z‖)
              = (X * (1 + z.im) ^ Nα * B) * ‖Work.Kernels.growthPrefactor 24 τ z‖ := by ring
            _ ≤ (max 1 X * (1 + z.im) ^ Nα * B) * ‖Work.Kernels.growthPrefactor 24 τ z‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (le_of_lt hB0))
                  (norm_nonneg _)

/-- The real and imaginary parts of `ofComplex (x + i t)`. -/
private lemma ofComplex_re_im (x t : ℝ) (ht : 0 < t) :
    (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).re = x ∧
      (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).im = t := by
  have him' : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_im]
  have hre' : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by
    simp [Complex.add_re, Complex.mul_re]
  have him : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by rw [him']; exact ht
  have hcoe := UpperHalfPlane.ofComplex_apply_of_im_pos him
  constructor
  · rw [← UpperHalfPlane.coe_re, hcoe, hre']
  · rw [← UpperHalfPlane.coe_im, hcoe, him']

theorem Kfun_bound_shift (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1/2 ∨ τ.re = -1/2) (him : 12 ≤ τ.im) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      (∀ (x : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → ∀ t : ℝ, 1 ≤ t →
        ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (t:ℂ)*Complex.I))‖
          ≤ C * (1 + t)^N * Real.exp (2 * Real.pi * t))
      ∧ (∀ (x R : ℝ), -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
        ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I))‖
          ≤ C * (1 + R)^N * Real.exp (2 * Real.pi * R)) := by
  obtain ⟨C, N, hC, hN, hbound⟩ := region_bound ℓ d hd τ hre him
  refine ⟨C, N, hC, hN, ?_, ?_⟩
  · intro x hx t ht1
    have hxlo : -1 ≤ x := by rcases hx with h | h | h <;> linarith
    have hxhi : x ≤ 1 := by rcases hx with h | h | h <;> linarith
    obtain ⟨hzre, hzim⟩ := ofComplex_re_im x t (by linarith)
    have h1 : -1 ≤ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).re := by
      rw [hzre]; exact hxlo
    have h2 : (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).re ≤ 1 := by
      rw [hzre]; exact hxhi
    have h3 : 1 ≤ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).im := by
      rw [hzim]; exact ht1
    have h4 : (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).re = -1
        ∨ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).re = 0
        ∨ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).re = 1
        ∨ τ.im + 1 ≤ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)).im := by
      rw [hzre]
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    have h5 := hbound _ h1 h2 h3 h4
    rwa [hzim] at h5
  · intro x R hxlo hxhi hR
    obtain ⟨hzre, hzim⟩ := ofComplex_re_im x R (by linarith)
    have h1 : -1 ≤ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).re := by
      rw [hzre]; exact hxlo
    have h2 : (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).re ≤ 1 := by
      rw [hzre]; exact hxhi
    have h3 : 1 ≤ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).im := by
      rw [hzim]; linarith
    have h4 : (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).re = -1
        ∨ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).re = 0
        ∨ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).re = 1
        ∨ τ.im + 1 ≤ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I)).im :=
      Or.inr (Or.inr (Or.inr (by rw [hzim]; exact hR)))
    have h5 := hbound _ h1 h2 h3 h4
    rwa [hzim] at h5

end Work.CKFinal.LineDecay
