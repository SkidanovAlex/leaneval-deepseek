import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# A lower bound for `‖Fhat f ξ‖` for `f` supported in an interval of length `L`

If `f ≥ 0` is continuous with compact support contained in `[a, a+L]` and `|ξ| ≤ 1/(8L)`,
then the phase `ξ u` varies by at most `2 π L |ξ| ≤ π/4` on the support of `f`.  Splitting
`u = c + (u - c)` with `c = a + L/2` and using that `‖e(-ξ(u-c))‖ = 1` shows that
`‖Fhat f ξ‖` is at least the real part of `∫ f(u) e(-ξ(u-c)) du`, which is
`∫ f(u) cos(2π ξ (u-c)) du ≥ cos(2π L |ξ|) ∫ f`.  This is the estimate
`norm_Fhat_ge_cos_mul_integral` below.
-/

namespace Work.GM.Affine

open MeasureTheory

theorem norm_Fhat_ge_cos_mul_integral {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hfnn : ∀ u, 0 ≤ f u) {a L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Set.Icc a (a + L)) {ξ : ℝ} (hξ : |ξ| ≤ 1 / (8 * L)) :
    Real.cos (2 * Real.pi * L * |ξ|) * (∫ u, f u) ≤ ‖Fhat f ξ‖ := by
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hcs
  have hfC : Integrable (fun u : ℝ => (f u : ℂ)) := hfint.ofReal
  -- (i) the product `|ξ| L` is at most `1/8`
  have hxiL : |ξ| * L ≤ 1 / 8 := by
    rcases eq_or_lt_of_le hL with h0 | hpos
    · rw [← h0, mul_zero]; norm_num
    · rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * L)] at hξ
      nlinarith [hξ]
  set c : ℝ := a + L / 2 with hcdef
  -- (ii) the angle `2 π L |ξ|` is at most `π`
  have hΘπ : 2 * Real.pi * L * |ξ| ≤ Real.pi := by
    have hLxi : L * |ξ| ≤ 1 / 8 := by linarith [hxiL]
    have h1 : 2 * Real.pi * (L * |ξ|) ≤ 2 * Real.pi * (1 / 8) :=
      mul_le_mul_of_nonneg_left hLxi (by positivity)
    have h2 : 2 * Real.pi * L * |ξ| = 2 * Real.pi * (L * |ξ|) := by ring
    rw [h2]
    nlinarith [Real.pi_pos]
  -- (iii) pointwise comparison of cosines on the support of `f`
  have hcos_pt : ∀ u : ℝ, f u ≠ 0 →
      Real.cos (2 * Real.pi * L * |ξ|) ≤ Real.cos (2 * Real.pi * (u - c) * ξ) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hsupp u hu
    have huc : |u - c| ≤ L / 2 := by
      rw [abs_le]
      constructor <;> rw [hcdef] <;> linarith
    have habs : |2 * Real.pi * (u - c) * ξ| ≤ 2 * Real.pi * L * |ξ| := by
      have h1 : |2 * Real.pi * (u - c) * ξ| = 2 * Real.pi * |u - c| * |ξ| := by
        simp only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [h1]
      have h2 : (2 * Real.pi) * |u - c| ≤ (2 * Real.pi) * (L / 2) :=
        mul_le_mul_of_nonneg_left huc (by positivity)
      have h3 : ((2 * Real.pi) * |u - c|) * |ξ| ≤ ((2 * Real.pi) * (L / 2)) * |ξ| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg ξ)
      have h4 : ((2 * Real.pi) * (L / 2)) * |ξ| ≤ ((2 * Real.pi) * L) * |ξ| :=
        mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos, hL]) (abs_nonneg ξ)
      linarith [h3, h4]
    rw [← Real.cos_abs (2 * Real.pi * (u - c) * ξ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hΘπ habs
  have hpt : ∀ u : ℝ, f u * Real.cos (2 * Real.pi * L * |ξ|)
      ≤ f u * Real.cos (-2 * Real.pi * (u - c) * ξ) := by
    intro u
    rcases eq_or_ne (f u) 0 with h | h
    · simp [h]
    · have hc := hcos_pt u h
      rw [show (-2 * Real.pi * (u - c) * ξ) = -(2 * Real.pi * (u - c) * ξ) by ring, Real.cos_neg]
      exact mul_le_mul_of_nonneg_left hc (hfnn u)
  -- (iv) integrability of the integrand of `Z`
  have hZint : Integrable (fun u : ℝ =>
      (f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)) := by
    refine hfC.mul_bdd (c := 1) ?_ ?_
    · exact (by fun_prop : Continuous fun u : ℝ =>
        Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)).aestronglyMeasurable
    · filter_upwards with u
      simp only [Complex.norm_exp_ofReal_mul_I]
      norm_num
  -- (v) the real part of `Z`
  have hZre : (∫ u : ℝ, (f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)).re
      = ∫ u, f u * Real.cos (-2 * Real.pi * (u - c) * ξ) := by
    have hre : (∫ u : ℝ, (f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)).re
        = ∫ u, ((f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)).re :=
      (integral_re hZint).symm
    rw [hre]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- (vi) `Fhat f ξ` is a unimodular constant times `Z`
  have hFhat : Fhat f ξ
      = Complex.exp (↑(-2 * Real.pi * c * ξ) * Complex.I)
        * ∫ u : ℝ, (f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I) := by
    rw [Fhat, Real.fourier_real_eq_integral_exp_smul, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    rw [smul_eq_mul]
    have hexp : Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I)
        = Complex.exp (↑(-2 * Real.pi * c * ξ) * Complex.I)
          * Complex.exp (↑(-2 * Real.pi * (v - c) * ξ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  -- (vii) assemble
  have hint1 : Integrable (fun u : ℝ => f u * Real.cos (2 * Real.pi * L * |ξ|)) :=
    hfint.mul_const _
  have hint2 : Integrable (fun u : ℝ => f u * Real.cos (-2 * Real.pi * (u - c) * ξ)) :=
    (hf.mul (Real.continuous_cos.comp (by fun_prop))).integrable_of_hasCompactSupport
      (hcs.mul_right (f' := fun u : ℝ => Real.cos (-2 * Real.pi * (u - c) * ξ)))
  have hmono : ∫ u, f u * Real.cos (2 * Real.pi * L * |ξ|)
      ≤ ∫ u, f u * Real.cos (-2 * Real.pi * (u - c) * ξ) :=
    MeasureTheory.integral_mono hint1 hint2 hpt
  have hint1eq : ∫ u, f u * Real.cos (2 * Real.pi * L * |ξ|)
      = Real.cos (2 * Real.pi * L * |ξ|) * ∫ u, f u := by
    rw [MeasureTheory.integral_mul_const, mul_comm]
  calc Real.cos (2 * Real.pi * L * |ξ|) * (∫ u, f u)
      = ∫ u, f u * Real.cos (2 * Real.pi * L * |ξ|) := hint1eq.symm
    _ ≤ ∫ u, f u * Real.cos (-2 * Real.pi * (u - c) * ξ) := hmono
    _ = (∫ u : ℝ, (f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)).re :=
        hZre.symm
    _ ≤ ‖∫ u : ℝ, (f u : ℂ) * Complex.exp (↑(-2 * Real.pi * (u - c) * ξ) * Complex.I)‖ :=
        Complex.re_le_norm _
    _ = ‖Fhat f ξ‖ := by rw [hFhat, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

end Work.GM.Affine
