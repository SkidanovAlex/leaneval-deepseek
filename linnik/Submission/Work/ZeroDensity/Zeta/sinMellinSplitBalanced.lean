import Mathlib
import Submission.Work.ZeroDensity.Zeta.gammaRotateAux

/-!
# The complete `sin` Mellin integral and the split at `A`

This file proves `Work.ZeroDensity.Zeta.sinMellinSplitBalanced`:

`∫_A^∞ sin v · v^{-s-1} dv = Γ(-s)·sin(-πs/2) - ∫_0^A sin v · v^{-s-1} dv`  (`0 < Re s < 1`, `A ≥ 1`),

by first proving the complete Mellin integral `∫_0^∞ sin v · v^{-s-1} dv = Γ(-s)·sin(-πs/2)` and
then splitting the range of integration.

The route to the complete integral: the *regularised* Mellin transform
`∫_0^∞ (e^{-zv} - 1) v^{W-1} dv = z^{-W} Γ(W)` (`-1 < Re W < 0`, `Re z > 0`), proved by integration
by parts from the rotated-contour form of Euler's Γ-integral
(`Work.ZeroDensity.Zeta.gamma_eq_Jrot_integral`, itself in Mathlib-only code); taking the
combination at `z = e^{∓iθ}` and passing `θ → π/2⁻` (dominated convergence) yields the value of
`∫_0^∞ sin v · v^{W-1} dv`.

Everything here is sorry-free; the only non-Mathlib dependency is the re-export of the
contour-rotation identity.
-/

open scoped Topology
open Filter MeasureTheory Set

namespace Work.ZeroDensity.Zeta

lemma expM1Integrable1 {W : ℂ} (hW0 : -1 < W.re) (hW1 : W.re < 0) {z : ℂ}
    (hz : ‖z‖ = 1) (hzre : 0 ≤ z.re) :
    IntegrableOn (fun x : ℝ => (Complex.exp (-((x:ℂ) * z)) - 1) * (W * (x:ℂ)^(W-1))) (Ioi (0:ℝ)) := by
  have hsub : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsub]
  refine IntegrableOn.union ?_ ?_
  · have hg : Integrable (fun x : ℝ => 2 * ‖W‖ * x ^ (W.re)) (volume.restrict (Ioc 0 1)) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := W.re) (by linarith)
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h).const_mul _
    refine Integrable.mono' hg (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hWnorm : ‖(x:ℂ)^(W-1)‖ = x^(W.re-1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; norm_num [Complex.sub_re]
    have hzn : ‖-((x:ℂ)*z)‖ = x := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hz, mul_one]
    have hexp : ‖Complex.exp (-((x:ℂ)*z)) - 1‖ ≤ 2 * x := by
      have h := Complex.norm_exp_sub_one_le (x := -((x:ℂ)*z)) (by rw [hzn]; linarith)
      rwa [hzn] at h
    rw [norm_mul, norm_mul, hWnorm]
    calc ‖Complex.exp (-((x:ℂ) * z)) - 1‖ * (‖W‖ * x ^ (W.re - 1))
        ≤ (2 * x) * (‖W‖ * x ^ (W.re - 1)) := by
          apply mul_le_mul_of_nonneg_right hexp; positivity
      _ = 2 * ‖W‖ * (x * x ^ (W.re - 1)) := by ring
      _ = 2 * ‖W‖ * x ^ (W.re) := by
          have hkey : W.re = (W.re - 1) + 1 := by ring
          conv_rhs => rw [hkey]
          rw [Real.rpow_add_one (ne_of_gt hx0) (W.re - 1)]
          ring
  · have hg : Integrable (fun x : ℝ => 2 * ‖W‖ * x ^ (W.re - 1)) (volume.restrict (Ioi 1)) := by
      exact ((integrableOn_Ioi_rpow_iff (t := 1) (by norm_num)).mpr (by linarith)).const_mul _
    refine Integrable.mono' hg (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    have hWnorm : ‖(x:ℂ)^(W-1)‖ = x^(W.re-1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; norm_num [Complex.sub_re]
    have hexp : ‖Complex.exp (-((x:ℂ)*z)) - 1‖ ≤ 2 := by
      have h1 : ‖Complex.exp (-((x:ℂ)*z))‖ = Real.exp (-(x * z.re)) := by
        rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]; simp
      have h2 : Real.exp (-(x * z.re)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc ‖Complex.exp (-((x:ℂ)*z)) - 1‖ ≤ ‖Complex.exp (-((x:ℂ)*z))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = Real.exp (-(x * z.re)) + 1 := by rw [norm_one, h1]
        _ ≤ 2 := by linarith
    rw [norm_mul, norm_mul, hWnorm]
    calc ‖Complex.exp (-((x:ℂ) * z)) - 1‖ * (‖W‖ * x ^ (W.re - 1)) ≤ 2 * (‖W‖ * x ^ (W.re - 1)) := by
          apply mul_le_mul_of_nonneg_right hexp; positivity
      _ = 2 * ‖W‖ * x ^ (W.re - 1) := by ring

lemma expM1Integrable0 {W : ℂ} (hW0 : -1 < W.re) (hW1 : W.re < 0) {z : ℂ}
    (hz : ‖z‖ = 1) (hzre : 0 ≤ z.re) (hWne : W ≠ 0) :
    IntegrableOn (fun x : ℝ => (Complex.exp (-((x:ℂ) * z)) - 1) * (x:ℂ)^(W-1)) (Ioi (0:ℝ)) := by
  have h := expM1Integrable1 hW0 hW1 hz hzre
  have hc : Integrable (fun x : ℝ => W⁻¹ * ((Complex.exp (-((x:ℂ) * z)) - 1) * (W * (x:ℂ)^(W-1))))
      (volume.restrict (Ioi (0:ℝ))) := h.const_mul W⁻¹
  refine hc.congr ?_
  filter_upwards with x
  field_simp

lemma expM1Integrable2 {W : ℂ} (hW0 : -1 < W.re) (hW1 : W.re < 0) {z : ℂ} (hz : ‖z‖ = 1) (hzre : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (-(z * Complex.exp (-((x:ℂ) * z)))) * (x:ℂ)^W) (Ioi (0:ℝ)) := by
  have hsub : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsub]
  refine IntegrableOn.union ?_ ?_
  · have hg : Integrable (fun x : ℝ => x ^ (W.re)) (volume.restrict (Ioc 0 1)) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := W.re) (by linarith)
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h)
    refine Integrable.mono' hg (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hWnorm : ‖(x:ℂ)^W‖ = x^(W.re) := Complex.norm_cpow_eq_rpow_re_of_pos hx0 W
    have hexp : ‖Complex.exp (-((x:ℂ)*z))‖ = Real.exp (-(x * z.re)) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [norm_mul, norm_neg, norm_mul, hz, one_mul, hWnorm, hexp]
    calc Real.exp (-(x * z.re)) * x ^ (W.re) ≤ 1 * x ^ (W.re) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hx0) _)
          exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = x ^ (W.re) := one_mul _
  · have hg : Integrable (fun x : ℝ => Real.exp (-z.re * x)) (volume.restrict (Ioi 1)) :=
      integrableOn_exp_mul_Ioi (by linarith) 1
    refine Integrable.mono' hg (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    have hx1le : (1:ℝ) ≤ x := le_of_lt hx1
    have hWnorm : ‖(x:ℂ)^W‖ = x^(W.re) := Complex.norm_cpow_eq_rpow_re_of_pos hx0 W
    have hexp : ‖Complex.exp (-((x:ℂ)*z))‖ = Real.exp (-z.re * x) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      congr 1; ring
    rw [norm_mul, norm_neg, norm_mul, hz, one_mul, hWnorm, hexp]
    calc Real.exp (-z.re * x) * x ^ (W.re) ≤ Real.exp (-z.re * x) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact Real.rpow_le_one_of_one_le_of_nonpos hx1le (le_of_lt hW1)
      _ = Real.exp (-z.re * x) := mul_one _

theorem expM1MulCpowIntegral {W : ℂ} (hW0 : -1 < W.re) (hW1 : W.re < 0) {θ : ℝ}
    (hθ : |θ| < Real.pi / 2) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.exp (-((x:ℂ) * Complex.exp (-(Complex.I * (θ:ℂ))))) - 1) * (x:ℂ) ^ (W - 1)
      = Complex.exp (Complex.I * (θ:ℂ) * W) * Complex.Gamma W := by
  set z : ℂ := Complex.exp (-(Complex.I * (θ:ℂ))) with hzoe
  have hznorm : ‖z‖ = 1 := by rw [hzoe, Complex.norm_exp]; simp
  have hzre : z.re = Real.cos θ := by
    rw [hzoe, Complex.exp_re]
    simp [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hWne : W ≠ 0 := by intro h; rw [h] at hW1; simp at hW1
  have hW1pos : 0 < (W+1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hzpos : 0 < z.re := by rw [hzre]; exact hcos
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y : ℝ => Complex.exp (-((y:ℂ) * z)) - 1)
      (-(z * Complex.exp (-((x:ℂ) * z)))) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := HasDerivAt.ofReal_comp (hasDerivAt_id x)
    have h2 : HasDerivAt (fun y : ℝ => (y:ℂ) * z) (1 * z) x := h1.mul_const z
    have h3 : HasDerivAt (fun y : ℝ => -((y:ℂ) * z)) (-(1 * z)) x := h2.neg
    have h4 : HasDerivAt (fun y : ℝ => Complex.exp (-((y:ℂ) * z)))
        (Complex.exp (-((x:ℂ) * z)) * (-(1 * z))) x := h3.cexp
    have h5 : HasDerivAt (fun y : ℝ => Complex.exp (-((y:ℂ) * z)) - 1)
        (Complex.exp (-((x:ℂ) * z)) * (-(1 * z))) x := h4.sub_const 1
    convert h5 using 1
    ring
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y : ℝ => (y:ℂ)^W) (W * (x:ℂ)^(W-1)) x := by
    intro x hx
    exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hWne
  have huv' : IntegrableOn (fun y : ℝ => (Complex.exp (-((y:ℂ) * z)) - 1) * (W * (y:ℂ)^(W-1))) (Ioi (0:ℝ)) :=
    expM1Integrable1 hW0 hW1 hznorm (le_of_lt hzpos)
  have hu'v : IntegrableOn (fun y : ℝ => (-(z * Complex.exp (-((y:ℂ) * z)))) * (y:ℂ)^W) (Ioi (0:ℝ)) :=
    expM1Integrable2 hW0 hW1 hznorm hzpos
  have hzero : Tendsto (fun x : ℝ => (Complex.exp (-((x:ℂ)*z)) - 1) * (x:ℂ)^W) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0:ℝ))
      (h := fun x : ℝ => 2 * x^(W.re+1)) ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · have h : Tendsto (fun x : ℝ => x ^ (W.re + 1)) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ (W.re+1))) :=
        (Real.continuousAt_rpow_const 0 (W.re+1) (Or.inr (by linarith))).tendsto
      have hh := h.const_mul (2:ℝ)
      simpa [Real.zero_rpow (by linarith : W.re+1 ≠ 0)] using hh.mono_left nhdsWithin_le_nhds
    · filter_upwards with x; exact norm_nonneg _
    · filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
      have hx0 : 0 < x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have hWnorm : ‖(x:ℂ)^W‖ = x^(W.re) := Complex.norm_cpow_eq_rpow_re_of_pos hx0 W
      have hzn : ‖-((x:ℂ)*z)‖ = x := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hznorm, mul_one]
      have hexp : ‖Complex.exp (-((x:ℂ)*z)) - 1‖ ≤ 2 * x := by
        have h := Complex.norm_exp_sub_one_le (x := -((x:ℂ)*z)) (by rw [hzn]; linarith)
        rwa [hzn] at h
      rw [norm_mul, hWnorm]
      calc ‖Complex.exp (-((x:ℂ) * z)) - 1‖ * x ^ (W.re) ≤ (2 * x) * x ^ (W.re) := by
            apply mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (le_of_lt hx0) _)
        _ = 2 * x ^ (W.re + 1) := by
            have hkey : W.re + 1 = 1 + W.re := by ring
            conv_rhs => rw [hkey]
            rw [Real.rpow_add hx0, Real.rpow_one]; ring
  have hinfty : Tendsto (fun x : ℝ => (Complex.exp (-((x:ℂ)*z)) - 1) * (x:ℂ)^W) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun x : ℝ => 2 * x^(W.re)) atTop (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => x^(-(-W.re))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (y := -W.re) (by linarith)
      simpa [neg_neg] using h.const_mul (2:ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0:ℝ))
      (h := fun x : ℝ => 2 * x^(W.re)) ?_ hb ?_ ?_
    · exact tendsto_const_nhds
    · filter_upwards with x; exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
      have hWnorm : ‖(x:ℂ)^W‖ = x^(W.re) := Complex.norm_cpow_eq_rpow_re_of_pos hx0 W
      have hexp : ‖Complex.exp (-((x:ℂ)*z)) - 1‖ ≤ 2 := by
        have h1 : ‖Complex.exp (-((x:ℂ)*z))‖ = Real.exp (-(x * z.re)) := by
          rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have h2 : Real.exp (-(x * z.re)) ≤ 1 := Real.exp_le_one_iff.mpr (by
          rw [hzre]; nlinarith [hcos])
        calc ‖Complex.exp (-((x:ℂ)*z)) - 1‖ ≤ ‖Complex.exp (-((x:ℂ)*z))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
          _ = Real.exp (-(x * z.re)) + 1 := by rw [norm_one, h1]
          _ ≤ 2 := by linarith
      rw [norm_mul, hWnorm]
      exact mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (le_of_lt hx0) _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0:ℝ))
    (u := fun y : ℝ => Complex.exp (-((y:ℂ) * z)) - 1)
    (v := fun y : ℝ => (y:ℂ)^W)
    (u' := fun y : ℝ => -(z * Complex.exp (-((y:ℂ) * z))))
    (v' := fun y : ℝ => W * (y:ℂ)^(W-1))
    hu hv huv' hu'v hzero hinfty
  have hA : ∫ x in Ioi (0:ℝ), (Complex.exp (-((x:ℂ)*z)) - 1) * (W * (x:ℂ)^(W-1))
      = W * ∫ x in Ioi (0:ℝ), (Complex.exp (-((x:ℂ)*z)) - 1) * (x:ℂ)^(W-1) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hB : ∫ x in Ioi (0:ℝ), (-(z * Complex.exp (-((x:ℂ)*z)))) * (x:ℂ)^W
      = -z * ∫ x in Ioi (0:ℝ), Complex.exp (-((x:ℂ)*z)) * (x:ℂ)^W := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hJrot : ∀ r : ℝ, Jrot (W+1) θ r = Complex.exp (-((r:ℂ)*z)) * (r:ℂ)^W := by
    intro r
    rw [Jrot_apply, show (W + 1) - 1 = W by ring, ← hzoe]
  have hJcongr : ∫ r in Ioi (0:ℝ), Jrot (W+1) θ r
      = ∫ r in Ioi (0:ℝ), Complex.exp (-((r:ℂ)*z)) * (r:ℂ)^W :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall hJrot)
  have hJval : ∫ r in Ioi (0:ℝ), Jrot (W+1) θ r
      = Complex.exp (Complex.I*(θ:ℂ)*(W+1)) * Complex.Gamma (W+1) := by
    have he : Complex.exp (-(Complex.I*(θ:ℂ)*(W+1))) ≠ 0 := Complex.exp_ne_zero _
    have h1 : Complex.Gamma (W+1) / Complex.exp (-(Complex.I*(θ:ℂ)*(W+1)))
        = ∫ r in Ioi (0:ℝ), Jrot (W+1) θ r := by
      rw [gamma_eq_Jrot_integral (W+1) hW1pos hθ, mul_div_cancel_left₀ _ he]
    have h2 : (Complex.exp (-(Complex.I*(θ:ℂ)*(W+1))))⁻¹ = Complex.exp (Complex.I*(θ:ℂ)*(W+1)) := by
      rw [Complex.exp_neg]; simp
    rw [← h1, div_eq_mul_inv, h2]; ring
  have hJ : ∫ r in Ioi (0:ℝ), Complex.exp (-((r:ℂ)*z)) * (r:ℂ)^W
      = Complex.exp (Complex.I*(θ:ℂ)*(W+1)) * (W * Complex.Gamma W) := by
    rw [← hJcongr, hJval, Complex.Gamma_add_one W hWne]
  have hmain : W * (∫ x in Ioi (0:ℝ), (Complex.exp (-((x:ℂ)*z)) - 1) * (x:ℂ)^(W-1))
      = z * (∫ x in Ioi (0:ℝ), Complex.exp (-((x:ℂ)*z)) * (x:ℂ)^W) := by
    rw [hA, hB] at hibp
    simpa using hibp
  have hcomb : z * Complex.exp (Complex.I*(θ:ℂ)*(W+1)) = Complex.exp (Complex.I*(θ:ℂ)*W) := by
    rw [hzoe, ← Complex.exp_add]; congr 1; ring
  have hWfinal : W * (∫ x in Ioi (0:ℝ), (Complex.exp (-((x:ℂ)*z)) - 1) * (x:ℂ)^(W-1))
      = W * (Complex.exp (Complex.I*(θ:ℂ)*W) * Complex.Gamma W) := by
    rw [hmain, hJ, ← hcomb]
    ring
  exact mul_left_cancel₀ hWne hWfinal

lemma sinMellinFamily {W : ℂ} (hW0 : -1 < W.re) (hW1 : W.re < 0) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    (∫ x in Ioi (0:ℝ), ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1))
      = Complex.sin ((θ:ℂ) * W) * Complex.Gamma W := by
  have hθ' : |(-θ)| < Real.pi / 2 := by rw [abs_neg]; exact hθ
  have hWne : W ≠ 0 := by intro h; rw [h] at hW1; simp at hW1
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  set z1 : ℂ := Complex.exp (-(Complex.I * (θ:ℂ))) with hz1def
  set z2 : ℂ := Complex.exp (-(Complex.I * ((-θ):ℂ))) with hz2def
  have hz1norm : ‖z1‖ = 1 := by rw [hz1def, Complex.norm_exp]; simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_im]
  have hz2norm : ‖z2‖ = 1 := by rw [hz2def, Complex.norm_exp]; simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_im]
  have hz1re : z1.re = Real.cos θ := by
    rw [hz1def, Complex.exp_re]
    simp [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hz1im : z1.im = -Real.sin θ := by
    rw [hz1def, Complex.exp_im]
    simp [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hz2re : z2.re = Real.cos θ := by
    rw [hz2def, Complex.exp_re]
    simp [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hz2im : z2.im = Real.sin θ := by
    rw [hz2def, Complex.exp_im]
    simp [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have int1 : IntegrableOn (fun x : ℝ => (Complex.exp (-((x:ℂ) * z1)) - 1) * (x:ℂ)^(W-1)) (Ioi (0:ℝ)) :=
    expM1Integrable0 hW0 hW1 hz1norm (le_of_lt (by rw [hz1re]; exact hcos)) hWne
  have int2 : IntegrableOn (fun x : ℝ => (Complex.exp (-((x:ℂ) * z2)) - 1) * (x:ℂ)^(W-1)) (Ioi (0:ℝ)) :=
    expM1Integrable0 hW0 hW1 hz2norm (le_of_lt (by rw [hz2re]; exact hcos)) hWne
  have h1 : ∫ x in Ioi (0:ℝ), (Complex.exp (-((x:ℂ) * z1)) - 1) * (x:ℂ)^(W-1)
      = Complex.exp (Complex.I * (θ:ℂ) * W) * Complex.Gamma W := by
    have h := expM1MulCpowIntegral (W := W) hW0 hW1 hθ
    simpa [z1, hz1def] using h
  have h2 : ∫ x in Ioi (0:ℝ), (Complex.exp (-((x:ℂ) * z2)) - 1) * (x:ℂ)^(W-1)
      = Complex.exp (Complex.I * ((-θ):ℂ) * W) * Complex.Gamma W := by
    have h := expM1MulCpowIntegral (W := W) hW0 hW1 hθ'
    simpa [z2, hz2def] using h
  have hG : ∫ x in Ioi (0:ℝ), ((Complex.exp (-((x:ℂ) * z1)) - 1) * (x:ℂ)^(W-1)
        - (Complex.exp (-((x:ℂ) * z2)) - 1) * (x:ℂ)^(W-1))
      = (2 * Complex.I) * ∫ x in Ioi (0:ℝ),
          ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have hw1re : (-((x:ℂ) * z1)).re = -(x * Real.cos θ) := by
      rw [Complex.neg_re, Complex.mul_re, hz1re, hz1im]; simp
    have hw1im : (-((x:ℂ) * z1)).im = x * Real.sin θ := by
      rw [Complex.neg_im, Complex.mul_im, hz1re, hz1im]; simp
    have hw2re : (-((x:ℂ) * z2)).re = -(x * Real.cos θ) := by
      rw [Complex.neg_re, Complex.mul_re, hz2re, hz2im]; simp
    have hw2im : (-((x:ℂ) * z2)).im = -(x * Real.sin θ) := by
      rw [Complex.neg_im, Complex.mul_im, hz2re, hz2im]; simp
    have hexp1 : Complex.exp (-((x:ℂ) * z1))
        = ((Real.exp (-(x * Real.cos θ)) * Real.cos (x * Real.sin θ) : ℝ) : ℂ)
          + ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * Complex.I := by
      rw [← Complex.re_add_im (Complex.exp (-((x:ℂ) * z1))), Complex.exp_re, Complex.exp_im, hw1re, hw1im]
    have hexp2 : Complex.exp (-((x:ℂ) * z2))
        = ((Real.exp (-(x * Real.cos θ)) * Real.cos (x * Real.sin θ) : ℝ) : ℂ)
          - ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * Complex.I := by
      rw [← Complex.re_add_im (Complex.exp (-((x:ℂ) * z2))), Complex.exp_re, Complex.exp_im, hw2re, hw2im,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [hexp1, hexp2]
    ring
  have hsub : (2 * Complex.I) * ∫ x in Ioi (0:ℝ),
        ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1)
      = Complex.exp (Complex.I * (θ:ℂ) * W) * Complex.Gamma W
        - Complex.exp (Complex.I * ((-θ):ℂ) * W) * Complex.Gamma W := by
    rw [← hG, MeasureTheory.integral_sub int1 int2, h1, h2]
  have hcre : Complex.exp (Complex.I * (θ:ℂ) * W) - Complex.exp (Complex.I * ((-θ):ℂ) * W)
      = (2 * Complex.I) * Complex.sin ((θ:ℂ) * W) := by
    have e1 : Complex.I * (θ:ℂ) * W = ((θ:ℂ) * W) * Complex.I := by ring
    have e2 : Complex.I * ((-θ):ℂ) * W = -(((θ:ℂ) * W) * Complex.I) := by ring
    rw [e1, e2, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have hmain : (2 * Complex.I) * ∫ x in Ioi (0:ℝ),
        ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1)
      = (2 * Complex.I) * (Complex.sin ((θ:ℂ) * W) * Complex.Gamma W) := by
    rw [hsub, ← sub_mul, hcre]
    ring
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero) hmain

lemma sinMellinFamilyTendsto {W : ℂ} (hW0 : -1 < W.re) (hW1 : W.re < 0) :
    Tendsto (fun θ : ℝ => ∫ x in Ioi (0:ℝ),
        ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1))
      (𝓝[<] (Real.pi / 2))
      (𝓝 (∫ x in Ioi (0:ℝ), ((Real.sin x : ℝ) : ℂ) * (x:ℂ)^(W-1))) := by
  set l := 𝓝[<] (Real.pi / 2) with hl
  have hev : ∀ᶠ θ in l, |θ| < Real.pi / 2 := by
    have h1 : Set.Iio (Real.pi / 2) ∈ l := self_mem_nhdsWithin
    have h2 : Set.Ioi (-(Real.pi / 2)) ∈ l := nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos]))
    filter_upwards [h1, h2] with θ hθ1 hθ2
    exact abs_lt.mpr ⟨hθ2, hθ1⟩
  have hbound_int : Integrable (fun x : ℝ => min x 1 * x ^ (W.re - 1)) (volume.restrict (Ioi (0:ℝ))) := by
    have hsub : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    have hP1 : IntegrableOn (fun x : ℝ => min x 1 * x ^ (W.re - 1)) (Ioc 0 1) := by
      have hg : Integrable (fun x : ℝ => x ^ (W.re)) (volume.restrict (Ioc 0 1)) := by
        have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := W.re) (by linarith)
        exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h)
      refine Integrable.mono' hg (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have hmin : min x 1 = x := min_eq_left hx1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (le_of_lt hx0) zero_le_one), hmin,
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx0) _)]
      have hkey : W.re = (W.re - 1) + 1 := by ring
      conv_rhs => rw [hkey]
      rw [Real.rpow_add_one (ne_of_gt hx0) (W.re - 1), mul_comm]
    have hP2 : IntegrableOn (fun x : ℝ => min x 1 * x ^ (W.re - 1)) (Ioi 1) := by
      have hg : Integrable (fun x : ℝ => x ^ (W.re - 1)) (volume.restrict (Ioi 1)) :=
        (integrableOn_Ioi_rpow_iff (t := 1) (by norm_num)).mpr (by linarith)
      refine Integrable.mono' hg (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
      have hx0 : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
      have hmin : min x 1 = 1 := min_eq_right hx1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (le_of_lt hx0) zero_le_one), hmin,
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx0) _), one_mul]
    rw [hsub]
    exact IntegrableOn.union hP1 hP2
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (l := l) (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun θ x => ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1))
    (f := fun x => ((Real.sin x : ℝ) : ℂ) * (x:ℂ)^(W-1))
    (fun x => min x 1 * x ^ (W.re - 1))
    ?_ ?_ hbound_int ?_
  · exact hmain
  · filter_upwards with θ
    exact (by fun_prop : AEStronglyMeasurable (fun x : ℝ => ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^(W-1)) (volume.restrict (Ioi (0:ℝ))))
  · filter_upwards [hev] with θ hθ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
    have hWnorm : ‖(x:ℂ)^(W-1)‖ = x^(W.re-1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; norm_num [Complex.sub_re]
    have hsin : |Real.sin (x * Real.sin θ)| ≤ min x 1 := by
      have h1 : |Real.sin (x * Real.sin θ)| ≤ |x * Real.sin θ| := Real.abs_sin_le_abs
      have h2 : |x * Real.sin θ| = x * |Real.sin θ| := by rw [abs_mul, abs_of_pos hx0]
      have h3 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      rw [h2] at h1
      refine le_min ?_ ?_
      · exact le_trans h1 (by nlinarith [h3, hx0, abs_nonneg (Real.sin θ)])
      · exact Real.abs_sin_le_one _
    have hexp : Real.exp (-(x * Real.cos θ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hWnorm, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-(x * Real.cos θ)) * |Real.sin (x * Real.sin θ)| * x ^ (W.re - 1)
        ≤ 1 * min x 1 * x ^ (W.re - 1) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hx0) _)
          exact mul_le_mul hexp hsin (abs_nonneg _) zero_le_one
      _ = min x 1 * x ^ (W.re - 1) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hcont : Continuous (fun θ : ℝ => ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ)) := by fun_prop
    have h1 : Tendsto (fun θ : ℝ => ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ))
        (𝓝 (Real.pi / 2)) (𝓝 (((Real.exp (-(x * Real.cos (Real.pi / 2))) * Real.sin (x * Real.sin (Real.pi / 2)) : ℝ) : ℂ))) :=
      hcont.continuousAt.tendsto
    have hval : ((Real.exp (-(x * Real.cos (Real.pi / 2))) * Real.sin (x * Real.sin (Real.pi / 2)) : ℝ) : ℂ)
        = ((Real.sin x : ℝ) : ℂ) := by
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    rw [hval] at h1
    exact (h1.mono_left nhdsWithin_le_nhds).mul_const _

lemma sinMellinIntegrableOnIoi {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    IntegrableOn (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v:ℂ)^(-s-1)) (Ioi (0:ℝ)) := by
  have hsub : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsub]
  refine IntegrableOn.union ?_ ?_
  · have hg : Integrable (fun v : ℝ => v ^ (-s.re)) (volume.restrict (Set.Ioc 0 1)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -s.re) (by linarith))
    refine Integrable.mono' hg (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    have ha0 : 0 < a := ha.1
    have hnorm2 : ‖(a:ℂ)^(-s-1)‖ = a^(-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ha0]
      norm_num [Complex.neg_re, Complex.sub_re]
    rw [Complex.norm_mul, hnorm2]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc |Real.sin a| * a ^ (-s.re - 1) ≤ a * a ^ (-s.re - 1) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt ha0) _)
          calc |Real.sin a| ≤ |a| := Real.abs_sin_le_abs
            _ = a := abs_of_pos ha0
      _ = a ^ (-s.re) := by
          conv_rhs => rw [show -s.re = 1 + (-s.re - 1) by ring, Real.rpow_add ha0, Real.rpow_one]
  · have hg : Integrable (fun v : ℝ => v ^ (-s.re - 1)) (volume.restrict (Set.Ioi 1)) :=
      (integrableOn_Ioi_rpow_iff (t := 1) (by norm_num)).mpr (by linarith)
    refine Integrable.mono' hg (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha1 : (1:ℝ) < a := Set.mem_Ioi.mp ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha1
    have hnorm2 : ‖(a:ℂ)^(-s-1)‖ = a^(-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ha0]
      norm_num [Complex.neg_re, Complex.sub_re]
    rw [Complex.norm_mul, hnorm2]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc |Real.sin a| * a ^ (-s.re - 1) ≤ 1 * a ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one a) (Real.rpow_nonneg (le_of_lt ha0) _)
      _ = a ^ (-s.re - 1) := one_mul _

theorem sinMellinComplete {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∫ v in Ioi (0:ℝ), ((Real.sin v : ℝ) : ℂ) * (v:ℂ)^(-s-1)
      = Complex.Gamma (-s) * Complex.sin (-(Real.pi : ℂ) * s / 2) := by
  have hW0 : -1 < (-s).re := by rw [Complex.neg_re]; linarith
  have hW1 : (-s).re < 0 := by rw [Complex.neg_re]; linarith
  have hevθ : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), |θ| < Real.pi / 2 := by
    have h1 : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := self_mem_nhdsWithin
    have h2 : Set.Ioi (-(Real.pi / 2)) ∈ 𝓝[<] (Real.pi / 2) :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos]))
    filter_upwards [h1, h2] with θ hθ1 hθ2
    exact abs_lt.mpr ⟨hθ2, hθ1⟩
  have hT1 := sinMellinFamilyTendsto (W := -s) hW0 hW1
  have heq : ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
      (∫ x in Ioi (0:ℝ), ((Real.exp (-(x * Real.cos θ)) * Real.sin (x * Real.sin θ) : ℝ) : ℂ) * (x:ℂ)^((-s)-1))
        = Complex.sin ((θ:ℂ) * (-s)) * Complex.Gamma (-s) := by
    filter_upwards [hevθ] with θ hθ
    exact sinMellinFamily (W := -s) hW0 hW1 hθ
  have hT2 : Tendsto (fun θ : ℝ => Complex.sin ((θ:ℂ) * (-s)) * Complex.Gamma (-s))
      (𝓝[<] (Real.pi / 2))
      (𝓝 (Complex.sin (((Real.pi/2 : ℝ) : ℂ) * (-s)) * Complex.Gamma (-s))) := by
    have hcont : Continuous (fun θ : ℝ => Complex.sin ((θ:ℂ) * (-s))) := by fun_prop
    exact (hcont.continuousAt.tendsto (x := Real.pi/2)).mono_left nhdsWithin_le_nhds |>.mul_const _
  have huniq := tendsto_nhds_unique (hT1.congr' heq) hT2
  have harg : (((Real.pi/2 : ℝ) : ℂ)) * (-s) = -(Real.pi : ℂ) * s / 2 := by
    push_cast; ring
  rw [harg] at huniq
  rw [mul_comm] at huniq
  exact huniq

theorem sinMellinSplitBalanced {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ} (hA : 1 ≤ A) :
    ∫ v in Set.Ioi A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)
      = Complex.Gamma (-s) * Complex.sin (-(Real.pi : ℂ) * s / 2)
        - ∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1) := by
  have hcomp := sinMellinComplete hs0 hs1
  have hInt := sinMellinIntegrableOnIoi hs0 hs1
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hset : Ioi (0:ℝ) \ Ioc 0 A = Ioi A := by
    ext x
    simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · rintro ⟨hx0, hnot⟩
      by_contra hx
      exact hnot ⟨hx0, le_of_not_gt hx⟩
    · intro hx
      exact ⟨by linarith, fun h => absurd h.2 (not_le.mpr hx)⟩
  have hsub : Ioc (0:ℝ) A ⊆ Ioi 0 := fun x hx => hx.1
  rw [← hset, setIntegral_sdiff measurableSet_Ioc hInt hsub, hcomp]

end Work.ZeroDensity.Zeta
