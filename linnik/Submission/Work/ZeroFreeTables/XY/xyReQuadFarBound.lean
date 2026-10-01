/-
# ZeroFreeTables — XY/xyReQuadFarBound

**Quadratic far-field decay of the real part.** For the test function of Heath-Brown (1992),
Lemma 7.2, with `λ = 4/3` (support `[0, 3/2]`), the real part of the Laplace transform
decays like `1/v²` — one power better than the modulus:

  `∃ C > 0, ∀ u v, |u| ≤ 1 → 1 ≤ |v| → |xyRe u v| ≤ C / v²`.

This is what the sup-estimates of Xylouris §2 (`Work.ZeroFreeTables.XY.xySup1`,
`Work.ZeroFreeTables.XY.xySup2`, i.e. `SupBoundOrd2`, `SupBoundOrderTwo`) consume on the far
range `|t| ≫ 1`: they bound the *real* part of `F = xyT.Fc` at the two points `u = -1` and
`u = λ₁ - 1`.

The gain over `xyReFarBound` (`C/|v|`) comes from two integrations by parts, using two
structural facts about the quintic `p = tf72poly (4/3)`:

* `p` has a **triple** zero at the right endpoint `3/2 = 2/(4/3)`, so `p(3/2) = p'(3/2) = 0`
  and the boundary terms of *both* integrations by parts vanish at the right end;
* `p` has **no linear term** (`p'(0) = 0`, see `deriv_tf72poly_zero`), so the `p'(0)/z²` term
  drops out as well.

The result is the exact identity (`tf72Fc_ibp_two`)

  `F(z) = p(0)/z + z⁻² ∫₀^{3/2} e^{-zt} p''(t) dt`,

and since `p(0)` is **real**, its real part is `p(0)·Re z/‖z‖²`, which is `O(1/|v|²)` in the
strip `|Re z| ≤ 1`; the remaining integral is bounded by the same `exp (3/2)·(3/2)·sup|p''|`
argument as in `tf72Fc_nearBound`. So `xyReQuadBound` gives the uniform `C/(1 + v²)` bound
for *all* `v`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.XY.xyReFarBound
import Submission.Work.ZeroFreeTables.XY.xyTwoSidedBound
import Submission.Work.ZeroFreeTables.XY.norm_intervalIntegral_exp_strip_le
import Submission.Work.ZeroFreeTables.XY.exp_neg_mul_ibp_two
import Submission.Work.ZeroFreeTables.XY.deriv_tf72poly_eq
import Submission.Work.ZeroFreeTables.XY.hasDerivAt_deriv_tf72poly

open MeasureTheory intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-! ## The two vanishing derivatives of the polynomial representative -/

/-- `tf72poly` has no linear term: its derivative vanishes at `0`. -/
lemma deriv_tf72poly_zero (lam : ℝ) : deriv (tf72poly lam) 0 = 0 := by
  rw [deriv_tf72poly_eq]
  ring

/-- `tf72poly` has a triple zero at the right endpoint, so its derivative vanishes there. -/
lemma deriv_tf72poly_at_b (lam : ℝ) (hlam : 0 < lam) :
    deriv (tf72poly lam) (2 / lam) = 0 := by
  rw [deriv_tf72poly_eq]
  rw [show 2 - lam * (2 / lam) = 0 by rw [mul_div_cancel₀ 2 hlam.ne']; ring]
  ring

/-- Continuity of the complexified second derivative of `tf72poly` on the interval of
integration. -/
lemma continuousOn_iteratedDeriv_two_tf72poly (lam : ℝ) :
    ContinuousOn (fun t : ℝ => ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))
      (Set.Icc (0:ℝ) (2 / lam)) := by
  have hcd : ContDiff ℝ 2 (tf72poly lam) := by unfold tf72poly; fun_prop
  exact (Complex.continuous_ofReal.comp (hcd.continuous_iteratedDeriv 2 le_rfl)).continuousOn

/-! ## The two-fold integration by parts -/

/-- **Exact two-fold integration by parts.** With `p = tf72poly lam` vanishing with its first
derivative at the right endpoint `2/λ` and `p'(0) = 0`,
`F(z) = p(0)/z + z⁻² ∫₀^{2/λ} e^{-zt} p''(t) dt` for `z ≠ 0`. -/
lemma tf72Fc_ibp_two (lam : ℝ) (hlam : 0 < lam) :
    ∀ z : ℂ, z ≠ 0 →
      tf72Fc lam z = tf72polyC lam 0 / z
        + (z ^ 2)⁻¹ * ∫ t in (0:ℝ)..(2 / lam),
            Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ) := by
  intro z hz
  have hb : (0:ℝ) ≤ 2 / lam := (div_pos two_pos hlam).le
  have hcont2 : ContinuousOn
      (fun t : ℝ => ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ)) (Set.uIcc (0:ℝ) (2 / lam)) := by
    rw [Set.uIcc_of_le hb]
    exact continuousOn_iteratedDeriv_two_tf72poly lam
  have hcongr : tf72Fc lam z
      = ∫ t in (0:ℝ)..(2 / lam), Complex.exp (-(z * (t : ℂ))) * tf72polyC lam t := by
    unfold tf72Fc
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb] at ht
    simp only [tf72f_eq_tf72poly lam hlam t ht, tf72polyC]
  rw [hcongr]
  have h2 := exp_neg_mul_ibp_two z hz (tf72polyC lam) (tf72polyC' lam)
    (fun t : ℝ => ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))
    (fun t _ => tf72polyC_hasDerivAt lam t)
    (fun t _ => (hasDerivAt_deriv_tf72poly lam t).ofReal_comp)
    (tf72polyC_cont lam).continuousOn
    (tf72polyC'_cont lam).continuousOn
    hcont2
    (by simp [tf72polyC, tf72poly_at_b lam hlam])
    (by simp [tf72polyC', deriv_tf72poly_at_b lam hlam])
  rw [h2]
  rw [show tf72polyC' lam 0 = 0 by simp [tf72polyC', deriv_tf72poly_zero lam]]
  ring

/-! ## The quadratic bound for the real part -/

/-- **Quadratic bound in the strip.** For `|Re z| ≤ 1` and `z ≠ 0` on the imaginary axis,
`|Re F(z)| ≤ (|p(0)| + M₂ · exp(2/λ) · (2/λ)) / (Im z)²`, where `M₂` bounds
`|p''|` on the interval of integration. -/
lemma tf72Fc_re_quadLe (lam M2 : ℝ) (hlam : 0 < lam) (hM2nn : 0 ≤ M2)
    (hM2 : ∀ t ∈ Set.Icc (0:ℝ) (2 / lam),
      ‖((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ)‖ ≤ M2) :
    ∀ z : ℂ, |z.re| ≤ 1 → z.im ≠ 0 →
      |(tf72Fc lam z).re|
        ≤ (|tf72poly lam 0| + Real.exp (2 / lam) * M2 * (2 / lam)) / z.im ^ 2 := by
  intro z hzre hzim
  have hb : (0:ℝ) ≤ 2 / lam := (div_pos two_pos hlam).le
  have hz : z ≠ 0 := by
    intro h
    exact hzim (by rw [h]; simp)
  have hzim2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hzim
  -- the boundary term `p(0)/z`: its real part is `p(0)·Re z/‖z‖²`
  have hA : |(((tf72poly lam 0 : ℝ) : ℂ) / z).re| ≤ |tf72poly lam 0| / z.im ^ 2 := by
    have h1 : (((tf72poly lam 0 : ℝ) : ℂ) / z).re
        = tf72poly lam 0 * (z.re / Complex.normSq z) := by
      rw [div_eq_mul_inv, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.inv_re]
      ring
    rw [h1]
    have h2 : |tf72poly lam 0 * (z.re / Complex.normSq z)|
        = |tf72poly lam 0| * (|z.re| / Complex.normSq z) := by
      rw [abs_mul, abs_div, abs_of_nonneg (Complex.normSq_nonneg z)]
    rw [h2]
    have h3 : |z.re| / Complex.normSq z ≤ 1 / z.im ^ 2 := by
      rw [div_le_div_iff₀ (Complex.normSq_pos.mpr hz) hzim2]
      rw [Complex.normSq_apply, one_mul]
      nlinarith [abs_nonneg z.re, hzre, sq_nonneg z.im, sq_nonneg z.re]
    calc |tf72poly lam 0| * (|z.re| / Complex.normSq z)
        ≤ |tf72poly lam 0| * (1 / z.im ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = |tf72poly lam 0| / z.im ^ 2 := by ring
  -- the remainder: `z⁻² ∫ e^{-zt} p''`
  have hJ : ‖∫ t in (0:ℝ)..(2 / lam),
        Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ)‖
      ≤ Real.exp (2 / lam) * M2 * (2 / lam) := by
    have hzdecomp : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
    have hrewrite : (∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))
        = ∫ t in (0:ℝ)..(2 / lam),
            Complex.exp (-(((z.re : ℂ) + (z.im : ℂ) * Complex.I) * (t : ℂ)))
              * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      rw [hzdecomp]
    rw [hrewrite]
    exact norm_intervalIntegral_exp_strip_le hb hzre
      (continuousOn_iteratedDeriv_two_tf72poly lam) M2 hM2nn hM2
  have hBnn : (0:ℝ) ≤ Real.exp (2 / lam) * M2 * (2 / lam) :=
    mul_nonneg (mul_nonneg (Real.exp_pos (2 / lam)).le hM2nn) hb
  have hR : |((z ^ 2)⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
        Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))).re|
      ≤ (Real.exp (2 / lam) * M2 * (2 / lam)) / z.im ^ 2 := by
    have h1 : |((z ^ 2)⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))).re|
        ≤ ‖(z ^ 2)⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖(z ^ 2)⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))‖
        = ‖(∫ t in (0:ℝ)..(2 / lam),
            Complex.exp (-(z * (t : ℂ))) * ((iteratedDeriv 2 (tf72poly lam) t : ℝ) : ℂ))‖
              / ‖z‖ ^ 2 := by
      rw [norm_mul, norm_inv, norm_pow]
      ring
    have hznorm2 : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
    have hzim_le : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
      have h := Complex.abs_im_le_norm z
      nlinarith [abs_nonneg z.im, norm_nonneg z, sq_abs z.im]
    rw [h2] at h1
    exact h1.trans ((div_le_div_of_nonneg_right hJ hznorm2.le).trans
      (div_le_div_of_nonneg_left hBnn hzim2 hzim_le))
  -- assemble: `Re F = Re(p(0)/z) + Re(z⁻²∫…)`
  have hF := tf72Fc_ibp_two lam hlam z hz
  have hA0 : tf72polyC lam 0 = ((tf72poly lam 0 : ℝ) : ℂ) := rfl
  have hsum : |tf72poly lam 0| / z.im ^ 2
        + (Real.exp (2 / lam) * M2 * (2 / lam)) / z.im ^ 2
      = (|tf72poly lam 0| + Real.exp (2 / lam) * M2 * (2 / lam)) / z.im ^ 2 := by ring
  rw [hF, hA0, Complex.add_re]
  exact ((abs_add_le _ _).trans (add_le_add hA hR)).trans hsum.le

/-! ## The far-field target -/

/-- **Quadratic far-field bound for `xyRe`**: `|xyRe u v| ≤ C/v²` for `|u| ≤ 1`, `|v| ≥ 1`.
This is one power of `v` better than `xyReFarBound`. -/
theorem xyReQuadFarBound : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 → 1 ≤ |v| →
    |Work.ZeroFreeTables.xyRe u v| ≤ C / v ^ 2 := by
  obtain ⟨M0, hM0⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 2 / ((4:ℝ) / 3))).exists_bound_of_continuousOn
      (continuousOn_iteratedDeriv_two_tf72poly ((4:ℝ) / 3))
  have hM2nn : (0:ℝ) ≤ max M0 0 := le_max_right _ _
  have hM2 : ∀ t ∈ Set.Icc (0:ℝ) (2 / ((4:ℝ) / 3)),
      ‖((iteratedDeriv 2 (tf72poly ((4:ℝ) / 3)) t : ℝ) : ℂ)‖ ≤ max M0 0 :=
    fun t ht => (hM0 t ht).trans (le_max_left _ _)
  have hEnn : (0:ℝ) ≤ Real.exp (2 / ((4:ℝ) / 3)) * max M0 0 * (2 / ((4:ℝ) / 3)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hM2nn) (by positivity)
  refine ⟨|tf72poly ((4:ℝ) / 3) 0| + Real.exp (2 / ((4:ℝ) / 3)) * max M0 0 * (2 / ((4:ℝ) / 3)) + 1,
    by linarith [abs_nonneg (tf72poly ((4:ℝ) / 3) 0), hEnn], ?_⟩
  intro u v hu hv
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hv
    linarith
  have h := tf72Fc_re_quadLe ((4:ℝ) / 3) (max M0 0) (by norm_num) hM2nn hM2
    ((u : ℂ) + (v : ℂ) * Complex.I) (by simpa using hu) (by simpa using hv0)
  have h3 : |Work.ZeroFreeTables.xyRe u v|
      = |(tf72Fc ((4:ℝ) / 3) ((u : ℂ) + (v : ℂ) * Complex.I)).re| := by
    rw [xyRe_eq_tf72Fc_re u v]
  rw [h3]
  refine h.trans ?_
  have h4 : (((u : ℂ) + (v : ℂ) * Complex.I).im) = v := by simp
  rw [h4]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg v)

/-! ## The uniform form for all `v` -/

/-- The quadratic far bound together with the boundedness near the real axis: for
`|u| ≤ 1` and **every** real `v`, `|xyRe u v| ≤ C/(1 + v²)`. -/
theorem xyReQuadBound : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 →
    |Work.ZeroFreeTables.xyRe u v| ≤ C / (1 + v ^ 2) := by
  obtain ⟨Cf, hCfpos, hCf⟩ := xyReQuadFarBound
  obtain ⟨Cn, hCnpos, hCn⟩ := xyRe_twoSided
  refine ⟨2 * Cf + 2 * Cn + 1, by linarith, fun u v hu => ?_⟩
  rcases le_or_gt |v| 1 with hv | hv
  · -- near range `|v| ≤ 1`
    have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv, sq_abs v, abs_nonneg v]
    have hnear : |Work.ZeroFreeTables.xyRe u v| ≤ Cn := by
      refine (hCn u v hu).trans ?_
      rw [div_le_iff₀ (by linarith [abs_nonneg v] : (0:ℝ) < 1 + |v|)]
      nlinarith [hCnpos, abs_nonneg v]
    have h2 : Cn ≤ (2 * Cf + 2 * Cn + 1) / 2 := by linarith [hCfpos]
    have h3 : (2 * Cf + 2 * Cn + 1) / 2 ≤ (2 * Cf + 2 * Cn + 1) / (1 + v ^ 2) :=
      div_le_div_of_nonneg_left (by linarith [hCfpos, hCnpos]) (by linarith [sq_nonneg v])
        (by linarith [hv2])
    linarith
  · -- far range `1 < |v|`
    have hv2 : 1 ≤ v ^ 2 := by nlinarith [hv, sq_abs v, abs_nonneg v]
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, abs_zero] at hv
      linarith
    have hfar : |Work.ZeroFreeTables.xyRe u v| ≤ Cf / v ^ 2 := hCf u v hu hv.le
    have hcmp : Cf / v ^ 2 ≤ (2 * Cf + 2 * Cn + 1) / (1 + v ^ 2) := by
      rw [div_le_div_iff₀ (sq_pos_of_ne_zero hv0) (by linarith [sq_nonneg v] : (0:ℝ) < 1 + v ^ 2)]
      nlinarith [hCfpos, hCnpos, hv2, sq_nonneg v]
    linarith

end Work.ZeroFreeTables.XY
