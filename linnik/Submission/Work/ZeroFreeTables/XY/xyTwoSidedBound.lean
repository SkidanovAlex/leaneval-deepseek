/-
# ZeroFreeTables — XY/xyTwoSidedBound

The **two-sided** (uniform in `v`) companion of `xyReFarBound`: for the test function of
Heath-Brown (1992), Lemma 7.2, with `λ = 4/3`,

  `∃ C > 0, ∀ u v, |u| ≤ 1 → ‖F(u + i v)‖ ≤ C / (1 + |v|)`,

where `F = xyT.Fc = tf72Fc (4/3)`. Since `|Re F| ≤ ‖F‖` and `|Im F| ≤ ‖F‖` this bounds both
the real part (`xyReTwoSided`, strengthening `xyReFarBound` to all `v`, not only `|v| ≥ 1`)
and the imaginary part (`xyImTwoSided`) with the single constant `C`.

The two regimes are glued as follows.

* `|v| ≥ 1`: `tf72Fc_stripBound` gives `‖F(u+iv)‖ ≤ C₁/|v|`, and `C₁/|v| ≤ (2C₁)/(1+|v|)`
  because `1 + |v| ≤ 2|v|`.
* `|v| ≤ 1`: `tf72Fc_nearBound` (the elementary triangle-inequality bound in the strip
  `|Re z| ≤ 1`, again an instance of `norm_intervalIntegral_exp_strip_le`) gives
  `‖F(u+iv)‖ ≤ C₂`, and `C₂ ≤ C/(1+|v|)` because `1 + |v| ≤ 2`.

Both regimes are dominated by `2*C₁ + 2*C₂ + 1`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.XY.xyReFarBound
import Submission.Work.ZeroFreeTables.XY.norm_intervalIntegral_exp_strip_le

open MeasureTheory intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- **Near-axis bound.** In the strip `|Re z| ≤ 1` the Laplace transform `tf72Fc lam` of HB
Lemma 7.2's test function is bounded by `exp (2/λ) * Mf * (2/λ)`, where `Mf` bounds the
polynomial representative `tf72poly lam` on the interval of integration. -/
lemma tf72Fc_nearBound (lam Mf : ℝ) (hlam : 0 < lam) (hMfnn : 0 ≤ Mf)
    (hMf : ∀ t ∈ Set.Icc (0:ℝ) (2 / lam), ‖tf72polyC lam t‖ ≤ Mf) :
    ∀ z : ℂ, |z.re| ≤ 1 → ‖tf72Fc lam z‖ ≤ Real.exp (2 / lam) * Mf * (2 / lam) := by
  intro z hzre
  have hb : (0:ℝ) ≤ 2 / lam := (div_pos two_pos hlam).le
  have hcont : ContinuousOn (tf72polyC lam) (Set.Icc (0:ℝ) (2 / lam)) :=
    (tf72polyC_cont lam).continuousOn
  have hcongr : tf72Fc lam z
      = ∫ t in (0:ℝ)..(2 / lam), Complex.exp (-(z * (t : ℂ))) * tf72polyC lam t := by
    unfold tf72Fc
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb] at ht
    simp only [tf72f_eq_tf72poly lam hlam t ht, tf72polyC]
  rw [hcongr]
  have hzdecomp : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
  have hrewrite : (∫ t in (0:ℝ)..(2 / lam), Complex.exp (-(z * (t : ℂ))) * tf72polyC lam t)
      = ∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(((z.re : ℂ) + (z.im : ℂ) * Complex.I) * (t : ℂ)))
            * tf72polyC lam t := by
    apply intervalIntegral.integral_congr
    intro t _
    rw [hzdecomp]
  rw [hrewrite]
  exact norm_intervalIntegral_exp_strip_le hb hzre hcont Mf hMfnn hMf

/-- **Two-sided strip bound** for `tf72Fc lam`: uniformly in the strip `|Re z| ≤ 1` and for
all `v`, `‖tf72Fc lam (u + iv)‖ ≤ C/(1 + |v|)`. -/
theorem tf72Fc_twoSided (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 →
      ‖tf72Fc lam ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C / (1 + |v|) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := tf72Fc_stripBound lam hlam
  obtain ⟨M0, hM0⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 2 / lam)).exists_bound_of_continuousOn
      ((tf72polyC_cont lam).continuousOn)
  have hMfnn : (0:ℝ) ≤ max M0 0 := le_max_right _ _
  have hMfb : ∀ t ∈ Set.Icc (0:ℝ) (2 / lam), ‖tf72polyC lam t‖ ≤ max M0 0 :=
    fun t ht => (hM0 t ht).trans (le_max_left _ _)
  have hC₂nn : (0:ℝ) ≤ Real.exp (2 / lam) * max M0 0 * (2 / lam) :=
    mul_nonneg (mul_nonneg (Real.exp_pos (2 / lam)).le hMfnn) (div_pos two_pos hlam).le
  refine ⟨2 * C₁ + 2 * (Real.exp (2 / lam) * max M0 0 * (2 / lam)) + 1, by linarith, ?_⟩
  intro u v hu
  have hnear : ‖tf72Fc lam ((u : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ Real.exp (2 / lam) * max M0 0 * (2 / lam) :=
    tf72Fc_nearBound lam (max M0 0) hlam hMfnn hMfb (((u : ℂ) + (v : ℂ) * Complex.I))
      (by simpa using hu)
  rcases le_or_gt |v| 1 with hv | hv
  · -- near regime `|v| ≤ 1`: the constant dominates `exp (2/λ) * Mf * (2/λ)`
    have h1 : (0:ℝ) < 1 + |v| := by linarith [abs_nonneg v]
    have h2 : 1 + |v| ≤ (2:ℝ) := by linarith [abs_nonneg v]
    have h3 : Real.exp (2 / lam) * max M0 0 * (2 / lam)
        ≤ (2 * C₁ + 2 * (Real.exp (2 / lam) * max M0 0 * (2 / lam)) + 1) / 2 := by
      linarith [hC₁pos]
    have h4 : (2 * C₁ + 2 * (Real.exp (2 / lam) * max M0 0 * (2 / lam)) + 1) / 2
        ≤ (2 * C₁ + 2 * (Real.exp (2 / lam) * max M0 0 * (2 / lam)) + 1) / (1 + |v|) :=
      div_le_div_of_nonneg_left (by linarith [hC₁pos, hC₂nn]) h1 h2
    linarith
  · -- far regime `1 < |v|`: `C₁/|v| ≤ (2*C₁)/(1+|v|) ≤ C/(1+|v|)`
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, abs_zero] at hv
      linarith
    have hfar : ‖tf72Fc lam ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C₁ / |v| := hC₁ u v hu hv0
    have hcmp : C₁ / |v|
        ≤ (2 * C₁ + 2 * (Real.exp (2 / lam) * max M0 0 * (2 / lam)) + 1) / (1 + |v|) := by
      rw [div_le_div_iff₀ (abs_pos.mpr hv0) (by linarith [abs_nonneg v])]
      nlinarith [hC₁pos, hC₂nn, abs_nonneg v, hv]
    linarith

/-- The Laplace transform of the test function `xyT` of `XYDefs` is `tf72Fc (4/3)`. -/
lemma xyT_Fc_eq : xyT.Fc = tf72Fc (4 / 3) := rfl

/-- The two-sided strip bound in the vocabulary of `XYDefs`: for the test function `xyT` of
the order-2 `λ₁`-estimate, `‖xyT.Fc (u + iv)‖ ≤ C/(1 + |v|)` for `|u| ≤ 1`. -/
theorem xyT_Fc_twoSided : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 →
    ‖xyT.Fc ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C / (1 + |v|) := by
  obtain ⟨C, hCpos, hC⟩ := tf72Fc_twoSided (4 / 3) (by norm_num)
  rw [xyT_Fc_eq]
  exact ⟨C, hCpos, hC⟩

/-- **Two-sided bound for `xyRe`**, uniform in `u` and `v`: this strengthens
`xyReFarBound` (which is the case `|v| ≥ 1`) to all real `v`. -/
theorem xyRe_twoSided : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 →
    |Work.ZeroFreeTables.xyRe u v| ≤ C / (1 + |v|) := by
  obtain ⟨C, hCpos, hC⟩ := tf72Fc_twoSided (4 / 3) (by norm_num)
  refine ⟨C, hCpos, fun u v hu => ?_⟩
  have h3 : |Work.ZeroFreeTables.xyRe u v|
      = |(tf72Fc (4 / 3) ((u : ℂ) + (v : ℂ) * Complex.I)).re| := by
    rw [xyRe_eq_tf72Fc_re u v]
  rw [h3]
  exact (Complex.abs_re_le_norm _).trans (hC u v hu)

/-- **Two-sided bound for the imaginary part** `Im F(u + iv)` of the Laplace transform of
`xyT`, uniform in `u` and `v`. -/
theorem xyIm_twoSided : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 →
    |(xyT.Fc ((u : ℂ) + (v : ℂ) * Complex.I)).im| ≤ C / (1 + |v|) := by
  obtain ⟨C, hCpos, hC⟩ := tf72Fc_twoSided (4 / 3) (by norm_num)
  refine ⟨C, hCpos, fun u v hu => ?_⟩
  rw [xyT_Fc_eq]
  exact (Complex.abs_im_le_norm _).trans (hC u v hu)

end Work.ZeroFreeTables.XY
