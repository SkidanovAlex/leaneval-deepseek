/-
# ZeroFreeTables — XY/xyReFarBound

`xyReFarBound`: the oscillatory Laplace transform `xyRe u v = Re F(u + i v)` of the test
function of Heath-Brown (1992), Lemma 7.2, with `λ = 4/3` (so that `x₀ = 3/2`) satisfies
`|xyRe u v| ≤ C / |v|` uniformly in the strip `|u| ≤ 1`, `|v| ≥ 1`.

The proof is the elementary integration by parts already used for the decay of `tf72Fc`
(`tf72Fc_decay`): on `[0, 3/2]` the test function `tf72f (4/3)` agrees with the quintic
`tf72poly (4/3)`, which vanishes at the right endpoint `3/2 = 2/(4/3)`; hence

  `∫₀^{3/2} e^{-zt} f = f(0)/z + z⁻¹ ∫₀^{3/2} e^{-zt} f'`,

and the integral of the (bounded) derivative is `O(1)`, uniformly in the strip `|Re z| ≤ 1`
because there `|e^{-zt}| = e^{-(Re z) t} ≤ e^{t} ≤ e^{3/2}`. Dividing by `|z| ≥ |Im z|`
gives the stated `O(1/|v|)` bound.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.tf72Fc_decay
import Submission.Work.ZeroFreeTables.exp_neg_mul_ibp
import Submission.Work.ZeroFreeTables.XY.norm_intervalIntegral_exp_strip_le

open MeasureTheory intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- `xyRe u v` is the real part of the Laplace transform of the test function `xyT` at the
point `u + i v`. -/
lemma xyRe_eq_tf72Fc_re (u v : ℝ) :
    Work.ZeroFreeTables.xyRe u v
      = (tf72Fc (4 / 3) ((u : ℂ) + (v : ℂ) * Complex.I)).re := rfl

/-- Uniform `O(1/|Im z|)` bound for the Laplace transform `tf72Fc lam` in the strip
`|Re z| ≤ 1`, in terms of a bound `M` for the derivative of the polynomial `tf72poly lam`
on the interval of integration. -/
lemma tf72Fc_strip_le (lam M : ℝ) (hlam : 0 < lam) (hMnn : 0 ≤ M)
    (hMb : ∀ t ∈ Set.Icc (0:ℝ) (2 / lam), ‖tf72polyC' lam t‖ ≤ M) :
    ∀ z : ℂ, |z.re| ≤ 1 → z.im ≠ 0 →
      ‖tf72Fc lam z‖
        ≤ (‖tf72polyC lam 0‖ + Real.exp (2 / lam) * M * (2 / lam)) / |z.im| := by
  intro z hzre hzim
  have hb : (0:ℝ) ≤ 2 / lam := (div_pos two_pos hlam).le
  have hcont : ContinuousOn (tf72polyC' lam) (Set.Icc (0:ℝ) (2 / lam)) :=
    (tf72polyC'_cont lam).continuousOn
  have hz : z ≠ 0 := by
    intro h
    exact hzim (by rw [h]; simp)
  -- replace `tf72f` by its polynomial representative on the interval of integration
  have hcongr : tf72Fc lam z
      = ∫ t in (0:ℝ)..(2 / lam), Complex.exp (-(z * (t : ℂ))) * tf72polyC lam t := by
    unfold tf72Fc
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb] at ht
    simp only [tf72f_eq_tf72poly lam hlam t ht, tf72polyC]
  -- integration by parts (the right boundary term vanishes: `tf72poly (2/λ) = 0`)
  have hIBP := exp_neg_mul_ibp (b := 2 / lam) z hz (g := tf72polyC lam) (g' := tf72polyC' lam)
    (fun t _ => tf72polyC_hasDerivAt lam t)
    (tf72polyC_cont lam).continuousOn
    (by rw [Set.uIcc_of_le hb]; exact hcont)
    (by simp [tf72polyC, tf72poly_at_b lam hlam])
  -- the derivative integral is uniformly bounded in the strip
  have hInt : ‖∫ t in (0:ℝ)..(2 / lam), Complex.exp (-(z * (t : ℂ))) * tf72polyC' lam t‖
      ≤ Real.exp (2 / lam) * M * (2 / lam) := by
    have hzdecomp : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
    have hrewrite : (∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(z * (t : ℂ))) * tf72polyC' lam t)
        = ∫ t in (0:ℝ)..(2 / lam),
            Complex.exp (-(((z.re : ℂ) + (z.im : ℂ) * Complex.I) * (t : ℂ)))
              * tf72polyC' lam t := by
      apply intervalIntegral.integral_congr
      intro t _
      rw [hzdecomp]
    rw [hrewrite]
    exact norm_intervalIntegral_exp_strip_le hb hzre hcont M hMnn hMb
  have hzimpos : 0 < |z.im| := abs_pos.mpr hzim
  have hnorm_v : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hEnn : (0:ℝ) ≤ Real.exp (2 / lam) * M * (2 / lam) :=
    mul_nonneg (mul_nonneg (Real.exp_pos (2 / lam)).le hMnn) hb
  have hA : ‖tf72polyC lam 0 / z‖ ≤ ‖tf72polyC lam 0‖ / |z.im| := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hzimpos hnorm_v
  have hB : ‖z⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
        Complex.exp (-(z * (t : ℂ))) * tf72polyC' lam t)‖
      ≤ (Real.exp (2 / lam) * M * (2 / lam)) / |z.im| := by
    have h1 : ‖z⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
          Complex.exp (-(z * (t : ℂ))) * tf72polyC' lam t)‖
        = ‖(∫ t in (0:ℝ)..(2 / lam),
            Complex.exp (-(z * (t : ℂ))) * tf72polyC' lam t)‖ / ‖z‖ := by
      rw [norm_mul, norm_inv]; ring
    rw [h1]
    exact (div_le_div_of_nonneg_right hInt (norm_nonneg z)).trans
      (div_le_div_of_nonneg_left hEnn hzimpos hnorm_v)
  have hsum : ‖tf72polyC lam 0‖ / |z.im| + (Real.exp (2 / lam) * M * (2 / lam)) / |z.im|
      = (‖tf72polyC lam 0‖ + Real.exp (2 / lam) * M * (2 / lam)) / |z.im| := by ring
  have hsplit : ‖tf72polyC lam 0 / z
        + z⁻¹ * (∫ t in (0:ℝ)..(2 / lam),
            Complex.exp (-(z * (t : ℂ))) * tf72polyC' lam t)‖
      ≤ (‖tf72polyC lam 0‖ + Real.exp (2 / lam) * M * (2 / lam)) / |z.im| :=
    (le_trans (norm_add_le _ _) (add_le_add hA hB)).trans hsum.le
  rw [hcongr, hIBP]
  exact hsplit

/-- The strip bound for `tf72Fc lam`, with the existential constant:
`∃ C > 0, ∀ u v, |u| ≤ 1 → v ≠ 0 → ‖tf72Fc lam (u + iv)‖ ≤ C/|v|`. -/
theorem tf72Fc_stripBound (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 → v ≠ 0 →
      ‖tf72Fc lam ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C / |v| := by
  have hcont : ContinuousOn (tf72polyC' lam) (Set.Icc (0:ℝ) (2 / lam)) :=
    (tf72polyC'_cont lam).continuousOn
  obtain ⟨M0, hM0⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 2 / lam)).exists_bound_of_continuousOn hcont
  refine ⟨max (‖tf72polyC lam 0‖ + Real.exp (2 / lam) * max M0 0 * (2 / lam)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro u v hu hv
  have hMnn : 0 ≤ max M0 0 := le_max_right _ _
  have hMb : ∀ t ∈ Set.Icc (0:ℝ) (2 / lam), ‖tf72polyC' lam t‖ ≤ max M0 0 :=
    fun t ht => (hM0 t ht).trans (le_max_left _ _)
  have h := tf72Fc_strip_le lam (max M0 0) hlam hMnn hMb ((u : ℂ) + (v : ℂ) * Complex.I)
    (by simpa using hu) (by simpa using hv)
  have h2 : (‖tf72polyC lam 0‖ + Real.exp (2 / lam) * max M0 0 * (2 / lam))
        / |((u : ℂ) + (v : ℂ) * Complex.I).im|
      = (‖tf72polyC lam 0‖ + Real.exp (2 / lam) * max M0 0 * (2 / lam)) / |v| := by simp
  rw [h2] at h
  exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) (abs_nonneg v))

theorem xyReFarBound : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, |u| ≤ 1 → 1 ≤ |v| →
    |Work.ZeroFreeTables.xyRe u v| ≤ C / |v| := by
  obtain ⟨C, hCpos, hC⟩ := tf72Fc_stripBound (4 / 3) (by norm_num)
  refine ⟨C, hCpos, fun u v hu hv => ?_⟩
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hv
    linarith
  have h1 : |(tf72Fc (4 / 3) ((u : ℂ) + (v : ℂ) * Complex.I)).re|
      ≤ ‖tf72Fc (4 / 3) ((u : ℂ) + (v : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _
  have h2 : ‖tf72Fc (4 / 3) ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C / |v| := hC u v hu hv0
  have h3 : |Work.ZeroFreeTables.xyRe u v|
      = |(tf72Fc (4 / 3) ((u : ℂ) + (v : ℂ) * Complex.I)).re| := by
    rw [xyRe_eq_tf72Fc_re u v]
  rw [h3]
  exact h1.trans h2

end Work.ZeroFreeTables.XY
