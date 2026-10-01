/-
# ZeroFreeTables — tf72Fc_decay

Decay of the Laplace transform `tf72Fc lam z = ∫₀^{2/λ} e^{-zt} f(t) dt` of the test
function of HB Lemma 7.2, uniform in the half-plane `0 ≤ Re z`:

  `∃ R > 0, ∀ z, 0 ≤ z.re → R ≤ ‖z‖ → ‖tf72Fc lam z‖ < ε`.

The point is that the interval of integration is compact: `tf72Fc lam` *is* the Laplace
transform of a compactly supported bounded function, so it tends to `0` at infinity in the
right half-plane.  The oscillatory part is handled by an integration by parts
(`exp_neg_mul_ibp`), which turns the integral into a boundary term `g 0 / z` of size
`O(1/‖z‖)` plus `z⁻¹` times an integral of the (bounded) derivative; this gives the uniform
estimate `‖tf72Fc lam z‖ ≤ C / ‖z‖` for `Re z ≥ 0`, whence the statement.

The relevant piece of `tf72f` is the polynomial `tf72poly`, which agrees with `tf72f lam`
on `[0, 2/λ]` and vanishes at the right endpoint.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.exp_neg_mul_ibp
import Submission.Work.ZeroFreeTables.norm_intervalIntegral_exp_neg_mul_le

open MeasureTheory intervalIntegral

namespace Work.ZeroFreeTables

/-- The polynomial that agrees with `tf72f lam` on `[0, 2/λ]`. -/
noncomputable def tf72poly (lam : ℝ) (t : ℝ) : ℝ :=
  (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2)

/-- Complex version of `tf72poly`. -/
noncomputable def tf72polyC (lam : ℝ) (t : ℝ) : ℂ := ((tf72poly lam t : ℝ) : ℂ)

/-- The derivative of `tf72poly`, as a complex-valued function. -/
noncomputable def tf72polyC' (lam : ℝ) (t : ℝ) : ℂ := ((deriv (tf72poly lam) t : ℝ) : ℂ)

lemma tf72polyC_hasDerivAt (lam : ℝ) (t : ℝ) :
    HasDerivAt (tf72polyC lam) (tf72polyC' lam t) t := by
  have hd : DifferentiableAt ℝ (tf72poly lam) t := by unfold tf72poly; fun_prop
  exact (hd.hasDerivAt).ofReal_comp

lemma tf72polyC_cont (lam : ℝ) : Continuous (tf72polyC lam) := by
  unfold tf72polyC tf72poly; fun_prop

lemma tf72polyC'_cont (lam : ℝ) : Continuous (tf72polyC' lam) := by
  unfold tf72polyC' tf72poly; fun_prop

lemma tf72poly_at_b (lam : ℝ) (hlam : 0 < lam) : tf72poly lam (2/lam) = 0 := by
  unfold tf72poly
  have h2 : 2 - lam * (2/lam) = 0 := by field_simp; ring
  rw [h2]; ring

lemma tf72f_eq_tf72poly (lam : ℝ) (hlam : 0 < lam) :
    ∀ t ∈ Set.Icc (0:ℝ) (2/lam), tf72f lam t = tf72poly lam t := by
  intro t ht
  simpa [tf72poly] using tf72f_eq_poly lam hlam t ht

/-- **Decay of the test function's Laplace transform in the closed right half-plane.**

For every `ε > 0` there is `R > 0` such that `‖tf72Fc lam z‖ < ε` for all `z` with
`0 ≤ Re z` and `‖z‖ ≥ R`. -/
theorem tf72Fc_decay (lam : ℝ) (hlam : 0 < lam) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ → ‖Work.ZeroFreeTables.tf72Fc lam z‖ < ε := by
  have hbpos : (0:ℝ) < 2/lam := by positivity
  have hcont' : ContinuousOn (tf72polyC' lam) (Set.Icc (0:ℝ) (2/lam)) :=
    (tf72polyC'_cont lam).continuousOn
  -- a uniform bound `M` for the derivative on the interval of integration
  obtain ⟨M0, hM0⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 2/lam)).exists_bound_of_continuousOn hcont'
  set M : ℝ := max M0 0 with hMdef
  have hMbound : ∀ t ∈ Set.Icc (0:ℝ) (2/lam), ‖tf72polyC' lam t‖ ≤ M :=
    fun t ht => (hM0 t ht).trans (le_max_left _ _)
  set C : ℝ := ‖tf72polyC lam 0‖ + M * (2/lam) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  set R : ℝ := C / ε + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  refine ⟨R, hRpos, ?_⟩
  intro z hzre hzR
  have hznorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hzR
  have hz : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hznorm_pos; exact lt_irrefl 0 hznorm_pos
  -- replace `tf72f` by the polynomial `tf72poly` on the interval of integration
  have hcongr : tf72Fc lam z
      = ∫ t in (0:ℝ)..(2/lam), Complex.exp (-(z * (t:ℂ))) * tf72polyC lam t := by
    unfold tf72Fc
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hbpos.le] at ht
    simp only [tf72f_eq_tf72poly lam hlam t ht, tf72polyC]
  -- integration by parts: boundary term plus `z⁻¹` times the integral of the derivative
  have hIBP := exp_neg_mul_ibp z hz (g := tf72polyC lam) (g' := tf72polyC' lam)
    (fun t _ => tf72polyC_hasDerivAt lam t)
    (tf72polyC_cont lam).continuousOn
    (by rw [Set.uIcc_of_le hbpos.le]; exact hcont')
    (by simp [tf72polyC, tf72poly_at_b lam hlam])
  -- the modulus of `exp` is at most `1` on `[0, 2/λ]`
  have hW : ‖∫ t in (0:ℝ)..(2/lam), Complex.exp (-(z * (t:ℂ))) * tf72polyC' lam t‖
      ≤ ∫ t in (0:ℝ)..(2/lam), ‖tf72polyC' lam t‖ :=
    norm_intervalIntegral_exp_neg_mul_le z hzre hbpos.le hcont'
  have hInt : ∫ t in (0:ℝ)..(2/lam), ‖tf72polyC' lam t‖ ≤ M * (2/lam) := by
    have h1 : ∫ t in (0:ℝ)..(2/lam), ‖tf72polyC' lam t‖ ≤ ∫ t in (0:ℝ)..(2/lam), M :=
      intervalIntegral.integral_mono_on hbpos.le
        ((tf72polyC'_cont lam).norm.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) hMbound
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using h1
  -- uniform bound `‖tf72Fc lam z‖ ≤ C / ‖z‖` in the closed right half-plane
  have hnorm : ‖tf72Fc lam z‖ ≤ C / ‖z‖ := by
    rw [hcongr, hIBP]
    calc ‖tf72polyC lam 0 / z
            + z⁻¹ * ∫ t in (0:ℝ)..(2/lam), Complex.exp (-(z * (t:ℂ))) * tf72polyC' lam t‖
        ≤ ‖tf72polyC lam 0 / z‖
            + ‖z⁻¹ * ∫ t in (0:ℝ)..(2/lam), Complex.exp (-(z * (t:ℂ))) * tf72polyC' lam t‖ :=
          norm_add_le _ _
      _ = ‖tf72polyC lam 0‖ / ‖z‖
            + ‖∫ t in (0:ℝ)..(2/lam), Complex.exp (-(z * (t:ℂ))) * tf72polyC' lam t‖ / ‖z‖ := by
          rw [norm_div, norm_mul, norm_inv]; ring
      _ ≤ ‖tf72polyC lam 0‖ / ‖z‖
            + (∫ t in (0:ℝ)..(2/lam), ‖tf72polyC' lam t‖) / ‖z‖ := by
          exact add_le_add_right (div_le_div_of_nonneg_right hW (norm_nonneg z)) _
      _ = (‖tf72polyC lam 0‖ + ∫ t in (0:ℝ)..(2/lam), ‖tf72polyC' lam t‖) / ‖z‖ := by ring
      _ ≤ (‖tf72polyC lam 0‖ + M * (2/lam)) / ‖z‖ := by
          exact div_le_div_of_nonneg_right (by linarith [hInt]) (norm_nonneg z)
      _ = C / ‖z‖ := by rw [hCdef]
  have hCR : C / ‖z‖ ≤ C / R := div_le_div_of_nonneg_left hCnn hRpos hzR
  have hlt : C / R < ε := by
    rw [div_lt_iff₀ hRpos]
    have heq : ε * R = C + ε := by
      rw [hRdef, div_eq_mul_inv, mul_add, mul_one, ← mul_assoc, mul_comm ε C, mul_assoc,
        mul_inv_cancel₀ hε.ne', mul_one]
    rw [heq]; linarith
  exact lt_of_le_of_lt (le_trans hnorm hCR) hlt

end Work.ZeroFreeTables
