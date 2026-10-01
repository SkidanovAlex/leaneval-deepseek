/-
# ZeroFreeTables — tf71Fc_decay

Heath-Brown (1992), §7: the Laplace transform `F(z) = ∫₀^{2γ} e^{−zt} f(t) dt` of the
Lemma 7.1 test function tends to `0` as `‖z‖ → ∞` through the closed right half-plane
`{0 ≤ Re z}` — this is what makes `F` a valid "test function" transform in HB's §7
variational problem (in particular it is used to see that `F` is a legitimate mollifier
in the half-plane of analyticity).

The decay is not just qualitative: integrating by parts against the exponential and
using `f(2γ) = 0` gives the *uniform* bound

  `‖F z‖ ≤ (‖f 0‖ + ∫₀^{2γ} ‖f'‖) / ‖z‖   (0 ≤ Re z)`,

the `1/‖z‖` coming from the jump of `f` at the origin (where `f 0 ≠ 0` in general) and the
boundedness of `f'` on the compact interval.  Since `F` agrees, on its interval of
integration, with the Laplace transform of the smooth closed form `tf71cfC`
(`tf71Fc_eq_integral_cf`), the hypotheses of the integration-by-parts identity
`exp_neg_mul_ibp` are met by `tf71cfC` and its derivative `tf71cfC'`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.tf71Fc_model
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.exp_neg_mul_ibp
import Submission.Work.ZeroFreeTables.norm_intervalIntegral_exp_neg_mul_le

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

/-- **Decay of `tf71Fc` in the closed right half-plane.**  For every `ε > 0` there is `R > 0`
with `‖tf71Fc θ lam z‖ < ε` for every `z` with `0 ≤ z.re` and `‖z‖ ≥ R`. -/
theorem tf71Fc_decay (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖Work.ZeroFreeTables.tf71Fc θ lam z‖ < ε := by
  have hT : (0:ℝ) < 2 * tf71γ θ lam := tf71_twoγ_pos hθ0 hθ1 hlam
  have hTle : (0:ℝ) ≤ 2 * tf71γ θ lam := hT.le
  -- A bound for the derivative on the interval of integration.
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * tf71γ θ lam))
    |>.exists_bound_of_continuousOn (tf71cfC'_cont θ lam).continuousOn
  set B : ℝ := max B0 0 * (2 * tf71γ θ lam) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact mul_nonneg (le_max_right _ _) hTle
  have hB : (∫ t in (0:ℝ)..(2 * tf71γ θ lam), ‖tf71cfC' θ lam t‖) ≤ B := by
    have hfi : IntervalIntegrable (fun t : ℝ => ‖tf71cfC' θ lam t‖)
        volume (0:ℝ) (2 * tf71γ θ lam) :=
      ((tf71cfC'_cont θ lam).norm).intervalIntegrable _ _
    have hgi : IntervalIntegrable (fun _ : ℝ => max B0 0) volume (0:ℝ) (2 * tf71γ θ lam) :=
      continuous_const.intervalIntegrable _ _
    calc (∫ t in (0:ℝ)..(2 * tf71γ θ lam), ‖tf71cfC' θ lam t‖)
        ≤ ∫ t in (0:ℝ)..(2 * tf71γ θ lam), max B0 0 :=
          intervalIntegral.integral_mono_on hTle hfi hgi
            (fun t ht => (hB0 t ht).trans (le_max_left _ _))
      _ = max B0 0 * (2 * tf71γ θ lam) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ = B := hBdef.symm
  have hRpos : 0 < (‖tf71cfC θ lam 0‖ + B) / ε + 1 := by
    have h1 : 0 ≤ (‖tf71cfC θ lam 0‖ + B) / ε :=
      div_nonneg (add_nonneg (norm_nonneg _) hBnn) hε.le
    linarith
  refine ⟨(‖tf71cfC θ lam 0‖ + B) / ε + 1, hRpos, ?_⟩
  intro z hz hzR
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hRpos hzR
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  -- `tf71Fc` is the Laplace transform of the smooth closed form on `[0, 2γ]`.
  have hmodel := tf71Fc_eq_integral_cf hθ0 hθ1 hlam z
  -- Integration by parts against the exponential, with the vanishing right endpoint.
  have hIBP := exp_neg_mul_ibp (b := 2 * tf71γ θ lam) z hz0 (tf71cfC θ lam) (tf71cfC' θ lam)
    (fun t _ => tf71cfC_hasDerivAt θ lam t)
    ((tf71cfC_cont θ lam).continuousOn.mono (Set.subset_univ _))
    ((tf71cfC'_cont θ lam).continuousOn.mono (Set.subset_univ _))
    (tf71cfC_at_twoγ hθ0 hθ1 hlam)
  -- The modulus of the exponential factor is at most `1` on `[0, 2γ]`.
  have hnorm := norm_intervalIntegral_exp_neg_mul_le (b := 2 * tf71γ θ lam)
    (h := tf71cfC' θ lam) z hz hTle ((tf71cfC'_cont θ lam).continuousOn.mono (Set.subset_univ _))
  have hJ : ‖∫ t in (0:ℝ)..(2 * tf71γ θ lam),
      Complex.exp (-(z * (t:ℂ))) * tf71cfC' θ lam t‖ ≤ B := hnorm.trans hB
  have hkey : ‖tf71Fc θ lam z‖ ≤ (‖tf71cfC θ lam 0‖ + B) / ‖z‖ := by
    calc ‖tf71Fc θ lam z‖
        = ‖∫ t in (0:ℝ)..(2 * tf71γ θ lam),
            Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t‖ := by
          rw [hmodel]
      _ = ‖tf71cfC θ lam 0 / z + z⁻¹ * ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
              Complex.exp (-(z * (t:ℂ))) * tf71cfC' θ lam t‖ := by
          rw [hIBP]
      _ ≤ ‖tf71cfC θ lam 0‖ / ‖z‖ + ‖z‖⁻¹ * B := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_div, norm_mul, norm_inv]
          have h2 := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr (norm_nonneg z))
          linarith
      _ = (‖tf71cfC θ lam 0‖ + B) / ‖z‖ := by
          rw [add_div, div_eq_mul_inv, div_eq_mul_inv]; ring
  have hfin : (‖tf71cfC θ lam 0‖ + B) / ‖z‖ < ε := by
    rw [div_lt_iff₀ hzn]
    have h1 : ε * ((‖tf71cfC θ lam 0‖ + B) / ε + 1) = (‖tf71cfC θ lam 0‖ + B) + ε := by
      field_simp
    have h2 : ε * ((‖tf71cfC θ lam 0‖ + B) / ε + 1) ≤ ε * ‖z‖ :=
      mul_le_mul_of_nonneg_left hzR hε.le
    linarith
  linarith

end Work.ZeroFreeTables
