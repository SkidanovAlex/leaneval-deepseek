import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71Fc_model
import Submission.Work.ZeroFreeTables.exp_neg_mul_ibp
import Submission.Work.ZeroFreeTables.norm_intervalIntegral_exp_neg_mul_le

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

/-- Weighted norm bound for the Laplace kernel on the strip `-1 ≤ Re z`.

For `0 ≤ b`, `-1 ≤ z.re` and `h` continuous on `[0,b]`, the modulus of the kernel
`exp (-(z * t))` is at most `exp b` on `[0,b]` (since `‖exp (-(z t))‖ = exp (-z.re * t)
≤ exp t ≤ exp b` for `0 ≤ t ≤ b`), hence
`‖∫₀^b exp (-(z t)) * h t‖ ≤ exp b * ∫₀^b ‖h t‖`. -/
theorem norm_intervalIntegral_exp_neg_mul_le_strip (z : ℂ) (hz : -(1:ℝ) ≤ z.re) {b : ℝ}
    (hb : 0 ≤ b) {h : ℝ → ℂ} (hcont : ContinuousOn h (Set.Icc (0:ℝ) b)) :
    ‖∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * h t‖
      ≤ Real.exp b * ∫ t in (0:ℝ)..b, ‖h t‖ := by
  have hexp_cont : Continuous (fun t : ℝ => Complex.exp (-(z * (t:ℂ)))) := by fun_prop
  have hFcont : ContinuousOn (fun t : ℝ => Complex.exp (-(z * (t:ℂ))) * h t)
      (Set.Icc (0:ℝ) b) :=
    (hexp_cont.continuousOn).mul hcont
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) b,
      ‖Complex.exp (-(z * (t:ℂ))) * h t‖ ≤ Real.exp b * ‖h t‖ := by
    intro t ht
    rw [norm_mul]
    have hexp : ‖Complex.exp (-(z * (t:ℂ)))‖ ≤ Real.exp b := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      nlinarith [hz, ht.1, ht.2]
    exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hfc : IntervalIntegrable
      (fun t : ℝ => ‖Complex.exp (-(z * (t:ℂ))) * h t‖) volume 0 b :=
    (hFcont.norm).intervalIntegrable_of_Icc hb
  have hgc : IntervalIntegrable (fun t : ℝ => Real.exp b * ‖h t‖) volume 0 b :=
    ((hcont.norm).const_mul (Real.exp b)).intervalIntegrable_of_Icc hb
  calc ‖∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * h t‖
      ≤ ∫ t in (0:ℝ)..b, ‖Complex.exp (-(z * (t:ℂ))) * h t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hb
    _ ≤ ∫ t in (0:ℝ)..b, Real.exp b * ‖h t‖ :=
        intervalIntegral.integral_mono_on hb hfc hgc hbound
    _ = Real.exp b * ∫ t in (0:ℝ)..b, ‖h t‖ :=
        intervalIntegral.integral_const_mul (Real.exp b) (fun t => ‖h t‖)

end Work.ZeroFreeTables

namespace Work.ZeroFreeTables.OffAxis

-- HINT. `Work.ZeroFreeTables.tf71Fc_decay` (Submission/Work/ZeroFreeTables/tf71Fc_decay.lean) already
-- proves the sharper `‖tf71Fc θ lam z‖ ≤ (‖tf71cfC θ lam 0‖ + B)/‖z‖` for `0 ≤ z.re`, via
-- `tf71Fc_eq_integral_cf`, `exp_neg_mul_ibp` (with `tf71cfC_at_twoγ`) and
-- `norm_intervalIntegral_exp_neg_mul_le`.  The same argument works on the strip `-1 ≤ z.re`
-- with the weighted bound `‖∫₀^b exp(-(z*t)) * h t‖ ≤ exp b * ∫₀^b ‖h t‖` (since
-- `‖exp(-(z*t))‖ = exp(-z.re * t) ≤ exp t` for `0 ≤ t ≤ b`); then
-- `C := ‖tf71cfC θ lam 0‖ + exp (2 * tf71γ θ lam) * B` works and `‖z‖ ≥ |z.im| ≥ 1`.
theorem tf71Fc_decay_strip (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, -(1:ℝ) ≤ z.re → 1 ≤ |z.im| → ‖tf71Fc θ lam z‖ ≤ C / |z.im| := by
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
  refine ⟨‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B + 1, ?_, ?_⟩
  · have h1 : 0 ≤ ‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B :=
      add_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hBnn)
    linarith
  · intro z hzre hzim
    have hznz : z ≠ 0 := by
      intro hz
      have h0 : |z.im| = 0 := by rw [hz]; simp
      linarith [hzim, h0]
    have hzimpos : 0 < |z.im| := lt_of_lt_of_le one_pos hzim
    have hnormz : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hnum : 0 ≤ ‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B :=
      add_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hBnn)
    -- `tf71Fc` is the Laplace transform of the smooth closed form on `[0, 2γ]`.
    have hmodel := tf71Fc_eq_integral_cf hθ0 hθ1 hlam z
    -- Integration by parts against the exponential, with the vanishing right endpoint.
    have hIBP := exp_neg_mul_ibp (b := 2 * tf71γ θ lam) z hznz (tf71cfC θ lam) (tf71cfC' θ lam)
      (fun t _ => tf71cfC_hasDerivAt θ lam t)
      ((tf71cfC_cont θ lam).continuousOn)
      ((tf71cfC'_cont θ lam).continuousOn)
      (tf71cfC_at_twoγ hθ0 hθ1 hlam)
    -- The weighted bound for the kernel on the strip `-1 ≤ Re z`.
    have hnorm := norm_intervalIntegral_exp_neg_mul_le_strip (b := 2 * tf71γ θ lam) z hzre hTle
      ((tf71cfC'_cont θ lam).continuousOn)
    have hJ : ‖∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        Complex.exp (-(z * (t:ℂ))) * tf71cfC' θ lam t‖
          ≤ Real.exp (2 * tf71γ θ lam) * B :=
      hnorm.trans (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le)
    have hkey : ‖tf71Fc θ lam z‖ ≤
        (‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B) / ‖z‖ := by
      calc ‖tf71Fc θ lam z‖
          = ‖∫ t in (0:ℝ)..(2 * tf71γ θ lam),
              Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t‖ := by rw [hmodel]
        _ = ‖tf71cfC θ lam 0 / z + z⁻¹ * ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
                Complex.exp (-(z * (t:ℂ))) * tf71cfC' θ lam t‖ := by rw [hIBP]
        _ ≤ ‖tf71cfC θ lam 0‖ / ‖z‖ + ‖z‖⁻¹ * (Real.exp (2 * tf71γ θ lam) * B) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_div, norm_mul, norm_inv]
            have h2 := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr (norm_nonneg z))
            linarith
        _ = (‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B) / ‖z‖ := by
            rw [add_div, div_eq_mul_inv, div_eq_mul_inv]; ring
    have hstep1 : (‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B) / ‖z‖
        ≤ (‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B) / |z.im| :=
      div_le_div_of_nonneg_left hnum hzimpos hnormz
    have hstep2 : (‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B) / |z.im|
        ≤ (‖tf71cfC θ lam 0‖ + Real.exp (2 * tf71γ θ lam) * B + 1) / |z.im| :=
      div_le_div_of_nonneg_right (by linarith) hzimpos.le
    linarith

end Work.ZeroFreeTables.OffAxis
