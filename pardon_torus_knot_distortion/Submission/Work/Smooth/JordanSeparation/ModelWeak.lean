import Mathlib
import Submission.Work.Smooth.JordanSeparation.WeakDefs
import Submission.Work.Smooth.JordanSeparation.norm_integrand_sub_model_le
import Submission.Work.Analysis.SqAddSq.tendsto_model_integral

/-!
# The local model estimates at a *regular* parameter

The two estimates `norm_integrand_sub_model_le` and `tendsto_model_integral` of the siblings
`Submission/Work/Smooth/JordanSeparation/norm_integrand_sub_model_le.lean` and
`Submission/Work/Analysis/SqAddSq/tendsto_model_integral.lean`, restated with the hypothesis
`deriv c.γ 0 ≠ 0` in place of `c.IsImmersion` (which their proofs use only at the parameter `0`).
-/

namespace Work.Smooth.JordanSeparation

open Work.Smooth.Jordan

noncomputable section

/-- `γ'(t) = ‖γ'(t)‖·unitTangent c t` at the regular parameter `0`, in the form used below. -/
theorem norm_integrand_sub_model_le_of_deriv_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) {η τ s : ℝ}
    (hη : 0 ≤ η) (hηρ : η ≤ ‖deriv c.γ 0‖ / 8)
    (hexp : ‖(c.γ τ - c.γ 0) - (τ : ℂ) * deriv c.γ 0‖ ≤ η * |τ|)
    (hder : ‖deriv c.γ τ - deriv c.γ 0‖ ≤ η)
    (hden : (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2 ≠ 0)
    (hs : 0 < s) :
    ‖(s : ℂ) * deriv c.γ τ / ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2)
      - (s : ℂ) * deriv c.γ 0 / ((deriv c.γ 0) ^ 2 * (τ : ℂ) ^ 2
          + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2)‖
    ≤ 4 * η * s / (((‖deriv c.γ 0‖ ^ 2) / 2) * τ ^ 2 + s ^ 2) := by
  have hρ : 0 < ‖deriv c.γ 0‖ := norm_pos_iff.mpr hreg
  exact norm_integrand_sub_model_aux hρ hη hηρ hs
    (deriv_eq_norm_mul_unitTangent' c 0) (norm_unitTangent_of_deriv_ne_zero c hreg) hexp hder hden

end

theorem tendsto_model_integral_of_deriv_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun s : ℝ => ∫ τ in (0 : ℝ)..ε,
        (s : ℂ) * deriv c.γ 0 /
          ((deriv c.γ 0) ^ 2 * (τ : ℂ) ^ 2
            + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((Real.pi / 2 : ℂ) * (starRingEnd ℂ) (Work.Smooth.JordanSeparation.unitTangent c 0))) := by
  set u := Work.Smooth.JordanSeparation.unitTangent c 0 with hu
  set d := deriv c.γ 0 with hd
  have hdne : d ≠ 0 := by rw [hd]; exact hreg
  set r := ‖d‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hdne
  have hur : ‖u‖ = 1 := by
    rw [hu]; exact Work.Smooth.JordanSeparation.norm_unitTangent_of_deriv_ne_zero c hreg
  have hd_eq : d = (r : ℂ) * u := by
    have hc : ((r : ℂ)) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hrpos
    have hthis : u = d / ((r : ℝ) : ℂ) := by
      rw [hu, Work.Smooth.JordanSeparation.unitTangent_def, ← hd, ← hr]
    rw [hthis]
    exact (mul_div_cancel₀ d hc).symm
  have hmain : ∀ s : ℝ, 0 < s →
      (∫ τ in (0 : ℝ)..ε, (s : ℂ) * d / (d ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2))
        = (starRingEnd ℂ u) * ((Real.arctan (ε * r / s) : ℝ) : ℂ) := by
    intro s hs
    have hpt : ∀ τ : ℝ, (s : ℂ) * d / (d ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2)
        = (starRingEnd ℂ u) * ((s * r / (r ^ 2 * τ ^ 2 + s ^ 2) : ℝ) : ℂ) := by
      intro τ
      rw [hd_eq]
      exact Work.Analysis.SqAddSq.integrand_complex_eq u hur r τ s hs
    rw [intervalIntegral.integral_congr (fun τ _ => hpt τ)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_ofReal]
    rw [show (∫ τ in (0 : ℝ)..ε, s * r / (r ^ 2 * τ ^ 2 + s ^ 2))
          = r * ∫ τ in (0 : ℝ)..ε, s / (r ^ 2 * τ ^ 2 + s ^ 2) by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro τ _
      rw [mul_comm s r]
      exact mul_div_assoc r s _]
    rw [Work.Analysis.SqAddSq.integral_s_div_sq_add_sq_local (by positivity) hs hε.le]
    rw [Real.sqrt_sq hrpos.le, ← mul_assoc, mul_one_div_cancel (ne_of_gt hrpos), one_mul]
  have hlim : Filter.Tendsto (fun s : ℝ => Real.arctan (ε * r / s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    have hk : 0 < ε * r := mul_pos hε hrpos
    have h1 : Filter.Tendsto (fun s : ℝ => s⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        Filter.atTop := tendsto_inv_nhdsGT_zero
    have h2 : Filter.Tendsto (fun s : ℝ => (ε * r) * s⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        Filter.atTop := h1.const_mul_atTop hk
    have h3 : Filter.Tendsto (fun s : ℝ => ε * r / s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        Filter.atTop := by simpa [div_eq_mul_inv] using h2
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h3
  have hH : Filter.Tendsto
      (fun s : ℝ => (starRingEnd ℂ u) * ((Real.arctan (ε * r / s) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((Real.pi / 2 : ℂ) * (starRingEnd ℂ u))) := by
    have h1 : Filter.Tendsto (fun s : ℝ => ((Real.arctan (ε * r / s) : ℝ) : ℂ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((Real.pi / 2 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (Real.pi / 2)).comp hlim
    have h2 := h1.const_mul (starRingEnd ℂ u)
    have heq : (starRingEnd ℂ u) * (((Real.pi / 2 : ℝ)) : ℂ)
        = (Real.pi / 2 : ℂ) * (starRingEnd ℂ u) := by
      rw [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    rw [← heq]
    exact h2
  refine hH.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hmain s hs).symm

end Work.Smooth.JordanSeparation
