import Mathlib
import Submission.Work.Pert.PinLogDev.Setup
import Submission.Work.Pert.PinLogDev.taylor_two
import Submission.Work.Pert.PinLogDev.wfun_estimates
import Submission.Work.Pert.PinLogDev.log_mul_one_add_re_pos

/-!
# `Work.Pert.PinLogDev.delta_model_taylor`

The *model* Taylor expansion of the PERT defect `deltaF u σ α w = liftF u σ α w - (w+1)` in the
coordinate `τ = τ_f(w)`: with `c = σ (u 0 ^ 2 - deriv u 0) / ((2πiα) (1 - σ u 0))`,

  `deltaF u σ α w = c · τ_f(w) + O(‖τ_f(w)‖²)`   for `‖τ_f(w)‖ ≤ θ`.

For `τ = τ_f(w)` the defect depends on `w` only through `τ`:
`deltaF u σ α w = (1/(2πiα)) log (1 - σ u τ/(1 + τ u τ)) - 1 = (1/(2πiα)) log (H τ) - 1` with
`H t = 1 - σ u t / (1 + t u t)`.  Since `H 0 = 1 - σ u 0 = exp (2πiα)` (the gate normalisation)
and `H` is holomorphic near `0`, we may write `H t = H 0 · (1 + w(t))` with
`w(t) = H t / H 0 - 1`, so

  `deltaF = (1/(2πiα)) log (1 + w(τ))`.

Now `w(τ) = O(τ)` and, using the second-order Taylor expansion of `u` at `0`,
`w(τ) = λ τ + O(τ²)` with `λ = σ (u 0 ^ 2 - deriv u 0)/(1 - σ u 0)`; the elementary bound
`‖log (1 + z) - z‖ ≤ ‖z‖² (1-‖z‖)⁻¹/2` of Mathlib converts this into the required estimate.

The three analytic inputs are `Work.Pert.PinLogDev.taylor_two` (second-order Taylor for `u`),
`Work.Pert.PinLogDev.wfun_estimates` (the two estimates on `w`) and
`Work.Pert.PinLogDev.log_mul_one_add_re_pos` (the branch of the logarithm).
-/

set_option linter.unusedVariables false

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-- The model function `H t = 1 - σ u t / (1 + t u t)`; on the gate `H (τ_f w) = 1 - sfun u σ α w`,
so that `deltaF u σ α w = (1/(2πiα)) log (H (τ_f w)) - 1`. -/
def Hfun (u : ℂ → ℂ) (σ : ℂ) : ℂ → ℂ := fun t => 1 - σ * u t / (1 + t * u t)

/-- The normalised deviation `w = H / H 0 - 1`, `H 0 = 1 - σ u 0`; `1 + w (τ_f w)` is the
`H`-value divided by its value at `0`. -/
def wfun (u : ℂ → ℂ) (σ : ℂ) : ℂ → ℂ := fun t => Hfun u σ t / (1 - σ * u 0) - 1

theorem delta_model_taylor {u : ℂ → ℂ} {σ α : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hα64 : ‖α‖ ≤ 1 / 64) (hαne : α ≠ 0)
    (hσr : ‖σ‖ < r) (hσ : σ ≠ 0)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) r))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huL : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r, ‖u z - u w‖ ≤ C * ‖z - w‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧
      ∀ w : ℂ, ‖Work.Pert.tauC σ α w‖ ≤ θ →
        ‖Work.Pert.PinLogDev.deltaF u σ α w
            - (σ * (u 0 ^ 2 - deriv u 0)
                / ((2 * Real.pi * Complex.I * α) * (1 - σ * u 0)))
              * Work.Pert.tauC σ α w‖ ≤ K * ‖Work.Pert.tauC σ α w‖ ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have him : (2 * Real.pi * Complex.I * α).im = 2 * Real.pi * α.re := by
    have h1 : (2 : ℂ) * Real.pi * Complex.I * α
        = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * α) := by push_cast; ring
    rw [h1]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hRe_le : |α.re| ≤ 1 / 64 := le_trans (Complex.abs_re_le_norm α) hα64
  have hRe_ub : α.re ≤ 1 / 64 := (abs_le.mp hRe_le).2
  have hRe_lb : -(1 / 64) ≤ α.re := (abs_le.mp hRe_le).1
  have him_abs : |(2 * Real.pi * Complex.I * α).im| ≤ Real.pi / 32 := by
    rw [him, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    nlinarith [hRe_le, hpi]
  have him_gt : -Real.pi < (2 * Real.pi * Complex.I * α).im := by
    rw [him]; nlinarith [hRe_lb, hpi]
  have him_le : (2 * Real.pi * Complex.I * α).im ≤ Real.pi := by
    rw [him]; nlinarith [hRe_ub, hpi]
  have hH0ne : 1 - σ * u 0 ≠ 0 := by rw [hnorm]; exact Complex.exp_ne_zero _
  have hreH0 : 0 < (1 - σ * u 0).re := by
    rw [hnorm, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by rw [him]; nlinarith [hRe_lb, hpi],
           by rw [him]; nlinarith [hRe_ub, hpi]⟩
  have hlogH0 : Complex.log (1 - σ * u 0) = 2 * Real.pi * Complex.I * α := by
    rw [hnorm]
    exact Complex.log_exp him_gt him_le
  obtain ⟨M, θu, hM, hθu, hTay⟩ := taylor_two hr hu (fun z hz => (hu2 z hz).2)
  obtain ⟨c₁, c₂, ρ, hc1, hc2, hρ, hEst⟩ := wfun_estimates hr hM hθu hu2 hTay hH0ne
  refine ⟨max (‖(1 / (2 * Real.pi * Complex.I * α))‖ * (c₁ ^ 2 + c₂)) 1,
      min ρ (1 / (2 * (c₁ + 1))), ?_, ?_, ?_⟩
  · exact lt_max_of_lt_right one_pos
  · exact lt_min hρ (by positivity)
  · intro w hw
    set t : ℂ := Work.Pert.tauC σ α w with ht
    have htθ : ‖t‖ ≤ min ρ (1 / (2 * (c₁ + 1))) := by rw [ht]; exact hw
    have htρ : ‖t‖ ≤ ρ := le_trans htθ (min_le_left _ _)
    have ht1 : ‖t‖ ≤ 1 / (2 * (c₁ + 1)) := le_trans htθ (min_le_right _ _)
    obtain ⟨hw1, hw2⟩ := hEst t htρ
    have hw1' : ‖wfun u σ t‖ ≤ c₁ * ‖t‖ := by
      have h := hw1
      simp only [wfun, Hfun] at h ⊢
      exact h
    have hw2' : ‖wfun u σ t - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t‖
        ≤ c₂ * ‖t‖ ^ 2 := by
      have h := hw2
      simp only [wfun, Hfun] at h ⊢
      exact h
    have hc1t : c₁ * ‖t‖ ≤ 1 / 2 := by
      have h2 : ‖t‖ * (2 * (c₁ + 1)) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (c₁ + 1))).mp ht1
      nlinarith [h2, hc1, norm_nonneg t]
    have hwt_half : ‖wfun u σ t‖ ≤ 1 / 2 := le_trans hw1' hc1t
    -- the log identity
    have hHfun_eq : Hfun u σ t = (1 - σ * u 0) * (1 + wfun u σ t) := by
      rw [show (1 + wfun u σ t) = Hfun u σ t / (1 - σ * u 0) from by
        simp only [wfun]; ring]
      rw [mul_div_cancel₀ _ hH0ne]
    have hlog : Complex.log (Hfun u σ t)
        = 2 * Real.pi * Complex.I * α + Complex.log (1 + wfun u σ t) := by
      rw [hHfun_eq, log_mul_one_add_re_pos hreH0 hwt_half, hlogH0]
    have hdelta : deltaF u σ α w
        = (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (Hfun u σ t) - 1 := by
      simp only [deltaF, liftF, sfun, Hfun]
      rw [← ht]
      ring
    have h2π : (2 : ℂ) * Real.pi * Complex.I * α ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) hαne
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hdelta2 : deltaF u σ α w
        = (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 + wfun u σ t) := by
      rw [hdelta, hlog, mul_add, div_mul_cancel₀ (1 : ℂ) h2π]
      ring
    have hlogw := Complex.norm_log_one_add_sub_self_le (z := wfun u σ t)
      (by linarith : ‖wfun u σ t‖ < 1)
    have hle : ‖wfun u σ t‖ ^ 2 * (1 - ‖wfun u σ t‖)⁻¹ / 2 ≤ ‖wfun u σ t‖ ^ 2 := by
      have h1 : (1 - ‖wfun u σ t‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖wfun u σ t‖) (by norm_num : (0 : ℝ) < 2)]
        norm_num
        linarith
      calc ‖wfun u σ t‖ ^ 2 * (1 - ‖wfun u σ t‖)⁻¹ / 2
          ≤ ‖wfun u σ t‖ ^ 2 * 2 / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = ‖wfun u σ t‖ ^ 2 := by ring
    have hlog1 : ‖Complex.log (1 + wfun u σ t) - wfun u σ t‖ ≤ c₁ ^ 2 * ‖t‖ ^ 2 := by
      refine le_trans hlogw ?_
      refine le_trans hle ?_
      have h3 : ‖wfun u σ t‖ ^ 2 ≤ (c₁ * ‖t‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) hw1'
      calc ‖wfun u σ t‖ ^ 2 ≤ (c₁ * ‖t‖) ^ 2 := h3
        _ = c₁ ^ 2 * ‖t‖ ^ 2 := by ring
    have hbound : ‖Complex.log (1 + wfun u σ t)
        - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t‖ ≤ (c₁ ^ 2 + c₂) * ‖t‖ ^ 2 := by
      have hsplit : Complex.log (1 + wfun u σ t)
          - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t
          = (Complex.log (1 + wfun u σ t) - wfun u σ t)
            + (wfun u σ t - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t) := by ring
      rw [hsplit]
      calc ‖(Complex.log (1 + wfun u σ t) - wfun u σ t)
              + (wfun u σ t - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t)‖
          ≤ ‖Complex.log (1 + wfun u σ t) - wfun u σ t‖
              + ‖wfun u σ t - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t‖ :=
            norm_add_le _ _
        _ ≤ c₁ ^ 2 * ‖t‖ ^ 2 + c₂ * ‖t‖ ^ 2 := add_le_add hlog1 hw2'
        _ = (c₁ ^ 2 + c₂) * ‖t‖ ^ 2 := by ring
    have hc_eq : (σ * (u 0 ^ 2 - deriv u 0)
            / ((2 * Real.pi * Complex.I * α) * (1 - σ * u 0)))
        = (1 / (2 * Real.pi * Complex.I * α))
            * (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) := by
      field_simp
    calc ‖deltaF u σ α w
            - (σ * (u 0 ^ 2 - deriv u 0)
                / ((2 * Real.pi * Complex.I * α) * (1 - σ * u 0))) * t‖
        = ‖deltaF u σ α w
            - (1 / (2 * Real.pi * Complex.I * α))
              * (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t‖ := by rw [hc_eq]
      _ = ‖(1 / (2 * Real.pi * Complex.I * α))
              * (Complex.log (1 + wfun u σ t)
                  - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t)‖ := by
            rw [hdelta2]; ring_nf
      _ = ‖(1 / (2 * Real.pi * Complex.I * α))‖
              * ‖Complex.log (1 + wfun u σ t)
                  - (σ * (u 0 ^ 2 - deriv u 0) / (1 - σ * u 0)) * t‖ := norm_mul _ _
      _ ≤ ‖(1 / (2 * Real.pi * Complex.I * α))‖ * ((c₁ ^ 2 + c₂) * ‖t‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ = (‖(1 / (2 * Real.pi * Complex.I * α))‖ * (c₁ ^ 2 + c₂)) * ‖t‖ ^ 2 := by ring
      _ ≤ max (‖(1 / (2 * Real.pi * Complex.I * α))‖ * (c₁ ^ 2 + c₂)) 1 * ‖t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

end
end Work.Pert.PinLogDev
