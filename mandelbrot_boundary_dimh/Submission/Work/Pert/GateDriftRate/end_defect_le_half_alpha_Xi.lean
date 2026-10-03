import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.norm_endDefect_le
import Submission.Work.Pert.sigma_le_half_rr
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.tauC_gate_bound
import Submission.Work.Pert.tauC_norm_le_sharp
import Submission.Work.Pert.GateDriftRate.gate_image_near_one
import Submission.Work.Pert.one_sub_sfun_mem_slitPlane
import Submission.Work.Pert.one_add_tauC_mul_u_ne_zero

namespace Work.Pert.GateDriftRate

open MandelDim Complex Metric

noncomputable section

variable {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ}

/-- **The defect as a function of the chart coordinate `τ`.**  For the perturbation datum
`(σ, u, α)` and `τ = tauC σ α w` the difference `liftF u σ α w - (w+1)` equals
`(2πiα)⁻¹ log (1 - σ u τ/(1 + τ u τ)) - 1`; this function of `τ` is what the Schwarz
argument applies to. -/
def defectF (u : ℂ → ℂ) (σ α : ℂ) (τ : ℂ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - σ * u τ / (1 + τ * u τ)) - 1

/-- The defect function evaluated at a chart point is the defect of the lift. -/
lemma defectF_tauC (w : ℂ) :
    defectF u σ α (Work.Pert.tauC σ α w)
      = Work.Pert.liftF u σ α w - (w + 1) := by
  unfold defectF Work.Pert.liftF Work.Pert.sfun Work.Pert.tauC
  ring

/-- The defect function at the lower end `τ = σ` is the end defect. -/
lemma defectF_sigma (hσu : 1 + σ * u σ ≠ 0) :
    defectF u σ α σ = Work.Pert.endDefect u σ α := by
  unfold defectF Work.Pert.endDefect
  have h1 : (1 : ℂ) - σ * u σ / (1 + σ * u σ) = 1 / (1 + σ * u σ) := by
    field_simp
    ring
  rw [h1]

/-- The defect function vanishes at the upper end `τ = 0` under the normalisation
`1 - σ u 0 = exp (2πiα)`. -/
lemma defectF_zero (hα0 : α ≠ 0) (hαre : |(2 * Real.pi * Complex.I * α).im| < Real.pi)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    defectF u σ α 0 = 0 := by
  unfold defectF
  have h1 : (1 : ℂ) - σ * u 0 / (1 + 0 * u 0) = Complex.exp (2 * Real.pi * Complex.I * α) := by
    simpa using hnorm
  rw [h1]
  have him : (2 * Real.pi * Complex.I * α).im = 2 * Real.pi * α.re := by simp
  rw [him] at hαre
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hαre
  have h2 : Complex.log (Complex.exp (2 * Real.pi * Complex.I * α))
      = 2 * Real.pi * Complex.I * α :=
    Complex.log_exp (by linarith) (by linarith)
  rw [h2]
  have hne : (2 * Real.pi * Complex.I * α) ≠ 0 := by
    simp [hα0, Real.pi_ne_zero, Complex.I_ne_zero]
  rw [one_div_mul_cancel hne, sub_self]

/-- **Arithmetic.**  For `0 ≤ v ≤ π/16` one has `e^v - 1 ≤ 4v/π`. -/
private lemma exp_sub_one_le_of_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ Real.pi / 16) :
    Real.exp v - 1 ≤ 4 * v / Real.pi := by
  have hv1 : v ≤ 1 := by linarith [h1, Real.pi_pos, Real.pi_lt_four]
  have hexp := Real.exp_bound' h0 hv1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at hexp
  have h2 : v + 3 / 4 * v ^ 2 ≤ 4 * v / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [h1, h0, Real.pi_lt_d4, Real.pi_pos, sq_nonneg (Real.pi)]
  linarith

/-- **Arithmetic.**  `2 (e^{2π‖α‖Ξ} - 1) / 32 ≤ Ξ‖α‖/2` under `Ξ‖α‖ ≤ 1/32`. -/
private lemma arith_final {Ξ : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hna : 0 ≤ ‖α‖)
    (hε : ‖α‖ * Ξ ≤ 1 / 32) :
    2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1) / 32 ≤ (1 / 2) * ‖α‖ * Ξ := by
  set v : ℝ := 2 * Real.pi * ‖α‖ * Ξ with hv
  have h0 : 0 ≤ v := by
    rw [hv]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) hna) hΞ.le
  have h1 : v ≤ Real.pi / 16 := by
    rw [hv]
    have hring : 2 * Real.pi * ‖α‖ * Ξ = 2 * Real.pi * (‖α‖ * Ξ) := by ring
    rw [hring]
    nlinarith [hε, Real.pi_pos]
  have hmain : Real.exp v - 1 ≤ 4 * v / Real.pi := exp_sub_one_le_of_le h0 h1
  have hkey : 4 * v / Real.pi = 8 * ‖α‖ * Ξ := by
    rw [hv]; field_simp; ring
  rw [hkey] at hmain
  rw [hv] at hmain
  linarith

/-- **The gate image contains the disk.**  From `gate_image_near_one`: for `τ` in the open disk
of radius `‖σ‖/(2(e^{2π‖α‖Ξ}-1))`, away from `0` and `σ`, the point `τ` is the `τ_f`-image of a
gate point. -/
lemma exists_tauC_gate_of_mem_ball (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hε : ‖α‖ * Ξ ≤ 1 / 32) (hσ : σ ≠ 0) {τ : ℂ}
    (hτ : τ ∈ Metric.ball (0 : ℂ) (‖σ‖ / (2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1))))
    (hτ0 : τ ≠ 0) (hτσ : τ ≠ σ) :
    ∃ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w = τ := by
  have hσnorm : 0 < ‖σ‖ := norm_pos_iff.mpr hσ
  have hαpos : 0 < ‖α‖ := by
    rcases lt_or_eq_of_le (norm_nonneg α) with h | h
    · exact h
    · exfalso
      have h1 : α = 0 := norm_eq_zero.mp h.symm
      rw [h1] at hInF1
      simp [MandelDim.InF1] at hInF1
  set d : ℝ := 2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1) with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    have h1 : 0 < 2 * Real.pi * ‖α‖ * Ξ := by
      have : 0 < 2 * Real.pi * ‖α‖ := by
        have h3 : (0 : ℝ) < 2 * Real.pi := by positivity
        exact mul_pos h3 hαpos
      exact mul_pos this hΞ
    have h2 : 1 < Real.exp (2 * Real.pi * ‖α‖ * Ξ) := Real.one_lt_exp_iff.mpr h1
    linarith
  have hτnorm : ‖τ‖ < ‖σ‖ / d := by
    rw [hddef] at hτ
    rwa [Metric.mem_ball, dist_zero_right] at hτ
  -- `E = 1 - σ/τ ≠ 0`
  have hE0 : (1 : ℂ) - σ / τ ≠ 0 := by
    intro hcon
    have h2 : σ = τ := by
      have h3 := sub_eq_zero.mp hcon
      have h4 := (eq_div_iff hτ0).mp h3
      simpa using h4.symm
    exact hτσ h2.symm
  -- the hypothesis of `gate_image_near_one`
  have hclose : d < ‖1 - (1 - σ / τ)‖ := by
    have h1 : (1 : ℂ) - (1 - σ / τ) = σ / τ := by ring
    rw [h1, norm_div, lt_div_iff₀ (norm_pos_iff.mpr hτ0)]
    rw [lt_div_iff₀ hdpos] at hτnorm
    linarith
  obtain ⟨w, hwQ, hwexp⟩ :=
    gate_image_near_one hΞ hInF1 hε hE0 (by rw [← hddef]; exact hclose)
  refine ⟨w, hwQ, ?_⟩
  have h1E : (1 : ℂ) - (1 - σ / τ) = σ / τ := by ring
  rw [Work.Pert.tauC, hwexp, h1E]
  field_simp

/-- **Holomorphy of the defect function on the covered disk.**  `defectF u σ α` is a composition
of the holomorphic function `τ ↦ 1 - σ u τ/(1 + τ u τ)` with the principal logarithm.  At every
point of the disk one checks: the denominator `1 + τ u τ` does not vanish, and the argument
`1 - σ u τ/(1 + τ u τ)` lies in the slit plane `ℂ ∖ (-∞,0]`.
The two exceptional points are handled separately; every other point of the disk is the image of a
gate point `w`, where `hNT` bounds `log (1 - sfun u σ α w)` by `(33/32)·2π‖α‖ < π`. -/
lemma defectF_differentiable' {Ξ r rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hr : 0 < r) (hα0 : α ≠ 0) (hα64 : ‖α‖ ≤ 1 / 64)
    (hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) rr)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hσb : ‖σ‖ < 1 / 2) (hσr : ‖σ‖ < r)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hcover : ∀ τ ∈ Metric.ball (0 : ℂ) r, τ ≠ 0 → τ ≠ σ →
      ∃ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w = τ)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    DifferentiableOn ℂ (defectF u σ α) (Metric.ball (0 : ℂ) r) := by
  have hσm : σ ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hσr
  have hσmr : σ ∈ Metric.ball (0 : ℂ) rr := hsub hσm
  have hbσ : ‖σ * u σ‖ < 1 := by
    rw [norm_mul]
    have h2 : ‖u σ‖ ≤ 2 := (hu2 σ hσmr).2
    have h1 : (0 : ℝ) ≤ ‖σ‖ := norm_nonneg σ
    nlinarith [hσb]
  have hσD : (1 : ℂ) + σ * u σ ≠ 0 := by
    intro h
    have h1 : σ * u σ = -1 := by linear_combination h
    rw [h1, norm_neg, norm_one] at hbσ
    linarith
  have hpt : ∀ τ ∈ Metric.ball (0 : ℂ) r, DifferentiableAt ℂ (defectF u σ α) τ := by
    intro τ hτ
    have hτrr : τ ∈ Metric.ball (0 : ℂ) rr := hsub hτ
    have huτ : DifferentiableAt ℂ u τ :=
      hu.differentiableAt (Metric.isOpen_ball.mem_nhds hτrr)
    have hDne : (1 : ℂ) + τ * u τ ≠ 0 := by
      by_cases h0 : τ = 0
      · rw [h0]; simp
      · by_cases hσ : τ = σ
        · rw [hσ]; exact hσD
        · obtain ⟨w, hw, hwτ⟩ := hcover τ hτ h0 hσ
          have h := Work.Pert.one_add_tauC_mul_u_ne_zero (u := u) (σ := σ) (α := α) (w := w)
            (hNT w hw)
          rwa [hwτ] at h
    have hslit : (1 : ℂ) - σ * u τ / (1 + τ * u τ) ∈ Complex.slitPlane := by
      by_cases h0 : τ = 0
      · rw [h0]
        have hg : (1 : ℂ) - σ * u 0 / (1 + 0 * u 0)
            = Complex.exp (2 * Real.pi * Complex.I * α) := by
          simpa [mul_zero, add_zero, div_one] using hnorm
        rw [hg]
        apply Work.Pert.exp_mem_slitPlane_of_abs_im_lt
        have h1 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
          rw [show (2 * Real.pi * Complex.I * α : ℂ)
                = ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * α by ring]
          rw [norm_mul, norm_mul, norm_mul]
          simp
        calc |(2 * Real.pi * Complex.I * α : ℂ).im|
            ≤ ‖(2 * Real.pi * Complex.I * α : ℂ)‖ := Complex.abs_im_le_norm _
          _ = 2 * Real.pi * ‖α‖ := h1
          _ ≤ 2 * Real.pi * (1 / 64) := by
              have h0 : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
              nlinarith [Real.pi_pos, hα64]
          _ < Real.pi := by nlinarith [Real.pi_pos]
      · by_cases hσ : τ = σ
        · rw [hσ]
          have hval : (1 : ℂ) - σ * u σ / (1 + σ * u σ) = (1 + σ * u σ)⁻¹ := by
            field_simp
            ring
          rw [hval]
          refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
          rw [Complex.inv_re]
          apply div_pos _ (Complex.normSq_pos.mpr hσD)
          have hre : ((1 : ℂ) + σ * u σ).re = 1 + (σ * u σ).re := by simp
          rw [hre]
          have h4 : -(‖σ * u σ‖) ≤ (σ * u σ).re := (abs_le.mp (Complex.abs_re_le_norm _)).1
          linarith
        · obtain ⟨w, hw, hwτ⟩ := hcover τ hτ h0 hσ
          have h := Work.Pert.one_sub_sfun_mem_slitPlane (u := u) (σ := σ) (α := α) (w := w)
            hα64 (hNT w hw)
          simpa [Work.Pert.sfun, hwτ] using h
    have hD : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) + z * u z) τ :=
      (differentiableAt_const (1 : ℂ)).add (differentiableAt_id.mul huτ)
    have hG : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - σ * u z / (1 + z * u z)) τ :=
      (differentiableAt_const (1 : ℂ)).sub ((huτ.const_mul σ).div hD hDne)
    have hlog : DifferentiableAt ℂ
        (fun z : ℂ => Complex.log ((1 : ℂ) - σ * u z / (1 + z * u z))) τ :=
      hG.clog hslit
    have hfin : DifferentiableAt ℂ
        (fun z : ℂ => (1 / (2 * Real.pi * Complex.I * α)) *
          Complex.log ((1 : ℂ) - σ * u z / (1 + z * u z)) - 1) τ :=
      (hlog.const_mul _).sub (differentiableAt_const (1 : ℂ))
    exact hfin
  exact fun τ hτ => (hpt τ hτ).differentiableWithinAt

theorem end_defect_le_half_alpha_Xi {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    ‖Work.Pert.endDefect u σ α‖ ≤ (1 / 2) * ‖α‖ * Ξ := by
  -- ## basic facts about `α`
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hα0 : α ≠ 0 := by intro h; rw [h] at hαre; simp at hαre
  have hna : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
  have hM1024 : (1024 : ℝ) ≤ M := by norm_num at hM ⊢; exact hM
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h1 : 1 / (32 * (M + 2 + Ξ)) ≤ 1 / 64 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hα64' : ‖α‖ < 1 / 64 := by
    have h1 : 1 / (32 * (M + 2 + Ξ)) < 1 / 64 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hε : ‖α‖ * Ξ ≤ 1 / 32 := by
    have h2 : ‖α‖ * Ξ ≤ Ξ / (32 * (M + 2 + Ξ)) :=
      calc ‖α‖ * Ξ ≤ (1 / (32 * (M + 2 + Ξ))) * Ξ := mul_le_mul_of_nonneg_right hα hΞ.le
        _ = Ξ / (32 * (M + 2 + Ξ)) := by ring
    have h3 : Ξ / (32 * (M + 2 + Ξ)) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hαsmall : |(2 * Real.pi * Complex.I * α).im| < Real.pi := by
    have h1 : (2 * Real.pi * Complex.I * α).im = 2 * Real.pi * α.re := by simp
    have h2 : α.re ≤ ‖α‖ := Complex.re_le_norm α
    rw [h1, abs_of_pos (by positivity)]
    nlinarith [hα64, Real.pi_pos, hαre, h2]
  -- ## the radius
  have hEpos : 0 < Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1 := by
    have h1 : 0 < 2 * Real.pi * ‖α‖ * Ξ := by
      have h2 : 0 < ‖α‖ := norm_pos_iff.mpr hα0
      exact mul_pos (mul_pos (by positivity) h2) hΞ
    linarith [Real.one_lt_exp_iff.mpr h1]
  have hEsmall : Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1 ≤ 1 / 4 := by
    have h0 : 0 ≤ 2 * Real.pi * ‖α‖ * Ξ := by positivity
    have h1 : 2 * Real.pi * ‖α‖ * Ξ ≤ Real.pi / 16 := by
      have h2 : 2 * Real.pi * ‖α‖ * Ξ = 2 * Real.pi * (‖α‖ * Ξ) := by ring
      rw [h2]; nlinarith [hε, Real.pi_pos]
    have h2 := exp_sub_one_le_of_le h0 h1
    have h3 : 4 * (2 * Real.pi * ‖α‖ * Ξ) / Real.pi = 8 * (‖α‖ * Ξ) := by
      field_simp; ring
    rw [h3] at h2
    linarith
  set r : ℝ := ‖σ‖ / (2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1)) with hrdef
  have hr : 0 < r := by rw [hrdef]; exact div_pos (norm_pos_iff.mpr hσ) (by linarith)
  have hσr : ‖σ‖ < r := by
    rw [hrdef, lt_div_iff₀ (by linarith : (0:ℝ) < 2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1))]
    nlinarith [norm_pos_iff.mpr hσ, hEsmall]
  have hσb : ‖σ‖ < 1 / 2 := by
    have h1 : ‖σ‖ ≤ 32 * ‖α‖ :=
      sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
    nlinarith [h1, hα64']
  -- ## the disk lies in the domain and is covered by the gate
  have hcover : ∀ τ ∈ Metric.ball (0 : ℂ) r, τ ≠ 0 → τ ≠ σ →
      ∃ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w = τ := by
    intro τ hτ hτ0 hτσ
    rw [hrdef] at hτ
    exact exists_tauC_gate_of_mem_ball hΞ hInF1 hε hσ hτ hτ0 hτσ
  have hσhalf : ‖σ‖ ≤ rr / 2 := sigma_le_half_rr hΞ hrr hM hInF1 hα hτQ
  have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) rr := by
    intro τ hτ
    rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
    by_cases h0 : τ = 0
    · rw [h0]; simpa using hrr
    by_cases h1 : τ = σ
    · rw [h1]; linarith
    · obtain ⟨w, hwQ, hwτ⟩ := hcover τ (by rwa [Metric.mem_ball, dist_zero_right]) h0 h1
      rw [← hwτ]
      simpa [Metric.mem_ball, dist_zero_right] using hτQ w hwQ
  have hdiff : DifferentiableOn ℂ (defectF u σ α) (Metric.ball (0 : ℂ) r) :=
    defectF_differentiable' hr hα0 hα64 hsub hu hu2 hσb hσr hnorm hcover hNT
  -- ## pointwise bound
  have hf0 : defectF u σ α 0 = 0 := defectF_zero hα0 hαsmall hnorm
  have hbound : ∀ τ ∈ Metric.ball (0 : ℂ) r, τ ≠ σ → ‖defectF u σ α τ‖ ≤ 1 / 32 := by
    intro τ hτ hτσ
    by_cases hτ0 : τ = 0
    · rw [hτ0, hf0]; norm_num
    · obtain ⟨w, hwQ, hwτ⟩ := hcover τ hτ hτ0 hτσ
      rw [← hwτ, defectF_tauC]
      exact hNT w hwQ
  -- ## Schwarz
  have hσball : σ ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hσr
  have hcase : ‖defectF u σ α σ‖ ≤ (1 / 2) * ‖α‖ * Ξ := by
    by_cases hle : ‖defectF u σ α σ‖ ≤ 1 / 32
    · have hmaps : Set.MapsTo (defectF u σ α) (Metric.ball (0 : ℂ) r)
          (Metric.closedBall (defectF u σ α 0) (1 / 32)) := by
        intro τ hτ
        rw [Metric.mem_closedBall, hf0, dist_zero_right]
        by_cases hτσ : τ = σ
        · rw [hτσ]; exact hle
        · exact hbound τ hτ hτσ
      have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hσball
      rw [hf0, dist_zero_right, dist_zero_right] at hsch
      have hval : (1 / 32) / r * ‖σ‖ = 2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1) / 32 := by
        rw [hrdef]; field_simp
      rw [hval] at hsch
      exact le_trans hsch (arith_final hΞ hna hε)
    · have hgt : 1 / 32 < ‖defectF u σ α σ‖ := not_le.mp hle
      have hmaps : Set.MapsTo (defectF u σ α) (Metric.ball (0 : ℂ) r)
          (Metric.closedBall (defectF u σ α 0) ‖defectF u σ α σ‖) := by
        intro τ hτ
        rw [Metric.mem_closedBall, hf0, dist_zero_right]
        by_cases hτσ : τ = σ
        · rw [hτσ]
        · exact le_trans (hbound τ hτ hτσ) hgt.le
      have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hσball
      rw [hf0, dist_zero_right, dist_zero_right] at hsch
      have hval : ‖defectF u σ α σ‖ / r * ‖σ‖
          = ‖defectF u σ α σ‖ * (2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1)) := by
        rw [hrdef]; field_simp
      rw [hval] at hsch
      exfalso
      nlinarith [hsch, hgt, hEsmall]
  -- ## conclude
  have hσu : 1 + σ * u σ ≠ 0 := by
    intro hcon
    have hmem : σ ∈ Metric.ball (0 : ℂ) rr := hsub hσball
    have huσ : ‖u σ‖ ≤ 2 := (hu2 σ hmem).2
    have h1 : σ * u σ = -1 := by linear_combination hcon
    have h2 : ‖σ * u σ‖ = 1 := by rw [h1, norm_neg, norm_one]
    rw [norm_mul] at h2
    nlinarith [huσ, hσb, norm_nonneg σ]
  rw [← defectF_sigma (u := u) (σ := σ) (α := α) hσu]
  exact hcase

end

end Work.Pert.GateDriftRate
