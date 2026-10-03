import Mathlib
import Submission.Work.Pert.PinLogDev.deltaF_axis_le
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.PinLogDev.tauC_axis_upper
import Submission.Work.Pert.PinLogDev.tauC_axis_lower
import Submission.Work.Pert.PinLogDev.small_data_of_nearOn

namespace Work.Pert.PinLogDev

open MandelDim Complex Metric
open Work.Pert.PinLogDev.AxisAux

set_option maxHeartbeats 4000000

/-- `‖2πiα‖ = 2π‖α‖`. -/
theorem norm_two_pi_I_mul (α : ℂ) : ‖2 * Real.pi * I * α‖ = 2 * Real.pi * ‖α‖ := by
  rw [norm_mul, norm_mul, norm_mul]
  simp [Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- **Core deviation estimate.**  Let `u` be a holomorphic nonvanishing cofactor on `ball 0 rr`,
`σ`, `α` the normal-form data of a perturbation with `1 - σ u 0 = exp (2πiα)`,
`‖u 0 - 1‖ ≤ 1/8`, `‖σ‖ ≤ 9/7 ‖2πiα‖` and `‖2πiα‖ ≤ 1/8`.  Then for any `w` whose `τ_f`-value
lies in `ball 0 rr` and has modulus `≤ 1/4`, the near-translation defect of the lift is bounded by
`(288/(7 rr) + 162/7) ‖τ_f w‖` — a constant independent of the data.

The proof is the algebra of Shishikura (A.1.7): with `P = 1 - s_f w`, `Q = 1 - σ u 0` and
`τ = τ_f w` one has the *identity*
`P - Q = σ ((u 0 - u τ) + u 0 (τ u τ)) / (1 + τ u τ)`,
`F w - (w+1) = (2πiα)⁻¹ (log P - log Q)`, `‖log P - log Q‖ ≤ 4‖P - Q‖` (both `P`, `Q` lie in the
disc of radius `3/4` about `1`), `‖1 + τ u τ‖ ≥ 1/2`, `‖u τ - u 0‖ ≤ (4/rr)‖τ‖` (Schwarz–Pick)
and `‖σ‖ ≤ (9/7)‖2πiα‖`. -/
theorem liftF_sub_le_of_tau_le {u : ℂ → ℂ} {σ α w : ℂ} {rr : ℝ} (hrr : 0 < rr)
    (huD : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (huB : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hu0 : ‖u 0 - 1‖ ≤ 1 / 8) (hα0 : α ≠ 0)
    (hσ : ‖σ‖ ≤ 9 / 7 * ‖2 * Real.pi * I * α‖)
    (hα8 : ‖2 * Real.pi * I * α‖ ≤ 1 / 8)
    (hlog : Complex.log (1 - σ * u 0) = 2 * Real.pi * I * α)
    (hτ : Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hτ4 : ‖Work.Pert.tauC σ α w‖ ≤ 1 / 4) :
    ‖Work.Pert.liftF u σ α w - (w + 1)‖
      ≤ (288 / (7 * rr) + 162 / 7) * ‖Work.Pert.tauC σ α w‖ := by
  set t : ℂ := 2 * Real.pi * I * α with htdef
  set τ : ℂ := Work.Pert.tauC σ α w with hτdef
  have ht18 : ‖t‖ ≤ 1 / 8 := hα8
  have hσt : ‖σ‖ ≤ 9 / 7 * ‖t‖ := hσ
  have hτ14 : ‖τ‖ ≤ 1 / 4 := hτ4
  have hτmem : τ ∈ Metric.ball (0 : ℂ) rr := hτ
  have hZnorm : ‖t‖ = 2 * Real.pi * ‖α‖ := norm_two_pi_I_mul α
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have htpos : 0 < ‖t‖ := by rw [hZnorm]; positivity
  have htne : ‖t‖ ≠ 0 := ne_of_gt htpos
  -- ## bounds on `u 0` and `σ`
  have hu0up : ‖u 0‖ ≤ 9 / 8 := by
    have h1 : (u 0 - 1) + 1 = u 0 := by ring
    rw [← h1]
    have h2 := norm_add_le (u 0 - 1) (1 : ℂ)
    simp only [norm_one] at h2
    linarith
  have hσ56 : ‖σ‖ ≤ 9 / 56 := by
    rw [hZnorm] at hσt
    have h' : 2 * Real.pi * ‖α‖ ≤ 1 / 8 := by rw [← hZnorm]; exact ht18
    nlinarith [hσt, h']
  -- ## the denominator `1 + τ u τ`
  have huτ2 : ‖u τ‖ ≤ 2 := (huB τ hτmem).2
  have hτmul : ‖τ * u τ‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖τ‖ * ‖u τ‖ ≤ (1 / 4) * ‖u τ‖ := mul_le_mul_of_nonneg_right hτ14 (norm_nonneg _)
      _ ≤ (1 / 4) * 2 := mul_le_mul_of_nonneg_left huτ2 (by norm_num)
      _ = 1 / 2 := by norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖1 + τ * u τ‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
    have h2 : ‖-(τ * u τ)‖ = ‖τ * u τ‖ := norm_neg _
    rw [norm_one, h2] at h
    have h3 : (1 : ℝ) - ‖τ * u τ‖ ≤ |1 - ‖τ * u τ‖| := le_abs_self _
    have h4 : (1 : ℂ) - -(τ * u τ) = 1 + τ * u τ := by ring
    rw [h4] at h
    linarith
  have hdenpos : 0 < ‖1 + τ * u τ‖ := by linarith
  have hdenne : 1 + τ * u τ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    norm_num at hden
  -- ## the algebraic identity for `P - Q`
  have hsfun : Work.Pert.sfun u σ α w = σ * u τ / (1 + τ * u τ) := by
    rw [Work.Pert.sfun, ← hτdef]
  have hPsubQ : (1 - Work.Pert.sfun u σ α w) - (1 - σ * u 0)
      = σ * ((u 0 - u τ) + u 0 * (τ * u τ)) / (1 + τ * u τ) := by
    have hden' : (1 + u τ * τ) ≠ 0 := by simpa only [mul_comm (u τ) τ] using hdenne
    rw [hsfun]
    field_simp
    ring
  -- ## `P` and `Q` lie in the disc of radius `3/4` about `1`
  have hP1 : ‖(1 - Work.Pert.sfun u σ α w) - 1‖ ≤ 3 / 4 := by
    have h1 : (1 - Work.Pert.sfun u σ α w) - 1 = -(σ * u τ) / (1 + τ * u τ) := by
      rw [hsfun]; ring
    rw [h1, norm_div, norm_neg, norm_mul]
    rw [div_le_iff₀ hdenpos]
    have h2 : ‖σ‖ * ‖u τ‖ ≤ 9 / 28 := by
      have h3 : ‖σ‖ * ‖u τ‖ ≤ (9 / 7 * ‖t‖) * 2 :=
        mul_le_mul hσt huτ2 (norm_nonneg _) (by positivity)
      nlinarith [h3, ht18]
    nlinarith [h2, hden]
  have hQ1 : ‖(1 - σ * u 0) - 1‖ ≤ 3 / 4 := by
    have h1 : (1 - σ * u 0) - 1 = -(σ * u 0) := by ring
    rw [h1, norm_neg, norm_mul]
    have h2 : ‖σ‖ * ‖u 0‖ ≤ 9 / 56 * (9 / 8) :=
      mul_le_mul hσ56 hu0up (norm_nonneg _) (by norm_num)
    nlinarith [h2]
  -- ## the bound on `‖P - Q‖`
  have hd0τ : ‖u τ - u 0‖ ≤ (4 / rr) * ‖τ‖ :=
    norm_sub_le_of_mem_ball_deriv hrr huD (fun z hz => (huB z hz).2) hu0 hτmem
  have hmain : ‖(1 - Work.Pert.sfun u σ α w) - (1 - σ * u 0)‖
      ≤ (18 / 7) * ‖t‖ * (4 / rr + 9 / 4) * ‖τ‖ := by
    rw [hPsubQ, norm_div, norm_mul]
    have hnum : ‖(u 0 - u τ) + u 0 * (τ * u τ)‖ ≤ (4 / rr + 9 / 4) * ‖τ‖ := by
      have h1 : ‖u 0 * (τ * u τ)‖ ≤ 9 / 4 * ‖τ‖ := by
        rw [norm_mul, norm_mul]
        have h2 : ‖u 0‖ * ‖u τ‖ ≤ 9 / 8 * 2 :=
          mul_le_mul hu0up huτ2 (norm_nonneg _) (by norm_num)
        calc ‖u 0‖ * (‖τ‖ * ‖u τ‖) = (‖u 0‖ * ‖u τ‖) * ‖τ‖ := by ring
          _ ≤ 9 / 8 * 2 * ‖τ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          _ = 9 / 4 * ‖τ‖ := by ring
      have h3 : ‖u 0 - u τ‖ ≤ (4 / rr) * ‖τ‖ := by
        rw [norm_sub_rev]
        exact hd0τ
      calc ‖(u 0 - u τ) + u 0 * (τ * u τ)‖
          ≤ ‖u 0 - u τ‖ + ‖u 0 * (τ * u τ)‖ := norm_add_le _ _
        _ ≤ (4 / rr) * ‖τ‖ + 9 / 4 * ‖τ‖ := add_le_add h3 h1
        _ = (4 / rr + 9 / 4) * ‖τ‖ := by ring
    have h4 : ‖σ‖ * ‖(u 0 - u τ) + u 0 * (τ * u τ)‖
        ≤ ‖σ‖ * ((4 / rr + 9 / 4) * ‖τ‖) :=
      mul_le_mul_of_nonneg_left hnum (norm_nonneg σ)
    calc ‖σ‖ * ‖(u 0 - u τ) + u 0 * (τ * u τ)‖ / ‖1 + τ * u τ‖
        ≤ ‖σ‖ * ((4 / rr + 9 / 4) * ‖τ‖) / (1 / 2) :=
          div_le_div₀ (by positivity) h4 (by norm_num) hden
      _ ≤ (18 / 7) * ‖t‖ * (4 / rr + 9 / 4) * ‖τ‖ := by
          have h5 : ‖σ‖ * ((4 / rr + 9 / 4) * ‖τ‖) / (1 / 2)
              = 2 * (‖σ‖ * ((4 / rr + 9 / 4) * ‖τ‖)) := by ring
          rw [h5]
          have h6 : ‖σ‖ * ((4 / rr + 9 / 4) * ‖τ‖)
              ≤ (9 / 7 * ‖t‖) * ((4 / rr + 9 / 4) * ‖τ‖) :=
            mul_le_mul_of_nonneg_right hσt (by positivity)
          nlinarith [h6]
  -- ## the logarithm comparison
  have hlog_le : ‖Complex.log (1 - Work.Pert.sfun u σ α w) - Complex.log (1 - σ * u 0)‖
      ≤ 4 * ((18 / 7) * ‖t‖ * (4 / rr + 9 / 4) * ‖τ‖) := by
    have h := log_sub_log_norm_le hP1 hQ1
    linarith
  -- ## the defect, in terms of the two logarithms
  rw [liftF_sub_eq hα0 hlog, norm_mul, norm_div, norm_one]
  have hstep : (1 / ‖t‖) * ‖Complex.log (1 - Work.Pert.sfun u σ α w)
        - Complex.log (1 - σ * u 0)‖
      ≤ (1 / ‖t‖) * (4 * ((18 / 7) * ‖t‖ * (4 / rr + 9 / 4) * ‖τ‖)) :=
    mul_le_mul_of_nonneg_left hlog_le (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

/-- The point `s i` lies in the lower gate `Qm Ξ α` as soon as `Ξ < s` and `Ξ < Re (1/α)`. -/
theorem imag_mem_Qm {Ξ s : ℝ} {α : ℂ} (hs : Ξ < s) (hΞ : 0 < Ξ) (hrec : Ξ < (1 / α).re) :
    (s : ℂ) * Complex.I ∈ Work.Pert.Qm Ξ α := by
  rw [Work.Pert.Qm, MandelDim.Qreg]
  constructor
  · intro b hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hre : ((s : ℂ) * Complex.I - ((Ξ : ℂ) - 1 / α)).re = (1 / α).re - Ξ := by
      simp [Complex.sub_re]
    have hpos : 0 < ((s : ℂ) * Complex.I - ((Ξ : ℂ) - 1 / α)).re := by rw [hre]; linarith
    linarith [abs_nonneg ((s : ℂ) * Complex.I - ((Ξ : ℂ) - 1 / α)).im]
  · intro b hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hre : ((s : ℂ) * Complex.I - (-(Ξ : ℂ))).re = Ξ := by simp
    have him : ((s : ℂ) * Complex.I - (-(Ξ : ℂ))).im = s := by simp
    rw [hre, him, abs_of_pos (by linarith : (0 : ℝ) < s)]
    linarith

/-- The point `-s i` lies in the lower gate `Qm Ξ α` as soon as `Ξ < s` and `Ξ < Re (1/α)`. -/
theorem neg_imag_mem_Qm {Ξ s : ℝ} {α : ℂ} (hs : Ξ < s) (hΞ : 0 < Ξ) (hrec : Ξ < (1 / α).re) :
    -((s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
  rw [Work.Pert.Qm, MandelDim.Qreg]
  constructor
  · intro b hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hre : (-((s : ℂ) * Complex.I) - ((Ξ : ℂ) - 1 / α)).re = (1 / α).re - Ξ := by
      simp [Complex.sub_re]
    have hpos : 0 < (-((s : ℂ) * Complex.I) - ((Ξ : ℂ) - 1 / α)).re := by rw [hre]; linarith
    linarith [abs_nonneg (-((s : ℂ) * Complex.I) - ((Ξ : ℂ) - 1 / α)).im]
  · intro b hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hre : (-((s : ℂ) * Complex.I) - (-(Ξ : ℂ))).re = Ξ := by simp
    have him : (-((s : ℂ) * Complex.I) - (-(Ξ : ℂ))).im = -s := by simp
    rw [hre, him, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < s)]
    linarith

/-- If `α` is in `𝓕₁` and `‖α‖ < 1/(√2 Ξ)` then `Ξ < Re (1/α)` (the `τ_f`-gate of height `Ξ`
lies above the vertex `Ξ - 1/α`). -/
theorem lt_re_inv_of_norm_lt {Ξ : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (h : ‖α‖ < 1 / (Real.sqrt 2 * Ξ)) : Ξ < (1 / α).re := by
  have hre : 0 < α.re := by
    have h1 := (abs_lt.mp hInF1).1
    have h2 := (abs_lt.mp hInF1).2
    linarith
  have hane : α ≠ 0 := by
    intro h0; rw [h0] at hre; simp at hre
  have han : 0 < ‖α‖ := norm_pos_iff.mpr hane
  have hle : ‖α‖ ≤ Real.sqrt 2 * α.re := by
    have hsq : α.im ^ 2 < α.re ^ 2 := by
      have h1 := (abs_lt.mp hInF1).2
      have h2 := (abs_lt.mp hInF1).1
      nlinarith [h1, h2, hre]
    have h2 : ‖α‖ ^ 2 ≤ 2 * α.re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hsq]
    have h3 : ‖α‖ ^ 2 ≤ (Real.sqrt 2 * α.re) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    calc ‖α‖ = Real.sqrt (‖α‖ ^ 2) := (Real.sqrt_sq (norm_nonneg α)).symm
      _ ≤ Real.sqrt ((Real.sqrt 2 * α.re) ^ 2) := Real.sqrt_le_sqrt h3
      _ = Real.sqrt 2 * α.re := Real.sqrt_sq (by positivity)
  have hA : Ξ * ‖α‖ < 1 / Real.sqrt 2 := by
    have h1 : Ξ * ‖α‖ < Ξ * (1 / (Real.sqrt 2 * Ξ)) := mul_lt_mul_of_pos_left h hΞ
    have h2 : Ξ * (1 / (Real.sqrt 2 * Ξ)) = 1 / Real.sqrt 2 := by field_simp
    linarith [h2.le, h2.ge, h1]
  have hB : (1 / Real.sqrt 2) * ‖α‖ ≤ α.re := by
    have h1 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2)
    rwa [show (1 / Real.sqrt 2) * (Real.sqrt 2 * α.re) = α.re from by field_simp] at h1
  rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < ‖α‖ ^ 2)]
  calc Ξ * ‖α‖ ^ 2 = (Ξ * ‖α‖) * ‖α‖ := by ring
    _ < (1 / Real.sqrt 2) * ‖α‖ := mul_lt_mul_of_pos_right hA han
    _ ≤ α.re := hB

theorem axis_decay_budget {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) (Ξ Yt : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hYt : Ξ < Yt) {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ (Kd Ms : ℝ), 0 ≤ Kd ∧ 0 < Ms ∧
      ∀ M : ℝ, Ms ≤ M → ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 128 ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) (1 / (1000 * (M + 1))) →
        f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) → α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        (∀ s : ℝ, Yt ≤ s →
          ‖Work.Pert.liftF u σ α ((s : ℂ) * Complex.I) - ((s : ℂ) * Complex.I + 1)‖ ≤ Kd / s) ∧
        (∀ s : ℝ, Yt ≤ s →
          ‖Work.Pert.liftF u σ α (-((s : ℂ) * Complex.I)) - (-((s : ℂ) * Complex.I) + 1)‖
            ≤ Kd / s + ε) := by
  obtain ⟨Msa, Ca, hMsapos, hCapos, hsmallA⟩ := small_data_of_nearOn hd hrr
  have hΞpos : 0 < Ξ := by linarith [Real.pi_pos]
  have hYtpos : 0 < Yt := by linarith
  -- ## the two constants of the budget
  set C₂ : ℝ := 288 / (7 * rr) + 162 / 7 with hC₂def
  have hC₂nn : 0 ≤ C₂ := by rw [hC₂def]; positivity
  have hC₂pos : 0 < C₂ := by rw [hC₂def]; positivity
  have hC₂eq : 288 / (7 * rr) + 162 / 7 = C₂ := hC₂def.symm
  set Kd : ℝ := 200 / rr + 200 with hKddef
  have hKdnn : 0 ≤ Kd := by rw [hKddef]; positivity
  have hKd4 : 4 * C₂ ≤ Kd := by
    rw [hKddef, hC₂def]
    have h7 : (7 : ℝ) * rr ≠ 0 := by positivity
    have hrr0 : rr ≠ 0 := ne_of_gt hrr
    field_simp
    nlinarith [hrr]
  -- ## the threshold on `M`
  set D1 : ℝ := 1 / (1024000 * Ca) with hD1def
  set D3 : ℝ := 1 / (1000 * (Real.sqrt 2 * Ξ * Ca)) with hD3def
  set D4 : ℝ := 1 / (2176000 * C₂ * Ca) with hD4def
  set δmax : ℝ := min D1 (min D3 D4) with hδmaxdef
  have hδmaxpos : 0 < δmax := by
    rw [hδmaxdef, hD1def, hD3def, hD4def]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set Ms : ℝ := max Msa (max 0 (1 / (1000 * δmax) + 1)) with hMsdef
  have hMspos : 0 < Ms := by
    rw [hMsdef]
    exact lt_of_lt_of_le hMsapos (le_max_left _ _)
  refine ⟨Kd, Ms, hKdnn, hMspos, ?_⟩
  intro M hM
  have hMMsa : Msa ≤ M := le_trans (le_max_left _ _) hM
  have hMδ : 1 / (1000 * δmax) + 1 ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  set δ₀ : ℝ := 1 / (1000 * (M + 1)) with hδ₀def
  have hM0 : 0 < M + 1 := by linarith [hMδ]
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact div_pos one_pos (by linarith [hM0])
  have hδ₀lt : δ₀ < δmax := by
    rw [hδ₀def, div_lt_iff₀ (by positivity : (0 : ℝ) < 1000 * (M + 1))]
    have h1 : 1 / (1000 * δmax) < M + 1 := by linarith [hMδ]
    have h3 := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < 1000 * δmax)
    have h4 : 1000 * δmax * (1 / (1000 * δmax)) = 1 := by field_simp
    have h5 : 1000 * δmax * (M + 1) = δmax * (1000 * (M + 1)) := by ring
    linarith [h3, h4.le, h4.ge, h5.le, h5.ge]
  have hδ₀D1 : δ₀ < D1 := lt_of_lt_of_le hδ₀lt (by
    rw [hδmaxdef]; exact min_le_left _ _)
  have hδ₀D3 : δ₀ < D3 := lt_of_lt_of_le hδ₀lt (by
    rw [hδmaxdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₀D4 : δ₀ < D4 := lt_of_lt_of_le hδ₀lt (by
    rw [hδmaxdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _))
  -- the three consequences on `M + 1`
  have hM1 : 1024 * Ca ≤ M + 1 := by
    have h := hδ₀D1
    rw [hδ₀def, hD1def, div_lt_div_iff₀ (by positivity : (0 : ℝ) < 1000 * (M + 1))
      (by positivity : (0 : ℝ) < 1024000 * Ca)] at h
    linarith
  have hM3 : Real.sqrt 2 * Ξ * Ca < M + 1 := by
    have h := hδ₀D3
    rw [hδ₀def, hD3def, div_lt_div_iff₀ (by positivity : (0 : ℝ) < 1000 * (M + 1))
      (by positivity : (0 : ℝ) < 1000 * (Real.sqrt 2 * Ξ * Ca))] at h
    linarith
  have hM4 : 2176 * C₂ * Ca ≤ M + 1 := by
    have h := hδ₀D4
    rw [hδ₀def, hD4def, div_lt_div_iff₀ (by positivity : (0 : ℝ) < 1000 * (M + 1))
      (by positivity : (0 : ℝ) < 2176000 * C₂ * Ca)] at h
    linarith
  refine ⟨C₂ * 17 * Ca / (M + 1), ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (mul_nonneg hC₂pos.le (by norm_num)) hCapos.le) hM0.le
  · -- ## `ε ≤ 1/128`
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < M + 1)]
    have h1 : (1 / 128) * (2176 * C₂ * Ca) ≤ (1 / 128) * (M + 1) :=
      mul_le_mul_of_nonneg_left hM4 (by norm_num)
    have h2 : (1 / 128) * (2176 * C₂ * Ca) = C₂ * 17 * Ca := by ring
    linarith [h1, h2.le, h2.ge]
  · -- ## the two axis bounds
    intro f Df u σ α hnear hf0 hInF1f hαeq huD huB hform hnorm hτQ
    have hInF1 : MandelDim.InF1 α := by rw [hαeq]; exact hInF1f
    obtain ⟨hu0, hσ9, hαC⟩ := hsmallA M hMMsa f Df u σ α hnear hf0 hαeq huD huB hform hnorm
    have hαre : 0 < α.re := by
      have h1 := (abs_lt.mp hInF1).1
      have h2 := (abs_lt.mp hInF1).2
      linarith
    have hα0 : α ≠ 0 := by
      intro h0; rw [h0] at hαre; simp at hαre
    have hαle : ‖α‖ ≤ 1 / 1024 := by
      have h1 : Ca / (M + 1) ≤ Ca / (1024 * Ca) :=
        div_le_div_of_nonneg_left hCapos.le (by positivity) hM1
      have h2 : Ca / (1024 * Ca) = 1 / 1024 := by field_simp
      linarith [hαC, h1, h2.le, h2.ge]
    have hα8 : ‖2 * Real.pi * I * α‖ ≤ 1 / 8 := by
      rw [norm_two_pi_I_mul]
      nlinarith [hαle, Real.pi_lt_four, Real.pi_pos, norm_nonneg α]
    have hαstrict : ‖α‖ < 1 / (Real.sqrt 2 * Ξ) := by
      have h1 : Ca / (M + 1) < Ca / (Real.sqrt 2 * Ξ * Ca) := by
        rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)
          (by positivity : (0 : ℝ) < Real.sqrt 2 * Ξ * Ca)]
        nlinarith [hM3, hCapos]
      have h2 : Ca / (Real.sqrt 2 * Ξ * Ca) = 1 / (Real.sqrt 2 * Ξ) := by field_simp
      linarith [hαC, h1, h2.le, h2.ge]
    have hrec : Ξ < (1 / α).re := lt_re_inv_of_norm_lt hΞpos hInF1 hαstrict
    have hlog : Complex.log (1 - σ * u 0) = 2 * Real.pi * I * α := by
      have him : (2 * Real.pi * Complex.I * α).im = 2 * Real.pi * α.re := by
        simp [Complex.mul_im]
      have h1 : -Real.pi < (2 * Real.pi * Complex.I * α).im := by
        rw [him]; nlinarith [Real.pi_pos, hαre]
      have h2 : (2 * Real.pi * Complex.I * α).im ≤ Real.pi := by
        rw [him]
        nlinarith [hαre, Real.pi_pos, Complex.re_le_norm α, hαle, Real.pi_lt_four]
      rw [hnorm, Complex.log_exp h1 h2]
    constructor
    · -- ## upper axis
      intro s hs
      have hs0 : 0 < s := by linarith [hYtpos, hs]
      have hs8 : (8 : ℝ) ≤ s := by nlinarith [hΞ, hYt, hs, Real.pi_gt_three]
      have hmem : Work.Pert.tauC σ α ((s : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) rr :=
        hτQ _ (imag_mem_Qm (by linarith) hΞpos hrec)
      have hτle : ‖Work.Pert.tauC σ α ((s : ℂ) * Complex.I)‖ ≤ 2 / s :=
        tauC_axis_upper hInF1 hs0 hσ9
      have hτ4 : ‖Work.Pert.tauC σ α ((s : ℂ) * Complex.I)‖ ≤ 1 / 4 := by
        have h2 : 2 / s ≤ 1 / 4 := by
          rw [div_le_div_iff₀ hs0 (by norm_num : (0 : ℝ) < 4)]
          linarith
        linarith
      have hcore := liftF_sub_le_of_tau_le hrr huD huB hu0 hα0 hσ9 hα8 hlog hmem hτ4
      rw [hC₂eq] at hcore
      have hbound : C₂ * ‖Work.Pert.tauC σ α ((s : ℂ) * Complex.I)‖ ≤ Kd / s := by
        have h1 : C₂ * (2 / s) ≤ Kd / s := by
          have hle : C₂ * 2 ≤ Kd := by linarith [hKd4]
          rw [show C₂ * (2 / s) = C₂ * 2 / s from by ring]
          exact div_le_div_of_nonneg_right hle hs0.le
        have h2 := mul_le_mul_of_nonneg_left hτle hC₂nn
        linarith
      linarith [hcore, hbound]
    · -- ## lower axis
      intro s hs
      have hs0 : 0 < s := by linarith [hYtpos, hs]
      have hmem : Work.Pert.tauC σ α (-((s : ℂ) * Complex.I)) ∈ Metric.ball (0 : ℂ) rr :=
        hτQ _ (neg_imag_mem_Qm (by linarith) hΞpos hrec)
      have hτle : ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖ ≤ 4 / s + 17 * ‖α‖ :=
        tauC_axis_lower hInF1 hs0 hσ9
      have hτ4 : ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖ ≤ 1 / 4 := by
        have h4s : 4 / s ≤ 4 / Yt := by
          rw [div_le_div_iff₀ hs0 hYtpos]
          nlinarith [hs]
        have h4Y : 4 / Yt ≤ 1 / 16 := by
          rw [div_le_div_iff₀ hYtpos (by norm_num : (0 : ℝ) < 16)]
          nlinarith [hΞ, hYt, Real.pi_gt_three]
        have h17 : 17 * ‖α‖ ≤ 17 / 1024 := by
          have := mul_le_mul_of_nonneg_left hαle (by norm_num : (0 : ℝ) ≤ 17)
          linarith
        linarith
      have hcore := liftF_sub_le_of_tau_le hrr huD huB hu0 hα0 hσ9 hα8 hlog hmem hτ4
      rw [hC₂eq] at hcore
      have hbound : C₂ * ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖
          ≤ Kd / s + C₂ * 17 * Ca / (M + 1) := by
        have h1 : C₂ * ‖Work.Pert.tauC σ α (-((s : ℂ) * Complex.I))‖
            ≤ C₂ * (4 / s + 17 * ‖α‖) := mul_le_mul_of_nonneg_left hτle hC₂nn
        have h2 : C₂ * (4 / s) ≤ Kd / s := by
          have hle : C₂ * 4 ≤ Kd := by linarith [hKd4]
          rw [show C₂ * (4 / s) = C₂ * 4 / s from by ring]
          exact div_le_div_of_nonneg_right hle hs0.le
        have h3 : C₂ * (17 * ‖α‖) ≤ C₂ * 17 * Ca / (M + 1) := by
          have h5 : ‖α‖ ≤ Ca / (M + 1) := hαC
          have h6 : C₂ * (17 * ‖α‖) ≤ C₂ * (17 * (Ca / (M + 1))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 17)) hC₂nn
          have h7 : C₂ * (17 * (Ca / (M + 1))) = C₂ * 17 * Ca / (M + 1) := by ring
          linarith [h6, h7.le, h7.ge]
        have h8 : C₂ * (4 / s + 17 * ‖α‖) = C₂ * (4 / s) + C₂ * (17 * ‖α‖) := by ring
        linarith [h1, h2, h3, h8.le, h8.ge]
      linarith [hcore, hbound]

end Work.Pert.PinLogDev
