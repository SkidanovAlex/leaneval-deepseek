import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_scale
import Submission.Work.Pert.tauC_gate_bound
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.gate_L1_arith
import Submission.Work.Pert.deriv_liftF_defect_le
import Submission.Work.Pert.lintegral_exp_defect_le

namespace Work.Pert

open MandelDim Complex

set_option maxHeartbeats 1000000

noncomputable section

/-!
# `Work.Pert.gate_scale_L1`

The two gates `Qm ξ₁ α`, `Qp ξ₁ α` of §4.2 are *near translations* for the lift
`F = liftF u σ α` in the strong (`L¹`) sense of `MandelDim.NearTranslationL1`: besides the
pointwise `1/32` bounds proved in `Work.Pert.gate_scale`, the derivative defect integrates to
at most `1/64` on every vertical line contained in the gate.

The two ingredients are

* `Work.Pert.deriv_liftF_defect_le`: the exact derivative formula of Shishikura (A.1.7)(ii)
  gives `‖F'(z) - 1‖ ≤ (32/ρmin + 16)‖σ‖²‖E(z)‖/‖1 - E(z)‖²`, `E(z) = exp (-(2πiα z))`;
* `Work.Pert.lintegral_exp_defect_le`: the lattice gap `ξ/2` of the gate bounds
  `∫⁻ y, ‖E(z)‖/‖1-E(z)‖² ≤ 1/(α.re ‖α‖ ξ)`.

Since `‖σ‖ ≤ 8π‖α‖` (from the normalisation `1 - σu(0) = exp(2πiα)` and `1/2 ≤ ‖u 0‖`) and
`‖α‖ ≤ √2 α.re` (`InF1 α`), the product is at most `64π²·48√2/ξ₁` for `ρmin ≤ 1`, which is
`< 1/64` as soon as `ξ₁ ≥ 10^{12}/min ρmin 1`. -/

/-- `‖2πiα‖ = 2π‖α‖`. -/
private lemma norm_two_pi_I_mul (α : ℂ) : ‖2 * Real.pi * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- `‖σ‖ ≤ 8π‖α‖` from the normalisation `1 - σ u 0 = exp (2πiα)` together with `1/2 ≤ ‖u 0‖`. -/
theorem sigma_norm_le_eight_pi {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hαs : ‖α‖ ≤ 1 / 10 ^ 6) : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hu0 : 1 / 2 ≤ ‖u 0‖ := (hub 0 h0mem).1
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    linear_combination -hnorm
  have h1 : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    rw [← norm_mul, hσu]
  have h2 : ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖
      = ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ := by
    rw [← norm_neg]; congr 1; ring
  have h3 : ‖2 * Real.pi * Complex.I * α‖ ≤ 1 := by
    rw [norm_two_pi_I_mul]
    have hp : Real.pi * ‖α‖ ≤ 4 * (1 / 10 ^ 6 : ℝ) :=
      mul_le_mul (le_of_lt Real.pi_lt_four) hαs (norm_nonneg α) (by norm_num)
    nlinarith
  have h4 : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ ≤ 4 * Real.pi * ‖α‖ := by
    have h := Complex.norm_exp_sub_one_le h3
    rw [norm_two_pi_I_mul] at h
    linarith
  have h5 : ‖σ‖ * (1 / 2) ≤ 4 * Real.pi * ‖α‖ := by
    calc ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u 0‖ := mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
      _ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := h1
      _ = ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ := h2
      _ ≤ 4 * Real.pi * ‖α‖ := h4
  linarith

/-- `exp (-(2πiα z)) ≠ 1` when `z` keeps distance `≥ ξ/2` from the lattice `ℤ/α`. -/
theorem exp_neg_ne_one_of_lattice {α z : ℂ} {ξ : ℝ} (hξ : 0 < ξ) (hαne : α ≠ 0)
    (hlat : ∀ k : ℤ, ξ / 2 ≤ ‖z - (k : ℂ) / α‖) :
    Complex.exp (-(2 * Real.pi * Complex.I * α * z)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hfac : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have h4 : (2 * Real.pi * Complex.I) * (-(α * z)) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
    rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ)]
    calc (2 * Real.pi * Complex.I) * (-(α * z)) = -(2 * Real.pi * Complex.I * α * z) := by ring
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
  have h5 : -(α * z) = (n : ℂ) := mul_left_cancel₀ hfac h4
  have h6 : α * z = -(n : ℂ) := by linear_combination -h5
  have h7 : z = -((n : ℂ) / α) := by
    have hgoal : z = (-(n : ℂ)) / α := by
      rw [eq_div_iff hαne]
      linear_combination h6
    rw [hgoal]; ring
  have h8 := hlat (-n)
  have h9 : z - ((-n : ℤ) : ℂ) / α = 0 := by
    rw [show ((-n : ℤ) : ℂ) = -(n : ℂ) by simp, neg_div, h7]; ring
  rw [h9, norm_zero] at h8
  linarith

/-- Monotonicity of `Qreg` in its two vertices: shrinking a gate keeps the near-translation. -/
theorem qreg_mono {b₁ b₂ c₁ c₂ : ℂ} (h₁ : c₁.re ≤ b₁.re) (h₁i : c₁.im = b₁.im)
    (h₂ : b₂.re ≤ c₂.re) (h₂i : b₂.im = c₂.im) :
    MandelDim.Qreg (some b₁) (some b₂) ⊆ MandelDim.Qreg (some c₁) (some c₂) := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  constructor
  · intro b hb
    have hbc : b = c₁ := by simpa [eq_comm] using hb
    rw [← hbc] at h₁ h₁i
    have h := hz1 b₁ (by simp)
    have hre : (z - b).re = (z - b₁).re + (b₁.re - b.re) := by
      simp only [Complex.sub_re]; ring
    have him : (z - b).im = (z - b₁).im := by simp only [Complex.sub_im, h₁i]
    rw [hre, him]
    linarith
  · intro b hb
    have hbc : b = c₂ := by simpa [eq_comm] using hb
    rw [← hbc] at h₂ h₂i
    have h := hz2 b₂ (by simp)
    have hre : (z - b).re = (z - b₂).re + (b₂.re - b.re) := by
      simp only [Complex.sub_re]; ring
    have him : (z - b).im = (z - b₂).im := by simp only [Complex.sub_im, h₂i]
    rw [hre, him]
    linarith

/-- `Qm` is decreasing in `ξ`. -/
theorem Qm_subset_of_le {α : ℂ} {ξ ξ' : ℝ} (h : ξ ≤ ξ') : Qm ξ' α ⊆ Qm ξ α := by
  have h₁ : (((ξ : ℂ) - 1 / α)).re ≤ (((ξ' : ℂ) - 1 / α)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have h₁i : (((ξ : ℂ) - 1 / α)).im = (((ξ' : ℂ) - 1 / α)).im := by
    simp only [Complex.sub_im, Complex.ofReal_im]
  have h₂ : (-(ξ' : ℂ)).re ≤ (-(ξ : ℂ)).re := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  have h₂i : (-(ξ : ℂ)).im = (-(ξ' : ℂ)).im := by
    simp only [Complex.neg_im, Complex.ofReal_im]
  intro z hz
  exact qreg_mono h₁ h₁i h₂ h₂i hz

/-- `Qp` is decreasing in `ξ`. -/
theorem Qp_subset_of_le {α : ℂ} {ξ ξ' : ℝ} (h : ξ ≤ ξ') : Qp ξ' α ⊆ Qp ξ α := by
  have h₁ : ((ξ : ℂ)).re ≤ ((ξ' : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have h₁i : ((ξ : ℂ)).im = ((ξ' : ℂ)).im := by simp only [Complex.ofReal_im]
  have h₂ : (-(ξ' : ℂ) + 1 / α).re ≤ (-(ξ : ℂ) + 1 / α).re := by
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    linarith
  have h₂i : (-(ξ : ℂ) + 1 / α).im = (-(ξ' : ℂ) + 1 / α).im := by
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im]
  intro z hz
  exact qreg_mono h₁ h₁i h₂ h₂i hz

/-- `NearTranslationOn` restricts to subsets. -/
theorem NearTranslationOn_mono {F : ℂ → ℂ} {Q Q' : Set ℂ}
    (h : MandelDim.NearTranslationOn F Q) (hsub : Q' ⊆ Q) :
    MandelDim.NearTranslationOn F Q' :=
  ⟨h.1.mono hsub, fun z hz => h.2 z (hsub hz)⟩

/-- The `τ_f`-bound on a line of lattice gap `10^12/(min ρmin 1)`: `scale_tau` at the scale
`ρmin' = min ρmin 1/10^6`. -/
theorem tauC_le_of_lattice {σ α z : ℂ} {ρmin : ℝ} (hρmin : 0 < ρmin)
    (hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖) (hαs : ‖α‖ ≤ min ρmin 1 / 10 ^ 12)
    (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hlat : ∀ k : ℤ, (10 ^ 12 / min ρmin 1) / 2 ≤ ‖z - (k : ℂ) / α‖) :
    1 - Complex.exp (-(2 * Real.pi * Complex.I * α * z)) ≠ 0 ∧
      ‖tauC σ α z‖ ≤ 16 * Real.pi * min ρmin 1 / 10 ^ 12 := by
  have hm : 0 < min ρmin 1 := lt_min hρmin zero_lt_one
  have h1 := scale_tau (σ := σ) (α := α) (ρmin := min ρmin 1 / 10 ^ 6) (w := z)
    (by positivity) hσ8 ?_ hαne hinf ?_
  · refine ⟨h1.1, ?_⟩
    calc ‖tauC σ α z‖ ≤ 16 * Real.pi * (min ρmin 1 / 10 ^ 6) / 10 ^ 6 := h1.2
      _ = 16 * Real.pi * min ρmin 1 / 10 ^ 12 := by ring
  · have heq : (min ρmin 1 / 10 ^ 6) / 10 ^ 6 = min ρmin 1 / 10 ^ 12 := by ring
    rw [heq]; exact hαs
  · intro k
    have heq : (10 ^ 6 / (min ρmin 1 / 10 ^ 6)) / 2 = (10 ^ 12 / min ρmin 1) / 2 := by
      field_simp
    rw [heq]; exact hlat k

/-- **The `L¹` gate estimate on one vertical line.**  If every point `x + iy` of a vertical line
lies in a gate of parameter `ξ ≥ 10^{12}/min ρmin 1`, then the derivative defect of the lift
`F = liftF u σ α` integrates to at most `1/64` along that line. -/
theorem lintegral_line_gate {ρmin : ℝ} {u : ℂ → ℂ} {σ α : ℂ} {ρ x ξ : ℝ}
    (hρmin : 0 < ρmin) (hρ : ρmin ≤ ρ)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ))
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hσs : ‖σ‖ ≤ min ρmin 1 / 10 ^ 12) (hαs : ‖α‖ ≤ min ρmin 1 / 10 ^ 12)
    (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hξ : 10 ^ 12 / min ρmin 1 ≤ ξ)
    (hlat : ∀ y : ℝ, ∀ k : ℤ, ξ / 2 ≤ ‖((x : ℂ) + y * Complex.I) - (k : ℂ) / α‖) :
    ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv (liftF u σ α) ((x : ℂ) + y * Complex.I) - 1‖
      ≤ ENNReal.ofReal (1 / 64) := by
  have hm : 0 < min ρmin 1 := lt_min hρmin zero_lt_one
  have hm1 : min ρmin 1 ≤ 1 := min_le_right _ _
  have hρ0 : 0 < ρ := lt_of_lt_of_le hρmin hρ
  have hαs6 : ‖α‖ ≤ 1 / 10 ^ 6 := by
    calc ‖α‖ ≤ min ρmin 1 / 10 ^ 12 := hαs
      _ ≤ 1 / 10 ^ 12 := div_le_div_of_nonneg_right hm1 (by norm_num)
      _ ≤ 1 / 10 ^ 6 := by norm_num
  have hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := sigma_norm_le_eight_pi hρ0 hub hnorm hαs6
  have hαre : 0 < α.re := by
    have h := hinf; simp only [MandelDim.InF1] at h
    have := abs_nonneg α.im; linarith
  have hξpos : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
  -- ## pointwise bound
  have hpt : ∀ y : ℝ, ‖deriv (liftF u σ α) ((x : ℂ) + y * Complex.I) - 1‖
      ≤ (32 / ρmin + 16) * ‖σ‖ ^ 2 *
        (‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
          / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖ ^ 2) := by
    intro y
    have hlaty : ∀ k : ℤ, (10 ^ 12 / min ρmin 1) / 2
        ≤ ‖((x : ℂ) + y * Complex.I) - (k : ℂ) / α‖ := by
      intro k
      have := hlat y k
      linarith
    obtain ⟨hζne, hτb⟩ := tauC_le_of_lattice hρmin hσ8 hαs hαne hinf hlaty
    have hτ1 : ‖tauC σ α ((x : ℂ) + y * Complex.I)‖ ≤ 1 / 16 := by
      have h2 : 16 * Real.pi * min ρmin 1 / 10 ^ 12 ≤ 1 / 16 := by
        have hp : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
        nlinarith [hm, hm1, hp, Real.pi_pos]
      linarith
    have hτ2 : ‖tauC σ α ((x : ℂ) + y * Complex.I)‖ ≤ ρmin / 2 := by
      have h2 : 16 * Real.pi * min ρmin 1 / 10 ^ 12 ≤ ρmin / 2 := by
        have h3 : min ρmin 1 ≤ ρmin := min_le_left _ _
        have hp : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
        nlinarith [hm, h3, hp, Real.pi_pos, hρmin]
      linarith
    have hE : Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I))) ≠ 1 := by
      intro h
      exact hζne (by rw [h]; ring)
    exact deriv_liftF_defect_le hρmin hρ hu hub hnorm hσ8 hαs6 hαne hτ1 hτ2 hE
  -- ## the integral bound
  have hB := lintegral_exp_defect_le (α := α) (x := x) (ξ := ξ) hαre hξpos (fun y k => hlat y k)
  have harith : (32 / ρmin + 16) * ‖σ‖ ^ 2 * (1 / (α.re * ‖α‖ * ξ)) ≤ 1 / 64 := by
    have hC : 0 ≤ (32 / ρmin + 16) * ‖σ‖ ^ 2 := by positivity
    have hbase := gate_L1_arith (ρmin := ρmin) (α := α) (σ := σ) hρmin hinf hσ8 hαs
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hC) hbase
    have hpos1 : 0 < α.re * ‖α‖ := mul_pos hαre (norm_pos_iff.mpr hαne)
    have hden : 0 < α.re * ‖α‖ * (10 ^ 12 / min ρmin 1) := mul_pos hpos1 (by positivity)
    have hle : α.re * ‖α‖ * (10 ^ 12 / min ρmin 1) ≤ α.re * ‖α‖ * ξ :=
      mul_le_mul_of_nonneg_left hξ (le_of_lt hpos1)
    exact one_div_le_one_div_of_le hden hle
  calc ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv (liftF u σ α) ((x : ℂ) + y * Complex.I) - 1‖
      ≤ ∫⁻ y : ℝ, ENNReal.ofReal ((32 / ρmin + 16) * ‖σ‖ ^ 2 *
          (‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
            / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α
                * ((x : ℂ) + y * Complex.I)))‖ ^ 2)) :=
        MeasureTheory.lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hpt y))
    _ = ∫⁻ y : ℝ, (ENNReal.ofReal ((32 / ρmin + 16) * ‖σ‖ ^ 2) *
          ENNReal.ofReal (‖Complex.exp (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
            / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α
                * ((x : ℂ) + y * Complex.I)))‖ ^ 2)) := by
        refine MeasureTheory.lintegral_congr (fun y => ?_)
        rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((32 / ρmin + 16) * ‖σ‖ ^ 2) *
        ∫⁻ y : ℝ, ENNReal.ofReal (‖Complex.exp
              (-(2 * Real.pi * Complex.I * α * ((x : ℂ) + y * Complex.I)))‖
            / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α
                * ((x : ℂ) + y * Complex.I)))‖ ^ 2) :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((32 / ρmin + 16) * ‖σ‖ ^ 2) * ENNReal.ofReal (1 / (α.re * ‖α‖ * ξ)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = ENNReal.ofReal ((32 / ρmin + 16) * ‖σ‖ ^ 2 * (1 / (α.re * ‖α‖ * ξ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (1 / 64) := ENNReal.ofReal_le_ofReal harith


theorem gate_scale_L1 (ρmin : ℝ) (hρmin : 0 < ρmin) :
    ∃ ξ₁ ε₀ : ℝ, 0 < ξ₁ ∧ 0 < ε₀ ∧
      ∀ {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ}, ρmin ≤ ρ →
        DifferentiableOn ℂ u (Metric.ball 0 ρ) →
        (∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        ‖σ‖ ≤ ε₀ → ‖α‖ ≤ ε₀ → α ≠ 0 → MandelDim.InF1 α →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ₁ α) ∧
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp ξ₁ α) := by
  obtain ⟨ξg, εg, hξgpos, hεgpos, hgate⟩ := gate_scale ρmin hρmin
  refine ⟨max ξg (10 ^ 12 / min ρmin 1), min εg (min ρmin 1 / 10 ^ 12), ?_, ?_, ?_⟩
  · exact lt_max_of_lt_right (by positivity)
  · exact lt_min hεgpos (by positivity)
  · intro u σ α ρ hρ hu hub hnorm hσs hαs hαne hinf
    have hεg : min εg (min ρmin 1 / 10 ^ 12) ≤ εg := min_le_left _ _
    have hεm : min εg (min ρmin 1 / 10 ^ 12) ≤ min ρmin 1 / 10 ^ 12 := min_le_right _ _
    have hgates := hgate hρ hu hub hnorm (le_trans hσs hεg) (le_trans hαs hεg) hαne hinf
    have hσs'' : ‖σ‖ ≤ min ρmin 1 / 10 ^ 12 := le_trans hσs hεm
    have hαs'' : ‖α‖ ≤ min ρmin 1 / 10 ^ 12 := le_trans hαs hεm
    have hξg_le : ξg ≤ max ξg (10 ^ 12 / min ρmin 1) := le_max_left _ _
    have hm_le : 10 ^ 12 / min ρmin 1 ≤ max ξg (10 ^ 12 / min ρmin 1) := le_max_right _ _
    have hξmaxpos : 0 < max ξg (10 ^ 12 / min ρmin 1) := lt_of_lt_of_le (by positivity) hm_le
    constructor
    · refine ⟨NearTranslationOn_mono hgates.2 (Qm_subset_of_le hξg_le), ?_⟩
      intro x hx
      exact lintegral_line_gate hρmin hρ hu hub hnorm hσs'' hαs'' hαne hinf hm_le
        (fun y k => (scale_lattice hξmaxpos hinf).2 (hx y) k)
    · refine ⟨NearTranslationOn_mono hgates.1 (Qp_subset_of_le hξg_le), ?_⟩
      intro x hx
      exact lintegral_line_gate hρmin hρ hu hub hnorm hσs'' hαs'' hαne hinf hm_le
        (fun y k => (scale_lattice hξmaxpos hinf).1 (hx y) k)

end

end Work.Pert
