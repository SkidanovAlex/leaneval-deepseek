import Mathlib
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.exists_tauC_gate_ge_fixed
import Submission.Work.Pert.norm_one_sub_exp_two_pi_I_lower
import Submission.Work.Pert.Setup
import Submission.Work.Pert.SmallOfNearOnConst
import Submission.Work.Pert.SmallDataArith

namespace Work.Pert

/-- PERT: the smallness data of (4.2.5), derived from a `NearOn`-neighbourhood on a ball.

The caller (`Work.Pert.Dsub_phi_star`) picks `ρ := min (r₀/2) (1/(K*η))` and `δ₀ := ρ^2/(K*η)`
with `K := 2^20*(C+1)` (`r₀, C` from `Work.Pert.small_of_nearOn`), so the two "regime"
hypotheses below hold with a huge margin (`δ₀/ρ² = 1/(Kη)`, `η δ₀/ρ = ρ/K`); then for every
admissible perturbation the three conclusions hold.

CHAIN (constants as stated, generous on purpose):
* `small_of_nearOn` (with its constant `C = 10`) gives `‖σ‖ ≤ 10 δ₀/ρ`, `‖σ u 0‖ ≤ δ₀/ρ` and
  `‖rotOf f‖ ≤ 10 δ₀/ρ`;
* `‖f'(0) - 1‖ = ‖σ u 0‖ ≤ δ₀/ρ ≤ 1/2`, so
  `2π‖α‖ = ‖log (f' 0)‖ ≤ (3/2)‖f' 0 - 1‖ ≤ (3/2) δ₀/ρ` (`Complex.norm_log_one_add_half_le_self`),
  giving `‖α‖ ≤ 1/1024` and `2π‖α‖η ≤ (3/2)/262144 < 1/64`; note `α ≠ 0` from `InF1`;
* `z = i η/2 ∈ Qm ξ₁ α` (`Work.Pert.I_mul_half_eta_mem_Qm`), so the hypothesis
  `τ_f '' (Qm ξ₁ α) ⊆ ball 0 rr` gives `rr ≥ ‖τ_f (iη/2)‖ ≥ 1/(4η)` via
  `Work.Pert.exists_tauC_gate_ge_of_norm_le` (its hypotheses: `0 < ξ₁`, `2ξ₁ < η`, `InF1`,
  `α ≠ 0`, the normalisation, `1/2 ≤ ‖u 0‖ ≤ 2` from `0 ∈ ball 0 rr`, and `‖α‖η ≤ 1/1024`,
  `‖α‖ ≤ 1/1024`, `σ ≠ 0` all derived above);
* hence `‖u 0 - 1‖ ≤ 10(δ₀/ρ² + δ₀/(ρ rr)) ≤ 10(δ₀/ρ² + 4η δ₀/ρ) ≤ 10(1/65536 + 1/65536)`
  `≤ 1/1024` by the two regime hypotheses. -/
theorem SmallData {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ Metric.closedBall (0 : ℂ) r₀ ⊆ D₀ ∧
    ∀ {ρ δ₀ η rr ξ₁ : ℝ} {f : ℂ → ℂ} {Df : Set ℂ} {u : ℂ → ℂ} {σ α : ℂ},
      0 < ρ → ρ ≤ r₀ → ρ ≤ 1 / 100 → 0 < δ₀ → 2 * δ₀ ≤ ρ → 0 < rr → 0 < η → 0 < ξ₁ →
      2 * ξ₁ < η → 65536 * δ₀ ≤ ρ ^ 2 → 262144 * η * δ₀ ≤ ρ →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ₀ → f 0 = 0 →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      MandelDim.InF1 (MandelDim.rotOf f) → α = MandelDim.rotOf f →
      (∀ z ∈ Work.Pert.Qm ξ₁ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
      MandelDim.QAdm (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) →
      ‖u 0 - 1‖ ≤ 1 / 1024 ∧ 1 / (4 * η) ≤ rr ∧ 2 * Real.pi * ‖α‖ * η ≤ 1 / 64 := by
  obtain ⟨r₀, hr₀pos, hr₀sub, hmain⟩ := SmallOfNearOnConst hd
  refine ⟨r₀, hr₀pos, hr₀sub, ?_⟩
  intro ρ δ₀ η rr ξ₁ f Df u σ α hρ hρr hρ100 hδ h2δ hrr hη hξ h2ξη hreg1 hreg2
    hnear hf0 hdiffu hbnd hform hnorm hInF1 hαeq htauC hQAdm
  -- ## `InF1 α`, `α ≠ 0`
  have hInF1α : MandelDim.InF1 α := by rw [hαeq]; exact hInF1
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1α
  have hα0 : α ≠ 0 := by intro hh; rw [hh] at hαre; simp at hαre
  -- ## the pinned-constant smallness data
  have hsm := hmain (f := f) (Df := Df) (ρ := ρ) (δ₀ := δ₀) (rr := rr) (u := u) (σ := σ)
    hρ hρr hδ h2δ hrr hnear hf0 hdiffu hbnd hform
  obtain ⟨hA, hB, hC⟩ := hsm
  have hαle : ‖α‖ ≤ 10 * δ₀ / ρ := by rw [hαeq]; exact hC
  -- ## the two regime estimates
  have hX : δ₀ / ρ ^ 2 ≤ 1 / 65536 := by
    rw [div_le_iff₀ (pow_pos hρ 2)]
    linarith
  have hδρ : δ₀ / ρ ≤ ρ / 65536 := by
    have he : δ₀ / ρ = ρ * (δ₀ / ρ ^ 2) := by field_simp
    rw [he]
    have h := mul_le_mul_of_nonneg_left hX (le_of_lt hρ)
    linarith
  have hZ : η * δ₀ / ρ ≤ 1 / 262144 := by
    rw [div_le_iff₀ hρ]
    linarith
  -- ## `‖α‖ ≤ 1/1024` and `‖α‖ η ≤ 1/1024`
  have hαsmall : ‖α‖ ≤ 1 / 1024 := by
    have h1 : 10 * δ₀ / ρ ≤ 1 / 1024 := by
      have h2 : 10 * (δ₀ / ρ) ≤ 10 * (ρ / 65536) := by linarith
      have h4 : ρ * (10 / 65536) ≤ (1 / 100) * (10 / 65536) :=
        mul_le_mul_of_nonneg_right hρ100 (by norm_num)
      have h5 : 10 * δ₀ / ρ = 10 * (δ₀ / ρ) := by ring
      linarith
    linarith
  have hαη : ‖α‖ * η ≤ 1 / 1024 := by
    have h1 : ‖α‖ * η ≤ (10 * δ₀ / ρ) * η :=
      mul_le_mul_of_nonneg_right hαle (le_of_lt hη)
    have h2 : (10 * δ₀ / ρ) * η = 10 * (η * δ₀ / ρ) := by ring
    have h3 : 10 * (η * δ₀ / ρ) ≤ 10 * (1 / 262144) := by linarith
    linarith
  -- ## `σ ≠ 0`
  have hσ0 : σ ≠ 0 := by
    intro hσ
    have hexp : Complex.exp (2 * Real.pi * Complex.I * α) = 1 := by rw [← hnorm, hσ]; ring
    have hzer : ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ = 0 := by rw [hexp]; simp
    have hle := norm_one_sub_exp_two_pi_I_lower (α := α) hαsmall
    rw [hzer] at hle
    have hαnorm : ‖α‖ = 0 := by
      have : ‖α‖ ≤ 0 := by nlinarith [Real.pi_pos]
      exact le_antisymm this (norm_nonneg α)
    exact hα0 (norm_eq_zero.mp hαnorm)
  -- ## the gate point where `τ_f` is large
  have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) rr := Metric.mem_ball_self hrr
  have hu0lo : 1 / 2 ≤ ‖u 0‖ := (hbnd 0 h0ball).1
  have hu0hi : ‖u 0‖ ≤ 2 := (hbnd 0 h0ball).2
  obtain ⟨z, hzQ, hzge⟩ :=
    exists_tauC_gate_ge_of_norm_le hξ h2ξη hInF1α hα0 hnorm hu0lo hu0hi hαη hαsmall hσ0
  have hzmem : Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr := htauC z hzQ
  have hznorm : ‖Work.Pert.tauC σ α z‖ < rr := by
    have h := Metric.mem_ball.mp hzmem
    rwa [dist_zero_right] at h
  have hrrge : 1 / (4 * η) ≤ rr := le_of_lt (lt_of_le_of_lt hzge hznorm)
  -- ## final assembly
  obtain ⟨hc0, hc3, _hc1, _hc2⟩ :=
    SmallDataArith (ρ := ρ) (δ₀ := δ₀) (η := η) (rr := rr)
      (c0 := ‖u 0 - 1‖) (c1 := ‖α‖) hρ hρ100 hδ hη hrr hreg1 hreg2 hrrge hA hαle
  exact ⟨hc0, hrrge, hc3⟩


end Work.Pert
