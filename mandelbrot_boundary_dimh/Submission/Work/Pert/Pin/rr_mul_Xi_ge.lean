import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.band_Qm_margins
import Submission.Work.Pert.closedBall_subset_Qm
import Submission.Work.PertCrux.norm_alpha_le_norm_one_sub_exp

namespace Work.Pert.Pin

open MandelDim Complex

/-- **The lower gate contains a point where `τ_f` is large.**

This is the relaxed form of `Work.PertCrux.tauC_ge_of_mem_Qm`: the witness `z = 2Ξi` of the gate
`Qm Ξ α` has `‖τ_f z‖ ≥ 1/(16Ξ)` as soon as `4πΞ‖α‖ ≤ 1/2` (the original version asks for the
twice as strong `8πΞ‖α‖ ≤ 1/2`, which is *not* implied by the perturbative hypotheses when `Ξ` is
large). The present hypothesis always holds here because `Ξ‖α‖ ≤ 1/32`.

Recall `τ_f w = σ/(1 - e^{-2πiαw})`, so `‖τ_f w‖` is large exactly when `αw` is close to an
integer; at `w = 2Ξi` the exponent is `-2πiα·2Ξi = 4πΞα`, and `1 - e^{4πΞα} ≈ -4πΞα`. -/
theorem exists_tauC_ge_of_mem_Qm {σ α u₀ : ℂ} {Ξ : ℝ} (hΞ : 0 < Ξ) (hαne : α ≠ 0)
    (h1 : 2 * Real.pi * ‖α‖ ≤ 1 / 2) (h2 : 4 * Real.pi * Ξ * ‖α‖ ≤ 1 / 2)
    (hRe : Ξ < (1 / α).re) (hu₀lo : 1 / 2 ≤ ‖u₀‖) (hu₀hi : ‖u₀‖ ≤ 2)
    (hnorm : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ∃ z ∈ Work.Pert.Qm Ξ α, 1 / (16 * Ξ) ≤ ‖Work.Pert.tauC σ α z‖ := by
  refine ⟨((2 * Ξ : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · -- membership in the lower gate
    rw [Work.Pert.mem_Qm_iff]
    constructor
    · have him : (0 : ℝ) ≤ |(((2 * Ξ : ℝ) : ℂ) * Complex.I).im + (1 / α).im| := abs_nonneg _
      have hre : (((2 * Ξ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
      rw [hre]
      linarith [hRe, him]
    · have hre : (((2 * Ξ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
      have him : |(((2 * Ξ : ℝ) : ℂ) * Complex.I).im| = 2 * Ξ := by
        rw [show (((2 * Ξ : ℝ) : ℂ) * Complex.I).im = 2 * Ξ from by simp]
        exact abs_of_pos (by linarith)
      rw [hre, him]
      linarith
  · -- `‖τ_f‖ ≥ 1/(16Ξ)` at `z = 2Ξi`
    -- the order-two Taylor bounds `‖exp x - 1‖ ≥ ‖x‖/2` (lower) and
    -- `‖exp x - 1‖ ≤ 2‖x‖` (upper, `Complex.norm_exp_sub_one_le`) for `‖x‖ ≤ 1/2`
    have hlow : ∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ‖x‖ / 2 ≤ ‖Complex.exp x - 1‖ := by
      intro x hx
      have hx1 : ‖x‖ ≤ 1 := by linarith
      have h1' : ‖Complex.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hx1
      have h3 : (Complex.exp x - 1) - (Complex.exp x - 1 - x) = x := by ring
      have hle := norm_sub_le (Complex.exp x - 1) (Complex.exp x - 1 - x)
      rw [h3] at hle
      nlinarith [hle, h1', norm_nonneg x, hx, sq_nonneg ‖x‖]
    -- the argument of the exponential at the witness
    have harg : -(2 * Real.pi * Complex.I * α * (((2 * Ξ : ℝ) : ℂ) * Complex.I))
        = 4 * Real.pi * Ξ * α := by
      calc -(2 * Real.pi * Complex.I * α * (((2 * Ξ : ℝ) : ℂ) * Complex.I))
          = -(2 * Real.pi * (((2 * Ξ : ℝ) : ℂ)) * α * (Complex.I * Complex.I)) := by ring
        _ = -(2 * Real.pi * (((2 * Ξ : ℝ) : ℂ)) * α * (-1)) := by rw [Complex.I_mul_I]
        _ = 4 * Real.pi * Ξ * α := by push_cast; ring
    have hz : Work.Pert.tauC σ α (((2 * Ξ : ℝ) : ℂ) * Complex.I)
        = σ / (1 - Complex.exp (4 * Real.pi * Ξ * α)) := by
      simp only [Work.Pert.tauC]
      rw [harg]
    rw [hz, norm_div]
    -- norm of the relevant exponent
    have hwnorm : ‖(4 * Real.pi * Ξ * α : ℂ)‖ = 4 * Real.pi * Ξ * ‖α‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_pos Real.pi_pos, abs_of_pos hΞ]
    -- the denominator is non-zero (used to invert the division)
    have hden_pos : 0 < ‖1 - Complex.exp (4 * Real.pi * Ξ * α)‖ := by
      have hwle : ‖(4 * Real.pi * Ξ * α : ℂ)‖ ≤ 1 / 2 := by rw [hwnorm]; linarith
      have h := hlow _ hwle
      have hwpos : 0 < ‖(4 * Real.pi * Ξ * α : ℂ)‖ := by
        rw [hwnorm]
        have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
        positivity
      rw [norm_sub_rev]
      linarith
    -- the lower bound on the multiplier `σ`
    have hσu : σ * u₀ = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
      linear_combination -hnorm
    have hu0pos : 0 < ‖u₀‖ := by linarith
    have h2pinorm : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_pos Real.pi_pos]
    have hσ_lb : Real.pi * ‖α‖ / 2 ≤ ‖σ‖ := by
      have hlow2 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ / 2
          ≤ ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ := by
        apply hlow; rw [h2pinorm]; exact h1
      have hnormσu : ‖σ‖ * ‖u₀‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
        rw [← norm_mul, hσu]
      have key : Real.pi * ‖α‖ ≤ ‖σ‖ * ‖u₀‖ := by
        rw [hnormσu, norm_sub_rev]
        have : Real.pi * ‖α‖ = ‖(2 * Real.pi * Complex.I * α : ℂ)‖ / 2 := by
          rw [h2pinorm]; ring
        linarith [hlow2]
      have key2 : Real.pi * ‖α‖ / ‖u₀‖ ≤ ‖σ‖ := by
        rw [div_le_iff₀ hu0pos]
        linarith [key]
      have key3 : Real.pi * ‖α‖ / 2 ≤ Real.pi * ‖α‖ / ‖u₀‖ :=
        div_le_div_of_nonneg_left (by positivity) hu0pos hu₀hi
      linarith
    rw [le_div_iff₀ hden_pos]
    -- upper bound on the denominator
    have hden_ub : ‖1 - Complex.exp (4 * Real.pi * Ξ * α)‖ ≤ 8 * Real.pi * Ξ * ‖α‖ := by
      have hwle1 : ‖(4 * Real.pi * Ξ * α : ℂ)‖ ≤ 1 := by rw [hwnorm]; linarith
      have h := Complex.norm_exp_sub_one_le (x := (4 * Real.pi * Ξ * α : ℂ)) hwle1
      rw [norm_sub_rev]
      calc ‖Complex.exp (4 * Real.pi * Ξ * α) - 1‖ ≤ 2 * ‖(4 * Real.pi * Ξ * α : ℂ)‖ := h
        _ = 8 * Real.pi * Ξ * ‖α‖ := by rw [hwnorm]; ring
    calc 1 / (16 * Ξ) * ‖1 - Complex.exp (4 * Real.pi * Ξ * α)‖
        ≤ 1 / (16 * Ξ) * (8 * Real.pi * Ξ * ‖α‖) := by
          apply mul_le_mul_of_nonneg_left hden_ub; positivity
      _ = Real.pi * ‖α‖ / 2 := by field_simp; ring
      _ ≤ ‖σ‖ := hσ_lb

/-- **The gate radius and the gate parameter are inversely comparable.**

The gate `Qm Ξ α` contains the point `z = 2Ξi`; there `τ_f z = σ/(1 - e^{4πΞα})` and, since
`Ξ‖α‖ ≤ 1/32` makes `4πΞα` small, `‖τ_f z‖ ≥ 1/(16Ξ)`.  The hypothesis `hτQ` (the image of the
gate is contained in the ball of radius `rr`) therefore forces `rr > 1/(16Ξ)`, i.e.
`rr · Ξ ≥ 1/16 ≥ 1/64`. -/
theorem rr_mul_Xi_ge {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) :
    1 / 64 ≤ rr * Ξ := by
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h : (2 : ℝ) ^ 10 ≤ M := hM
    norm_num at h
    exact h
  -- `α ≠ 0` (and `Ξ < Re (1/α)`) from the perturbative data
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hαne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hXpos : 0 < M + 2 + Ξ := by linarith
  have hden : 0 < 32 * (M + 2 + Ξ) := by linarith
  -- the two smallness conditions on the exponent
  have h1 : 2 * Real.pi * ‖α‖ ≤ 1 / 2 := by
    have h32 : (32768 : ℝ) ≤ 32 * (M + 2 + Ξ) := by linarith
    have hbound : ‖α‖ ≤ 1 / 32768 := by
      have hle : 1 / (32 * (M + 2 + Ξ)) ≤ 1 / 32768 :=
        one_div_le_one_div_of_le (by norm_num) h32
      linarith
    have hstep : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * (1 / 32768) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    nlinarith [hstep, Real.pi_lt_four]
  have h2 : 4 * Real.pi * Ξ * ‖α‖ ≤ 1 / 2 := by
    have hΞle : Ξ ≤ M + 2 + Ξ := by linarith
    have hstep : 4 * Real.pi * Ξ * ‖α‖ ≤ 4 * Real.pi * Ξ * (1 / (32 * (M + 2 + Ξ))) :=
      mul_le_mul_of_nonneg_left hα (by positivity)
    have hval : 4 * Real.pi * Ξ * (1 / (32 * (M + 2 + Ξ))) ≤ Real.pi / 8 := by
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith [Real.pi_pos, hΞle, hΞ]
    linarith [hstep, hval, Real.pi_lt_four]
  -- the gate extends past the imaginary axis
  have hRe : Ξ < (1 / α).re := by
    have hkey := Work.Pert.band_Qm_key_bound hΞ hM hInF1 hα
    have h2p : (2 : ℝ) ^ 10 = 1024 := by norm_num
    rw [h2p] at hkey
    linarith
  -- the witness of the gate at which `τ_f` is large
  obtain ⟨z, hzQ, hzb⟩ :=
    exists_tauC_ge_of_mem_Qm (σ := σ) (α := α) (u₀ := u 0) hΞ hαne h1 h2 hRe
      (hu2 0 (by rw [Metric.mem_ball, dist_self]; exact hrr)).1
      (hu2 0 (by rw [Metric.mem_ball, dist_self]; exact hrr)).2 hnorm
  have hzm : Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr := hτQ z hzQ
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzm
  have hlt : 1 / (16 * Ξ) < rr := lt_of_le_of_lt hzb hzm
  have h16 : 0 < 16 * Ξ := by linarith
  have hkey : 1 < rr * (16 * Ξ) := (div_lt_iff₀ h16).mp hlt
  nlinarith [hkey]

end Work.Pert.Pin
