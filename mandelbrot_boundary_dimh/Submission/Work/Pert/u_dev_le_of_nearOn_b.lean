import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.u_dev_le_of_nearOn_b`

Sharpened form of the PROVED `Work.Pert.u_dev_le_of_nearOn`: same hypotheses, same proof, but the
additive constant `2 * (1/1024)` is replaced by `1/1024`:

  `‖u τ - u 0‖ ≤ 1/1024 + 2 * ((δ₀/ρ + B ρ²) / (ρ - ‖τ‖))`.

With `H z = f z - z - z²`, `V = dslope H 0`, `Λ = δ₀/ρ + B ρ²`, the proof establishes
`u τ - 1 = (V τ - V σ)/(τ - σ)`, `‖V τ - V σ‖ ≤ (2Λ/(ρ - ‖τ‖)) ‖τ - σ‖` and `V σ = -σ`, whence
`‖u τ - u 0‖ ≤ 2Λ/(ρ - ‖τ‖) + ‖u 0 - 1‖`; the `1/1024` is not doubled.
-/

namespace Work.Pert
open Metric

-- `hu` and `hbdd` are part of the requested statement but are not needed for this estimate.
set_option linter.unusedVariables false in

theorem u_dev_le_of_nearOn_b {f₀ f : ℂ → ℂ} {Df : Set ℂ} {u : ℂ → ℂ} {σ : ℂ} {ρ δ₀ B rr : ℝ}
    (hρ : 0 < ρ) (hσ : σ ≠ 0) (h0 : f 0 = 0) (hB : 0 ≤ B)
    (hu : DifferentiableOn ℂ u (Metric.ball 0 rr))
    (hbdd : ∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hform : ∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z)
    (hu0 : ‖u 0 - 1‖ ≤ 1 / 1024)
    (hnear : MandelDim.NearOn f₀ f Df (Metric.closedBall 0 ρ) δ₀)
    (hf0b : ∀ z ∈ Metric.closedBall 0 ρ, ‖f₀ z - z - z ^ 2‖ ≤ B * ‖z‖ ^ 3) :
    ∀ τ : ℂ, ‖τ‖ < ρ → τ ∈ Metric.ball 0 rr → 2 * ‖σ‖ ≤ ‖τ‖ →
      ‖u τ - u 0‖ ≤ 1 / 1024 + 2 * ((δ₀ / ρ + B * ρ ^ 2) / (ρ - ‖τ‖)) := by
  intro τ hτρ hτrr h2σ
  obtain ⟨hDfopen, hsub, hfdiff, hclose⟩ := hnear
  set s : ℝ := ‖τ‖ with hs
  set Λ : ℝ := δ₀ / ρ + B * ρ ^ 2 with hΛ
  have hρnn : (0 : ℝ) ≤ ρ := hρ.le
  -- ## elementary consequences of the hypotheses
  have hf0_0 : f₀ 0 = 0 := by
    have h := hf0b 0 (Metric.mem_closedBall_self hρ.le)
    have h1 : f₀ 0 - 0 - 0 ^ 2 = f₀ 0 := by ring
    rw [h1] at h
    have h2 : ‖(0 : ℂ)‖ ^ 3 = 0 := by simp
    rw [h2, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hδ0pos : 0 < δ₀ := by
    have h := hclose 0 (Metric.mem_closedBall_self hρ.le)
    have h1 : f 0 - f₀ 0 = 0 := by rw [h0, hf0_0, sub_zero]
    rwa [h1, norm_zero] at h
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]
    exact add_nonneg (div_nonneg hδ0pos.le hρnn) (mul_nonneg hB (sq_nonneg ρ))
  have hs_lt_ρ : s < ρ := by rw [hs]; exact hτρ
  have hρs_pos : 0 < ρ - s := sub_pos.mpr hs_lt_ρ
  -- ## the holomorphic function `H z = f z - z - z ^ 2`
  set H : ℂ → ℂ := fun z => f z - z - z ^ 2 with hH
  have hH0 : H 0 = 0 := by rw [hH]; simp [h0]
  have hballDf : Metric.ball 0 ρ ⊆ Df := fun z hz => hsub (Metric.ball_subset_closedBall hz)
  have hHdiff_ball : DifferentiableOn ℂ H (Metric.ball 0 ρ) := by
    rw [hH]
    have h1 : DifferentiableOn ℂ f (Metric.ball 0 ρ) := hfdiff.mono hballDf
    have h2 : DifferentiableOn ℂ (fun z : ℂ => z + z ^ 2) (Metric.ball 0 ρ) := by fun_prop
    have h3 : (fun z : ℂ => f z - z - z ^ 2) = fun z : ℂ => f z - (z + z ^ 2) := by
      funext z; ring
    rw [h3]
    exact h1.sub h2
  -- ## the constraint on `H`
  have hHbound_closed : ∀ z ∈ Metric.closedBall 0 ρ, ‖H z‖ ≤ δ₀ + B * ‖z‖ ^ 3 := by
    intro z hz
    have h1 : ‖f z - f₀ z‖ < δ₀ := hclose z hz
    have h2 : ‖f₀ z - z - z ^ 2‖ ≤ B * ‖z‖ ^ 3 := hf0b z hz
    have h3 : H z = (f z - f₀ z) + (f₀ z - z - z ^ 2) := by rw [hH]; ring
    rw [h3]
    linarith [norm_add_le (f z - f₀ z) (f₀ z - z - z ^ 2)]
  have hHbound_ball : ∀ z ∈ Metric.ball 0 ρ, ‖H z‖ ≤ δ₀ + B * ρ ^ 3 := by
    intro z hz
    have hz1 : ‖z‖ ≤ ρ := by
      have h := hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact h.le
    have hb := hHbound_closed z (Metric.ball_subset_closedBall hz)
    have hz3 : ‖z‖ ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ (norm_nonneg z) hz1 3
    have hBz : B * ‖z‖ ^ 3 ≤ B * ρ ^ 3 := mul_le_mul_of_nonneg_left hz3 hB
    linarith
  have hHmaps : Set.MapsTo H (Metric.ball 0 ρ) (Metric.closedBall (H 0) (δ₀ + B * ρ ^ 3)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, hH0, sub_zero]
    exact hHbound_ball z hz
  have hHschwarz : ∀ z ∈ Metric.ball 0 ρ, ‖H z‖ ≤ ((δ₀ + B * ρ ^ 3) / ρ) * ‖z‖ := by
    intro z hz
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hHdiff_ball hHmaps hz
    rw [dist_eq_norm, hH0, sub_zero, dist_eq_norm, sub_zero] at h
    exact h
  have hΛeq : Λ = (δ₀ + B * ρ ^ 3) / ρ := by
    rw [hΛ]; field_simp
  -- ## `V = H / id`, the holomorphic extension of `H z / z`
  set V : ℂ → ℂ := dslope H 0 with hV
  have hVdiff : DifferentiableOn ℂ V (Metric.ball 0 ρ) := by
    rw [hV]
    exact (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 hρ)).mpr hHdiff_ball
  have hVbound : ∀ z ∈ Metric.ball 0 ρ, ‖V z‖ ≤ Λ := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [hV, dslope_same, hΛeq]
      exact Complex.norm_deriv_le_div_of_mapsTo_ball hHdiff_ball hHmaps hρ
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hVz : V z = H z / z := by
        rw [hV, dslope_of_ne _ hz0, slope_def_module, hH0, sub_zero, sub_zero, smul_eq_mul,
          div_eq_inv_mul]
      rw [hVz, hΛeq, norm_div, div_le_iff₀ hzpos]
      linarith [hHschwarz z hz]
  -- ## Cauchy (Schwarz) estimate for `V'`
  have hVderiv : ∀ w ∈ Metric.ball 0 ρ, ‖deriv V w‖ ≤ 2 * Λ / (ρ - ‖w‖) := by
    intro w hw
    have hwρ : ‖w‖ < ρ := by
      have h := hw
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact h
    have hR : 0 < ρ - ‖w‖ := sub_pos.mpr hwρ
    have hsubb : Metric.ball w (ρ - ‖w‖) ⊆ Metric.ball 0 ρ := by
      intro z hz
      have hzw : ‖z - w‖ < ρ - ‖w‖ := by
        have h := hz
        rwa [Metric.mem_ball, dist_eq_norm] at h
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
        _ < ρ := by linarith
    have hmaps : Set.MapsTo V (Metric.ball w (ρ - ‖w‖)) (Metric.closedBall (V w) (2 * Λ)) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hzρ : z ∈ Metric.ball 0 ρ := hsubb hz
      calc ‖V z - V w‖ ≤ ‖V z‖ + ‖V w‖ := norm_sub_le _ _
        _ ≤ Λ + Λ := add_le_add (hVbound z hzρ) (hVbound w hw)
        _ = 2 * Λ := by ring
    exact Complex.norm_deriv_le_div_of_mapsTo_ball (hVdiff.mono hsubb) hmaps hR
  -- ## the segment `[σ, τ]` stays in `closedBall 0 s`
  have hσmem : σ ∈ Metric.closedBall (0 : ℂ) s := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith [h2σ, norm_nonneg σ, hs]
  have hτmem : τ ∈ Metric.closedBall (0 : ℂ) s := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hs.ge
  have hseg_closed : segment ℝ σ τ ⊆ Metric.closedBall (0 : ℂ) s :=
    Convex.segment_subset (convex_closedBall (0 : ℂ) s) hσmem hτmem
  have hseg_ball : segment ℝ σ τ ⊆ Metric.ball 0 ρ := by
    intro z hz
    have h := hseg_closed hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt h hs_lt_ρ
  have hseg_le : ∀ z ∈ segment ℝ σ τ, ‖z‖ ≤ s := by
    intro z hz
    have h := hseg_closed hz
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  -- ## mean value inequality along the segment
  have hMVT : ‖V τ - V σ‖ ≤ (2 * Λ / (ρ - s)) * ‖τ - σ‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le ?_ ?_ (convex_segment σ τ)
      (left_mem_segment ℝ σ τ) (right_mem_segment ℝ σ τ)
    · intro x hx
      exact hVdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hseg_ball hx))
    · intro x hx
      have hxρ : x ∈ Metric.ball 0 ρ := hseg_ball hx
      have hxρ' : ‖x‖ < ρ := by
        have h := hxρ
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      have h1 : ‖deriv V x‖ ≤ 2 * Λ / (ρ - ‖x‖) := hVderiv x hxρ
      have hden : ρ - s ≤ ρ - ‖x‖ := by linarith [hseg_le x hx]
      have h2 : 2 * Λ / (ρ - ‖x‖) ≤ 2 * Λ / (ρ - s) :=
        div_le_div_of_nonneg_left (by linarith [hΛnn]) hρs_pos hden
      linarith
  -- ## `σ` lies in `ball 0 rr`, so `hform` applies there
  have hs_lt_rr : s < rr := by
    have h := hτrr
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    rw [hs]; exact h
  have hσ_ball : σ ∈ Metric.ball 0 rr := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : ‖σ‖ ≤ s := by linarith [h2σ, norm_nonneg σ, hs]
    linarith
  have hfσ : f σ = σ := by
    have h := hform σ hσ_ball
    simpa using h
  have hHσ : H σ = -(σ ^ 2) := by
    rw [hH]
    show f σ - σ - σ ^ 2 = -(σ ^ 2)
    rw [hfσ]; ring
  have hVσ : V σ = -σ := by
    rw [hV, dslope_of_ne _ hσ, slope_def_module, hHσ, hH0, sub_zero, sub_zero, smul_eq_mul]
    field_simp
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    have h1 : ‖σ‖ = 0 := by linarith [norm_nonneg σ, h2σ, hs]
    exact hσ (norm_eq_zero.mp h1)
  have hHτ : H τ = τ * (τ - σ) * u τ - τ ^ 2 := by
    rw [hH]
    show f τ - τ - τ ^ 2 = τ * (τ - σ) * u τ - τ ^ 2
    rw [hform τ hτrr]; ring
  have hVτ : V τ = (τ - σ) * u τ - τ := by
    rw [hV, dslope_of_ne _ hτ0, slope_def_module, hHτ, hH0, sub_zero, sub_zero, smul_eq_mul]
    field_simp
  -- ## the exact identity `u τ - 1 = (V τ - V σ)/(τ - σ)`
  have hτσ : τ ≠ σ := by
    intro h
    rw [h] at hs
    have h1 : ‖σ‖ = 0 := by linarith [norm_nonneg σ, h2σ, hs]
    exact hσ (norm_eq_zero.mp h1)
  have hkey : u τ - 1 = (V τ - V σ) / (τ - σ) := by
    rw [hVτ, hVσ, eq_div_iff (sub_ne_zero.mpr hτσ)]
    ring
  -- ## assembly
  have hmain : ‖u τ - u 0‖ ≤ 2 * Λ / (ρ - s) + 1 / 1024 := by
    have h1 : u τ - u 0 = (u τ - 1) + (1 - u 0) := by ring
    rw [h1]
    have h2 : ‖V τ - V σ‖ / ‖τ - σ‖ ≤ 2 * Λ / (ρ - s) := by
      rw [div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hτσ))]
      linarith [hMVT]
    calc ‖(u τ - 1) + (1 - u 0)‖ ≤ ‖u τ - 1‖ + ‖1 - u 0‖ := norm_add_le _ _
      _ = ‖V τ - V σ‖ / ‖τ - σ‖ + ‖u 0 - 1‖ := by
            rw [hkey, norm_div, norm_sub_rev (1 : ℂ) (u 0)]
      _ ≤ 2 * Λ / (ρ - s) + 1 / 1024 := by linarith [h2, hu0]

  have hfin : ‖u τ - u 0‖ ≤ 1 / 1024 + 2 * (Λ / (ρ - s)) := by
    have h2' : 1 / 1024 + 2 * (Λ / (ρ - s)) = 2 * Λ / (ρ - s) + 1 / 1024 := by ring
    rw [h2']
    exact hmain
  calc ‖u τ - u 0‖ ≤ 1 / 1024 + 2 * (Λ / (ρ - s)) := hfin
    _ = 1 / 1024 + 2 * ((δ₀ / ρ + B * ρ ^ 2) / (ρ - ‖τ‖)) := by rw [hΛ, hs]

end Work.Pert
