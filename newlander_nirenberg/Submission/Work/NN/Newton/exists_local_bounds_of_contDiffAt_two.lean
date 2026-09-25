import Mathlib

open Set Filter
open scoped Topology

namespace Work.NN.Newton

/-- A `C²` function `F` with `F 0 = 0`, defined on a real normed space, admits a neighbourhood
of `0` on which it and its differential are bounded and Lipschitz. -/
theorem exists_local_bounds_of_contDiffAt_two
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : X → Y} (hF : ContDiffAt ℝ 2 F 0) (h0 : F 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      (∀ z, ‖z‖ ≤ ρ → ‖F z‖ ≤ K * ‖z‖) ∧
      (∀ z w, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖F z - F w‖ ≤ K * ‖z - w‖) ∧
      (∀ z, ‖z‖ ≤ ρ → DifferentiableAt ℝ F z) ∧
      (∀ z, ‖z‖ ≤ ρ → ‖fderiv ℝ F z‖ ≤ K) ∧
      (∀ z w, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖fderiv ℝ F z - fderiv ℝ F w‖ ≤ K * ‖z - w‖) := by
  -- `F` is `C¹` around `0`, hence differentiable there; the differential then gives a local
  -- `O(‖z‖)` estimate because `F 0 = 0`.
  have hF1 : ContDiffAt ℝ 1 F 0 := hF.of_le (by norm_num)
  have hdF0 : DifferentiableAt ℝ F 0 := hF1.differentiableAt (by norm_num)
  have hlittle : (fun y : X => F y - F 0 - (fderiv ℝ F 0) (y - 0)) =o[𝓝 0] (fun y : X => y - 0) :=
    hdF0.hasFDerivAt.isLittleO
  have hb : ∀ᶠ y in 𝓝 (0 : X), ‖F y‖ ≤ (‖fderiv ℝ F 0‖ + 1) * ‖y‖ := by
    have hb' : ∀ᶠ y in 𝓝 (0 : X), ‖F y - (fderiv ℝ F 0) y‖ ≤ ‖y‖ := by
      have h := hlittle.bound (show (0:ℝ) < 1 by norm_num)
      filter_upwards [h] with y hy
      simpa [h0] using hy
    filter_upwards [hb'] with y hy
    have h1 : ‖F y‖ ≤ ‖F y - (fderiv ℝ F 0) y‖ + ‖(fderiv ℝ F 0) y‖ := by
      calc ‖F y‖ = ‖(F y - (fderiv ℝ F 0) y) + (fderiv ℝ F 0) y‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖(fderiv ℝ F 0) y‖ ≤ ‖fderiv ℝ F 0‖ * ‖y‖ := (fderiv ℝ F 0).le_opNorm y
    nlinarith [norm_nonneg y, norm_nonneg (fderiv ℝ F 0)]
  -- `F` is locally Lipschitz near `0` ...
  obtain ⟨KF, tF, htF, hLipF⟩ := hF1.exists_lipschitzOnWith
  obtain ⟨rF, hrF, hrFsub⟩ := Metric.mem_nhds_iff.mp htF
  -- ... and so is its differential (since `F` is `C²`).
  have hG1 : ContDiffAt ℝ 1 (fderiv ℝ F) 0 := ContDiffAt.fderiv_right_succ hF
  obtain ⟨KG, tG, htG, hLipG⟩ := hG1.exists_lipschitzOnWith
  obtain ⟨rG, hrG, hrGsub⟩ := Metric.mem_nhds_iff.mp htG
  -- `F` is differentiable near `0`.
  have hEv : ∀ᶠ y in 𝓝 (0:X), ContDiffAt ℝ 2 F y := hF.eventually (by norm_num)
  obtain ⟨rd, hrd, hrdsub⟩ := Metric.eventually_nhds_iff.mp hEv
  -- the ball on which the `O(‖z‖)` estimate holds.
  obtain ⟨rb, hrb, hbsub⟩ := Metric.eventually_nhds_iff.mp hb
  -- choose the radius as (half) the smallest of the four radii.
  set ρ : ℝ := (min (min rF rG) (min rd rb)) / 2 with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    have : 0 < min (min rF rG) (min rd rb) := by
      apply lt_min <;> apply lt_min <;> assumption
    linarith
  have hρF : ρ < rF := by
    rw [hρ]
    have hle : min (min rF rG) (min rd rb) ≤ rF := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hρG : ρ < rG := by
    rw [hρ]
    have hle : min (min rF rG) (min rd rb) ≤ rG := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hρd : ρ < rd := by
    rw [hρ]
    have hle : min (min rF rG) (min rd rb) ≤ rd := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hρb : ρ < rb := by
    rw [hρ]
    have hle : min (min rF rG) (min rd rb) ≤ rb := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  -- the common constant: the largest of all bounds needed.
  set K : ℝ := max (max (‖fderiv ℝ F 0‖ + 1) (KF:ℝ)) (max (KG:ℝ) (‖fderiv ℝ F 0‖ + (KG:ℝ) * ρ)) with hKdef
  have hK1 : (‖fderiv ℝ F 0‖ + 1) ≤ K := by rw [hKdef]; exact le_max_of_le_left (le_max_left _ _)
  have hKF : (KF:ℝ) ≤ K := by rw [hKdef]; exact le_max_of_le_left (le_max_right _ _)
  have hKG : (KG:ℝ) ≤ K := by rw [hKdef]; exact le_max_of_le_right (le_max_left _ _)
  have hKρ : ‖fderiv ℝ F 0‖ + (KG:ℝ) * ρ ≤ K := by rw [hKdef]; exact le_max_of_le_right (le_max_right _ _)
  have hKnn : (0:ℝ) ≤ K := le_trans (by positivity : (0:ℝ) ≤ ‖fderiv ℝ F 0‖ + 1) hK1
  refine ⟨ρ, hρpos, K, hKnn, ?_, ?_, ?_, ?_, ?_⟩
  · -- `‖F z‖ ≤ K ‖z‖`
    intro z hz
    have hbound := hbsub (by rw [dist_eq_norm, sub_zero]; linarith)
    calc ‖F z‖ ≤ (‖fderiv ℝ F 0‖ + 1) * ‖z‖ := hbound
      _ ≤ K * ‖z‖ := mul_le_mul_of_nonneg_right hK1 (norm_nonneg z)
  · -- `F` is `K`-Lipschitz
    intro z w hz hw
    have hzG : dist z (0:X) < rF := by rw [dist_eq_norm, sub_zero]; linarith
    have hwG : dist w (0:X) < rF := by rw [dist_eq_norm, sub_zero]; linarith
    have hdist := hLipF.dist_le_mul z (hrFsub hzG) w (hrFsub hwG)
    rw [dist_eq_norm, dist_eq_norm] at hdist
    calc ‖F z - F w‖ ≤ (KF:ℝ) * ‖z - w‖ := hdist
      _ ≤ K * ‖z - w‖ := mul_le_mul_of_nonneg_right hKF (norm_nonneg _)
  · -- `F` is differentiable on the ball
    intro z hz
    have : dist z (0:X) < rd := by rw [dist_eq_norm, sub_zero]; linarith
    exact (hrdsub this).differentiableAt (by norm_num)
  · -- `fderiv F` is bounded
    intro z hz
    have hzG : dist z (0:X) < rG := by rw [dist_eq_norm, sub_zero]; linarith
    have h0G : (0:X) ∈ tG := mem_of_mem_nhds htG
    have hdist := hLipG.dist_le_mul z (hrGsub hzG) 0 h0G
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at hdist
    have h1 : ‖fderiv ℝ F z‖ ≤ ‖fderiv ℝ F 0‖ + (KG:ℝ) * ‖z‖ := by
      calc ‖fderiv ℝ F z‖ = ‖(fderiv ℝ F z - fderiv ℝ F 0) + fderiv ℝ F 0‖ := by congr 1; abel
        _ ≤ ‖fderiv ℝ F z - fderiv ℝ F 0‖ + ‖fderiv ℝ F 0‖ := norm_add_le _ _
        _ ≤ (KG:ℝ) * ‖z‖ + ‖fderiv ℝ F 0‖ := by linarith
        _ = ‖fderiv ℝ F 0‖ + (KG:ℝ) * ‖z‖ := by ring
    calc ‖fderiv ℝ F z‖ ≤ ‖fderiv ℝ F 0‖ + (KG:ℝ) * ‖z‖ := h1
      _ ≤ ‖fderiv ℝ F 0‖ + (KG:ℝ) * ρ :=
            add_le_add_right (mul_le_mul_of_nonneg_left hz (by positivity : (0:ℝ) ≤ (KG:ℝ))) _
      _ ≤ K := hKρ
  · -- `fderiv F` is `K`-Lipschitz
    intro z w hz hw
    have hzG : dist z (0:X) < rG := by rw [dist_eq_norm, sub_zero]; linarith
    have hwG : dist w (0:X) < rG := by rw [dist_eq_norm, sub_zero]; linarith
    have hdist := hLipG.dist_le_mul z (hrGsub hzG) w (hrGsub hwG)
    rw [dist_eq_norm, dist_eq_norm] at hdist
    calc ‖fderiv ℝ F z - fderiv ℝ F w‖ ≤ (KG:ℝ) * ‖z - w‖ := hdist
      _ ≤ K * ‖z - w‖ := mul_le_mul_of_nonneg_right hKG (norm_nonneg _)

end Work.NN.Newton
