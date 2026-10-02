import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Set Filter

namespace Work.LandLeaves

/-- Continuity of `w ↦ r (1 / w)` on the closed annulus `R ≤ ‖w‖ ≤ R'`, where
`r z = F z - (1 / z + a₁ * z)` and `F` is differentiable on the punctured unit disk. -/
private lemma cci_aux_cont (F : ℂ → ℂ) (a₁ : ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ F {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}) (hR : 1 < R) {R' : ℝ} (hRR' : R < R')
    (r : ℂ → ℂ) (hrdef : r = fun z => F z - (1 / z + a₁ * z)) :
    ContinuousOn (fun w : ℂ => r (1 / w)) (Metric.closedBall 0 R' \ Metric.ball 0 R) := by
  rw [hrdef]
  have h_maps : MapsTo (fun w : ℂ => 1 / w) (Metric.closedBall 0 R' \ Metric.ball 0 R)
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    intro w hw
    have hwR : R ≤ ‖w‖ := by
      have h1 : w ∉ Metric.ball (0:ℂ) R := hw.2
      rw [Metric.mem_ball, not_lt, dist_zero_right] at h1
      exact h1
    have hnorm : ‖(1:ℂ) / w‖ = 1 / ‖w‖ := by rw [norm_div, norm_one]
    refine ⟨?_, ?_⟩
    · rw [hnorm]; exact one_div_pos.mpr (lt_of_lt_of_le (lt_trans one_pos hR) hwR)
    · rw [hnorm]
      exact lt_of_le_of_lt (one_div_le_one_div_of_le (lt_trans one_pos hR) hwR)
        (by rw [div_lt_one (lt_trans one_pos hR)]; exact hR)
  have h_inv : ContinuousOn (fun w : ℂ => 1 / w) (Metric.closedBall 0 R' \ Metric.ball 0 R) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro w hw
    have hwR : R ≤ ‖w‖ := by
      have h1 : w ∉ Metric.ball (0:ℂ) R := hw.2
      rw [Metric.mem_ball, not_lt, dist_zero_right] at h1
      exact h1
    intro h
    have hw0 : w = 0 := h
    rw [hw0, norm_zero] at hwR
    linarith [lt_trans one_pos hR]
  have h1z : ContinuousOn (fun z : ℂ => 1 / z) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    intro h
    have hz0 : z = 0 := h
    rw [hz0, norm_zero] at hz
    exact lt_irrefl 0 hz.1
  have hlin : ContinuousOn (fun z : ℂ => a₁ * z) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    continuousOn_const.mul continuousOn_id
  exact (hd.continuousOn.sub (h1z.add hlin)).comp h_inv h_maps

/-- `w ↦ r (1 / w)` is complex differentiable on the open annulus `R < ‖w‖ < R'`, where
`r z = F z - (1 / z + a₁ * z)`. -/
private lemma cci_aux_diff (F : ℂ → ℂ) (a₁ : ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ F {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}) (hR : 1 < R) {R' : ℝ}
    (r : ℂ → ℂ) (hrdef : r = fun z => F z - (1 / z + a₁ * z)) :
    ∀ z ∈ (Metric.ball 0 R' \ Metric.closedBall 0 R) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => r (1 / w)) z := by
  intro z hz
  have hzR : R < ‖z‖ := by
    have h1 : z ∉ Metric.closedBall (0:ℂ) R := hz.1.2
    rw [Metric.mem_closedBall, not_le, dist_zero_right] at h1
    exact h1
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzR; linarith [lt_trans one_pos hR]
  have hS : (1/z) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    have hnorm : ‖(1:ℂ)/z‖ = 1/‖z‖ := by rw [norm_div, norm_one]
    refine ⟨?_, ?_⟩
    · rw [hnorm]; exact one_div_pos.mpr (lt_trans (lt_trans one_pos hR) hzR)
    · rw [hnorm]
      exact lt_of_le_of_lt (one_div_le_one_div_of_le (lt_trans one_pos hR) hzR.le)
        (by rw [div_lt_one (lt_trans one_pos hR)]; exact hR)
  have hSopen : IsOpen {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hFd : DifferentiableAt ℂ F (1/z) := hd.differentiableAt (hSopen.mem_nhds hS)
  have hzne : (1/z) ≠ 0 := by
    have hS' : 0 < ‖(1:ℂ)/z‖ ∧ ‖(1:ℂ)/z‖ < 1 := hS
    intro h; rw [h, norm_zero] at hS'; exact lt_irrefl 0 hS'.1
  have hzinv : DifferentiableAt ℂ (fun w : ℂ => 1/w) z :=
    (differentiableAt_const (c := (1:ℂ))).div differentiableAt_id hz0
  have hr : DifferentiableAt ℂ r (1/z) := by
    rw [hrdef]
    exact hFd.sub (((differentiableAt_const (c := (1:ℂ))).div differentiableAt_id hzne).add
      ((differentiableAt_const (c := a₁)).mul differentiableAt_id))
  exact hr.comp z hzinv

theorem circleIntegralCompInv (F : ℂ → ℂ) (a₁ : ℂ) (C R : ℝ) (hC : 0 ≤ C) (hR : 1 < R)
    (hd : DifferentiableOn ℂ F {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1})
    (hF : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ 1 / R → ‖F z - (1 / z + a₁ * z)‖ ≤ C * ‖z‖ ^ 2) :
    circleIntegral (fun w => F (1 / w)) 0 R = 2 * Real.pi * Complex.I * a₁ := by
  have hR0 : 0 < R := lt_trans one_pos hR
  set r : ℂ → ℂ := fun z => F z - (1 / z + a₁ * z) with hrdef
  -- `r` is continuous on the sphere of radius `R` (it is `F(1/w) - (w + a₁/w)` there)
  have hsphere_sub : Metric.sphere (0:ℂ) R ⊆ Metric.closedBall (0:ℂ) (R + 1) \ Metric.ball (0:ℂ) R := by
    intro w hw
    rw [Metric.mem_sphere, dist_zero_right] at hw
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; linarith
    · rw [Metric.mem_ball, dist_zero_right]; exact not_lt.mpr (le_of_eq hw.symm)
  have hRcont : ContinuousOn (fun w : ℂ => r (1 / w)) (Metric.sphere (0:ℂ) R) :=
    (cci_aux_cont F a₁ R hd hR (by linarith) r hrdef).mono hsphere_sub
  have hRint : CircleIntegrable (fun w : ℂ => r (1 / w)) 0 R :=
    ContinuousOn.circleIntegrable hR0.le hRcont
  -- key vanishing: the integral of `r (1 / w)` over the circle of radius `R` is zero
  have hrho : circleIntegral (fun w : ℂ => r (1 / w)) 0 R = 0 := by
    have hann : ∀ R' : ℝ, R < R' →
        circleIntegral (fun w : ℂ => r (1 / w)) 0 R'
          = circleIntegral (fun w : ℂ => r (1 / w)) 0 R := by
      intro R' hRR'
      exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hR0 hRR'.le
        countable_empty (cci_aux_cont F a₁ R hd hR hRR' r hrdef)
        (cci_aux_diff F a₁ R hd hR r hrdef)
    have hbound : ∀ R' : ℝ, R < R' →
        ‖circleIntegral (fun w : ℂ => r (1 / w)) 0 R'‖ ≤ 2 * Real.pi * C / R' := by
      intro R' hRR'
      have hR'0 : 0 < R' := lt_trans hR0 hRR'
      have hb : ∀ z ∈ Metric.sphere (0:ℂ) R', ‖r (1 / z)‖ ≤ C / R' ^ 2 := by
        intro z hz
        rw [Metric.mem_sphere, dist_zero_right] at hz
        have hnorm : ‖(1:ℂ)/z‖ = 1 / R' := by rw [norm_div, norm_one, hz]
        have h1 : ‖r (1/z)‖ ≤ C * ‖(1:ℂ)/z‖ ^ 2 :=
          hF (1/z) (by rw [hnorm]; exact one_div_pos.mpr hR'0)
            (by rw [hnorm]; exact one_div_le_one_div_of_le hR0 hRR'.le)
        have h2 : C * ‖(1:ℂ)/z‖ ^ 2 = C / R' ^ 2 := by rw [hnorm]; ring
        rwa [h2] at h1
      refine (circleIntegral.norm_integral_le_of_norm_le_const hR'0.le hb).trans (le_of_eq ?_)
      field_simp
    have hM : ∀ R' : ℝ, R < R' →
        ‖circleIntegral (fun w : ℂ => r (1 / w)) 0 R‖ ≤ 2 * Real.pi * C / R' := by
      intro R' hRR'
      rw [← hann R' hRR']
      exact hbound R' hRR'
    have hev : (fun _ : ℝ => ‖circleIntegral (fun w : ℂ => r (1 / w)) 0 R‖)
        ≤ᶠ[Filter.atTop] (fun R' : ℝ => 2 * Real.pi * C / R') := by
      filter_upwards [Filter.eventually_gt_atTop R] with R' hR'
      exact hM R' hR'
    have htend : Filter.Tendsto (fun R' : ℝ => 2 * Real.pi * C / R') Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := 2 * Real.pi * C)
        (f := Filter.atTop)).div_atTop (tendsto_id (α := ℝ))
    have hle : ‖circleIntegral (fun w : ℂ => r (1 / w)) 0 R‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  -- the two explicit integrals
  have hW : CircleIntegrable (fun w : ℂ => w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le continuousOn_id
  have hAcont : ContinuousOn (fun w : ℂ => a₁ / w) (Metric.sphere (0:ℂ) R) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro w hw
    rw [Metric.mem_sphere, dist_zero_right] at hw
    intro h
    have hw0 : w = 0 := h
    rw [hw0, norm_zero] at hw
    linarith
  have hA : CircleIntegrable (fun w : ℂ => a₁ / w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le hAcont
  have hW_val : circleIntegral (fun w : ℂ => w) 0 R = 0 := by
    simpa using circleIntegral.integral_sub_zpow_of_ne (n := (1:ℤ)) (by norm_num) (0:ℂ) (0:ℂ) R
  have hA_val : circleIntegral (fun w : ℂ => a₁ / w) 0 R = 2 * Real.pi * Complex.I * a₁ := by
    have h1 : circleIntegral (fun w : ℂ => a₁ / w) 0 R
        = a₁ * circleIntegral (fun w : ℂ => (w - 0)⁻¹) 0 R := by
      rw [← circleIntegral.integral_const_mul (a₁) (fun w : ℂ => (w - 0)⁻¹) 0 R]
      apply circleIntegral.integral_congr (c := 0) (R := R) hR0.le
      intro z hz
      simp [div_eq_mul_inv]
    rw [h1, circleIntegral.integral_sub_center_inv 0 hR0.ne']
    ring
  -- assemble
  have hdecomp : circleIntegral (fun w : ℂ => F (1 / w)) 0 R
      = circleIntegral (fun w : ℂ => w + a₁ / w) 0 R
        + circleIntegral (fun w : ℂ => r (1 / w)) 0 R :=
    calc circleIntegral (fun w : ℂ => F (1 / w)) 0 R
        = circleIntegral (fun w : ℂ => (w + a₁ / w) + r (1 / w)) 0 R := by
          apply circleIntegral.integral_congr hR0.le
          intro w hw
          rw [hrdef]
          simp only [one_div_one_div]
          ring
      _ = circleIntegral (fun w : ℂ => w + a₁ / w) 0 R
            + circleIntegral (fun w : ℂ => r (1 / w)) 0 R :=
          circleIntegral.integral_add (hW.add hA) hRint
  have hsplit : circleIntegral (fun w : ℂ => w + a₁ / w) 0 R
      = circleIntegral (fun w : ℂ => w) 0 R + circleIntegral (fun w : ℂ => a₁ / w) 0 R :=
    circleIntegral.integral_add hW hA
  rw [hdecomp, hsplit, hW_val, hA_val, hrho]
  ring

end Work.LandLeaves
