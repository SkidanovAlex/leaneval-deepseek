import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Area

open Complex Metric

open scoped Topology

/-- The logarithmic derivative of a holomorphic function with exactly one simple zero inside a
circle has circle integral `2πi`: this is the argument principle in the special case of a single
simple zero. -/
theorem circleIntegral_deriv_div_eq_two_pi_I {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) {p : ℂ} (hp : p ∈ Metric.ball 0 R) (hp0 : h p = 0)
    (hpderiv : deriv h p ≠ 0) (huniq : ∀ w ∈ Metric.closedBall 0 R, h w = 0 → w = p) :
    circleIntegral (fun w => deriv h w / h w) 0 R = 2 * Real.pi * Complex.I := by
  have hpn : ‖p‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hp
  set g : ℂ → ℂ := dslope h p with hgdef
  have hp1 : p ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
  have hp_nhds : Metric.ball (0 : ℂ) 1 ∈ 𝓝 p := isOpen_ball.mem_nhds hp1
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    rw [hgdef]
    exact (Complex.differentiableOn_dslope hp_nhds).2 hh
  have hgan : AnalyticOnNhd ℂ g (Metric.ball 0 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2 hg_diff
  have hgdan : AnalyticOnNhd ℂ (deriv g) (Metric.ball 0 1) := hgan.deriv_of_isOpen isOpen_ball
  have hgdan_d : DifferentiableOn ℂ (deriv g) (Metric.ball 0 1) := hgdan.differentiableOn
  have hgan_d : DifferentiableOn ℂ g (Metric.ball 0 1) := hgan.differentiableOn
  have hgp : g p = deriv h p := by rw [hgdef]; exact dslope_same h p
  have hg_ne : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
    intro z hz hz0
    by_cases hzp : z = p
    · rw [hzp] at hz0
      exact hpderiv (hgp ▸ hz0)
    · have hz0' : h z = 0 := by
        have h1 : (z - p) * g z = h z := by
          rw [hgdef]; simpa using sub_smul_dslope_of_zero hp0 z
        rw [← h1, hz0, mul_zero]
      exact absurd (huniq z hz hz0') hzp
  -- differentiability / continuity of `deriv g / g`
  have hphi_diff : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball 0 R) :=
    (hgdan_d.mono (Metric.ball_subset_ball hR1.le)).div (hgan_d.mono (Metric.ball_subset_ball hR1.le))
      (fun z hz => hg_ne z (Metric.ball_subset_closedBall hz))
  have hphi_cont : ContinuousOn (fun z => deriv g z / g z) (Metric.closedBall 0 R) :=
    (hgdan_d.continuousOn.mono (Metric.closedBall_subset_ball hR1)).div
      (hgan_d.continuousOn.mono (Metric.closedBall_subset_ball hR1)) (fun z hz => hg_ne z hz)
  have hphi : DiffContOnCl ℂ (fun z => deriv g z / g z) (Metric.ball 0 R) := by
    refine DiffContOnCl.mk hphi_diff ?_
    rw [closure_ball _ hR.ne']
    exact hphi_cont
  have hzero : circleIntegral (fun z => deriv g z / g z) 0 R = 0 :=
    DiffContOnCl.circleIntegral_eq_zero hR.le hphi
  -- the pointwise decomposition on the circle
  have hprod : h = fun w => (w - p) * g w := by
    funext w
    rw [hgdef]
    simpa using (sub_smul_dslope_of_zero hp0 w).symm
  have hkey : Set.EqOn (fun z => deriv h z / h z) (fun z => (z - p)⁻¹ + deriv g z / g z)
      (Metric.sphere 0 R) := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.closedBall_subset_ball hR1 (Metric.sphere_subset_closedBall hz)
    have hzp : z ≠ p := by
      intro hzp
      have hzR : ‖p‖ = R := by
        rw [hzp] at hz
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      linarith
    have hgzd : DifferentiableAt ℂ g z := hgan_d.differentiableAt (isOpen_ball.mem_nhds hz1)
    have hderiv : deriv h z = g z + (z - p) * deriv g z := by
      have hd : HasDerivAt (fun w => (w - p) * g w) (1 * g z + (z - p) * deriv g z) z :=
        ((hasDerivAt_id z).sub_const p).mul hgzd.hasDerivAt
      rw [hprod]
      have hthis : deriv (fun w => (w - p) * g w) z = 1 * g z + (z - p) * deriv g z := hd.deriv
      rw [hthis]
      ring
    have hz_ne_g : g z ≠ 0 := hg_ne z (Metric.sphere_subset_closedBall hz)
    have hzh : h z = (z - p) * g z := congrFun hprod z
    change deriv h z / h z = (z - p)⁻¹ + deriv g z / g z
    rw [hderiv, hzh]
    have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
    field_simp
  -- integrability and assembly
  have hA : CircleIntegrable (fun z => (z - p)⁻¹) 0 R := by
    rw [circleIntegrable_sub_inv_iff]
    right
    intro hmem
    have : ‖p‖ = |R| := by simpa [Metric.mem_sphere, dist_eq_norm] using hmem
    rw [abs_of_pos hR] at this
    linarith
  have hB : CircleIntegrable (fun z => deriv g z / g z) 0 R :=
    ContinuousOn.circleIntegrable hR.le (hphi_cont.mono (Metric.sphere_subset_closedBall))
  rw [circleIntegral.integral_congr hR.le hkey,
    circleIntegral.integral_add hA hB,
    circleIntegral.integral_sub_inv_of_mem_ball hp, hzero, add_zero]

end Work.Area
