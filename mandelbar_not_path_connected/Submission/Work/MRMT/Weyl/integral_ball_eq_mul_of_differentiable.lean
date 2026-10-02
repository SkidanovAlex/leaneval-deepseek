import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Weyl

open MeasureTheory Complex Metric Real Set Function Filter

noncomputable section

/-- **Circle mean value property, `(-π, π)` form.** For an entire function `g`, the integral of
`g` over the circle of centre `c` and radius `r`, parametrised by `θ ∈ (-π, π)` via the circle map,
equals `2π • g c`. This is the standard circle mean value property
(`DiffContOnCl.circleAverage`) together with `2π`-periodicity of `θ ↦ g (circleMap c r θ)`. -/
theorem integral_Ioo_circleMap_eq_of_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (c : ℂ) (r : ℝ) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap c r θ) = (2 * Real.pi : ℝ) • g c := by
  have hcirc : Real.circleAverage g c r = g c :=
    (hg.diffContOnCl (s := Metric.ball c |r|)).circleAverage
  have htwo : ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap c r θ) = (2 * Real.pi : ℝ) • g c := by
    rw [Real.circleAverage_def] at hcirc
    have h2 := congrArg (fun x : ℂ => (2 * Real.pi : ℝ) • x) hcirc
    rwa [smul_inv_smul₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)] at h2
  have hper : Function.Periodic (fun θ => g (circleMap c r θ)) (2 * Real.pi) :=
    (periodic_circleMap c r).comp g
  have hshift : ∫ θ in (-Real.pi)..Real.pi, g (circleMap c r θ) =
      ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap c r θ) := by
    have h1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have h2 : (0:ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
    simpa only [h1, h2] using hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      hshift, htwo]

/-- The point of the slit plane at polar coordinates `(r, θ)` lies on the circle map:
`c + polarCoord.symm (r, θ) = circleMap c r θ`. -/
theorem add_polarCoord_symm_eq_circleMap (c : ℂ) (r θ : ℝ) :
    c + Complex.polarCoord.symm (r, θ) = circleMap c r θ := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin]

/-- **Mean value property, ball (area) form.** An entire function equals its average over any ball:
`∫ z in ball c R, g z = (π R²) * g c`.

Proof route (all ingredients in Mathlib): `circleAverage`/`DiffContOnCl.circleAverage` gives the
*circle* mean value `∫ θ in 0..2π, g (c + R e^{iθ}) = 2π * g c`; polar coordinates
(`Complex.integral_comp_polarCoord_symm`, applied to `w ↦ g (c + w) * 1_{‖w‖ < R}` and Fubini)
convert `∫_{ball c R} g` into `∫_0^R r * (∫_{-π}^{π} g (c + r e^{iθ}) dθ) dr`; the inner integral is
`2π * g c` by the circle mean value (the interval `(-π, π)` vs `[0, 2π]` is handled by
`2π`-periodicity). -/
theorem integral_ball_eq_mul_of_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    ∫ z in Metric.ball c R, g z = ((Real.pi * R ^ 2 : ℝ) : ℂ) * g c := by
  classical
  -- circle mean value in the `(-π, π)` parametrisation
  have hcirc : ∀ r : ℝ, ∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap c r θ)
      = (2 * Real.pi : ℝ) • g c := fun r =>
    integral_Ioo_circleMap_eq_of_differentiable hg c r
  -- translate the ball to be centred at the origin
  have htrans : ∫ z in Metric.ball c R, g z = ∫ w in Metric.ball 0 R, g (c + w) := by
    have h3 : (fun w => (Metric.ball c R).indicator g (c + w))
        = (fun w => (Metric.ball 0 R).indicator (fun w => g (c + w)) w) := by
      funext w
      rw [Set.indicator_apply, Set.indicator_apply]
      congr 1
      rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, add_sub_cancel_left, sub_zero]
    rw [← integral_indicator measurableSet_ball,
        ← integral_add_left_eq_self ((Metric.ball c R).indicator g) c, h3]
    exact integral_indicator measurableSet_ball
  -- the centred integrand, cut off outside the ball
  set F : ℂ → ℂ := (Metric.ball (0:ℂ) R).indicator (fun w => g (c + w)) with hF
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn
    ((hg.continuous.comp (continuous_const.add continuous_id)).continuousOn)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self hR.le))
  have hFbound : ∀ z, ‖F z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ Metric.ball (0:ℂ) R
    · rw [hF, Set.indicator_of_mem hz]
      exact hM z (Metric.ball_subset_closedBall hz)
    · rw [hF, Set.indicator_of_notMem hz, norm_zero]
      exact hM0
  have hFzero : ∀ z, R ≤ ‖z‖ → F z = 0 := by
    intro z hz
    rw [hF, Set.indicator_of_notMem]
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact not_lt.mpr hz
  have hFint : ∫ w in Metric.ball 0 R, g (c + w) = ∫ w, F w := by
    rw [hF]
    exact (integral_indicator measurableSet_ball).symm
  -- polar change of variables
  have hpolar : ∫ w, F w = ∫ p in Complex.polarCoord.target, p.1 • F (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm F).symm
  have hbox_sub : Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ Complex.polarCoord.target := by
    intro p hp
    rw [Complex.polarCoord_target]
    exact ⟨hp.1.1, hp.2⟩
  have hφzero : ∀ p ∈ Complex.polarCoord.target,
      p ∉ Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi →
      p.1 • F (Complex.polarCoord.symm p) = 0 := by
    intro p ht hb
    rw [Complex.polarCoord_target] at ht
    have h1 : (0:ℝ) < p.1 := ht.1
    have h2 : R ≤ p.1 := by
      by_contra h
      exact hb ⟨⟨h1, not_le.mp h⟩, ht.2⟩
    have h3 : R ≤ ‖Complex.polarCoord.symm p‖ := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos h1]; exact h2
    rw [hFzero _ h3, smul_zero]
  -- since `F` is supported in the ball, the polar integral lives on the box `(0,R) × (-π,π)`
  have hbox : ∫ p in Complex.polarCoord.target, p.1 • F (Complex.polarCoord.symm p)
      = ∫ p in Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 • F (Complex.polarCoord.symm p) := by
    rw [← integral_indicator Complex.polarCoord.open_target.measurableSet,
        ← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    congr 1
    funext p
    by_cases hb : p ∈ Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem (hbox_sub hb), Set.indicator_of_mem hb]
    · by_cases ht : p ∈ Complex.polarCoord.target
      · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hb]
        exact hφzero p ht hb
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hb]
  have hFmeas : Measurable F := by
    rw [hF]
    exact ((hg.continuous.comp (continuous_const.add continuous_id)).measurable).indicator
      measurableSet_ball
  have hsymm_meas : Measurable Complex.polarCoord.symm := by
    have h' : Complex.polarCoord.symm
        = fun p : ℝ × ℝ => p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
      funext Complex.polarCoord_symm_apply
    rw [h']
    fun_prop
  have hφint : IntegrableOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (R * M) ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · exact (measurable_fst.smul (hFmeas.comp hsymm_meas)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
        with p hp
      have hp1 : p.1 ∈ Set.Ioo (0:ℝ) R := hp.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp1.1]
      calc p.1 * ‖F (Complex.polarCoord.symm p)‖
          ≤ p.1 * M := mul_le_mul_of_nonneg_left (hFbound _) hp1.1.le
        _ ≤ R * M := mul_le_mul_of_nonneg_right hp1.2.le hM0
  -- Fubini
  have hFubini : ∫ p in Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • F (Complex.polarCoord.symm p)
      = ∫ r in Set.Ioo (0:ℝ) R, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • F (Complex.polarCoord.symm (r, θ)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, MeasureTheory.setIntegral_prod _ hφint]
  -- inner integral: the circle mean value
  have hinner : ∀ r ∈ Set.Ioo (0:ℝ) R,
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, r • F (Complex.polarCoord.symm (r, θ))
        = r • ((2 * Real.pi : ℝ) • g c) := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hsymm_in : ∀ θ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0:ℂ) R := by
      intro θ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
        abs_of_pos hrpos]
      exact hr.2
    have heq : (fun θ => r • F (Complex.polarCoord.symm (r, θ)))
        = fun θ => r • g (circleMap c r θ) := by
      funext θ
      rw [hF, Set.indicator_of_mem (hsymm_in θ), add_polarCoord_symm_eq_circleMap]
    rw [heq, MeasureTheory.integral_smul, hcirc r]
  -- outer integral: `∫_0^R r · 2π = π R²`
  have houter : ∫ r in Set.Ioo (0:ℝ) R, r • ((2 * Real.pi : ℝ) • g c)
      = ((Real.pi * R ^ 2 : ℝ) : ℂ) * g c := by
    have h1 : ∫ r in Set.Ioo (0:ℝ) R, r • ((2 * Real.pi : ℝ) • g c)
        = ∫ r in Set.Ioo (0:ℝ) R, (2 * Real.pi * r) • g c := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro r _
      show r • ((2 * Real.pi : ℝ) • g c) = (2 * Real.pi * r) • g c
      rw [smul_smul]
      congr 1
      ring
    rw [h1, integral_smul_const]
    have hid : ∫ r in Set.Ioo (0:ℝ) R, 2 * Real.pi * r = Real.pi * R ^ 2 := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_const_mul,
          integral_id]
      ring
    rw [hid]
    exact RCLike.real_smul_eq_coe_mul _ _
  calc ∫ z in Metric.ball c R, g z
      = ∫ w in Metric.ball 0 R, g (c + w) := htrans
    _ = ∫ w, F w := hFint
    _ = ∫ p in Complex.polarCoord.target, p.1 • F (Complex.polarCoord.symm p) := hpolar
    _ = ∫ p in Set.Ioo (0:ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 • F (Complex.polarCoord.symm p) := hbox
    _ = ∫ r in Set.Ioo (0:ℝ) R, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • F (Complex.polarCoord.symm (r, θ)) := hFubini
    _ = ∫ r in Set.Ioo (0:ℝ) R, r • ((2 * Real.pi : ℝ) • g c) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hinner
    _ = ((Real.pi * R ^ 2 : ℝ) : ℂ) * g c := houter

end

end Work.MRMT.Weyl
