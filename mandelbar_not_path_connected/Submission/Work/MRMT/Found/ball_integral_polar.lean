import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Complex Metric Real Set Function Filter

theorem ball_integral_polar {f : ℂ → ℝ} (hf : Continuous f) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in Metric.ball (0 : ℂ) R, f z)
      = ∫ ρ in (0 : ℝ)..R, ρ * (∫ θ in (-Real.pi)..Real.pi,
          f (ρ * Complex.exp (θ * Complex.I))) := by
  classical
  -- the integrand cut off outside the ball
  set F : ℂ → ℝ := (Metric.ball (0 : ℂ) R).indicator f with hF
  -- a uniform bound `M` for `F`
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self hR))
  have hFbound : ∀ z, ‖F z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : ℂ) R
    · rw [hF, Set.indicator_of_mem hz]
      exact hM z (Metric.ball_subset_closedBall hz)
    · rw [hF, Set.indicator_of_notMem hz, norm_zero]
      exact hM0
  have hFzero : ∀ z, R ≤ ‖z‖ → F z = 0 := by
    intro z hz
    rw [hF, Set.indicator_of_notMem]
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact not_lt.mpr hz
  have hFint : ∫ z in Metric.ball (0 : ℂ) R, f z = ∫ z, F z := by
    rw [hF]
    exact (integral_indicator measurableSet_ball).symm
  -- polar change of variables
  have hpolar : ∫ z, F z = ∫ p in Complex.polarCoord.target,
      p.1 • F (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm F).symm
  have hbox_sub : Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆
      Complex.polarCoord.target := by
    intro p hp
    rw [Complex.polarCoord_target]
    exact ⟨hp.1.1, hp.2⟩
  have hφzero : ∀ p ∈ Complex.polarCoord.target,
      p ∉ Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi →
      p.1 • F (Complex.polarCoord.symm p) = 0 := by
    intro p ht hb
    rw [Complex.polarCoord_target] at ht
    have h1 : (0 : ℝ) < p.1 := ht.1
    have h2 : R ≤ p.1 := by
      by_contra h
      exact hb ⟨⟨h1, not_le.mp h⟩, ht.2⟩
    have h3 : R ≤ ‖Complex.polarCoord.symm p‖ := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos h1]; exact h2
    rw [hFzero _ h3, smul_zero]
  -- since `F` is supported in the ball, the polar integral lives on the box `(0,R) × (-π,π)`
  have hbox : ∫ p in Complex.polarCoord.target, p.1 • F (Complex.polarCoord.symm p)
      = ∫ p in Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 • F (Complex.polarCoord.symm p) := by
    rw [← integral_indicator Complex.polarCoord.open_target.measurableSet,
        ← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    congr 1
    funext p
    by_cases hb : p ∈ Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem (hbox_sub hb), Set.indicator_of_mem hb]
    · by_cases ht : p ∈ Complex.polarCoord.target
      · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hb]
        exact hφzero p ht hb
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hb]
  have hFmeas : Measurable F := by
    rw [hF]
    exact hf.measurable.indicator measurableSet_ball
  have hsymm_meas : Measurable Complex.polarCoord.symm := by
    have h' : Complex.polarCoord.symm
        = fun p : ℝ × ℝ => p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
      funext Complex.polarCoord_symm_apply
    rw [h']
    fun_prop
  have hφint : IntegrableOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (R * M) ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · exact (measurable_fst.smul (hFmeas.comp hsymm_meas)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
      have hp1 : p.1 ∈ Set.Ioo (0 : ℝ) R := hp.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp1.1]
      calc p.1 * ‖F (Complex.polarCoord.symm p)‖
          ≤ p.1 * M := mul_le_mul_of_nonneg_left (hFbound _) hp1.1.le
        _ ≤ R * M := mul_le_mul_of_nonneg_right hp1.2.le hM0
  -- Fubini
  have hFubini : ∫ p in Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • F (Complex.polarCoord.symm p)
      = ∫ r in Set.Ioo (0 : ℝ) R, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • F (Complex.polarCoord.symm (r, θ)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, MeasureTheory.setIntegral_prod _ hφint]
  -- the inner integral is the circle integral of `f`
  have hinner : ∀ r ∈ Set.Ioo (0 : ℝ) R,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi, r • F (Complex.polarCoord.symm (r, θ)))
        = r * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            f (r * Complex.exp (θ * Complex.I))) := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hsymm_in : ∀ θ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) R := by
      intro θ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
        abs_of_pos hrpos]
      exact hr.2
    have heq : (fun θ => F (Complex.polarCoord.symm (r, θ)))
        = fun θ : ℝ => f (r * Complex.exp ((θ : ℂ) * Complex.I)) := by
      funext θ
      rw [hF, Set.indicator_of_mem (hsymm_in θ)]
      congr 1
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
      simp
    rw [MeasureTheory.integral_smul, heq]
    rfl
  -- convert the iterated integral to the interval-integral form of the statement
  have hstep : (∫ r in Set.Ioo (0 : ℝ) R, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r • F (Complex.polarCoord.symm (r, θ)))
      = ∫ ρ in (0 : ℝ)..R, ρ * (∫ θ in (-Real.pi)..Real.pi,
          f (ρ * Complex.exp (θ * Complex.I))) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hinner]
    have hin2 : ∀ r : ℝ,
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, f (r * Complex.exp (θ * Complex.I)))
          = ∫ θ in (-Real.pi)..Real.pi, f (r * Complex.exp (θ * Complex.I)) := by
      intro r
      rw [intervalIntegral.integral_of_le
            (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun r _ => by rw [hin2 r])]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR]
  calc ∫ z in Metric.ball (0 : ℂ) R, f z
      = ∫ z, F z := hFint
    _ = ∫ p in Complex.polarCoord.target, p.1 • F (Complex.polarCoord.symm p) := hpolar
    _ = ∫ p in Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 • F (Complex.polarCoord.symm p) := hbox
    _ = ∫ r in Set.Ioo (0 : ℝ) R, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • F (Complex.polarCoord.symm (r, θ)) := hFubini
    _ = ∫ ρ in (0 : ℝ)..R, ρ * (∫ θ in (-Real.pi)..Real.pi,
          f (ρ * Complex.exp (θ * Complex.I))) := hstep

end Work.MRMT.Found
