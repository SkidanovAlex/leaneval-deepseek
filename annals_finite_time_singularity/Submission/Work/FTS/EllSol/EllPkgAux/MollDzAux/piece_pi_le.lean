import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

/-- Support estimate for the reflected branch of the `θ`-convolution: with `ρ` bounded by `M`
and vanishing outside `(-ε, ε)`, and `ε ≤ 1/2`, `θ ∈ (-1/4, π/2 + 1/4)`, the integrand
`t ↦ |ρ (θ + t - π)| |g t|` is supported in `(π - θ - ε, π/2) ⊂ (0, π/2)`, so

`∫_{t < π/2} |ρ (θ + t - π)| |g t| ≤ M ∫_{[0, π/2]} |g t|`. -/
theorem piece_pi_le {ρ g : ℝ → ℝ} (hρc : Continuous ρ) {ε M θ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, |ρ x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → ρ x = 0)
    (hg : ContinuousOn g (Set.Icc 0 (Real.pi / 2)))
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    ∫ t in Set.Iio (Real.pi / 2), |ρ (θ + t - Real.pi)| * |g t|
      ≤ M * ∫ t in Set.Icc (0 : ℝ) (Real.pi / 2), |g t| := by
  -- `a := π - θ - ε` is the left edge of the support of `t ↦ ρ (θ + t - π)`, and it is positive.
  set a : ℝ := Real.pi - θ - ε with ha
  set c : ℝ := Real.pi / 2 with hc
  have ha_pos : 0 < a := by
    rw [ha]; linarith [hθ.2, hε1, Real.pi_gt_three]
  have ha_nn : 0 ≤ a := le_of_lt ha_pos
  -- the integrand vanishes to the left of `a`
  have hzero : ∀ t : ℝ, t < a → |ρ (θ + t - Real.pi)| * |g t| = 0 := by
    intro t ht
    have hpos : 0 < Real.pi - θ - t := by rw [ha] at ht; linarith
    have hx : ε < |θ + t - Real.pi| := by
      rw [show θ + t - Real.pi = -(Real.pi - θ - t) by ring, abs_neg, abs_of_pos hpos]
      linarith
    rw [hvan _ hx, abs_zero, zero_mul]
  -- hence the integral over `(-∞, π/2)` is the integral over `[a, π/2)`
  have hmain : ∫ t in Set.Iio c, |ρ (θ + t - Real.pi)| * |g t|
      = ∫ t in Set.Ico a c, |ρ (θ + t - Real.pi)| * |g t| := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iio ?_ ?_
    · intro t ht; exact ht.2
    · intro t ht
      exact hzero t (by by_contra h; exact ht.2 ⟨le_of_not_gt h, ht.1⟩)
  have hico : ∫ t in Set.Ico a c, |ρ (θ + t - Real.pi)| * |g t|
      = ∫ t in Set.Icc a c, |ρ (θ + t - Real.pi)| * |g t| :=
    (MeasureTheory.integral_Icc_eq_integral_Ico).symm
  -- integrability on the compact interval `[a, c]`
  have hcontF : ContinuousOn (fun t : ℝ => |ρ (θ + t - Real.pi)| * |g t|) (Set.Icc a c) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((hρc.comp ((continuous_const.add continuous_id).sub continuous_const)).abs).continuousOn
    · exact hg.abs.mono (Set.Icc_subset_Icc_left ha_nn)
  have hInt1 : IntegrableOn (fun t : ℝ => |ρ (θ + t - Real.pi)| * |g t|) (Set.Icc a c) volume :=
    hcontF.integrableOn_compact isCompact_Icc
  have hcont2 : ContinuousOn (fun t : ℝ => M * |g t|) (Set.Icc a c) :=
    continuousOn_const.mul (hg.abs.mono (Set.Icc_subset_Icc_left ha_nn))
  have hInt2 : IntegrableOn (fun t : ℝ => M * |g t|) (Set.Icc a c) volume :=
    hcont2.integrableOn_compact isCompact_Icc
  -- pointwise domination by `M * |g|`
  have hmono : ∫ t in Set.Icc a c, |ρ (θ + t - Real.pi)| * |g t|
      ≤ ∫ t in Set.Icc a c, M * |g t| :=
    MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Icc
      (fun t _ => mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _))
  have hMout : ∫ t in Set.Icc a c, M * |g t| = M * ∫ t in Set.Icc a c, |g t| := by
    rw [MeasureTheory.integral_const_mul]
  -- and `[a, c] ⊆ [0, c]`
  have hset : ∫ t in Set.Icc a c, |g t| ≤ ∫ t in Set.Icc 0 c, |g t| := by
    refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
    · exact (hg.abs.mono (Set.Icc_subset_Icc_left (le_refl (0 : ℝ)))).integrableOn_compact
        isCompact_Icc
    · filter_upwards with x using abs_nonneg (g x)
    · filter_upwards with x hx using ⟨le_trans ha_nn hx.1, hx.2⟩
  calc ∫ t in Set.Iio (Real.pi / 2), |ρ (θ + t - Real.pi)| * |g t|
      = ∫ t in Set.Ico a c, |ρ (θ + t - Real.pi)| * |g t| := hmain
    _ = ∫ t in Set.Icc a c, |ρ (θ + t - Real.pi)| * |g t| := hico
    _ ≤ ∫ t in Set.Icc a c, M * |g t| := hmono
    _ = M * ∫ t in Set.Icc a c, |g t| := hMout
    _ ≤ M * ∫ t in Set.Icc 0 c, |g t| := mul_le_mul_of_nonneg_left hset hM0

end Work.FTS.EllSol.EllPkgAux.MollDzAux
