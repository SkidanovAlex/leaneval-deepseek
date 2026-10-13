import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open MeasureTheory Set

/-- The contribution of the "negative" angular piece of a mollification kernel: for a bump `ρ`
supported in `[-ε,ε]` with `|ρ| ≤ M`, the `θ`-shifted weight `t ↦ |ρ (θ + t)|` may be compared
with the indicator of `[0, π/2]`, because for `θ > -1/4`, `ε ≤ 1/2` and `t > π/2` one has
`θ + t > π/2 - 1/4 > ε`, so `ρ (θ + t) = 0` there. -/
theorem piece_neg_le {ρ g : ℝ → ℝ} (hρc : Continuous ρ) {ε M θ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, |ρ x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → ρ x = 0)
    (hg : ContinuousOn g (Set.Icc 0 (Real.pi / 2)))
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    ∫ t in Set.Ioi (0 : ℝ), |ρ (θ + t)| * |g t| ≤ M * ∫ t in Set.Icc (0 : ℝ) (Real.pi / 2), |g t| := by
  set F : ℝ → ℝ := fun t => |ρ (θ + t)| * |g t| with hF
  -- The integrand vanishes for `t > π/2`, so the integral over `Ioi 0` is the one over `Ioc 0 (π/2)`.
  have hstep1 : ∫ t in Set.Ioi (0:ℝ), F t = ∫ t in Set.Ioc (0:ℝ) (Real.pi / 2), F t := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
    · exact Set.Ioc_subset_Ioi_self
    · intro t ht
      have ht0 : 0 < t := ht.1
      have htpi : Real.pi / 2 < t := by
        by_contra hle
        exact ht.2 ⟨ht0, not_lt.mp hle⟩
      have h1 : ε < θ + t := by linarith [hθ.1, hε1, htpi, Real.pi_gt_three]
      have h2 : 0 < θ + t := by linarith [hε0, h1]
      have habs : |θ + t| = θ + t := abs_of_pos h2
      have hrho : ρ (θ + t) = 0 := hvan (θ + t) (by rw [habs]; exact h1)
      simp [hF, hrho]
  -- Integrability bookkeeping on `Ioc 0 (π/2)`.
  have hcontF : ContinuousOn F (Set.Icc 0 (Real.pi/2)) := by
    have h1 : Continuous fun t => |ρ (θ + t)| := (hρc.comp (continuous_const.add continuous_id)).abs
    exact h1.continuousOn.mul hg.abs
  have hFint : IntegrableOn F (Set.Ioc 0 (Real.pi/2)) :=
    (hcontF.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hgabsint : IntegrableOn (fun t => |g t|) (Set.Icc 0 (Real.pi/2)) := hg.abs.integrableOn_Icc
  have hMgint : IntegrableOn (fun t => M * |g t|) (Set.Ioc 0 (Real.pi/2)) :=
    (hgabsint.mono_set Set.Ioc_subset_Icc_self).const_mul M
  -- Pointwise domination `F ≤ M |g|` on `Ioc 0 (π/2)`.
  have hstep2 : ∫ t in Set.Ioc 0 (Real.pi/2), F t ≤ ∫ t in Set.Ioc 0 (Real.pi/2), M * |g t| := by
    refine setIntegral_mono_ae_restrict hFint hMgint ?_
    filter_upwards with t
    rw [hF]
    exact mul_le_mul_of_nonneg_right (hM (θ+t)) (abs_nonneg _)
  have hstep3 : ∫ t in Set.Ioc 0 (Real.pi/2), M * |g t| = M * ∫ t in Set.Ioc 0 (Real.pi/2), |g t| := by
    rw [MeasureTheory.integral_const_mul]
  -- Enlarge the integration set from `Ioc 0 (π/2)` to `Icc 0 (π/2)`.
  have hstep4 : ∫ t in Set.Ioc 0 (Real.pi/2), |g t| ≤ ∫ t in Set.Icc 0 (Real.pi/2), |g t| := by
    refine setIntegral_mono_set hgabsint ?_ ?_
    · filter_upwards with t using abs_nonneg (g t)
    · filter_upwards with t ht using Set.Ioc_subset_Icc_self ht
  calc ∫ t in Set.Ioi (0:ℝ), |ρ (θ + t)| * |g t|
      = ∫ t in Set.Ioi (0:ℝ), F t := rfl
    _ = ∫ t in Set.Ioc 0 (Real.pi/2), F t := hstep1
    _ ≤ ∫ t in Set.Ioc 0 (Real.pi/2), M * |g t| := hstep2
    _ = M * ∫ t in Set.Ioc 0 (Real.pi/2), |g t| := hstep3
    _ ≤ M * ∫ t in Set.Icc 0 (Real.pi/2), |g t| := mul_le_mul_of_nonneg_left hstep4 hM0

end Work.FTS.EllSol.EllPkgAux.MollDzAux
