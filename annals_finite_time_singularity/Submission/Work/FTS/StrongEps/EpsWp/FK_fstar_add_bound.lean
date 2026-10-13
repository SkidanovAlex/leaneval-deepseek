import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular moment of `F_* + f` is bounded by `B + 1` when `FK f` is bounded by `B`

`FK F z = ∫_θ F(z,θ)·K(θ) dθ` is the angular moment `(F,K)_{L²_θ}(z)` of the paper
(`Work.Construction.FK`).  Here we show that adding the fundamental profile `F_*` to a
perturbation `f` whose angular moment is bounded by `B` only increases the bound by the
(explicit) constant `sup_z |FK F_* z| ≤ 1`.

The mathematics is the linearity of `FK` in its argument together with the computation
`FK F_* = α·2z/(1+z)²` (`Work.FTS.Nonlinear.FstarPkg.FK_Fstar`):

* on `Iθ = [0,π/2]`, `(F_* + f)·K = F_*·K + f·K` pointwise, so the integrand splits;
* the profile part `F_*·K = (α·F_*(z)/c(α))·(Γ·K)` is a constant multiple of the continuous
  function `Γ·K`, hence integrable on the compact `Iθ`;
* if the sum of the two integrands is integrable, `MeasureTheory.integral_add` splits the
  integral and the triangle inequality plus `FK_Fstar` bound the profile contribution by
  `1` and the `f`-contribution by `B`;
* if it is not integrable, the Bochner integral is `0` (`MeasureTheory.integral_undef`) and
  the claim reduces to `0 ≤ B + 1`.

The bound on the profile is sharp: `|α·2z/(1+z)²| ≤ 1` for `0 < α ≤ 1` and `z ≥ 0`, since
`0 ≤ 2z/(1+z)² ≤ 1` (`2z ≤ (1+z)² = 1 + 2z + z²`).
-/

namespace Work.FTS.StrongEps.EpsWp

open MeasureTheory

theorem FK_fstar_add_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    (hfk : ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Construction.FK f z| ≤ B) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z| ≤ B + 1 := by
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  -- the profile part and the perturbation part of the integrand of `FK (F_* + f) z`
  set a : ℝ → ℝ := fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ with ha
  set cl : ℝ → ℝ := fun θ => f z θ * Work.Spaces.K θ with hcl
  -- `Γ·K` is continuous on the compact `Iθ`, hence integrable
  have hGamK : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
    have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
      (Real.continuous_sin.continuousOn).mul ((Real.continuous_cos.continuousOn).pow 2)
    have hGam : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
      show ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Work.Spaces.Iθ
      exact hbase.rpow_const (fun θ _ => Or.inr (div_nonneg hα.le (by norm_num)))
    have hK : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ) Work.Spaces.Iθ := by
      show ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
      fun_prop
    exact (hGam.mul hK).integrableOn_Icc
  -- hence so is the profile part `F_*·K`, a constant multiple of `Γ·K`
  have ha_eq : a = fun θ => (α * Work.FM.Fstar z / Work.Spaces.c α)
      * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    funext θ
    simp only [ha, Work.Construction.Fstar]
    ring
  have hAint : Integrable a (volume.restrict Work.Spaces.Iθ) := by
    rw [ha_eq]
    exact hGamK.const_mul _
  -- the integrand of `FK (F_* + f) z` is `a + cl` on `Iθ`
  have hgoal : Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = ∫ θ in Work.Spaces.Iθ, (a θ + cl θ) := by
    rw [Work.Construction.FK]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    simp only [ha, hcl]
    ring
  rw [hgoal]
  by_cases hint : Integrable (fun θ => a θ + cl θ) (volume.restrict Work.Spaces.Iθ)
  · -- integrable case: split the integral, bound the two pieces separately
    have hclInt : Integrable cl (volume.restrict Work.Spaces.Iθ) := by
      refine (hint.sub hAint).congr ?_
      filter_upwards with θ
      simp only [Pi.sub_apply]
      ring
    rw [MeasureTheory.integral_add hAint hclInt]
    have hAval : ∫ θ in Work.Spaces.Iθ, a θ = α * (2 * z / (1 + z) ^ 2) := by
      rw [ha]
      exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1
    have hCval : ∫ θ in Work.Spaces.Iθ, cl θ = Work.Construction.FK f z := by
      rw [hcl]
      rfl
    rw [hAval, hCval]
    -- `|α·2z/(1+z)²| ≤ 1`
    have hden : 0 < (1 + z) ^ 2 := pow_pos (by linarith [hz0]) 2
    have ht0 : 0 ≤ 2 * z / (1 + z) ^ 2 := div_nonneg (by linarith [hz0]) hden.le
    have ht1 : 2 * z / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one hden]
      nlinarith [sq_nonneg z]
    have hboundα : |α * (2 * z / (1 + z) ^ 2)| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg hα.le ht0)]
      simpa using mul_le_mul hα1 ht1 ht0 zero_le_one
    calc |α * (2 * z / (1 + z) ^ 2) + Work.Construction.FK f z|
        ≤ |α * (2 * z / (1 + z) ^ 2)| + |Work.Construction.FK f z| := abs_add_le _ _
      _ ≤ 1 + B := add_le_add hboundα (hfk z hz)
      _ = B + 1 := by ring
  · -- non-integrable case: the Bochner integral is `0`
    rw [MeasureTheory.integral_undef hint]
    simp only [abs_zero]
    linarith

end Work.FTS.StrongEps.EpsWp
