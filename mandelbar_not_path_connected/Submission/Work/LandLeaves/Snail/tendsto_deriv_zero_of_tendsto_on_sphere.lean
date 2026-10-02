import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Convergence of the derivative at the centre from convergence on the sphere

If a sequence of functions `g n`, holomorphic on the closed disc of radius `R > 0`, is uniformly
bounded by `M` on the boundary circle and converges pointwise to `0` on that circle, then the
derivatives `(g n)' 0` converge to `0`.

The point of the argument is that holomorphy upgrades a *pointwise* statement on the circle to an
integral identity at the centre: Cauchy's integral formula for the first derivative writes
`deriv (g n) 0` as `(2πi)⁻¹ ∮ z in C(0,R), g n z / z ^ 2 dz`, and the dominated convergence theorem
(applicable because the boundary values are uniformly bounded and the circle has finite measure)
turns the pointwise convergence on the circle into convergence of these circle integrals.
-/

namespace Work.LandLeaves.Snail

open Complex MeasureTheory Filter Topology
open scoped Interval Real

/-- Auxiliary statement: if a sequence of functions `f n`, continuous on the sphere `‖z‖ = R`
(`R > 0`), is uniformly bounded there by `C` and converges pointwise to `0` on that sphere, then
the circle integrals `∮ z in C(0, R), f n z` converge to `0`.

This is the "dominated convergence" half of the argument: the circle integral is an interval
integral `∫ θ in [0, 2π], deriv (circleMap 0 R) θ • f n (circleMap 0 R θ)` whose integrand is
bounded by `R * C` and converges pointwise to `0`. -/
theorem tendsto_circleIntegral_zero_of_tendsto_on_sphere
    {f : ℕ → ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hcont : ∀ n, ContinuousOn (f n) (Metric.sphere (0 : ℂ) R))
    (hbdd : ∀ n, ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f n z‖ ≤ C)
    (hconv : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      Filter.Tendsto (fun n => f n z) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∮ z in C((0 : ℂ), R), f n z) Filter.atTop (nhds 0) := by
  have hcontF : ∀ n, Continuous
      (fun θ : ℝ => deriv (circleMap (0 : ℂ) R) θ • f n (circleMap (0 : ℂ) R θ)) := by
    intro n
    have h1 : Continuous (fun θ : ℝ => deriv (circleMap (0 : ℂ) R) θ) := by
      simp only [deriv_circleMap]
      fun_prop
    have h2 : Continuous (fun θ : ℝ => f n (circleMap (0 : ℂ) R θ)) :=
      ContinuousOn.comp_continuous (hcont n) (continuous_circleMap 0 R)
        (fun θ => circleMap_mem_sphere 0 hR.le θ)
    exact h1.smul h2
  have key : Filter.Tendsto
      (fun n => ∫ θ, deriv (circleMap (0 : ℂ) R) θ • f n (circleMap (0 : ℂ) R θ)
        ∂(volume.restrict (Set.Ioc 0 (2 * π)))) Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioc 0 (2 * π)))
      (F := fun n θ => deriv (circleMap (0 : ℂ) R) θ • f n (circleMap (0 : ℂ) R θ))
      (f := fun _ => 0) (fun _ : ℝ => R * C)
      (fun n => (hcontF n).aestronglyMeasurable)
      (integrable_const_iff.mpr (Or.inr inferInstance))
      (fun n => Filter.Eventually.of_forall (fun θ => ?_))
      (Filter.Eventually.of_forall (fun θ => ?_))
    · simpa using h
    · have hz : circleMap (0 : ℂ) R θ ∈ Metric.sphere (0 : ℂ) R :=
        circleMap_mem_sphere 0 hR.le θ
      have hd : ‖deriv (circleMap (0 : ℂ) R) θ‖ = R := by
        rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
          abs_of_pos hR]
      calc ‖deriv (circleMap (0 : ℂ) R) θ • f n (circleMap (0 : ℂ) R θ)‖
          = ‖deriv (circleMap (0 : ℂ) R) θ‖ * ‖f n (circleMap (0 : ℂ) R θ)‖ :=
            norm_smul _ _
        _ ≤ R * C := by
            rw [hd]
            exact mul_le_mul (le_refl R) (hbdd n _ hz) (norm_nonneg _) hR.le
    · have hz : circleMap (0 : ℂ) R θ ∈ Metric.sphere (0 : ℂ) R :=
        circleMap_mem_sphere 0 hR.le θ
      simpa using (hconv _ hz).const_smul (deriv (circleMap (0 : ℂ) R) θ)
  have hcongr : ∀ n, ∮ z in C((0 : ℂ), R), f n z
      = ∫ θ, deriv (circleMap (0 : ℂ) R) θ • f n (circleMap (0 : ℂ) R θ)
        ∂(volume.restrict (Set.Ioc 0 (2 * π))) := by
    intro n
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simpa only [hcongr] using key

theorem tendsto_deriv_zero_of_tendsto_on_sphere {g : ℕ → ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hdiff : ∀ n, DifferentiableOn ℂ (g n) (Metric.closedBall (0 : ℂ) R))
    (hbdd : ∀ n, ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g n z‖ ≤ M)
    (hconv : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      Filter.Tendsto (fun n => g n z) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => deriv (g n) 0) Filter.atTop (nhds 0) := by
  -- The auxiliary function `z ↦ g n z / z ^ 2`, which by Cauchy's formula integrates to the
  -- derivative of `g n` at `0`; it is continuous and bounded by `M / R ^ 2` on the circle.
  have hcont : ∀ n, ContinuousOn (fun z : ℂ => (z ^ 2)⁻¹ • g n z)
      (Metric.sphere (0 : ℂ) R) := by
    intro n
    have h1 : ContinuousOn (fun z : ℂ => (z ^ 2)⁻¹) (Metric.sphere (0 : ℂ) R) := by
      have hp : DifferentiableOn ℂ (fun z : ℂ => (z ^ 2)⁻¹) (Metric.sphere (0 : ℂ) R) := by
        refine (DifferentiableOn.pow (f := fun z : ℂ => z) ?_ 2).inv ?_
        · exact differentiableOn_id
        · intro z hz
          have hzR : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
          have hznz : z ≠ 0 := by
            intro h0
            rw [h0, norm_zero] at hzR
            exact (ne_of_lt hR) hzR
          exact pow_ne_zero 2 hznz
      exact hp.continuousOn
    exact h1.smul ((hdiff n).continuousOn.mono Metric.sphere_subset_closedBall)
  have hbdd' : ∀ n, ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖(z ^ 2)⁻¹ • g n z‖ ≤ M / R ^ 2 := by
    intro n z hz
    have hzR : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
    have hnorm1 : ‖((z : ℂ) ^ 2)⁻¹‖ = 1 / R ^ 2 := by
      rw [norm_inv, norm_pow, hzR, one_div]
    calc ‖(z ^ 2)⁻¹ • g n z‖ = ‖((z : ℂ) ^ 2)⁻¹‖ * ‖g n z‖ := norm_smul _ _
      _ ≤ (1 / R ^ 2) * M := by
          rw [hnorm1]
          exact mul_le_mul_of_nonneg_left (hbdd n z hz) (by positivity)
      _ = M / R ^ 2 := by ring
  have hconv' : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      Filter.Tendsto (fun n => (z ^ 2)⁻¹ • g n z) Filter.atTop (nhds 0) := by
    intro z hz
    simpa using (hconv z hz).const_smul ((z ^ 2)⁻¹ : ℂ)
  have hcircle :=
    tendsto_circleIntegral_zero_of_tendsto_on_sphere (f := fun n z => (z ^ 2)⁻¹ • g n z)
      (R := R) (C := M / R ^ 2) hR hcont hbdd' hconv'
  -- Cauchy's integral formula for the first derivative at the centre.
  have hform : ∀ n, deriv (g n) 0
      = (2 * π * I)⁻¹ • ∮ z in C((0 : ℂ), R), (z ^ 2)⁻¹ • g n z := by
    intro n
    have h := DifferentiableOn.deriv_eq_smul_circleIntegral (f := g n) (c := 0) (R := R) hR
      (hdiff n)
    have h' := congrArg (fun x => (2 * π * I)⁻¹ • x) h
    rw [smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul] at h'
    rw [← h']
    congr 1
    exact circleIntegral.integral_congr hR.le (fun z _ => by simp)
  have h2 := hcircle.const_smul ((2 * π * I)⁻¹ : ℂ)
  have hfun : (fun n => (2 * π * I)⁻¹ • ∮ z in C((0 : ℂ), R), (z ^ 2)⁻¹ • g n z)
      = fun n => deriv (g n) 0 := by
    funext n; exact (hform n).symm
  rw [hfun] at h2
  simpa using h2

end Work.LandLeaves.Snail
