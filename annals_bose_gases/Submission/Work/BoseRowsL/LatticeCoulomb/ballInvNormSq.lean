import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseRowsL.LatticeCoulomb.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.ballInvNormSq`

The Newtonian `1/‖q‖²` integral over a ball of radius `ρ` in `ℝ³`:

`∫_{‖q‖ ≤ ρ} ‖q‖⁻² dq = 4πρ`  (and the same for the open ball, and integrability).

The value follows from the polar-coordinate formula
(`MeasureTheory.integral_fun_norm_addHaar`) for a radial function on a finite-dimensional
real inner product space: for `f : ℝ → F`,

`∫_{ball 0 ρ} f ‖x‖ = dim E • μ.real (ball 0 1) • ∫_{y ∈ (0,ρ)} y^(dim E - 1) • f y`,

which we prove here from Mathlib's whole-space formula by multiplying `f` with the
indicator of `(0, ρ)`.  In dimension `3` this reads
`∫_{ball 0 ρ} f ‖x‖ = 4π ∫_0^ρ y² f y dy`, and with `f y = (y²)⁻¹` the inner integral is
`∫_0^ρ 1 dy = ρ`, giving `4πρ`.

Note `(‖q‖ ^ 2)⁻¹` is well defined at `q = 0` (with value `0`) but is *unbounded* near
`0`; integrability nevertheless holds because `1/r² · r² = 1` in the shell measure.  It is
obtained here from `MeasureTheory.integrableOn_fun_norm_addHaar`, which reduces it to the
integrability of the constant `1` on `(0, ρ)`.
-/

namespace Work.BoseRowsL.LatticeCoulomb

open MeasureTheory Metric

/-- The one-dimensional bookkeeping step of the polar-coordinate formula: multiplying by
the indicator of `(0, ρ)` inside the integral over `(0, ∞)` amounts to restricting the
integral to `(0, ρ)`. -/
private lemma integral_Ioi_indicator_Iio {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (ρ : ℝ) (n : ℕ) :
    ∫ y in Set.Ioi (0 : ℝ), (y ^ n) • ((Set.Iio ρ).indicator f y)
      = ∫ y in Set.Ioo (0 : ℝ) ρ, (y ^ n) • f y := by
  rw [← integral_indicator measurableSet_Ioi]
  convert integral_indicator measurableSet_Ioo (μ := volume) (f := fun y => y ^ n • f y) using 2
  ext y
  by_cases h1 : y ∈ Set.Ioi (0:ℝ) <;> by_cases h2 : y ∈ Set.Iio ρ <;>
    simp_all [Set.mem_Ioo, Set.indicator_of_mem, Set.indicator_of_notMem]

/-- Polar-coordinate formula for the integral of a radial function over a ball: for a
finite-dimensional real inner product space `E` of dimension `n`, an additive Haar measure
`μ` and `f : ℝ → F`,

`∫_{ball 0 ρ} f ‖x‖ ∂μ = n • μ.real (ball 0 1) • ∫_{y ∈ (0,ρ)} y^(n-1) • f y`,

obtained from `MeasureTheory.integral_fun_norm_addHaar` by writing the ball integral as the
integral over all of `E` of `f` composed with `‖·‖` and the indicator of `(0, ρ)`. -/
private lemma integral_ball_comp_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) (ρ : ℝ) :
    ∫ x in Metric.ball (0 : E) ρ, f ‖x‖ ∂μ =
      Module.finrank ℝ E • μ.real (Metric.ball 0 1) •
        ∫ y in Set.Ioo (0 : ℝ) ρ, y ^ (Module.finrank ℝ E - 1) • f y := by
  have hind : ∫ x in Metric.ball (0 : E) ρ, f ‖x‖ ∂μ
      = ∫ x, ((Set.Iio ρ).indicator f) ‖x‖ ∂μ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with x
    classical
    by_cases h : ‖x‖ < ρ <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, mem_ball, dist_eq_norm, h]
  rw [hind, integral_fun_norm_addHaar]
  rw [integral_Ioi_indicator_Iio]

theorem ballInvNormSq (ρ : ℝ) (hρ : 0 ≤ ρ) :
    MeasureTheory.IntegrableOn (fun q : EuclideanSpace ℝ (Fin 3) => (‖q‖ ^ 2)⁻¹)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ) MeasureTheory.volume ∧
      ((∫ q in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, (‖q‖ ^ 2)⁻¹)
        = 4 * Real.pi * ρ) ∧
      ((∫ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ, (‖q‖ ^ 2)⁻¹)
        = 4 * Real.pi * ρ) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- the volume of the unit ball in `ℝ³`
  have hfr : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1)
      = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  -- the sphere is null, so the closed ball and the open ball have the same integral
  have hae : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ
      =ᵐ[volume] Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Metric.closedBall_sdiff_ball, Measure.addHaar_sphere]
    · rw [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty]
  -- integrability of the one-dimensional reduction: `y^(3-1) • (y²)⁻¹ = 1` on `(0, ρ)`
  have h1d : MeasureTheory.IntegrableOn
      (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) • ((y^2)⁻¹))
      (Set.Ioo 0 ρ) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.congr_fun (f := fun _ : ℝ => (1:ℝ)) ?_ ?_ measurableSet_Ioo
    · exact MeasureTheory.integrableOn_const (hs := by simp [Real.volume_Ioo]) (hC := by simp)
    · intro y hy
      have hy0 : y ≠ 0 := ne_of_gt hy.1
      show (1:ℝ) = y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) • ((y^2)⁻¹)
      rw [hfin]
      norm_num
      exact (mul_inv_cancel₀ (pow_ne_zero 2 hy0)).symm
  have hball : MeasureTheory.IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) => (‖q‖ ^ 2)⁻¹)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ) MeasureTheory.volume :=
    (MeasureTheory.integrableOn_fun_norm_addHaar (μ := volume)
      (f := fun y : ℝ => (y^2)⁻¹)).mpr h1d
  -- the one-dimensional integral
  have h1 : ∫ y in Set.Ioo (0 : ℝ) ρ,
      y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) • ((y^2)⁻¹) = ρ := by
    have heq : Set.EqOn (fun y : ℝ =>
          y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) • ((y^2)⁻¹))
        (fun _ : ℝ => (1:ℝ)) (Set.Ioo 0 ρ) := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt hy.1
      rw [hfin]
      norm_num
      exact mul_inv_cancel₀ (pow_ne_zero 2 hy0)
    rw [setIntegral_congr_fun measurableSet_Ioo heq, setIntegral_const]
    rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by simpa using hρ)]
    simp
  have hballval : ∫ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ, (‖q‖ ^ 2)⁻¹
      = 4 * Real.pi * ρ := by
    rw [integral_ball_comp_norm (μ := volume) (f := fun y : ℝ => (y^2)⁻¹) (ρ := ρ),
      h1, hfr, hfin]
    norm_num
    ring
  refine ⟨hball.congr_set_ae hae, ?_, hballval⟩
  rw [setIntegral_congr_set hae, hballval]

end Work.BoseRowsL.LatticeCoulomb
