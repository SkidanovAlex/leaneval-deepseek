import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Commons.Analysis.MeasureTheory.polar_integral

/-!
# Radial × homogeneous integrands on `EuclideanSpace ℝ (Fin n)`

Polar-coordinate factorisation of the integral of a product of a radial profile
`φ ‖x‖` (`φ` continuous with compact support) and a function `h` that is
positively homogeneous of degree `d`:

  `∫ x, φ ‖x‖ * h x = (∫_{r>0} φ r * r^(n-1+d) dr) * (∫_{‖θ‖=1} h θ dθ)`.

The proof uses the commons polar-coordinate identity
`Commons.Analysis.MeasureTheory.polar_integral`, evaluates the integrand on
`x = r • θ` (`r > 0`, `‖θ‖ = 1`) using the homogeneity of `h`, and then factors the
resulting product integrand with the (hypothesis-free) Bochner lemmas
`integral_mul_const`/`integral_const_mul`.  The remaining step rewrites the
measure `volumeIoiPow (n-1)` (density `r^(n-1) dr`) as a Lebesgue integral over
`Ioi 0` and combines the exponents.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal

namespace Commons.Analysis.MeasureTheory

/-- Integral against `Measure.volumeIoiPow m` (the measure on `(0, ∞)` with density
`r ↦ r^m` with respect to Lebesgue measure) as a Lebesgue integral over `Ioi 0`. -/
lemma integral_volumeIoiPow_eq_integral_Ioi_mul_pow (m : ℕ) (g : ℝ → ℝ) :
    ∫ r : Set.Ioi (0:ℝ), g r.1 ∂(Measure.volumeIoiPow m) =
      ∫ r in Set.Ioi (0:ℝ), r ^ m * g r := by
  rw [Measure.volumeIoiPow]
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (f := fun r : Set.Ioi (0:ℝ) => (r.1 ^ m).toNNReal)
      (g := fun r => g r.1)]
  · rw [integral_subtype_comap measurableSet_Ioi (fun a : ℝ => ((a ^ m).toNNReal : ℝ≥0) • g a)]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    show ((x ^ m).toNNReal : ℝ≥0) • g x = x ^ m * g x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem integral_radial_mul_homogeneous
    {n : ℕ} [Nonempty (Fin n)]
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℕ)
    (hd : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)), 0 < t → x ≠ 0 → h (t • x) = t ^ d * h x)
    (hint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => φ ‖x‖ * h x) MeasureTheory.volume) :
    (∫ x, φ ‖x‖ * h x) =
      (∫ r in Set.Ioi (0:ℝ), φ r * r ^ (n - 1 + d)) *
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, h θ ∂MeasureTheory.volume.toSphere) := by
  let V := EuclideanSpace ℝ (Fin n)
  have hdim : Module.finrank ℝ V = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  -- polar coordinates on `V`
  have hpol := Commons.Analysis.MeasureTheory.polar_integral V
      (fun x : V => φ ‖x‖ * h x) (by simpa [V] using hint)
  -- evaluation of the integrand on `r • θ`
  have hpoint : ∀ (θ : Metric.sphere (0 : V) 1) (r : Set.Ioi (0:ℝ)),
      φ ‖(r:ℝ) • (θ : V)‖ * h ((r:ℝ) • (θ : V)) =
        (φ r * r ^ d) * h θ := by
    intro θ r
    have hθnorm : ‖(θ : V)‖ = 1 := (mem_sphere_zero_iff_norm).mp θ.2
    have hθne : (θ : V) ≠ 0 := by
      intro hh; rw [hh] at hθnorm; simp at hθnorm
    have hrn : ‖(r:ℝ) • (θ : V)‖ = (r:ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt r.2), hθnorm, mul_one]
    rw [hrn, hd r (θ : V) r.2 hθne]
    ring
  calc
    (∫ x : V, φ ‖x‖ * h x)
        = ∫ θ : Metric.sphere (0 : V) 1,
            ∫ r : Set.Ioi (0:ℝ),
              (φ ‖(r:ℝ) • (θ : V)‖ * h ((r:ℝ) • (θ : V)))
              ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1))
            ∂(MeasureTheory.volume.toSphere) := hpol
    _ = ∫ θ : Metric.sphere (0 : V) 1,
            ∫ r : Set.Ioi (0:ℝ),
              (φ r * r ^ d) * h θ
              ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1))
            ∂(MeasureTheory.volume.toSphere) := by
          apply integral_congr_ae
          filter_upwards with θ
          apply integral_congr_ae
          filter_upwards with r
          exact hpoint θ r
    _ = ∫ θ : Metric.sphere (0 : V) 1,
            (∫ r : Set.Ioi (0:ℝ), φ r * r ^ d
                ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1))) * h θ
            ∂(MeasureTheory.volume.toSphere) := by
          apply integral_congr_ae
          filter_upwards with θ
          exact integral_mul_const (h θ) (fun r : Set.Ioi (0:ℝ) => (φ r * r ^ d))
    _ = (∫ r : Set.Ioi (0:ℝ), φ r * r ^ d
            ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1))) *
          ∫ θ : Metric.sphere (0 : V) 1, h θ ∂(MeasureTheory.volume.toSphere) := by
          exact integral_const_mul _ _
    _ = (∫ r in Set.Ioi (0:ℝ), φ r * r ^ (n - 1 + d)) *
          ∫ θ : Metric.sphere (0 : V) 1, h θ ∂(MeasureTheory.volume.toSphere) := by
          congr 1
          rw [integral_volumeIoiPow_eq_integral_Ioi_mul_pow (Module.finrank ℝ V - 1)
            (fun x => φ x * x ^ d), hdim]
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          show x ^ (n - 1) * (φ x * x ^ d) = φ x * x ^ (n - 1 + d)
          rw [pow_add]
          ring

end Commons.Analysis.MeasureTheory