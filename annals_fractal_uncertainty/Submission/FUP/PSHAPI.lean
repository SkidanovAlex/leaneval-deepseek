import Submission.FUP.BMReduction

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators Real

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# Closure properties of plurisubharmonic functions

Basic API for the definition `IsPSH` of `BMReduction` (upper semicontinuous plus the
sub-mean-value property on complex disks): sums, pointwise maxima, constants, and positive
scalar multiples.  These are exactly the closure properties used in §5 of the paper, where the
weight `φ = 2u + 20d·log|z|_∞ + ρ u₀ + (ρ/2)(⟨y⟩-1)` is built as a sum of plurisubharmonic
functions, and `log|z|_∞ = max_j log|z_j|` is plurisubharmonic as a maximum of plurisubharmonic
functions.

The hypotheses of continuity are needed only so that the circle averages are integrals of
continuous functions; the functions produced by §3 are continuous.
-/

/-- The circle `θ ↦ z + e^{iθ}w` is continuous. -/
lemma continuous_circlePt (z w : ℂᵈ) : Continuous fun θ : ℝ => z + circlePt θ w := by
  refine Continuous.add continuous_const ?_
  apply continuous_pi
  intro i
  have hfun : (fun θ : ℝ => circlePt θ w i)
      = fun θ : ℝ => (Real.cos θ + Real.sin θ * Complex.I) * w i := by
    funext θ
    rw [circlePt_apply, Complex.exp_ofReal_mul_I]
  rw [hfun]
  fun_prop

lemma SubMeanValue.add {u v : ℂᵈ → ℝ} (huc : Continuous u) (hvc : Continuous v)
    (hu : SubMeanValue u) (hv : SubMeanValue v) :
    SubMeanValue fun z => u z + v z := by
  intro z w
  have h1 : IntervalIntegrable (fun θ : ℝ => u (z + circlePt θ w)) volume 0 (2 * π) :=
    (huc.comp (continuous_circlePt z w)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => v (z + circlePt θ w)) volume 0 (2 * π) :=
    (hvc.comp (continuous_circlePt z w)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2, add_div]
  linarith [hu z w, hv z w]

lemma SubMeanValue.sup {u v : ℂᵈ → ℝ} (huc : Continuous u) (hvc : Continuous v)
    (hu : SubMeanValue u) (hv : SubMeanValue v) :
    SubMeanValue fun z => max (u z) (v z) := by
  intro z w
  have h1 : IntervalIntegrable (fun θ : ℝ => u (z + circlePt θ w)) volume 0 (2 * π) :=
    (huc.comp (continuous_circlePt z w)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => v (z + circlePt θ w)) volume 0 (2 * π) :=
    (hvc.comp (continuous_circlePt z w)).intervalIntegrable _ _
  have hmax : IntervalIntegrable
      (fun θ : ℝ => max (u (z + circlePt θ w)) (v (z + circlePt θ w))) volume 0 (2 * π) :=
    (((huc.comp (continuous_circlePt z w)).max (hvc.comp (continuous_circlePt z w)))).intervalIntegrable _ _
  have hm1 : (∫ θ in (0 : ℝ)..(2 * π), u (z + circlePt θ w))
      ≤ ∫ θ in (0 : ℝ)..(2 * π), max (u (z + circlePt θ w)) (v (z + circlePt θ w)) :=
    intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * π) h1 hmax
      (fun θ => le_max_left _ _)
  have hm2 : (∫ θ in (0 : ℝ)..(2 * π), v (z + circlePt θ w))
      ≤ ∫ θ in (0 : ℝ)..(2 * π), max (u (z + circlePt θ w)) (v (z + circlePt θ w)) :=
    intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * π) h2 hmax
      (fun θ => le_max_right _ _)
  have h2π : (0 : ℝ) < 2 * π := by positivity
  refine max_le ?_ ?_
  · calc u z ≤ (∫ θ in (0 : ℝ)..(2 * π), u (z + circlePt θ w)) / (2 * π) := hu z w
      _ ≤ (∫ θ in (0 : ℝ)..(2 * π), max (u (z + circlePt θ w)) (v (z + circlePt θ w))) / (2 * π) :=
          div_le_div_of_nonneg_right hm1 h2π.le
  · calc v z ≤ (∫ θ in (0 : ℝ)..(2 * π), v (z + circlePt θ w)) / (2 * π) := hv z w
      _ ≤ (∫ θ in (0 : ℝ)..(2 * π), max (u (z + circlePt θ w)) (v (z + circlePt θ w))) / (2 * π) :=
          div_le_div_of_nonneg_right hm2 h2π.le

lemma IsPSH.add {u v : ℂᵈ → ℝ} (huc : Continuous u) (hvc : Continuous v)
    (hu : IsPSH u) (hv : IsPSH v) : IsPSH fun z => u z + v z :=
  ⟨hu.1.add hv.1, hu.2.add huc hvc hv.2⟩

lemma IsPSH.sup {u v : ℂᵈ → ℝ} (huc : Continuous u) (hvc : Continuous v)
    (hu : IsPSH u) (hv : IsPSH v) : IsPSH fun z => max (u z) (v z) :=
  ⟨hu.1.sup hv.1, hu.2.sup huc hvc hv.2⟩

lemma SubMeanValue.const (c : ℝ) : SubMeanValue fun _ : ℂᵈ => c := by
  intro z w
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_div_cancel_left₀ c h2π.ne']

lemma IsPSH.const (c : ℝ) : IsPSH fun _ : ℂᵈ => c :=
  ⟨upperSemicontinuous_const, SubMeanValue.const c⟩

end Submission.FUP
