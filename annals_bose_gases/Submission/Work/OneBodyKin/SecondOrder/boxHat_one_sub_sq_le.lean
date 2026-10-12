import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le`

The box Fourier profile of the centred unit cube is

  `boxHat 1 ρ = ∫_{acube 1} cos⟪ρ,z⟫ dz`,

and it vanishes at the origin to *second order*: `1 − boxHat 1 ρ = O(‖ρ‖²)`.  Quantitatively,
the unit cube has volume `1` and `‖z‖² ≤ 3/4` on it, so

  1 − boxHat 1 ρ = ∫_{acube 1} (1 − cos⟪ρ,z⟫) dz,
  0 ≤ 1 − cos⟪ρ,z⟫ ≤ ⟪ρ,z⟫²/2 ≤ (3/8)‖ρ‖²   for `z ∈ acube 1`,

hence `0 ≤ 1 − boxHat 1 ρ ≤ (3/8)‖ρ‖²` and therefore

  `(1 − boxHat 1 ρ)² ≤ (9/64)‖ρ‖⁴`   (`boxHat_one_sub_sq_le`).

The constant `9/64` is exactly the square of `3/8`, i.e. it comes from
`⟪ρ,z⟫² ≤ ‖ρ‖² · sup_{z ∈ acube 1} ‖z‖² = (3/4)‖ρ‖²`.

This is the estimate named `(hχ)` in `Work.OneBodyKin.Localize`; it is proved here as a
standalone pointwise statement about `boxHat 1`.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The centred unit cube has volume `1`. -/
lemma volume_acube_one :
    (volume : Measure ℝ³) (Submission.BoseGases.acube (1 : ℝ)) = 1 := by
  rw [Submission.BoseGases.acube_volume 1 (by norm_num)]
  norm_num

/-- The (real) measure of the centred unit cube is `1`. -/
lemma volumeReal_acube_one :
    (volume : Measure ℝ³).real (Submission.BoseGases.acube (1 : ℝ)) = 1 := by
  rw [MeasureTheory.measureReal_def, volume_acube_one]
  norm_num

/-- On the centred unit cube, `‖z‖² ≤ 3/4` (each coordinate is at most `1/2` in absolute value
and there are three coordinates). -/
lemma norm_sq_le_of_mem_acube_one {z : ℝ³} (hz : z ∈ Submission.BoseGases.acube (1 : ℝ)) :
    ‖z‖ ^ 2 ≤ 3 / 4 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hz' : ∀ i : Fin 3, ‖z.ofLp i‖ ≤ 1 / 2 := by
    intro i
    have h := hz i
    rw [Set.mem_Icc] at h
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  calc ∑ i, ‖z.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 / 2 : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz' i) 2)
    _ = 3 / 4 := by norm_num [Fin.sum_univ_three]

/-- Pointwise second-order vanishing of the cosine on the unit cube:
`1 − cos⟪ρ,z⟫ ≤ (3/8)‖ρ‖²` for `z ∈ acube 1`. -/
lemma one_sub_cos_le_of_mem_acube_one (ρ : ℝ³) {z : ℝ³}
    (hz : z ∈ Submission.BoseGases.acube (1 : ℝ)) :
    1 - Real.cos (inner ℝ ρ z) ≤ (3 / 8) * ‖ρ‖ ^ 2 := by
  -- `1 - cos θ ≤ θ²/2`.
  have hθ : 1 - Real.cos (inner ℝ ρ z) ≤ (inner ℝ ρ z) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := inner ℝ ρ z)]
  -- `θ² ≤ ‖ρ‖²‖z‖² ≤ (3/4)‖ρ‖²` on the cube.
  have hinner : (inner ℝ ρ z) ^ 2 ≤ ‖ρ‖ ^ 2 * ‖z‖ ^ 2 := by
    have h1 : (inner ℝ ρ z) ^ 2 ≤ (‖ρ‖ * ‖z‖) ^ 2 := by
      rw [← sq_abs (inner ℝ ρ z)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm ρ z) 2
    calc (inner ℝ ρ z) ^ 2 ≤ (‖ρ‖ * ‖z‖) ^ 2 := h1
      _ = ‖ρ‖ ^ 2 * ‖z‖ ^ 2 := by ring
  nlinarith [hθ, hinner, norm_sq_le_of_mem_acube_one hz, sq_nonneg ‖ρ‖]

/-- `cos⟪ρ,·⟫` is integrable on the centred unit cube (it is bounded there and the cube has
finite measure). -/
lemma integrableOn_cos_acube_one (ρ : ℝ³) :
    IntegrableOn (fun z : ℝ³ => Real.cos (inner ℝ ρ z))
      (Submission.BoseGases.acube (1 : ℝ)) :=
  IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top 1 (by norm_num)) (by fun_prop) 1
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _))

/-- The identity `1 = ∫_{acube 1} 1` (the cube has volume one). -/
lemma one_eq_integral_one_acube_one :
    (1 : ℝ) = ∫ _z in Submission.BoseGases.acube (1 : ℝ), (1 : ℝ) := by
  rw [setIntegral_const, volumeReal_acube_one, one_smul]

/-- **The box profile at the origin, to second order**: the mean-value identity
`1 − boxHat 1 ρ = ∫_{acube 1} (1 − cos⟪ρ,z⟫) dz`, from `boxHat 1 0 = vol (acube 1) = 1`. -/
lemma one_sub_boxHat_eq_integral (ρ : ℝ³) :
    1 - Work.OneBodyKin.boxHat 1 ρ
      = ∫ z in Submission.BoseGases.acube (1 : ℝ), ((1 : ℝ) - Real.cos (inner ℝ ρ z)) := by
  have honeint : IntegrableOn (fun _ : ℝ³ => (1 : ℝ))
      (Submission.BoseGases.acube (1 : ℝ)) :=
    integrableOn_const (by rw [volume_acube_one]; exact ENNReal.one_ne_top)
  have hsub : (∫ z in Submission.BoseGases.acube (1 : ℝ), ((1 : ℝ) - Real.cos (inner ℝ ρ z)))
      = (∫ z in Submission.BoseGases.acube (1 : ℝ), (1 : ℝ))
        - (∫ z in Submission.BoseGases.acube (1 : ℝ), Real.cos (inner ℝ ρ z)) :=
    integral_sub honeint (integrableOn_cos_acube_one ρ)
  rw [Work.OneBodyKin.boxHat, hsub, setIntegral_const, volumeReal_acube_one]
  simp

/-- **The box profile is at most one**: `0 ≤ 1 − boxHat 1 ρ`. -/
lemma one_sub_boxHat_nonneg (ρ : ℝ³) : 0 ≤ 1 - Work.OneBodyKin.boxHat 1 ρ := by
  rw [one_sub_boxHat_eq_integral]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable 1)] with z hz
  exact sub_nonneg.mpr (Real.cos_le_one _)

/-- **Second-order vanishing of the box profile**: `1 − boxHat 1 ρ ≤ (3/8)‖ρ‖²`. -/
lemma one_sub_boxHat_le (ρ : ℝ³) :
    1 - Work.OneBodyKin.boxHat 1 ρ ≤ (3 / 8) * ‖ρ‖ ^ 2 := by
  rw [one_sub_boxHat_eq_integral]
  have hbound : (∫ z in Submission.BoseGases.acube (1 : ℝ), ((1 : ℝ) - Real.cos (inner ℝ ρ z)))
      ≤ (∫ _z in Submission.BoseGases.acube (1 : ℝ), ((3 : ℝ) / 8 * ‖ρ‖ ^ 2)) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable 1)] with z hz
      exact sub_nonneg.mpr (Real.cos_le_one _)
    · exact integrableOn_const (by rw [volume_acube_one]; exact ENNReal.one_ne_top)
    · filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable 1)] with z hz
      exact one_sub_cos_le_of_mem_acube_one ρ hz
  rwa [setIntegral_const, volumeReal_acube_one, one_smul] at hbound

/-- **The box Fourier profile vanishes at the origin to second order**:
`(1 − boxHat 1 ρ)² ≤ (9/64)‖ρ‖⁴`. -/
theorem boxHat_one_sub_sq_le (ρ : EuclideanSpace ℝ (Fin 3)) :
    (1 - Work.OneBodyKin.boxHat 1 ρ) ^ 2 ≤ (9 / 64) * ‖ρ‖ ^ 4 := by
  calc (1 - Work.OneBodyKin.boxHat 1 ρ) ^ 2
      ≤ ((3 / 8) * ‖ρ‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (one_sub_boxHat_nonneg ρ) (one_sub_boxHat_le ρ) 2
    _ = (9 / 64) * ‖ρ‖ ^ 4 := by ring

end Work.OneBodyKin.SecondOrder
