import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Submission.Commons.MeasureTheory.lintegral_log_kernel_empirical_sum_injective

set_option maxHeartbeats 1600000

open MeasureTheory
open scoped BigOperators ENNReal

namespace Commons.MeasureTheory

/-- The logarithmic energy of an empirical measure: for a finite family of distinct points
`a i` of an arbitrary measurable space with all singletons measurable, the integral of a
kernel `F` against the product of the empirical measure `∑ δ_{a i}` with itself is the
finite double sum of `F` over the pairs of points. -/
lemma lintegral_prod_dirac_fin {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {n : ℕ} (a : Fin n → α) (F : α × α → ENNReal) :
    ∫⁻ z, F z ∂ ((∑ i : Fin n, MeasureTheory.Measure.dirac (a i)).prod
        (∑ i : Fin n, MeasureTheory.Measure.dirac (a i)))
      = ∑ i : Fin n, ∑ j : Fin n, F (a i, a j) := by
  have hmeasure : (∑ i : Fin n, MeasureTheory.Measure.dirac (a i)).prod
        (∑ i : Fin n, MeasureTheory.Measure.dirac (a i))
      = MeasureTheory.Measure.sum
          (fun p : Fin n × Fin n => MeasureTheory.Measure.dirac (a p.1, a p.2)) := by
    rw [← MeasureTheory.Measure.sum_fintype (fun i : Fin n => MeasureTheory.Measure.dirac (a i))]
    rw [MeasureTheory.Measure.prod_sum]
    simp_rw [MeasureTheory.Measure.dirac_prod_dirac]
  rw [hmeasure, MeasureTheory.lintegral_sum_measure]
  simp_rw [MeasureTheory.lintegral_dirac]
  rw [tsum_fintype, Fintype.sum_prod_type]

/-- The integral of the logarithmic kernel `log (D / ‖z.1 - z.2‖)` against the product of the
empirical measure carried by the points `x i : K ⊆ ℂ` equals the explicit finite expression
`((N-1)/N) log D - (2/N^2) log ∏_{i} ∏_{j<i} ‖x_j - x_i‖`. -/
theorem lintegral_log_kernel_empK {K : Set ℂ} {N : ℕ} (hN : 1 ≤ N) (x : Fin N → K)
    (hx : Function.Injective x) {D : ℝ} (hD : 0 < D)
    (hDiam : ∀ i j : Fin N, ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖ ≤ D)
    (ν : MeasureTheory.ProbabilityMeasure K) (hν : (ν : MeasureTheory.Measure K)
      = (N : ENNReal)⁻¹ • ∑ i : Fin N, MeasureTheory.Measure.dirac (x i)) :
    ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖))
        ∂((ν : MeasureTheory.Measure K).prod (ν : MeasureTheory.Measure K))
      = ENNReal.ofReal ((((N : ℝ) - 1) / N) * Real.log D
          - (2 / (N : ℝ) ^ 2) * Real.log
              (∏ i : Fin N, ∏ j ∈ Finset.Iio i, ‖((x j : K) : ℂ) - ((x i : K) : ℂ)‖)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hinvnn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  have hginj : Function.Injective (fun i : Fin N => ((x i : K) : ℂ)) :=
    fun i j h => hx (Subtype.val_injective h)
  -- nonnegativity of each logarithmic kernel value on the empirical measure
  have hnn : ∀ i j : Fin N, 0 ≤ Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖) :=
    fun i j => log_dist_ratio_nonneg (fun i : Fin N => ((x i : K) : ℂ)) hginj hD hDiam i j
  -- the product measure, written through the empirical decomposition and the scalar factor
  have hprod : (ν : Measure K).prod (ν : Measure K)
      = ((N : ENNReal)⁻¹ * (N : ENNReal)⁻¹) •
          ((∑ i : Fin N, Measure.dirac (x i)).prod (∑ i : Fin N, Measure.dirac (x i))) := by
    rw [hν, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [hprod, lintegral_smul_measure, smul_eq_mul]
  -- the integral against the product of the two empirical sums is the double sum
  rw [lintegral_prod_dirac_fin]
  -- convert the double sum of `ofReal`s into an `ofReal` of the double sum
  have hinner : ∀ i : Fin N,
      (∑ j : Fin N, ENNReal.ofReal (Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖)))
        = ENNReal.ofReal (∑ j : Fin N,
            Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖)) := by
    intro i
    exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn i j)).symm
  have hconv : (∑ i : Fin N, ∑ j : Fin N,
        ENNReal.ofReal (Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖)))
      = ENNReal.ofReal (∑ i : Fin N, ∑ j : Fin N,
          Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖)) := by
    simp_rw [hinner]
    exact (ENNReal.ofReal_sum_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))).symm
  rw [hconv]
  -- the scalar factor `(N)⁻¹` as an `ofReal`
  have hc : (N : ENNReal)⁻¹ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  rw [hc]
  have hpair : ENNReal.ofReal ((N : ℝ)⁻¹) * ENNReal.ofReal ((N : ℝ)⁻¹)
      = ENNReal.ofReal ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) := (ENNReal.ofReal_mul hinvnn).symm
  rw [hpair]
  have hsq : ENNReal.ofReal ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) *
        ENNReal.ofReal (∑ i : Fin N, ∑ j : Fin N,
          Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖))
      = ENNReal.ofReal (((N : ℝ)⁻¹ * (N : ℝ)⁻¹) *
          (∑ i : Fin N, ∑ j : Fin N,
            Real.log (D / ‖((x i : K) : ℂ) - ((x j : K) : ℂ)‖))) :=
    (ENNReal.ofReal_mul (mul_nonneg hinvnn hinvnn)).symm
  rw [hsq]
  congr 1
  -- the explicit closed form for the double sum of log-kernel values
  rw [sum_log_dist_ratio_eq hN (fun i : Fin N => ((x i : K) : ℂ)) hginj hD]
  field_simp

end Commons.MeasureTheory