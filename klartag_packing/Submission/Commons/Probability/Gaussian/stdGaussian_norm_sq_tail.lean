import Mathlib
import Submission.Commons.Probability.Gaussian.integral_exp_mul_sq_norm_stdGaussian
import Submission.Commons.Measure.Markov.measureReal_markov

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

/-- Integrability of `x ↦ exp (t * x ^ 2)` against the standard Gaussian on `ℝ`, for `t < 1 / 2`.
Obtained from the explicit Gaussian density, which turns the integrand into
`(√(2π))⁻¹ * exp (-(1/2 - t) * x ^ 2)`. -/
private theorem integrable_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    MeasureTheory.Integrable (fun x : ℝ => Real.exp (t * x ^ 2))
      (ProbabilityTheory.gaussianReal 0 1) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero (0:ℝ) (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (ProbabilityTheory.measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun x => ProbabilityTheory.gaussianPDF_lt_top))]
  simp_rw [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul]
  have hpt : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  simp_rw [hpt]
  exact (integrable_exp_neg_mul_sq (by linarith : (0:ℝ) < 1/2 - t)).const_mul _

/-- Integrability of `x ↦ exp (t * ‖x‖ ^ 2)` against the standard Gaussian on
`EuclideanSpace ℝ (Fin n)`, for `t < 1 / 2`.  Transferred from the product of `n` copies of the
one-dimensional statement via `stdGaussian = (Measure.pi gaussianReal).map (toLp 2)`. -/
private theorem integrable_exp_mul_sq_norm_stdGaussian {n : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (t * ‖x‖ ^ 2))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hφ : Measurable (fun y : Fin n → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) :=
    WithLp.measurable_toLp 2 (Fin n → ℝ)
  have hF : Measurable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (t * ‖x‖ ^ 2)) := by fun_prop
  rw [← map_pi_eq_stdGaussian (ι := Fin n)]
  rw [integrable_map_measure hF.aestronglyMeasurable hφ.aemeasurable]
  have hpt : ∀ y : Fin n → ℝ, Real.exp (t * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = ∏ i, Real.exp (t * y i ^ 2) := by
    intro y
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  simp_rw [hpt]
  exact Integrable.fintype_prod (fun _ => integrable_exp_mul_sq_gaussianReal ht)

/-- **Tail bound for the squared norm of a standard Gaussian vector.**  For `u ≥ 0`, the standard
Gaussian measure on `EuclideanSpace ℝ (Fin n)` gives the set `{x | u ≤ ‖x‖ ^ 2}` mass at most
`2 ^ n * exp (-(3 / 8) u)`.

The proof is Chernoff's method with parameter `θ = 3 / 8 < 1 / 2`: for `θ < 1 / 2` the Laplace
transform of the squared norm is `(1 - 2θ) ^ (-n/2)`, which at `θ = 3 / 8` equals `2 ^ n`. -/
theorem stdGaussian_norm_sq_tail {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | u ≤ ‖x‖ ^ 2}
      ≤ (2 : ℝ) ^ n * Real.exp (-(3 / 8) * u) := by
  set μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) with hμ
  have hbase : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((3/8 : ℝ) * ‖x‖ ^ 2)) μ := by
    rw [hμ]
    exact integrable_exp_mul_sq_norm_stdGaussian (by norm_num)
  have hf_eq : (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((3/8 : ℝ) * (‖x‖ ^ 2 - u)))
      = fun x => Real.exp (-((3/8 : ℝ) * u)) * Real.exp ((3/8 : ℝ) * ‖x‖ ^ 2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hint : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((3/8 : ℝ) * (‖x‖ ^ 2 - u))) μ := by
    rw [hf_eq]
    exact hbase.const_mul _
  have hmarkov := Commons.Measure.Markov.measureReal_markov (μ := μ)
      (f := fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((3/8 : ℝ) * (‖x‖ ^ 2 - u)))
      (ae_of_all _ (fun x => Real.exp_nonneg _)) hint 1 (by norm_num)
  have hset : {x : EuclideanSpace ℝ (Fin n) | 1 ≤ Real.exp ((3/8 : ℝ) * (‖x‖ ^ 2 - u))}
      = {x | u ≤ ‖x‖ ^ 2} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [Real.one_le_exp_iff]
    constructor <;> intro h <;> nlinarith
  rw [hset] at hmarkov
  have hval : ∫ x, Real.exp ((3/8 : ℝ) * (‖x‖ ^ 2 - u)) ∂μ
      = Real.exp (-((3/8 : ℝ) * u)) * 2 ^ n := by
    rw [hf_eq, integral_const_mul]
    have h2 : ((Real.sqrt (1 - 2 * ((3:ℝ)/8)))⁻¹) ^ n = 2 ^ n := by
      have h1 : 1 - 2 * ((3:ℝ)/8) = 1/4 := by norm_num
      rw [h1]
      have hs : Real.sqrt ((1:ℝ)/4) = 1/2 := by
        rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hs]
      norm_num
    rw [hμ, integral_exp_mul_sq_norm_stdGaussian (n := n) (t := (3/8 : ℝ)) (by norm_num), h2]
  rw [hval] at hmarkov
  rw [one_mul] at hmarkov
  calc μ.real {x | u ≤ ‖x‖ ^ 2} ≤ Real.exp (-((3/8 : ℝ) * u)) * 2 ^ n := hmarkov
    _ = (2 : ℝ) ^ n * Real.exp (-(3 / 8) * u) := by
        rw [show -((3:ℝ)/8 * u) = -(3/8) * u by ring]; ring

end Commons.Probability.Gaussian
