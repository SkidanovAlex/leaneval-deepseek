import Mathlib
import Submission.Commons.Probability.Reflection.fin_maximal_tail_Phi_of_map_pi
import Submission.Commons.Probability.Reflection.iid_stdGaussian_maximal_tail_Phi
import Submission.Commons.Probability.Gaussian.stdGaussian_map_neg

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Commons.Probability.Gaussian

/-! ## Auxiliary estimates for the standard Gaussian tail

We prove the classical Mills-ratio bound for the standard Gaussian law on `ℝ`:
for `z > 0`,
`P(Y ≥ z) ≤ exp (-(z^2)/2) / (sqrt (2 π) * z)`.
The proof compares the density with `y ↦ (y / z) * density y` on `(z, ∞)`, whose integral is
computed with the fundamental theorem of calculus.
-/

private lemma tendsto_exp_neg_sq_div_two :
    Tendsto (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) atTop (nhds 0) := by
  have h : Tendsto (fun y : ℝ => -(y ^ 2) / 2) atTop atBot := by
    have h2 : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
      tendsto_pow_atTop (α := ℝ) (by norm_num)
    have h3 : Tendsto (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2) atTop atTop :=
      h2.const_mul_atTop (by norm_num)
    have h4 : Tendsto (fun y : ℝ => -((1 / 2 : ℝ) * y ^ 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h3
    have heq : (fun y : ℝ => -((1 / 2 : ℝ) * y ^ 2)) = (fun y : ℝ => -(y ^ 2) / 2) := by
      funext y; ring
    rwa [heq] at h4
  exact Real.tendsto_exp_atBot.comp h

private lemma hasDerivAt_neg_exp_neg_sq_div_two (y : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) (y * Real.exp (-(y ^ 2) / 2)) y := by
  have hbase : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (Real.exp (-(y ^ 2) / 2) * (-y)) y := by
    have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-y) y := by
      have h3 := (hasDerivAt_pow 2 y).neg.div_const 2
      have heq : (fun x : ℝ => (-fun x => x ^ 2) x / 2) = (fun y : ℝ => -(y ^ 2) / 2) := by
        funext x; simp
      rw [heq] at h3
      exact h3.congr_deriv
        (by rw [show (↑(2 : ℕ) * y ^ (2 - 1) : ℝ) = 2 * y by norm_num]; ring)
    exact h2.exp
  exact hbase.neg.congr_deriv (by ring)

/-- Integrability of `y ↦ y * exp (-(y^2)/2)` on `(z, ∞)` for `z ≥ 0`. -/
private lemma integrableOn_Ioi_mul_exp_neg_sq {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun y : ℝ => y * Real.exp (-(y ^ 2) / 2)) (Ioi z) := by
  have hlim : Tendsto (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) atTop (nhds 0) := by
    simpa using tendsto_exp_neg_sq_div_two.neg
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun y : ℝ => -Real.exp (-(y ^ 2) / 2))
    (g' := fun y : ℝ => y * Real.exp (-(y ^ 2) / 2)) ?_ ?_ ?_ hlim
  · fun_prop
  · intro y hy
    exact hasDerivAt_neg_exp_neg_sq_div_two y
  · intro y hy
    exact mul_nonneg (by linarith [hy.out]) (Real.exp_nonneg _)

/-- Integrability of `y ↦ exp (-(y^2)/2)` on `(z, ∞)` for `z ≥ 0`. -/
private lemma integrableOn_Ioi_exp_neg_sq {z : ℝ} (_hz : 0 ≤ z) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) (Ioi z) := by
  have hglob : Integrable (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) (volume : Measure ℝ) := by
    refine (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).congr ?_
    filter_upwards with y
    rw [show -(1 / 2 : ℝ) * y ^ 2 = -(y ^ 2) / 2 by ring]
  exact hglob.integrableOn

/-- **Mills-ratio identity.** For `z ≥ 0`, `∫_z^∞ y exp (-(y^2)/2) dy = exp (-(z^2)/2)`. -/
private lemma integral_Ioi_mul_exp_neg_sq {z : ℝ} (hz : 0 ≤ z) :
    ∫ y in Ioi z, y * Real.exp (-(y ^ 2) / 2) = Real.exp (-(z ^ 2) / 2) := by
  have hlim : Tendsto (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) atTop (nhds 0) := by
    simpa using tendsto_exp_neg_sq_div_two.neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun y : ℝ => -Real.exp (-(y ^ 2) / 2))
    (g' := fun y : ℝ => y * Real.exp (-(y ^ 2) / 2)) (a := z) (l := 0)
    (by fun_prop)
    (fun y hy => hasDerivAt_neg_exp_neg_sq_div_two y)
    (fun y hy => mul_nonneg (by linarith [hy.out]) (Real.exp_nonneg _))
    hlim
  rw [h]
  simp

/-- **Mills-ratio bound.** For `z > 0`, `∫_z^∞ exp (-(y^2)/2) dy ≤ exp (-(z^2)/2) / z`. -/
private lemma integral_Ioi_exp_neg_sq_le {z : ℝ} (hz : 0 < z) :
    ∫ y in Ioi z, Real.exp (-(y ^ 2) / 2) ≤ Real.exp (-(z ^ 2) / 2) / z := by
  have hz0 : (0:ℝ) ≤ z := le_of_lt hz
  have hint1 : IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) (Ioi z) :=
    integrableOn_Ioi_exp_neg_sq hz0
  have hint2 : IntegrableOn (fun y : ℝ => y * Real.exp (-(y ^ 2) / 2)) (Ioi z) :=
    integrableOn_Ioi_mul_exp_neg_sq hz0
  have hmono : ∫ y in Ioi z, z * Real.exp (-(y ^ 2) / 2)
      ≤ ∫ y in Ioi z, y * Real.exp (-(y ^ 2) / 2) := by
    refine integral_mono_ae (hint1.const_mul z) hint2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_le_mul_of_nonneg_right (le_of_lt hy) (Real.exp_nonneg _)
  rw [integral_const_mul, integral_Ioi_mul_exp_neg_sq hz0] at hmono
  rw [le_div_iff₀ hz]
  linarith

private lemma gaussianPDFReal_zero_one (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
  simp only [gaussianPDFReal]
  norm_num

/-- `P(Y ≥ 0) = 1 / 2` for a standard Gaussian `Y`. -/
private lemma stdGaussian_real_Ici_zero :
    (ProbabilityTheory.stdGaussian ℝ).real (Ici (0 : ℝ)) = 1 / 2 := by
  have hNull : NullSingletonClass (ProbabilityTheory.stdGaussian ℝ) := by
    rw [Commons.Probability.Reflection.stdGaussian_real_eq]
    exact nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hsym : (ProbabilityTheory.stdGaussian ℝ).real (Ici (0 : ℝ))
      = (ProbabilityTheory.stdGaussian ℝ).real (Iic (0 : ℝ)) := by
    have h1 := map_measureReal_apply (μ := ProbabilityTheory.stdGaussian ℝ)
      (f := fun y : ℝ => -y) measurable_neg (s := Ici (0 : ℝ)) measurableSet_Ici
    have hpre : (fun y : ℝ => -y) ⁻¹' Ici (0 : ℝ) = Iic (0 : ℝ) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
      constructor <;> intro h <;> linarith
    rw [Commons.Probability.Gaussian.stdGaussian_map_neg] at h1
    rw [h1, hpre]
  have hzero : (ProbabilityTheory.stdGaussian ℝ).real ({(0:ℝ)} : Set ℝ) = 0 := by
    rw [Measure.real_def, NullSingletonClass.measure_singleton]
    simp
  have hU : Ici (0:ℝ) ∪ Iic (0:ℝ) = univ := by
    ext x; simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_univ, iff_true]
    exact le_total 0 x
  have hI : Ici (0:ℝ) ∩ Iic (0:ℝ) = {(0:ℝ)} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · rintro rfl; norm_num
  have hunion := measureReal_union_add_inter (μ := ProbabilityTheory.stdGaussian ℝ)
    (s := Ici (0:ℝ)) (t := Iic (0:ℝ)) measurableSet_Iic
  rw [hU, hI] at hunion
  have hμuniv : (ProbabilityTheory.stdGaussian ℝ).real univ = 1 := by
    rw [Measure.real_def, measure_univ]; simp
  rw [hμuniv, hzero, add_zero] at hunion
  rw [hsym] at hunion
  linarith

theorem stdGaussian_real_tail_le (z : ℝ) (hz : 0 < z) : (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | z ≤ y} ≤ min (1 / 2) (Real.exp (-(z ^ 2) / 2) / (Real.sqrt (2 * Real.pi) * z)) := by
  refine le_min ?_ ?_
  · calc (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | z ≤ y}
        ≤ (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | 0 ≤ y} :=
          Commons.Probability.Reflection.stdGaussian_real_tail_antitone (le_of_lt hz)
      _ = 1 / 2 := stdGaussian_real_Ici_zero
  · have hmain : (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | z ≤ y}
        ≤ Real.exp (-(z ^ 2) / 2) / (Real.sqrt (2 * Real.pi) * z) := by
      rw [Commons.Probability.Reflection.stdGaussian_real_eq, Measure.real_def,
        gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
      rw [ENNReal.toReal_ofReal (integral_nonneg (fun y => gaussianPDFReal_nonneg 0 1 y))]
      have hIci : ({y : ℝ | z ≤ y} : Set ℝ) = Set.Ici z := rfl
      rw [hIci, integral_Ici_eq_integral_Ioi]
      simp only [gaussianPDFReal_zero_one]
      rw [integral_const_mul]
      have hle := integral_Ioi_exp_neg_sq_le hz
      have hc0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
      calc (Real.sqrt (2 * Real.pi))⁻¹ * (∫ y in Ioi z, Real.exp (-(y ^ 2) / 2))
          ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(z ^ 2) / 2) / z) :=
            mul_le_mul_of_nonneg_left hle hc0
        _ = Real.exp (-(z ^ 2) / 2) / (Real.sqrt (2 * Real.pi) * z) := by
            field_simp
    exact hmain

end Commons.Probability.Gaussian
