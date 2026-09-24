import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law

/-!
# The first moment of the exponential partial sums on the canonical space

`canonM = ⊗_{n ∈ ℕ} Exp(1)` is the product of standard exponential laws on `ℝ^ℕ` and
`cSum x k = x 0 + ⋯ + x (k-1)`.  The integrand `exp (-(cSum x k))` depends only on the first
`k` coordinates, so the integral factorises as the `k`-th power of the single-coordinate
integral `∫ e^{-t} d Exp(1) = 1/2`:

  `∫ exp (-(cSum x k)) d canonM = (1/2)^k`.

The single-coordinate integral is computed from the (gamma) density of `expMeasure 1`.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- `∫ e^{-t}` against the standard exponential law `Exp(1) = expMeasure 1` equals `1/2`. -/
theorem integral_exp_neg_expMeasure_one :
    (∫ t : ℝ, Real.exp (-t) ∂ (ProbabilityTheory.expMeasure 1)) = 1/2 := by
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (by change Measurable (fun x => ENNReal.ofReal (gammaPDFReal 1 1 x))
        exact (measurable_gammaPDFReal 1 1).ennreal_ofReal)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hint : (fun x : ℝ => (gammaPDF 1 1 x).toReal • Real.exp (-x))
      = fun x => (Set.Ici (0:ℝ)).indicator (fun x => Real.exp (-(2*x))) x := by
    funext x
    rw [smul_eq_mul]
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos one_pos x)]
    rw [gammaPDFReal]
    split_ifs with h
    · rw [Real.Gamma_one, Real.one_rpow, sub_self, Real.rpow_zero,
        Set.indicator_of_mem (show x ∈ Set.Ici (0:ℝ) from h)]
      norm_num
      rw [← Real.exp_add]; congr 1; ring
    · rw [Set.indicator_of_notMem (by simpa using h)]
      ring
  rw [hint, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  rw [show (∫ x : ℝ in Set.Ioi 0, Real.exp (-(2*x)))
        = ∫ x : ℝ in Set.Ioi 0, Real.exp ((-2:ℝ)*x) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    show Real.exp (-(2*x)) = Real.exp ((-2:ℝ)*x)
    congr 1; ring]
  rw [integral_exp_mul_Ioi (by norm_num : (-2:ℝ) < 0) 0]
  norm_num

theorem moment_cSum (k : ℕ) : (∫ x : ℕ → ℝ, Real.exp (-(cSum x k)) ∂canonM) = (1/2:ℝ)^k := by
  set I : Finset ℕ := Finset.range k with hI
  have hcard : Fintype.card ↥I = k := by rw [Fintype.card_coe, hI, Finset.card_range]
  have hmap : canonM.map (Finset.restrict I) = Measure.pi (fun _ : ↥I => expLaw) := by
    show (Measure.infinitePi (fun _ : ℕ => expLaw)).map (Finset.restrict I) = _
    exact Measure.infinitePi_map_restrict (fun _ : ℕ => expLaw)
  have hcs : ∀ x : ℕ → ℝ, (∑ i : ↥I, (Finset.restrict I x) i) = cSum x k := by
    intro x
    show (∑ i : ↥I, x i) = cSum x k
    rw [cSum, hI, Finset.sum_coe_sort]
  have hf : Measurable (fun y : ↥I → ℝ => Real.exp (-(∑ i, y i))) := by fun_prop
  have step1 : (∫ x : ℕ → ℝ, Real.exp (-(cSum x k)) ∂canonM)
      = ∫ x : ℕ → ℝ, Real.exp (-(∑ i : ↥I, (Finset.restrict I x) i)) ∂canonM := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hcs x]
  rw [step1]
  have key : (∫ x : ℕ → ℝ, Real.exp (-(∑ i : ↥I, (Finset.restrict I x) i)) ∂canonM)
      = ∫ y : ↥I → ℝ, Real.exp (-(∑ i : ↥I, y i)) ∂ Measure.pi (fun _ : ↥I => expLaw) := by
    rw [← hmap]
    exact (integral_map (μ := canonM) (φ := Finset.restrict I)
            (f := fun y : ↥I → ℝ => Real.exp (-(∑ i, y i)))
            (Finset.measurable_restrict I).aemeasurable hf.aestronglyMeasurable).symm
  rw [key]
  have hcongr : (fun y : ↥I → ℝ => Real.exp (-(∑ i, y i)))
      = fun y => ∏ i, (fun t : ℝ => Real.exp (-t)) (y i) := by
    funext y
    rw [← Finset.sum_neg_distrib (f := fun i : ↥I => y i), Real.exp_sum]
  rw [hcongr, integral_fintype_prod_eq_pow (fun t : ℝ => Real.exp (-t)) (μ := expLaw), hcard]
  rw [show (∫ t : ℝ, Real.exp (-t) ∂expLaw) = 1/2 from integral_exp_neg_expMeasure_one]

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
