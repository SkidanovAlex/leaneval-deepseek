import Mathlib.Analysis.Fourier.AddCircle
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

set_option linter.unusedVariables false

/-- The `enorm` of a complex number to the power `2` is the `ofReal` of the square of its
norm. -/
lemma enorm_complex_pow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  have h : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
    rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]; norm_cast
  rw [h, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  exact (ENNReal.ofReal_pow (norm_nonneg z) 2).symm

/-- The interval integral against a character `e(-2πi n θ)` is the `n`-th `fourierCoeffOn`
coefficient on `[0,1]`. -/
lemma intervalIntegral_char_eq_fourierCoeffOn (g : ℝ → ℂ) (n : ℤ) :
    ∫ θ in (0:ℝ)..1, g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
      = fourierCoeffOn (by norm_num : (0:ℝ) < 1) g n := by
  have hfourier : ∀ x : ℝ, fourier (-n) (x : AddCircle (1-0:ℝ))
      = Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(x:ℂ))) := by
    intro x
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [fourierCoeffOn_eq_integral]
  rw [show (1:ℝ) / ((1:ℝ) - (0:ℝ)) = 1 by norm_num, one_smul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [smul_eq_mul]
  rw [hfourier]
  ring

/-- **Plancherel for a bounded measurable circle multiplier, in `ℝ≥0∞` form.**  For a bounded
measurable `m : ℝ → ℂ` and a square-integrable periodic `g`, the `ℝ≥0∞`-valued sum of the
squared `enorm`s of the Fourier coefficients of `m · g` equals the weighted `L²` integral:

`∑'_n ‖∫_{[0,1]} m(θ) g(θ) e(-2πi n θ) dθ‖ₑ² = ofReal (∫_{[0,1]} ‖m(θ)‖² ‖g(θ)‖² dθ)`.

This is the `ℝ≥0∞` companion of `Commons.Analysis.Fourier.multiplier_plancherel_circle`; being
stated with `∑'` in `ℝ≥0∞` it requires no summability side conditions. -/
theorem plancherel_circle_enorm_sq (m g : ℝ → ℂ) (hm : Measurable m)
    (hmb : ∃ C : ℝ, ∀ θ, ‖m θ‖ ≤ C)
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    (∑' n : ℤ, ‖∫ θ in (0:ℝ)..1,
        m θ * g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ))
      = ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖m θ‖ ^ 2 * ‖g θ‖ ^ 2) := by
  have hab : (0:ℝ) < 1 := by norm_num
  obtain ⟨C, hC⟩ := hmb
  have hm_top : MemLp m ⊤ (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound (p := ⊤) hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hhmg : MemLp (fun θ => m θ * g θ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.ae_eq (ae_of_all _ fun θ => mul_comm (g θ) (m θ)) (hg.mul' hm_top)
  have hsumm : Summable (fun n : ℤ => ‖fourierCoeffOn hab (fun θ => m θ * g θ) n‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn hab hhmg).summable
  have hcongr : (∑' n : ℤ, ‖∫ θ in (0:ℝ)..1,
        m θ * g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ))
      = ∑' n : ℤ, ENNReal.ofReal (‖fourierCoeffOn hab (fun θ => m θ * g θ) n‖ ^ 2) := by
    refine tsum_congr (fun n => ?_)
    rw [enorm_complex_pow_two, intervalIntegral_char_eq_fourierCoeffOn]
  rw [hcongr, ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsumm,
    (hasSum_sq_fourierCoeffOn hab hhmg).tsum_eq]
  congr 1
  rw [show ((1:ℝ) - 0)⁻¹ = 1 by norm_num, one_smul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [norm_mul, mul_pow]

/-- **Finite square-function bound.**  Let `m j` be bounded measurable multipliers whose squared
moduli have summable sums bounded by `A²`, and let `P` be a bounded measurable function.  Then
for every finite set `t` of indices,

`∑_{j ∈ t} ∫_{[0,1]} ‖m j(θ)‖² ‖P(θ)‖² dθ ≤ A² ∫_{[0,1]} ‖P(θ)‖² dθ`.

This is the pointwise-bound step of the square-function estimate: the finite sum of symbols is
bounded by the (summable) full sum, and linearity of the integral makes the conclusion
elementary. -/
lemma sum_intervalIntegral_sq_mul_le (m : ℕ → ℝ → ℂ) (A : ℝ)
    (hm : ∀ j, Measurable (m j))
    (hb : ∀ j, ∃ C : ℝ, ∀ θ, ‖m j θ‖ ≤ C)
    (hsum : ∀ θ, Summable (fun j : ℕ => ‖m j θ‖ ^ 2) ∧ ∑' j : ℕ, ‖m j θ‖ ^ 2 ≤ A ^ 2)
    (P : ℝ → ℂ) (hPm : Measurable P) (hPb : ∃ M : ℝ, ∀ θ, ‖P θ‖ ≤ M) (t : Finset ℕ) :
    ∑ j ∈ t, ∫ θ in (0:ℝ)..1, ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2
      ≤ A ^ 2 * ∫ θ in (0:ℝ)..1, ‖P θ‖ ^ 2 := by
  have hA : 0 ≤ A ^ 2 := le_trans (tsum_nonneg fun j => sq_nonneg _) (hsum 0).2
  obtain ⟨M, hM⟩ := hPb
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hpoint : ∀ θ, ∑ j ∈ t, ‖m j θ‖ ^ 2 ≤ A ^ 2 := fun θ =>
    le_trans ((hsum θ).1.sum_le_tsum t (fun j _ => sq_nonneg _)) (hsum θ).2
  have hInt : ∀ j ∈ t, IntervalIntegrable (fun θ => ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2) volume 0 1 := by
    intro j _
    obtain ⟨C, hC⟩ := hb j
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine Integrable.of_bound ?_ (C ^ 2 * M ^ 2) (ae_of_all _ fun θ => ?_)
    · exact (((hm j).norm.pow_const 2).mul (hPm.norm.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hC θ) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hM θ) 2) (sq_nonneg _) (sq_nonneg _)
  have hIntA : IntervalIntegrable (fun θ => A ^ 2 * ‖P θ‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine Integrable.of_bound ?_ (A ^ 2 * M ^ 2) (ae_of_all _ fun θ => ?_)
    · exact (measurable_const.mul (hPm.norm.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hM θ) 2) hA
  rw [(intervalIntegral.integral_finsetSum hInt).symm]
  have hIntsum : IntervalIntegrable (fun x : ℝ => ∑ i ∈ t, ‖m i x‖ ^ 2 * ‖P x‖ ^ 2)
      volume 0 1 := by
    have h := IntervalIntegrable.sum t hInt
    rw [show (∑ i ∈ t, (fun θ => ‖m i θ‖ ^ 2 * ‖P θ‖ ^ 2 : ℝ → ℝ))
        = (fun x : ℝ => ∑ i ∈ t, ‖m i x‖ ^ 2 * ‖P x‖ ^ 2) from by
      ext x; rw [Finset.sum_apply]] at h
    exact h
  refine le_trans (intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    hIntsum hIntA (fun x _ => ?_)) ?_
  · rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg _)
  · exact le_of_eq (intervalIntegral.integral_const_mul (A ^ 2) (fun θ => ‖P θ‖ ^ 2))

/-- **Square-function bound for a family of bounded multipliers on the circle.**  Let
`m : ℕ → ℝ → ℂ` be measurable, `1`-periodic, bounded multipliers whose squared moduli have
*summable* and bounded sums: `Summable (fun j => ‖m j θ‖²)` and `∑'_j ‖m j θ‖² ≤ A²` for every
`θ`.  Then the square function of the associated multiplier operators is bounded on `ℓ²(ℤ)`:

`∫⁻_m ∑'_j ‖(m j · f̂)∨(m)‖² ∂count ≤ A² ∫⁻_n ‖f n‖² ∂count`.

(The summability hypothesis is necessary: in `ℝ`, `∑'` of a non-summable nonnegative family is
`0`, so without it the hypothesis would be vacuous exactly when the family of squares
diverges.)  This is the standard "square function" consumption of Plancherel
(`Commons.Analysis.Fourier.multiplier_plancherel_circle` plus Tonelli): it converts a
pointwise bound on a family of symbols into an `ℓ²(ℤ)` bound for the ℓ²-sum of the associated
operators, and is the tool behind Bourgain's sparsification step (his (4.31)). -/
theorem multiplier_square_function_l2 (m : ℕ → ℝ → ℂ) (A : ℝ)
    (hm : ∀ j, Measurable (m j)) (hper : ∀ j, Function.Periodic (m j) 1)
    (hb : ∀ j, ∃ C : ℝ, ∀ θ, ‖m j θ‖ ≤ C)
    (hsum : ∀ θ, Summable (fun j : ℕ => ‖m j θ‖ ^ 2) ∧ ∑' j : ℕ, ‖m j θ‖ ^ 2 ≤ A ^ 2)
    (f : ℤ → ℂ) (s : Finset ℤ) (hf : ∀ n, n ∉ s → f n = 0) :
    ∫⁻ m', (∑' j : ℕ, ‖∫ θ in (0:ℝ)..1,
        m j θ * (∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
          * Complex.exp (-(2*Real.pi*Complex.I*(((m':ℤ):ℂ))*(θ:ℂ)))‖ₑ^(2:ℝ))
      ∂MeasureTheory.Measure.count
    ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ n, ‖f n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  classical
  set P : ℝ → ℂ := fun θ => ∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))
    with hPdef
  have hPcont : Continuous P := by
    rw [hPdef]
    refine continuous_finsetSum _ (fun n _ => ?_)
    fun_prop
  have hPm : Measurable P := hPcont.measurable
  have hMbound : ∀ θ : ℝ, ‖P θ‖ ≤ ∑ n ∈ s, ‖f n‖ := fun θ => by
    rw [hPdef]
    calc ‖∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖
        ≤ ∑ n ∈ s, ‖f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ s, ‖f n‖ := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          have hexp : ‖Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ = 1 := by
            rw [show 2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)
                  = ((2*Real.pi*(n:ℝ)*θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
            rw [Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, hexp, mul_one]
  have hPb : ∃ M : ℝ, ∀ θ, ‖P θ‖ ≤ M := ⟨_, hMbound⟩
  have hPmem : MemLp P 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound hPm.aestronglyMeasurable (∑ n ∈ s, ‖f n‖) (ae_of_all _ hMbound)
  have hLHS : ∫⁻ m', (∑' j : ℕ, ‖∫ θ in (0:ℝ)..1,
        m j θ * P θ * Complex.exp (-(2*Real.pi*Complex.I*(((m':ℤ):ℂ))*(θ:ℂ)))‖ₑ^(2:ℝ))
      ∂MeasureTheory.Measure.count
      = ∑' j : ℕ, ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2) := by
    rw [lintegral_count, ENNReal.tsum_comm]
    refine tsum_congr (fun j => ?_)
    exact plancherel_circle_enorm_sq (m j) P (hm j) (hb j) hPmem
  rw [hLHS]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun t => ?_)
  have hI0 : ∀ j, 0 ≤ ∫ θ in (0:ℝ)..1, ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2 := fun j =>
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by positivity)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hI0 j)]
  refine le_trans (ENNReal.ofReal_le_ofReal
    (sum_intervalIntegral_sq_mul_le m A hm hb hsum P hPm hPb t)) ?_
  rw [ENNReal.ofReal_mul (sq_nonneg A)]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  have hplanch : ∫ θ in (0:ℝ)..1, ‖P θ‖ ^ 2 = ∑ n ∈ s, ‖f n‖ ^ 2 := by
    rw [hPdef]
    exact (plancherel_trig_polynomial s f).symm
  rw [hplanch, ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg _)]
  calc ∑ n ∈ s, ENNReal.ofReal (‖f n‖ ^ 2)
      = ∑ n ∈ s, ‖f n‖ₑ ^ (2:ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [enorm_complex_pow_two]
    _ ≤ ∑' n : ℤ, ‖f n‖ₑ ^ (2:ℝ) := ENNReal.sum_le_tsum s
    _ = ∫⁻ n, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        (lintegral_count (fun n : ℤ => ‖f n‖ₑ ^ (2:ℝ))).symm

end

end Commons.Analysis.Fourier