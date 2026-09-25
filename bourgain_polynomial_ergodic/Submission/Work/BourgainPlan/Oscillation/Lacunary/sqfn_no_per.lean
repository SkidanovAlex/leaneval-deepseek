import Submission.Commons.Analysis.Fourier.multiplier_square_function_l2

/-!
# The circle square-function bound without the periodicity hypothesis

`Commons.Analysis.Fourier.multiplier_square_function_l2` proves, for a family of bounded measurable
circle multipliers `m j`, the `ℓ²(ℤ)` square-function estimate

`∫⁻_{m'} Σ'_j |(m j · P)^(m')|² d# ≤ A² ∫⁻_n |f n|² d#`,

under the additional hypothesis that every `m j` is `1`-periodic.  That hypothesis is never used in
the proof (the estimate only ever sees the multipliers through their `L²(0,1]` integrals and their
pointwise bounds), but it is a *hypothesis* of the published statement, so it cannot be supplied for
the genuinely non-periodic cut multipliers `r θ · 1_{d_i < θ ≤ c_i}` of the lacunary oscillation
argument.

This file records the same statement with the periodicity hypothesis dropped, by the same proof.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

set_option linter.unusedVariables false

/-- **Plancherel square function for measurable bounded multipliers** (no periodicity needed).

For measurable multipliers `m j : ℝ → ℂ` whose pointwise squared moduli are summable with
`∑'_j ‖m j θ‖² ≤ A²`, and a finitely supported `f`, the `ℓ²(ℤ)` norm of the square function
`Σ'_j |(m j · f̂)∨|²` is bounded by `A² ∫⁻‖f‖²`. -/
theorem sqfn_no_per (m : ℕ → ℝ → ℂ) (A : ℝ)
    (hm : ∀ j, Measurable (m j))
    (hb : ∀ j, ∃ C : ℝ, ∀ θ, ‖m j θ‖ ≤ C)
    (hsum : ∀ θ, Summable (fun j : ℕ => ‖m j θ‖ ^ 2) ∧ ∑' j : ℕ, ‖m j θ‖ ^ 2 ≤ A ^ 2)
    (f : ℤ → ℂ) (s : Finset ℤ) :
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
    exact Commons.Analysis.Fourier.plancherel_circle_enorm_sq (m j) P (hm j) (hb j) hPmem
  rw [hLHS]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun t => ?_)
  have hI0 : ∀ j, 0 ≤ ∫ θ in (0:ℝ)..1, ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2 := fun j =>
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by positivity)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hI0 j)]
  refine le_trans (ENNReal.ofReal_le_ofReal
    (Commons.Analysis.Fourier.sum_intervalIntegral_sq_mul_le m A hm hb hsum P hPm hPb t)) ?_
  rw [ENNReal.ofReal_mul (sq_nonneg A)]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  have hplanch : ∫ θ in (0:ℝ)..1, ‖P θ‖ ^ 2 = ∑ n ∈ s, ‖f n‖ ^ 2 := by
    rw [hPdef]
    exact (Commons.Analysis.Fourier.plancherel_trig_polynomial s f).symm
  rw [hplanch, ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg _)]
  calc ∑ n ∈ s, ENNReal.ofReal (‖f n‖ ^ 2)
      = ∑ n ∈ s, ‖f n‖ₑ ^ (2:ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Commons.Analysis.Fourier.enorm_complex_pow_two]
    _ ≤ ∑' n : ℤ, ‖f n‖ₑ ^ (2:ℝ) := ENNReal.sum_le_tsum s
    _ = ∫⁻ n, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        (lintegral_count (fun n : ℤ => ‖f n‖ₑ ^ (2:ℝ))).symm

end

end Work.BourgainPlan.Oscillation.Lacunary
