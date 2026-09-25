import Mathlib
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial
import Submission.Commons.Analysis.Fourier.multiplier_square_function_l2
import Submission.Commons.Analysis.Fourier.nested_indicator_l2_bound

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped BigOperators ENNReal

set_option linter.unusedVariables false

/-- **Transfer of a maximal `ℓ²` bound to a fixed bounded multiplier.**

Let `χ : ℕ → ℝ → ℂ` be a family whose maximal Fourier-coefficient operator is bounded on
`L²(0,1)` by `B`: for every `Q ∈ L²(0,1)`,

`∫⁻_m (⨆_k ‖∫_0^1 χ_k(θ) Q(θ) e(-2πi m θ) dθ‖)² dcount ≤ B² ∫_0^1 ‖Q‖²`.

If `Ψ` is measurable with `‖Ψ‖ ≤ cap`, then the same maximal operator with symbols `Ψ χ_k`
is bounded by `B·cap`, at least when tested against finitely supported coefficient sequences:
the symbol `Ψ` is simply absorbed into the function `Q ↦ Ψ Q`, so the hypothesis applies to
`G = Ψ · F` where `F` is the trigonometric polynomial with coefficients `g`.  Plancherel for
trigonometric polynomials converts `∫_0^1 ‖F‖²` into the `ℓ²` norm of `g`. -/
theorem maximal_l2_of_fixed_multiplier
    (χ : ℕ → ℝ → ℂ) (Ψ : ℝ → ℂ) (B cap : ℝ) (hB : 0 ≤ B) (hcap : 0 ≤ cap)
    (hmax : ∀ (Q : ℝ → ℂ), MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, χ k θ * Q θ *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ))
    (hΨm : Measurable Ψ) (hΨbd : ∀ θ, ‖Ψ θ‖ ≤ cap) :
    ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, (Ψ θ * χ k θ) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (B ^ 2 * cap ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by
  intro g s hgs
  classical
  -- The trigonometric polynomial with coefficients `g` supported on `s`.
  let F : ℝ → ℂ := fun θ =>
    ∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))
  -- The same polynomial multiplied by the fixed symbol `Ψ`.
  let G : ℝ → ℂ := fun θ => Ψ θ * F θ
  have hFcont : Continuous F := by
    change Continuous (fun θ : ℝ =>
      ∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ)))
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  have hFbd : ∀ θ, ‖F θ‖ ≤ ∑ j ∈ s, ‖g j‖ := by
    intro θ
    change ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))‖
      ≤ ∑ j ∈ s, ‖g j‖
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hE : ‖Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))‖ = 1 := by
      rw [show 2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ)
            = ((2 * Real.pi * (j:ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hE, mul_one]
  have hFmem : MemLp F 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound hFcont.measurable.aestronglyMeasurable (∑ j ∈ s, ‖g j‖)
      (ae_of_all _ hFbd)
  have hGmeas : Measurable G := hΨm.mul hFcont.measurable
  have hGbd : ∀ θ, ‖G θ‖ ≤ cap * ∑ j ∈ s, ‖g j‖ := by
    intro θ
    show ‖Ψ θ * F θ‖ ≤ cap * ∑ j ∈ s, ‖g j‖
    rw [norm_mul]
    exact mul_le_mul (hΨbd θ) (hFbd θ) (norm_nonneg _) hcap
  have hGmem : MemLp G 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound hGmeas.aestronglyMeasurable (cap * ∑ j ∈ s, ‖g j‖) (ae_of_all _ hGbd)
  -- Apply the hypothesis to `G = Ψ · F`.
  have hhmax := hmax G hGmem
  -- The integrands of the two maximal functions agree because `χ_k · G = (Ψ χ_k) · F`.
  have hLHS_eq :
      (∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, (Ψ θ * χ k θ) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count)
        = ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, χ k θ * G θ *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count := by
    apply lintegral_congr
    intro m
    congr 1
    apply iSup_congr
    intro k
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    show (Ψ θ * χ k θ) *
          (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))
        = χ k θ * (Ψ θ * (∑ j ∈ s, g j *
            Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))
    ring
  -- Pointwise comparison between `‖G‖` and `‖F‖`.
  have hpt : ∀ θ : ℝ, ‖G θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (cap ^ 2) * ‖F θ‖ₑ ^ (2:ℝ) := by
    intro θ
    have hbdθ : ‖G θ‖ ≤ cap * ‖F θ‖ := by
      show ‖Ψ θ * F θ‖ ≤ cap * ‖F θ‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hΨbd θ) (norm_nonneg _)
    rw [enorm_complex_pow_two, enorm_complex_pow_two, ← ENNReal.ofReal_mul (sq_nonneg cap)]
    apply ENNReal.ofReal_le_ofReal
    calc ‖G θ‖ ^ 2 ≤ (cap * ‖F θ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbdθ 2
      _ = cap ^ 2 * ‖F θ‖ ^ 2 := by ring
  have hstepG : ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖G θ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (cap ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖F θ‖ₑ ^ (2:ℝ) := by
    calc ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖G θ‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (cap ^ 2) * ‖F θ‖ₑ ^ (2:ℝ) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (cap ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖F θ‖ₑ ^ (2:ℝ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Plancherel: the `L²` norm of `F` is the `ℓ²` norm of the coefficients `g`.
  have hFint : ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖F θ‖ₑ ^ (2:ℝ)
      = ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by
    have hplanch : ∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2 = ∑ j ∈ s, ‖g j‖ ^ 2 := by
      show ∫ θ in (0:ℝ)..1,
          ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))‖ ^ 2
        = ∑ j ∈ s, ‖g j‖ ^ 2
      exact (plancherel_trig_polynomial s g).symm
    have h1 : ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖F θ‖ₑ ^ (2:ℝ)
        = ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2) := by
      rw [NestedIndicator.lintegral_enorm_rpow_two (volume.restrict (Set.Ioc (0:ℝ) 1)) hFmem]
      congr 1
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      apply integral_congr_ae
      filter_upwards with a
      rw [Real.rpow_two]
    have h2 : ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2)
        = ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by
      rw [hplanch, ENNReal.ofReal_sum_of_nonneg (fun j hj => sq_nonneg _)]
      rw [Finset.sum_congr rfl (fun j hj => (enorm_complex_pow_two (g j)).symm)]
      rw [lintegral_count]
      exact (tsum_eq_sum (s := s) (fun m hm => by
        rw [hgs m hm]
        simp)).symm
    rw [h1, h2]
  calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, (Ψ θ * χ k θ) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count
      = ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, χ k θ * G θ *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count := hLHS_eq
    _ ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖G θ‖ₑ ^ (2:ℝ) := hhmax
    _ ≤ ENNReal.ofReal (B ^ 2) * (ENNReal.ofReal (cap ^ 2) *
          ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖F θ‖ₑ ^ (2:ℝ)) := mul_le_mul' le_rfl hstepG
    _ = ENNReal.ofReal (B ^ 2 * cap ^ 2) *
          ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖F θ‖ₑ ^ (2:ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg B)]
    _ = ENNReal.ofReal (B ^ 2 * cap ^ 2) *
          ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by rw [hFint]

end Commons.Analysis.Fourier
