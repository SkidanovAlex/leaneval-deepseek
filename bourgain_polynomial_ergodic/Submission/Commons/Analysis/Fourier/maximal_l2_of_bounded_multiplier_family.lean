import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Fourier.multiplier_plancherel_circle
import Submission.Commons.Analysis.Fourier.multiplier_square_function_l2
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- For a nonnegative `ℝ≥0∞`-valued sequence, the square of the supremum is bounded by the
sum of the squares. -/
lemma iSup_sq_le_tsum_sq (b : ℕ → ℝ≥0∞) :
    (⨆ n, b n) ^ (2 : ℝ) ≤ ∑' n, b n ^ (2 : ℝ) := by
  have hle : (⨆ n, b n) ≤ (∑' n, b n ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
    apply iSup_le; intro n
    calc b n = (b n ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
            rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ (∑' n, b n ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
            ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun n => b n ^ (2 : ℝ)) n) (by norm_num)
  calc (⨆ n, b n) ^ (2 : ℝ)
      ≤ ((∑' n, b n ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ∑' n, b n ^ (2 : ℝ) := by rw [← ENNReal.rpow_mul]; norm_num

theorem maximal_l2_of_bounded_multiplier_family
    (ψ : ℕ → ℝ → ℂ) (A : ℕ → ℝ)
    (hψ : ∀ n, Measurable (ψ n)) (hbd : ∀ n θ, ‖ψ n θ‖ ≤ A n)
    (hsum : Summable (fun n => A n ^ 2)) :
    ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ n : ℕ, ‖∫ θ in (0:ℝ)..1, ψ n θ *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (∑' n, A n ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  intro g s hgs
  let F : ℝ → ℂ := fun θ => ∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))
  let c : ℕ → ℤ → ℂ := fun n m =>
    ∫ θ in (0:ℝ)..1, ψ n θ * F θ * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))
  change ∫⁻ m : ℤ, (⨆ n : ℕ, ‖c n m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (∑' n, A n ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
  -- `F` is the trigonometric polynomial with coefficients `g` on `s`.
  have hFcont : Continuous F := by
    change Continuous (fun θ : ℝ =>
      ∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ)))
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  have hFmeas : Measurable F := hFcont.measurable
  set C : ℝ := ∑ j ∈ s, ‖g j‖ with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hCbd : ∀ θ, ‖F θ‖ ≤ C := by
    intro θ
    change ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))‖ ≤ C
    rw [hCdef]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hE : ‖Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))‖ = 1 := by
      rw [show 2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ)
            = ((2 * Real.pi * (j:ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hE, mul_one]
  have hFmem : MemLp F 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound hFmeas.aestronglyMeasurable C (ae_of_all _ hCbd)
  -- Step 1: `(sup_n b_n)^2 ≤ ∑_n b_n^2` pointwise, then integrate.
  have hstep1 : ∫⁻ m : ℤ, (⨆ n : ℕ, ‖c n m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, ∑' n : ℕ, ‖c n m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
    lintegral_mono (fun m => iSup_sq_le_tsum_sq (fun n => ‖c n m‖ₑ))
  -- `K` is the right-hand-side `ℓ²` norm of `g`.
  set K : ℝ≥0∞ := ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hKdef
  have hFK : ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2) = K := by
    rw [hKdef, lintegral_count]
    have hplanch : ∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2 = ∑ j ∈ s, ‖g j‖ ^ 2 := by
      change ∫ θ in (0:ℝ)..1,
          ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))‖ ^ 2
        = ∑ j ∈ s, ‖g j‖ ^ 2
      exact (plancherel_trig_polynomial s g).symm
    rw [hplanch, ENNReal.ofReal_sum_of_nonneg (fun j hj => sq_nonneg _)]
    rw [Finset.sum_congr rfl (fun j hj => (enorm_complex_pow_two (g j)).symm)]
    exact (tsum_eq_sum (s := s) (fun m hm => by rw [hgs m hm]; simp)).symm
  -- Termwise: Plancherel for the multiplier `ψ n`, then the pointwise bound `‖ψ n θ‖ ≤ A n`.
  have hterm : ∀ n : ℕ,
      ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖ψ n θ‖ ^ 2 * ‖F θ‖ ^ 2)
        ≤ ENNReal.ofReal (A n ^ 2) * ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2) := by
    intro n
    have hIntψ : IntervalIntegrable (fun θ : ℝ => ‖ψ n θ‖ ^ 2 * ‖F θ‖ ^ 2) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine Integrable.of_bound ?_ (A n ^ 2 * C ^ 2) (ae_of_all _ fun θ => ?_)
      · exact (((hψ n).norm.pow_const 2).mul (hFmeas.norm.pow_const 2)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbd n θ) 2)
          (pow_le_pow_left₀ (norm_nonneg _) (hCbd θ) 2) (sq_nonneg _) (sq_nonneg _)
    have hIntA : IntervalIntegrable (fun θ : ℝ => A n ^ 2 * ‖F θ‖ ^ 2) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine Integrable.of_bound ?_ (A n ^ 2 * C ^ 2) (ae_of_all _ fun θ => ?_)
      · exact (measurable_const.mul (hFmeas.norm.pow_const 2)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hCbd θ) 2) (sq_nonneg _)
    have hIntmono : ∫ θ in (0:ℝ)..1, ‖ψ n θ‖ ^ 2 * ‖F θ‖ ^ 2
        ≤ A n ^ 2 * ∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2 := by
      have h1 : ∫ θ in (0:ℝ)..1, ‖ψ n θ‖ ^ 2 * ‖F θ‖ ^ 2
          ≤ ∫ θ in (0:ℝ)..1, A n ^ 2 * ‖F θ‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hIntψ hIntA
          (fun x hx => mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hbd n x) 2) (sq_nonneg _))
      rwa [intervalIntegral.integral_const_mul] at h1
    rw [← ENNReal.ofReal_mul (sq_nonneg (A n))]
    exact ENNReal.ofReal_le_ofReal hIntmono
  calc ∫⁻ m : ℤ, (⨆ n : ℕ, ‖c n m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, ∑' n : ℕ, ‖c n m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := hstep1
    _ = ∑' n : ℕ, ∫⁻ m : ℤ, ‖c n m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
          rw [lintegral_count, ENNReal.tsum_comm]
          exact tsum_congr (fun n => (lintegral_count (fun m : ℤ => ‖c n m‖ₑ ^ (2:ℝ))).symm)
    _ = ∑' n : ℕ, ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖ψ n θ‖ ^ 2 * ‖F θ‖ ^ 2) := by
          refine tsum_congr (fun n => ?_)
          dsimp only [c]
          rw [lintegral_count]
          exact plancherel_circle_enorm_sq (ψ n) F (hψ n) ⟨A n, hbd n⟩ hFmem
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (A n ^ 2) * ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2) :=
          ENNReal.tsum_le_tsum hterm
    _ = (∑' n : ℕ, ENNReal.ofReal (A n ^ 2)) * ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2) :=
          ENNReal.tsum_mul_right
    _ = ENNReal.ofReal (∑' n, A n ^ 2) * ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖F θ‖ ^ 2) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsum]
    _ = ENNReal.ofReal (∑' n, A n ^ 2) * K := by rw [hFK]
    _ = ENNReal.ofReal (∑' n, A n ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
          rw [hKdef]

end

end Commons.Analysis.Fourier