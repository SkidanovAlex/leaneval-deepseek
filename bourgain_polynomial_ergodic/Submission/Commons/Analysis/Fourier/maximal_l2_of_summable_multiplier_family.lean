import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Fourier.multiplier_plancherel_circle
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- The `enorm` of a complex number is the `ofReal` of its norm. -/
private lemma enorm_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  simp [enorm_eq_nnnorm]

/-- Squaring commutes with a supremum of nonnegative extended reals. -/
private lemma iSup_sq' (x : ℕ → ℝ≥0∞) : (⨆ n, x n) ^ 2 = ⨆ n, (x n) ^ 2 := by
  apply le_antisymm
  · rw [pow_two, ENNReal.mul_iSup]
    refine iSup_le (fun n => ?_)
    rw [ENNReal.iSup_mul]
    refine iSup_le (fun m => ?_)
    have h : x m * x n ≤ x m ^ 2 ⊔ x n ^ 2 := by
      by_cases hc : x m ≤ x n
      · calc x m * x n ≤ x n * x n := mul_le_mul' hc le_rfl
          _ = x n ^ 2 := by rw [pow_two]
          _ ≤ x m ^ 2 ⊔ x n ^ 2 := le_sup_right
      · push Not at hc
        calc x m * x n ≤ x m * x m := mul_le_mul' le_rfl hc.le
          _ = x m ^ 2 := by rw [pow_two]
          _ ≤ x m ^ 2 ⊔ x n ^ 2 := le_sup_left
    exact le_trans h (sup_le (le_iSup (fun k => x k ^ 2) m) (le_iSup (fun k => x k ^ 2) n))
  · refine iSup_le (fun n => ?_)
    exact pow_le_pow_left' (le_iSup (fun k => x k) n) 2

/-- Cauchy--Schwarz for a countable supremum in `ℝ≥0∞`: the square of the supremum is
dominated by the sum of the squares. -/
private lemma sup_rpow_two_le_tsum (x : ℕ → ℝ≥0∞) :
    (⨆ n, x n) ^ (2 : ℝ) ≤ ∑' n, (x n) ^ (2 : ℝ) := by
  have h1 : (⨆ n, x n) ^ (2 : ℝ) = (⨆ n, x n) ^ 2 := ENNReal.rpow_natCast _ 2
  have h2 : ∀ n, (x n) ^ (2:ℝ) = (x n) ^ 2 := fun n => ENNReal.rpow_natCast _ 2
  rw [h1, show (∑' n, (x n) ^ (2:ℝ)) = ∑' n, (x n) ^ 2 from tsum_congr h2, iSup_sq']
  exact iSup_le (fun n => ENNReal.le_tsum (f := fun n => (x n) ^ 2) n)

/-- **Plancherel summability for a bounded multiplier.**  The squared Fourier coefficients of
the product of a bounded measurable multiplier with a square-integrable function are summable;
this is the summability underlying `Commons.Analysis.Fourier.multiplier_plancherel_circle`. -/
private lemma summable_multiplier_plancherel (m g : ℝ → ℂ) (hm : Measurable m)
    (hmb : ∃ C : ℝ, ∀ θ, ‖m θ‖ ≤ C)
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    Summable (fun n : ℤ => ‖∫ θ in (0:ℝ)..1, m θ * g θ *
        Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))‖ ^ 2) := by
  have hab : (0:ℝ) < 1 := by norm_num
  obtain ⟨C, hC⟩ := hmb
  have hm_top : MemLp m ⊤ (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound (p := ⊤) hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hhmg : MemLp (fun θ => m θ * g θ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.ae_eq (ae_of_all _ fun θ => mul_comm (g θ) (m θ)) (hg.mul' hm_top)
  have hfourier : ∀ (n : ℤ) (x : ℝ), fourier (-n) (x : AddCircle (1-0:ℝ))
      = Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(x:ℂ))) := by
    intro n x
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have key : ∀ n : ℤ, fourierCoeffOn hab (fun θ => m θ * g θ) n
      = ∫ θ in (0:ℝ)..1, m θ * g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))) := by
    intro n
    rw [fourierCoeffOn_eq_integral]
    rw [show (1:ℝ) / ((1:ℝ) - (0:ℝ)) = 1 by norm_num, one_smul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [smul_eq_mul]
    rw [hfourier]
    ring
  refine (hasSum_sq_fourierCoeffOn hab hhmg).summable.congr (fun n => ?_)
  rw [key n]

/-- The pointwise bound on the integrals of a bounded multiplier against a continuous function:
`∫ ‖ψ‖² ‖f‖² ≤ A² ∫ ‖f‖²` whenever `‖ψ‖ ≤ A`. -/
private lemma integral_norm_sq_le (ψ : ℝ → ℂ) (hψ : Measurable ψ) (A : ℝ) (hA : 0 ≤ A)
    (hbd : ∀ θ, ‖ψ θ‖ ≤ A) (f : ℝ → ℂ) (hf : Continuous f) :
    ∫ θ in (0:ℝ)..1, ‖ψ θ‖^2 * ‖f θ‖^2 ≤ A^2 * ∫ θ in (0:ℝ)..1, ‖f θ‖^2 := by
  have hle : ∀ θ, ‖ψ θ‖^2 * ‖f θ‖^2 ≤ A^2 * ‖f θ‖^2 := by
    intro θ
    have h1 : ‖ψ θ‖^2 ≤ A^2 := by
      have := hbd θ
      nlinarith [norm_nonneg (ψ θ)]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hInt2 : Integrable (fun θ => A^2 * ‖f θ‖^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0:ℝ) ≤ 1 by norm_num)).mp
      ((continuous_const.mul ((hf.norm).pow 2)).intervalIntegrable 0 1)
  have hmeas : AEStronglyMeasurable (fun θ => ‖ψ θ‖^2 * ‖f θ‖^2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    exact (hψ.norm.pow_const 2).mul (hf.norm.pow 2).measurable
  have hInt1 : Integrable (fun θ => ‖ψ θ‖^2 * ‖f θ‖^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    Integrable.mono' hInt2 hmeas (ae_of_all _ (fun θ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle θ))
  have key := integral_mono_of_nonneg (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    (ae_of_all _ (fun θ => by positivity)) hInt2 (ae_of_all _ hle)
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num),
      intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact key

/-- The squares of a nonnegative summable real family are summable. -/
private lemma summable_sq_of_summable (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (hsum : Summable A) :
    Summable (fun n : ℕ => A n ^ 2) := by
  have hle : ∀ n, A n ≤ ∑' k : ℕ, A k := fun n => hsum.le_tsum n (fun j _ => hA j)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    (hsum.mul_left (∑' k : ℕ, A k))
  calc A n ^ 2 = A n * A n := by ring
    _ ≤ (∑' k : ℕ, A k) * A n := mul_le_mul_of_nonneg_right (hle n) (hA n)

/-- `∑_n A_n² ≤ (∑_n A_n)²` for a nonnegative summable real family. -/
private lemma tsum_sq_le_sq_tsum (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (hsum : Summable A) :
    ∑' n : ℕ, A n ^ 2 ≤ (∑' n : ℕ, A n) ^ 2 := by
  have hle : ∀ n, A n ≤ ∑' k : ℕ, A k := fun n => hsum.le_tsum n (fun j _ => hA j)
  have hsummS : Summable (fun n : ℕ => (∑' k : ℕ, A k) * A n) := hsum.mul_left _
  have hbound : ∀ n, A n ^ 2 ≤ (∑' k : ℕ, A k) * A n := by
    intro n
    calc A n ^ 2 = A n * A n := by ring
      _ ≤ (∑' k : ℕ, A k) * A n := mul_le_mul_of_nonneg_right (hle n) (hA n)
  calc ∑' n : ℕ, A n ^ 2 ≤ ∑' n : ℕ, (∑' k : ℕ, A k) * A n :=
        Summable.tsum_le_tsum hbound (summable_sq_of_summable A hA hsum) hsummS
    _ = (∑' k : ℕ, A k) * ∑' n : ℕ, A n := hsum.tsum_mul_left _
    _ = (∑' n : ℕ, A n) ^ 2 := by ring

theorem maximal_l2_of_summable_multiplier_family
    (ψ : ℕ → ℝ → ℂ) (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n)
    (hψ : ∀ n, Measurable (ψ n)) (hbd : ∀ n θ, ‖ψ n θ‖ ≤ A n)
    (hsum : Summable A) :
    ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ n : ℕ, ‖∫ θ in (0:ℝ)..1, ψ n θ *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((∑' n, A n) ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  intro g s hgs
  set f : ℝ → ℂ := fun θ => ∑ j ∈ s, g j *
    Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ)) with hf_def
  set c : ℕ → ℤ → ℂ := fun n m => ∫ θ in (0:ℝ)..1, ψ n θ * f θ *
    Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ))) with hc_def
  set G : ℝ≥0∞ := ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hG_def
  have hf_cont : Continuous f := by
    rw [hf_def]
    refine continuous_finsetSum s (fun j _ => ?_)
    fun_prop
  have hf_memLp : MemLp f 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont.continuousOn
    refine MemLp.of_bound hf_cont.aestronglyMeasurable.restrict C ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => hC x (Set.Ioc_subset_Icc_self hx)
  -- The value of the right-hand side.
  have hG : G = ENNReal.ofReal (∑ j ∈ s, ‖g j‖ ^ 2) := by
    rw [hG_def, lintegral_count]
    have hpt : ∀ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖g m‖ ^ 2) := fun m => by
      rw [enorm_eq_ofReal_norm', ENNReal.ofReal_pow (norm_nonneg (g m)) 2]
      exact ENNReal.rpow_natCast _ 2
    rw [tsum_congr hpt]
    have hsumm : Summable (fun m : ℤ => ‖g m‖ ^ 2) :=
      summable_of_ne_finset_zero (s := s) (fun m hm => by rw [hgs m hm, norm_zero]; norm_num)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg (‖g m‖)) hsumm]
    rw [tsum_eq_sum (s := s) (fun m hm => by rw [hgs m hm, norm_zero]; norm_num)]
  -- The per-`n` bound.
  have hC : ∀ n : ℕ, ∑' m : ℤ, (‖c n m‖ₑ) ^ (2:ℝ) ≤ ENNReal.ofReal (A n ^ 2) * G := by
    intro n
    have hbdn : ∃ C : ℝ, ∀ θ, ‖ψ n θ‖ ≤ C := ⟨A n, hbd n⟩
    have hPlan := multiplier_plancherel_circle (ψ n) f (hψ n) hbdn hf_memLp
    have hsumm : Summable (fun m : ℤ => ‖c n m‖ ^ 2) :=
      summable_multiplier_plancherel (ψ n) f (hψ n) hbdn hf_memLp
    have hIntLe := integral_norm_sq_le (ψ n) (hψ n) (A n) (hA n) (hbd n) f hf_cont
    have htrig : (∫ θ in (0:ℝ)..1, ‖f θ‖ ^ 2) = ∑ j ∈ s, ‖g j‖ ^ 2 := by
      refine (intervalIntegral.integral_congr ?_).trans (plancherel_trig_polynomial s g).symm
      intro θ _
      simp only [hf_def]
    have h2 : ∑' m : ℤ, ‖c n m‖ ^ 2 ≤ A n ^ 2 * ∑ j ∈ s, ‖g j‖ ^ 2 := by
      rw [hPlan]
      calc ∫ θ in (0:ℝ)..1, ‖ψ n θ‖^2 * ‖f θ‖^2 ≤ A n^2 * ∫ θ in (0:ℝ)..1, ‖f θ‖^2 := hIntLe
        _ = A n^2 * ∑ j ∈ s, ‖g j‖^2 := by rw [htrig]
    have h1 : ∑' m : ℤ, (‖c n m‖ₑ) ^ (2:ℝ) = ENNReal.ofReal (∑' m : ℤ, ‖c n m‖ ^ 2) := by
      have hpt : ∀ m : ℤ, (‖c n m‖ₑ) ^ (2:ℝ) = ENNReal.ofReal (‖c n m‖ ^ 2) := fun m => by
        rw [enorm_eq_ofReal_norm', ENNReal.ofReal_pow (norm_nonneg (c n m)) 2]
        exact ENNReal.rpow_natCast _ 2
      rw [tsum_congr hpt]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg (‖c n m‖)) hsumm).symm
    rw [h1]
    calc ENNReal.ofReal (∑' m : ℤ, ‖c n m‖ ^ 2)
        ≤ ENNReal.ofReal (A n ^ 2 * ∑ j ∈ s, ‖g j‖ ^ 2) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (A n ^ 2) * ENNReal.ofReal (∑ j ∈ s, ‖g j‖ ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg (A n))
      _ = ENNReal.ofReal (A n ^ 2) * G := by rw [← hG]
  have hAsq := tsum_sq_le_sq_tsum A hA hsum
  have hfinal : ∫⁻ m : ℤ, (⨆ n : ℕ, ‖c n m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((∑' n, A n) ^ 2) * G := by
    calc ∫⁻ m : ℤ, (⨆ n : ℕ, ‖c n m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
        = ∑' m : ℤ, (⨆ n : ℕ, ‖c n m‖ₑ) ^ (2:ℝ) := lintegral_count _
      _ ≤ ∑' m : ℤ, ∑' n : ℕ, (‖c n m‖ₑ) ^ (2:ℝ) :=
          ENNReal.tsum_le_tsum (fun m => sup_rpow_two_le_tsum (fun n => ‖c n m‖ₑ))
      _ = ∑' n : ℕ, ∑' m : ℤ, (‖c n m‖ₑ) ^ (2:ℝ) := ENNReal.tsum_comm
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (A n ^ 2) * G := ENNReal.tsum_le_tsum (fun n => hC n)
      _ = (∑' n : ℕ, ENNReal.ofReal (A n ^ 2)) * G := ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' n : ℕ, A n ^ 2) * G := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg (A n))
            (summable_sq_of_summable A hA hsum)]
      _ ≤ ENNReal.ofReal ((∑' n : ℕ, A n) ^ 2) * G :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hAsq) le_rfl
  simpa only [hc_def, hf_def, hG_def] using hfinal

end

end Commons.Analysis.Fourier