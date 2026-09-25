import Mathlib
import Submission.Work.BourgainPlan.Oscillation.plancherel_circle_enorm_sq_Ioc
import Submission.Commons.Analysis.Fourier.maximal_l2_of_bounded_multiplier_family

namespace Work.BourgainPlan.Oscillation

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section


/-- `ℝ≥0∞.ofReal` of a Bochner integral of a nonnegative function is bounded by the
lower Lebesgue integral of the `ofReal`. -/
private lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases h : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae hf h]
    exact ENNReal.ofReal_toReal_le
  · have hni : ¬ Integrable f μ := fun hi => h hi.aestronglyMeasurable
    rw [integral_undef hni]; simp

/-- The interval-integral version on `(0,1]`. -/
private lemma ofReal_intervalIntegral_le_lintegral (g : ℝ → ℝ)
    (hg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] g) :
    ENNReal.ofReal (∫ θ in (0:ℝ)..1, g θ) ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (g θ) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ofReal_integral_le_lintegral (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) hg

theorem nbrhd_sup_shell_l2 (K : ℝ) (hK : 0 ≤ K) (φ : ℕ → ℝ → ℝ)
    (hφm : ∀ t, Measurable (φ t)) (hφ0 : ∀ t, ∀ θ, 0 ≤ φ t θ)
    (hφsum : ∀ θ, ∀ N : ℕ, Finset.sum (Finset.range N) (fun t => (φ t θ) ^ 2) ≤ K)
    (Q : ℝ → ℂ) (hQ : MeasureTheory.MemLp Q 2 (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))) :
    ∫⁻ x : ℤ, (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ) ^ (2 : ℝ)
      ∂MeasureTheory.Measure.count
    ≤ ENNReal.ofReal K * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2 : ℝ) := by
  have hnorm_phi : ∀ t θ, ‖((φ t θ : ℝ) : ℂ)‖ = φ t θ := by
    intro t θ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 t θ)]
  have hphi_sq_le : ∀ t θ, (φ t θ) ^ 2 ≤ K := by
    intro t θ
    have htmem : t ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.lt_succ_self t)
    exact le_trans (Finset.single_le_sum (fun s _ => sq_nonneg (φ s θ)) htmem) (hφsum θ (t + 1))
  -- per-`t` Plancherel + domination by the `ℝ≥0∞` integral
  have hterm : ∀ t : ℕ,
      ∫⁻ x : ℤ, ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count
        ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((φ t θ)^2 * ‖Q θ‖^2) := by
    intro t
    have hm : Measurable (fun θ : ℝ => ((φ t θ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hφm t)
    have hbd : ∃ C : ℝ, ∀ θ, θ ∈ Set.Ioc (0:ℝ) 1 → ‖((φ t θ : ℝ) : ℂ)‖ ≤ C :=
      ⟨Real.sqrt K, fun θ _ => by
        rw [hnorm_phi t θ]
        exact (Real.le_sqrt (hφ0 t θ) hK).mpr (hphi_sq_le t θ)⟩
    have hpl := plancherel_circle_enorm_sq_Ioc (fun θ : ℝ => ((φ t θ : ℝ) : ℂ)) Q hm hbd hQ
    rw [lintegral_count, hpl]
    have hcongr : (∫ θ in (0:ℝ)..1, ‖((φ t θ : ℝ) : ℂ)‖ ^ 2 * ‖Q θ‖ ^ 2)
        = ∫ θ in (0:ℝ)..1, (φ t θ)^2 * ‖Q θ‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [hnorm_phi t θ]
    rw [hcongr]
    exact ofReal_intervalIntegral_le_lintegral (fun θ => (φ t θ)^2 * ‖Q θ‖^2)
      (ae_of_all _ (fun θ => by positivity))
  -- measurability for the exchange of `∑'` and `∫⁻` in `θ`
  have hmeas : ∀ t : ℕ, AEMeasurable
      (fun θ : ℝ => ENNReal.ofReal ((φ t θ)^2 * ‖Q θ‖^2))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro t
    have h1 : AEMeasurable (fun θ : ℝ => (φ t θ)^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      ((hφm t).pow_const 2).aemeasurable
    have h2 : AEMeasurable (fun θ : ℝ => ‖Q θ‖^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (hQ.aestronglyMeasurable.aemeasurable.norm).pow_const 2
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h1.mul h2)
  -- pointwise bound of the `t`-sum: `∑'_t φ_t(θ)² ≤ K`
  have hsum_bound : ∀ θ : ℝ, ∑' t : ℕ, ENNReal.ofReal ((φ t θ)^2) ≤ ENNReal.ofReal K := by
    intro θ
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (f := fun t => (φ t θ)^2) (fun t _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hφsum θ (s.sup id + 1))
    · intro t ht
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) ht))
    · intro t _ _; exact sq_nonneg _
  -- pointwise bound of the `θ`-integrand
  have hpoint : ∀ θ : ℝ,
      ∑' t : ℕ, ENNReal.ofReal ((φ t θ)^2 * ‖Q θ‖^2) ≤ ENNReal.ofReal K * ‖Q θ‖ₑ ^ (2:ℝ) := by
    intro θ
    have hfac : ∀ t : ℕ, ENNReal.ofReal ((φ t θ)^2 * ‖Q θ‖^2)
        = ENNReal.ofReal ((φ t θ)^2) * ‖Q θ‖ₑ ^ (2:ℝ) := by
      intro t
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      exact (Commons.Analysis.Fourier.enorm_complex_pow_two (Q θ)).symm
    simp only [hfac]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hsum_bound θ) bot_le
  calc ∫⁻ x : ℤ, (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ) ^ (2:ℝ)
      ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, ∑' t : ℕ, ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x =>
          Commons.Analysis.Fourier.iSup_sq_le_tsum_sq
            (fun t => ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ))
    _ = ∑' t : ℕ, ∫⁻ x : ℤ, ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count := by
        rw [lintegral_count, ENNReal.tsum_comm]
        exact tsum_congr (fun t => (lintegral_count (fun x : ℤ =>
          ‖∫ θ in (0:ℝ)..1, (φ t θ : ℂ) * Q θ *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ ^ (2:ℝ))).symm)
    _ ≤ ∑' t : ℕ, ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((φ t θ)^2 * ‖Q θ‖^2) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ θ in Set.Ioc (0:ℝ) 1, ∑' t : ℕ, ENNReal.ofReal ((φ t θ)^2 * ‖Q θ‖^2) := by
        rw [← lintegral_tsum hmeas]
    _ ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal K * ‖Q θ‖ₑ ^ (2:ℝ) :=
        lintegral_mono hpoint
    _ = ENNReal.ofReal K * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ) := by
        rw [lintegral_const_mul' (ENNReal.ofReal K) _ ENNReal.ofReal_ne_top]

end

end Work.BourgainPlan.Oscillation
