import Mathlib
import Submission.Commons.Analysis.Fourier.lintegral_iSup_band_sum_dilation_le
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.Fourier

open Commons.Analysis.Maximal (hlMax)

/-- The finite supremum of `NNReal`s commutes with the coercion to `ℝ≥0∞`. -/
lemma nnreal_sup_coe_eq_iSup {K : ℕ} (g : Fin K → NNReal) :
    ((Finset.univ.sup g : NNReal) : ENNReal) = ⨆ k : Fin K, ((g k : NNReal) : ENNReal) := by
  rcases isEmpty_or_nonempty (Fin K) with h | h
  · have hempty : (Finset.univ : Finset (Fin K)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (fun hne => hne.elim fun x _ => h.false x)
    rw [hempty, Finset.sup_empty]
    exact le_antisymm bot_le (iSup_le (fun k => (h.false k).elim))
  · obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
    have hsup : Finset.univ.sup g = g b :=
      le_antisymm (Finset.sup_le_iff.mpr (fun i _ => hb i (Finset.mem_univ i)))
        (Finset.le_sup (f := g) (b := b) (Finset.mem_univ b))
    rw [hsup]
    exact le_antisymm (le_iSup (fun k : Fin K => ((g k : NNReal) : ENNReal)) b)
      (iSup_le (fun k => ENNReal.coe_le_coe.mpr (hb k (Finset.mem_univ k))))

/-- The `enorm` of a vector indexed by `Fin K` is the supremum of the `enorm`s of its
coordinates (the finite-dimensional sup norm of `Pi`). -/
lemma pi_enorm_eq_iSup {K : ℕ} (v : Fin K → ℂ) : ‖v‖ₑ = ⨆ k : Fin K, ‖v k‖ₑ := by
  have h1 : ‖v‖ₑ = ((Finset.univ.sup (fun b => ‖v b‖₊) : NNReal) : ENNReal) := by
    rw [enorm_eq_nnnorm, Pi.nnnorm_def]
  rw [h1, nnreal_sup_coe_eq_iSup]
  exact iSup_congr (fun k => (enorm_eq_nnnorm (v k)).symm)

theorem lintegral_iSup_pi_window_le (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MeasureTheory.MemLp (f k) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      ∫⁻ x : ℝ, (⨆ (t : {t : ℝ // 0 < t}),
          ‖(fun k : Fin K => ∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))‖ₑ) ^ (2 : ℝ)
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := maximal_dilation_convolution_enorm_le_hlMax Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  refine ⟨C₁ ^ 2 * C₀ ^ 2, by positivity, fun K f hf => ?_⟩
  have hpoint : ∀ x : ℝ,
      (⨆ t : {t : ℝ // 0 < t},
          ‖(fun k : Fin K => ∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))‖ₑ) ^ (2 : ℝ)
        ≤ ∑ k : Fin K, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) := by
    intro x
    have hsup : (⨆ t : {t : ℝ // 0 < t},
          ‖(fun k : Fin K => ∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))‖ₑ)
        = ⨆ k : Fin K, ⨆ t : {t : ℝ // 0 < t},
            ‖∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ))))‖ₑ := by
      have h1 : (⨆ t : {t : ℝ // 0 < t},
            ‖(fun k : Fin K => ∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))‖ₑ)
          = ⨆ t : {t : ℝ // 0 < t}, ⨆ k : Fin K,
              ‖∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ))))‖ₑ :=
        iSup_congr (fun t => pi_enorm_eq_iSup _)
      rw [h1, iSup_comm]
    rw [hsup]
    calc (⨆ k : Fin K, ⨆ t : {t : ℝ // 0 < t},
            ‖∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ))))‖ₑ) ^ (2 : ℝ)
        = ⨆ k : Fin K, (⨆ t : {t : ℝ // 0 < t},
            ‖∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ))))‖ₑ) ^ (2 : ℝ) :=
          iSup_rpow_two _
      _ ≤ ∑ k : Fin K, (⨆ t : {t : ℝ // 0 < t},
            ‖∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ))))‖ₑ) ^ (2 : ℝ) := by
          refine iSup_le (fun k => ?_)
          simpa using Finset.single_le_sum
            (s := Finset.univ)
            (f := fun k : Fin K => (⨆ t : {t : ℝ // 0 < t},
              ‖∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ))))‖ₑ) ^ (2 : ℝ))
            (fun i _ => bot_le) (Finset.mem_univ k)
      _ ≤ ∑ k : Fin K, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact ENNReal.rpow_le_rpow (hC₁ (f k) (hf k) x) (by norm_num)
  have hmeas : ∀ k : Fin K,
      AEMeasurable (fun x : ℝ => (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ))
        (volume : Measure ℝ) := by
    intro k
    have h1 : Measurable (fun x : ℝ => ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) :=
      (Commons.Analysis.Maximal.measurable_hlMax _).const_mul _
    exact (h1.pow_const (2 : ℝ)).aemeasurable
  have hmeas2 : ∀ k : Fin K,
      AEMeasurable (fun x : ℝ => ‖f k x‖ₑ ^ (2 : ℝ)) (volume : Measure ℝ) := by
    intro k
    exact ((hf k).aemeasurable.enorm).pow_const (2 : ℝ)
  have hkbound : ∀ k : Fin K,
      ∫⁻ x : ℝ, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (C₁ ^ 2 * C₀ ^ 2) * ∫⁻ x : ℝ, ‖f k x‖ₑ ^ (2 : ℝ) := by
    intro k
    have hmul : ∫⁻ x : ℝ, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ)
        = (ENNReal.ofReal C₁) ^ 2 * ∫⁻ x : ℝ, (hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) := by
      have h1 : ∀ x : ℝ, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ)
          = (ENNReal.ofReal C₁) ^ 2 * (hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) := by
        intro x
        rw [ENNReal.rpow_two, ENNReal.rpow_two, mul_pow]
      simp only [h1]
      exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    have hHL : ∫⁻ x : ℝ, (hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x : ℝ, ‖f k x‖ₑ ^ (2 : ℝ) := by
      simpa only [enorm_norm_eq_enorm, hlMax, ENNReal.rpow_two, Real.rpow_two]
        using hC₀ (fun y : ℝ => ‖f k y‖)
    calc ∫⁻ x : ℝ, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ)
        = (ENNReal.ofReal C₁) ^ 2 * ∫⁻ x : ℝ, (hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) := hmul
      _ ≤ (ENNReal.ofReal C₁) ^ 2 * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x : ℝ, ‖f k x‖ₑ ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hHL bot_le
      _ = ENNReal.ofReal (C₁ ^ 2 * C₀ ^ 2) * ∫⁻ x : ℝ, ‖f k x‖ₑ ^ (2 : ℝ) := by
          rw [← ENNReal.ofReal_pow hC₁pos.le 2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hlast : (∫⁻ x : ℝ, ∑ k : Fin K, ‖f k x‖ₑ ^ (2 : ℝ))
      = ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) := by
    refine lintegral_congr (fun x => ?_)
    have h1 : ∀ k : Fin K, ‖f k x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f k x‖ ^ 2) := by
      intro k
      rw [ENNReal.rpow_two, enorm_complex_eq_ofReal, ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [h1]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg (‖f k x‖))]
  calc ∫⁻ x : ℝ, (⨆ t : {t : ℝ // 0 < t},
        ‖(fun k : Fin K => ∫ y : ℝ, f k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))‖ₑ) ^ (2 : ℝ)
      ≤ ∫⁻ x : ℝ, ∑ k : Fin K, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_mono hpoint
    _ = ∑ k : Fin K, ∫⁻ x : ℝ, (ENNReal.ofReal C₁ * hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_finsetSum' Finset.univ (fun k _ => hmeas k)
    _ ≤ ∑ k : Fin K, ENNReal.ofReal (C₁ ^ 2 * C₀ ^ 2) * ∫⁻ x : ℝ, ‖f k x‖ₑ ^ (2 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hkbound k)
    _ = ENNReal.ofReal (C₁ ^ 2 * C₀ ^ 2) * ∑ k : Fin K, ∫⁻ x : ℝ, ‖f k x‖ₑ ^ (2 : ℝ) := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal (C₁ ^ 2 * C₀ ^ 2) * ∫⁻ x : ℝ, ∑ k : Fin K, ‖f k x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_finsetSum' Finset.univ (fun k _ => hmeas2 k)]
    _ = ENNReal.ofReal (C₁ ^ 2 * C₀ ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) := by
        rw [hlast]

end Commons.Analysis.Fourier
