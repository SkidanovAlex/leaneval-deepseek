import Mathlib
import Submission.Commons.Analysis.Probability.lepingle_variation_sigma_finite_ls
import Submission.Port.Aesm

namespace Work.Analysis.Probability

open MeasureTheory
open scoped ENNReal

theorem doob_maximal_weak_sigmaFinite {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.SigmaFinite μ] (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    [MeasureTheory.SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ) (hf : MeasureTheory.Integrable f μ)
    {lam : ℝ} (hlam : 0 < lam) :
    μ {ω | ENNReal.ofReal lam < ⨆ n : ℕ, ‖(MeasureTheory.condExp (ℱ n) μ f) ω‖ₑ}
      ≤ ENNReal.ofReal lam⁻¹ * MeasureTheory.eLpNorm f 1 μ := by
  classical
  -- `n ↦ ‖𝔼[f | ℱ n]‖` is a nonnegative submartingale, by Jensen for the conditional expectation.
  have hsub : Submartingale (fun n ω => ‖condExp (ℱ n) μ f ω‖) ℱ μ := by
    have hmart : Martingale (fun n => condExp (ℱ n) μ f) ℱ μ := martingale_condExp f ℱ μ
    refine ⟨fun n => (stronglyMeasurable_condExp (m := ℱ n)).norm, ?_, ?_⟩
    · intro i j hij
      filter_upwards [norm_condExp_le (μ := μ) (m := ℱ i) (condExp (ℱ j) μ f),
        hmart.condExp_ae_eq hij] with ω h1 h2
      calc ‖condExp (ℱ i) μ f ω‖ = ‖condExp (ℱ i) μ (condExp (ℱ j) μ f) ω‖ := by rw [h2]
        _ ≤ condExp (ℱ i) μ (fun ω => ‖condExp (ℱ j) μ f ω‖) ω := h1
    · intro n
      exact (integrable_condExp (m := ℱ n) (f := f)).norm
  -- The maximal event is the increasing union of the finite-horizon maximal events.
  have hset : {ω | ENNReal.ofReal lam < ⨆ n : ℕ, ‖condExp (ℱ n) μ f ω‖ₑ}
      = ⋃ N, {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω} := by
    have hps : ∀ N ω, lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω ↔
        ∃ j ≤ N, lam < ‖condExp (ℱ j) μ f ω‖ := by
      intro N ω
      rw [Pi.partialSups_apply, partialSups_apply, Finset.lt_sup'_iff]
      constructor
      · rintro ⟨j, hj, hlt⟩
        exact ⟨j, Finset.mem_Iic.mp hj, hlt⟩
      · rintro ⟨j, hj, hlt⟩
        exact ⟨j, Finset.mem_Iic.mpr hj, hlt⟩
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hps]
    constructor
    · intro hω
      rw [lt_iSup_iff] at hω
      obtain ⟨n, hn⟩ := hω
      have hn' : lam < ‖condExp (ℱ n) μ f ω‖ := by
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le] at hn
        simpa [Real.norm_eq_abs] using hn
      exact ⟨n, n, le_rfl, hn'⟩
    · rintro ⟨N, j, hj, hlt⟩
      rw [lt_iSup_iff]
      refine ⟨j, ?_⟩
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le]
      simpa [Real.norm_eq_abs] using hlt
  -- Weak-type bound for each finite horizon, via Doob's maximal inequality.
  have hbound : ∀ N, μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω}
      ≤ ENNReal.ofReal lam⁻¹ * eLpNorm f 1 μ := by
    intro N
    have h1 : ENNReal.ofReal lam
          * μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω}
        ≤ ∫⁻ ω in {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω},
            ENNReal.ofReal (‖condExp (ℱ N) μ f ω‖) ∂μ :=
      SFDoob.submartingale_maximal_weak (μ := μ) (𝒢 := ℱ)
        (f := fun n ω => ‖condExp (ℱ n) μ f ω‖) hsub (fun n ω => norm_nonneg _) hlam
    have h2 : ∫⁻ ω in {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω},
          ENNReal.ofReal (‖condExp (ℱ N) μ f ω‖) ∂μ ≤ eLpNorm f 1 μ := by
      have hJ : (fun ω => ‖condExp (ℱ N) μ f ω‖) ≤ᵐ[μ]
          fun ω => condExp (ℱ N) μ (fun ω => ‖f ω‖) ω :=
        norm_condExp_le (μ := μ) (m := ℱ N) f
      have hnn : 0 ≤ᵐ[μ] (fun ω => condExp (ℱ N) μ (fun ω => ‖f ω‖) ω) :=
        condExp_nonneg (μ := μ) (m := ℱ N) (Filter.Eventually.of_forall (fun ω => norm_nonneg _))
      calc ∫⁻ ω in {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω},
            ENNReal.ofReal (‖condExp (ℱ N) μ f ω‖) ∂μ
          = ∫⁻ ω in {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω},
              ‖condExp (ℱ N) μ f ω‖ₑ ∂μ := by
            apply lintegral_congr; intro ω
            simp only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
        _ ≤ ∫⁻ ω in {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω},
              ‖condExp (ℱ N) μ (fun ω => ‖f ω‖) ω‖ₑ ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_of_ae hJ, ae_restrict_of_ae hnn] with ω h1' h2'
            rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal
              (calc |condExp (ℱ N) μ f ω| = ‖condExp (ℱ N) μ f ω‖ := (Real.norm_eq_abs _).symm
                _ ≤ condExp (ℱ N) μ (fun ω => ‖f ω‖) ω := h1'
                _ = |condExp (ℱ N) μ (fun ω => ‖f ω‖) ω| := (abs_of_nonneg h2').symm)
        _ ≤ ∫⁻ ω, ‖condExp (ℱ N) μ (fun ω => ‖f ω‖) ω‖ₑ ∂μ :=
            setLIntegral_le_lintegral _ _
        _ = eLpNorm (fun ω => condExp (ℱ N) μ (fun ω => ‖f ω‖) ω) 1 μ :=
            (eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)).symm
        _ ≤ eLpNorm (fun ω => ‖f ω‖) 1 μ := eLpNorm_condExp_le_eLpNorm _ le_rfl
        _ = eLpNorm f 1 μ := eLpNorm_norm (hf := by pw_aesm) f
    have h3 : ENNReal.ofReal lam
          * μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω} ≤ eLpNorm f 1 μ :=
      h1.trans h2
    calc μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω}
        = 1 * μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω} :=
          (one_mul _).symm
      _ = (ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam)
            * μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω} := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le), inv_mul_cancel₀ (ne_of_gt hlam),
            ENNReal.ofReal_one]
      _ = ENNReal.ofReal lam⁻¹
            * (ENNReal.ofReal lam
                * μ {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω}) :=
          mul_assoc _ _ _
      _ ≤ ENNReal.ofReal lam⁻¹ * eLpNorm f 1 μ := mul_le_mul_of_nonneg_left h3 bot_le
  rw [hset]
  have hmono : Monotone (fun N : ℕ =>
      {ω | lam < partialSups (fun n ω => ‖condExp (ℱ n) μ f ω‖) N ω}) := by
    intro i j hij ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_lt_of_le hω
      (partialSups_monotone (fun n ω => ‖condExp (ℱ n) μ f ω‖) hij ω)
  rw [Monotone.measure_iUnion hmono]
  exact iSup_le hbound

end Work.Analysis.Probability
