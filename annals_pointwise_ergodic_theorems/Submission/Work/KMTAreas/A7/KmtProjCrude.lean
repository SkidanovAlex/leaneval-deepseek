import Mathlib
import Submission.Work.KMTContract.kmtKernel_decay
import Submission.Work.KMTContract.kmtProj_tendsto_truncZ
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal

theorem KmtProjCrude {ρ : ℝ} (l : ℕ) (k : ℤ) {q : ℝ} (hq : 1 < q) :
    ∃ C : NNReal, 0 < C ∧ ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal q)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm f (ENNReal.ofReal q)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  -- The IW kernel of the symbol of `kmtProj ρ l k`.
  set kern : ℤ → ℂ := fun j => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j with hkern
  -- It decays like `j^{-2}`, hence lies in `ℓ¹`.
  obtain ⟨c, _hcpos, hdec⟩ := Work.KMTContract.kmtKernel_decay ρ l k
  have hsumm : Summable (fun j : ℤ => ‖kern j‖) :=
    Work.KMTContract.kernel_l1_of_decay (c := kern) (C := c) hdec
  -- Its `ℓ¹` norm `A` is the constant of the bound.
  set A : ℝ := ∑' j : ℤ, ‖kern j‖ with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact tsum_nonneg (fun _ => norm_nonneg _)
  set C' : NNReal := ⟨A + 1, by linarith⟩ with hC'def
  have hCA : (C' : ℝ) = A + 1 := rfl
  refine ⟨C', by exact_mod_cast (show (0:ℝ) < A + 1 by linarith), ?_⟩
  intro f
  -- The kernel and the data as `ℝ≥0∞`-valued functions.
  set K : ℤ → ℝ≥0∞ := fun j => ‖kern j‖ₑ with hK
  set Φ : ℤ → ℝ≥0∞ := fun j => ‖f j‖ₑ with hΦ
  have hKae : AEMeasurable K (Measure.count : Measure ℤ) := (measurable_of_countable K).aemeasurable
  have hΦae : AEMeasurable Φ (Measure.count : Measure ℤ) := (measurable_of_countable Φ).aemeasurable
  -- The projection is the convolution with the kernel, hence is pointwise dominated by the
  -- (nonnegative) convolution integral.
  have hpoint : ∀ n : ℤ, ‖Work.KMTContract.kmtProj ρ l k f n‖ₑ
      ≤ ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ) := by
    intro n
    have h1 : ‖Work.KMTContract.kmtProj ρ l k f n‖ₑ ≤ ∑' j : ℤ, K j * Φ (n - j) := by
      rw [Work.KMTContract.kmtProj_apply]
      refine (enorm_tsum_le_tsum_enorm).trans (le_of_eq (tsum_congr (fun j => ?_)))
      simp only [hK, hΦ]
      exact enorm_mul _ _
    have h2 : (∑' j : ℤ, K j * Φ (n - j)) = ∑' y : ℤ, K (n - y) * Φ y := by
      simpa using (Equiv.tsum_eq (Equiv.subLeft n) (fun j : ℤ => K j * Φ (n - j))).symm
    rw [lintegral_count, ← h2]
    exact h1
  -- Monotonicity of `eLpNorm` turns the pointwise bound into an `ℓ^q` bound.
  have hstep2 : eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal q)
        (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ))
          (ENNReal.ofReal q) (Measure.count : Measure ℤ) :=
    eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
  -- Young's convolution inequality at the endpoint `p = 1`: `ℓ¹ ∗ ℓ^q → ℓ^q`.
  have hconv : eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ))
        (ENNReal.ofReal q) (Measure.count : Measure ℤ)
      ≤ eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
        * eLpNorm Φ (ENNReal.ofReal q) (Measure.count : Measure ℤ) :=
    Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
      (K := K) (Φ := Φ) (p := q) (q := q) (r := 1) (le_of_lt hq) le_rfl (by ring) hKae hΦae
  -- `‖K‖_{ℓ¹} = A`.
  have hKnorm : eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
      = ENNReal.ofReal A := by
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count, hAdef]
    rw [ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℤ => ‖kern j‖)
      (fun j => norm_nonneg _) hsumm]
    exact tsum_congr (fun j => by simp [hK])
  have hΦnorm : eLpNorm Φ (ENNReal.ofReal q) (Measure.count : Measure ℤ)
      = eLpNorm f (ENNReal.ofReal q) (Measure.count : Measure ℤ) := by
    rw [hΦ]
    exact eLpNorm_enorm (hf := by pw_aesm) f
  calc eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal q)
        (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ))
          (ENNReal.ofReal q) (Measure.count : Measure ℤ) := hstep2
    _ ≤ eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
          * eLpNorm Φ (ENNReal.ofReal q) (Measure.count : Measure ℤ) := hconv
    _ = ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal q) (Measure.count : Measure ℤ) := by
          rw [hKnorm, hΦnorm]
    _ ≤ ENNReal.ofReal (C' : ℝ) * eLpNorm f (ENNReal.ofReal q) (Measure.count : Measure ℤ) := by
          gcongr
          rw [hCA]
          exact le_of_lt (by linarith)

end Work.KMTAreas.A7
