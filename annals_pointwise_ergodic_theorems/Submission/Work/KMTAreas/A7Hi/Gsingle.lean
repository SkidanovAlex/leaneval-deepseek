import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7rand.eLpNorm_iwConv_le_kernelMass

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

/-- **The single-scale `ℓ^p` bound for the IW projection of the modulated `d`-fold bump.**
For every `N`, `k₂` there is a constant `C` with
`‖Tle ρ l (φ̃_{N,t}) g‖_{ℓ^p} ≤ C ‖g‖_{ℓ^p}`, uniformly in `t ∈ [1/2,1]`. -/
theorem Tle_varphitildeNt_single_scale (P : Polynomial ℤ) (ρ : ℝ) (l : ℕ) (p : ENNReal)
    (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℕ → ℕ → ℝ, (∀ N k₂, 0 < C N k₂) ∧
      ∀ (N k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (Tle ρ l (varphitildeNt P P.natDegree N k₂ t) g) p
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          ≤ ENNReal.ofReal (C N k₂) *
              MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have key : ∀ (N k₂ : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (Tle ρ l (varphitildeNt P P.natDegree N k₂ t) g) p
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro N k₂
    obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN P.natDegree N k₂
    set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
      (1 + (N : ℝ)) ^ P.natDegree) with hMv
    set S : ℝ := ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2 with hS
    set K : ℝ := (2 * Mv + 1) ^ 2 with hK
    have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
    have hKpos : 0 < K := by rw [hK]; positivity
    have hSnn : 0 ≤ S := by rw [hS]; exact tsum_nonneg (fun j => by positivity)
    have hcardnn : (0 : ℝ) ≤ ((iwArithFreqs ρ l).card : ℝ) := Nat.cast_nonneg _
    refine ⟨((iwArithFreqs ρ l).card : ℝ) * Cf * K * S + 1, by positivity, ?_⟩
    intro t ht g
    have ht1 : |t| ≤ 1 := by
      obtain ⟨h1, h2⟩ := ht
      rw [abs_le]
      exact ⟨by linarith, h2⟩
    have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
      le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
    have hdec : ∀ j : ℤ,
        ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
          (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖
          ≤ (((iwArithFreqs ρ l).card : ℝ) * Cf * K) / (1 + |(j : ℝ)|) ^ 2 := by
      intro j
      rw [iwKernel_varphitildeNt_eq P ρ l P.natDegree N k₂ t j]
      have h1 : ‖arithChar ρ l (-j)‖ ≤ ((iwArithFreqs ρ l).card : ℝ) :=
        norm_arithChar_le_ ρ l (-j)
      have h2 : ‖FourierTransform.fourier (varphitildeN P.natDegree N k₂)
            ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
        refine le_trans (hCfdec ((j : ℝ) - PevalR P ((N : ℝ) * t))) ?_
        have hmaj := one_div_sq_le_of_abs_sub_le hMnonneg hc j
        have hKeq : K = (2 * Mv + 1) ^ 2 := hK
        calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
            = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
          _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
              rw [hKeq]
              exact hmaj
          _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
      calc ‖arithChar ρ l (-j) *
              FourierTransform.fourier (varphitildeN P.natDegree N k₂)
                ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
          = ‖arithChar ρ l (-j)‖ *
              ‖FourierTransform.fourier (varphitildeN P.natDegree N k₂)
                ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ := norm_mul _ _
        _ ≤ ((iwArithFreqs ρ l).card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
            mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
        _ = ((iwArithFreqs ρ l).card : ℝ) * Cf * K / (1 + |(j : ℝ)|) ^ 2 := by ring
    -- the `ℓ¹` mass of the kernel
    have hmass : (∑' j : ℤ, ENNReal.ofReal
          ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
            (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖)
        ≤ ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * Cf * K * S + 1) := by
      have hκ : Summable fun j : ℤ =>
          ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
            (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖ :=
        Work.KMTContract.kernel_l1_of_decay hdec
      have hbase : Summable fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2 := summable_one_div_sq_int
      have hle : (∑' j : ℤ, ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
              (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖)
          ≤ (((iwArithFreqs ρ l).card : ℝ) * Cf * K) * S := by
        calc (∑' j : ℤ, ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
                (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖)
            ≤ ∑' j : ℤ, (((iwArithFreqs ρ l).card : ℝ) * Cf * K) *
                (1 / (1 + |(j : ℝ)|) ^ 2) := by
              refine Summable.tsum_le_tsum (fun j => ?_) hκ (hbase.mul_left _)
              have h3 := hdec j
              rw [div_eq_mul_one_div] at h3
              exact h3
          _ = (((iwArithFreqs ρ l).card : ℝ) * Cf * K) * S := by rw [hS, tsum_mul_left]
      calc (∑' j : ℤ, ENNReal.ofReal
              ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
                (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖)
          = ENNReal.ofReal (∑' j : ℤ, ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
                (periodize (varphitildeNt P P.natDegree N k₂ t))) j‖) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hκ).symm
        _ ≤ ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * Cf * K * S + 1) :=
            ENNReal.ofReal_le_ofReal (by linarith [hle])
    -- Young
    refine (Work.KMTAreas.A7rand.eLpNorm_iwConv_le_kernelMass
      (A := iwArithFreqs ρ l)
      (Φ := periodize (varphitildeNt P P.natDegree N k₂ t)) hp.le g).trans ?_
    exact mul_le_mul_of_nonneg_right hmass bot_le
  choose C hC using key
  exact ⟨C, fun N k₂ => (hC N k₂).1, fun N k₂ t ht g => (hC N k₂).2 t ht g⟩

end

end Work.KMTAreas.A7Hi
