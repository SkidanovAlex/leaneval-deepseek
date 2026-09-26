import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.SpikeCircle.SphereBoundAux
import Submission.Work.Asymptotics.SpikeCircle.spikeStripBound
import Submission.Work.Asymptotics.SpikeCircle.spike_KPlus8_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KMinus8_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KPlus24_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KMinus24_bound

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

set_option maxHeartbeats 1000000

open Work.Kernels

theorem spikeCircleBound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ → ‖Work.Kernels.Kfun ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  rcases hd with rfl | rfl
  · -- `d = 8`
    obtain ⟨C1, N1, hC1, hN1, h1⟩ := spike_KPlus8_bound
    obtain ⟨C2, N2, hC2, hN2, h2⟩ := spike_KMinus8_bound ℓ
    obtain ⟨C3, hC3, h3⟩ := spikeStripBound ℓ 8 (Or.inl rfl) 3 (by norm_num)
    have hN : (0 : ℝ) ≤ max N1 N2 := le_trans hN1 (le_max_left _ _)
    refine ⟨max (max ((C1 + C2 + 1) / 2) C3) 1, max N1 N2, by positivity, hN, ?_⟩
    intro τ ζ hτ hζ hne
    have hone : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
      Real.one_le_rpow (one_le_scale τ) hN
    have hsp : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
      Real.rpow_nonneg (scale_pos τ).le _
    by_cases hcase : τ.im ≤ 3
    · refine le_trans (h3 τ ζ hτ hζ hcase hne) ?_
      have hC3le : C3 ≤ max (max ((C1 + C2 + 1) / 2) C3) 1 :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      calc C3 ≤ C3 * (Work.Kernels.scale τ) ^ max N1 N2 :=
            le_mul_of_one_le_right hC3.le hone
        _ ≤ max (max ((C1 + C2 + 1) / 2) C3) 1 * (Work.Kernels.scale τ) ^ max N1 N2 :=
            mul_le_mul_of_nonneg_right hC3le hsp
    · have h3' : 3 ≤ τ.im := le_of_not_ge hcase
      have hK : Work.Kernels.Kfun ℓ 8 τ ζ
          = (Work.Kernels.KPlus 8 τ ζ + Work.Kernels.KMinus ℓ 8 τ ζ) / 2 := rfl
      rw [hK]
      refine le_trans (half_add_bound hC1 hC2 hN1 hN2
        (h1 τ ζ hτ hζ h3') (h2 τ ζ hτ hζ h3')) ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_left _ _) (le_max_left _ _)) hsp
  · -- `d = 24`
    obtain ⟨H1, hKP1⟩ := SBs_KPlus24
    obtain ⟨H2, C2, N2, _hH2, hC2, hN2, hb2⟩ := KM24_spike_bound ℓ
    obtain ⟨C1, N1, hC1, hN1, hb1⟩ := SBs.to_bound hKP1 le_rfl
    have hH3 : (3 : ℝ) ≤ max (max 3 H1) H2 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    obtain ⟨C3, hC3, h3⟩ := spikeStripBound ℓ 24 (Or.inr rfl) (max (max 3 H1) H2) hH3
    have hN : (0 : ℝ) ≤ max N1 N2 := le_trans hN1 (le_max_left _ _)
    refine ⟨max (max ((C1 + C2 + 1) / 2) C3) 1, max N1 N2, by positivity, hN, ?_⟩
    intro τ ζ hτ hζ hne
    have hone : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
      Real.one_le_rpow (one_le_scale τ) hN
    have hsp : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
      Real.rpow_nonneg (scale_pos τ).le _
    by_cases hcase : τ.im ≤ max (max 3 H1) H2
    · refine le_trans (h3 τ ζ hτ hζ hcase hne) ?_
      have hC3le : C3 ≤ max (max ((C1 + C2 + 1) / 2) C3) 1 :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      calc C3 ≤ C3 * (Work.Kernels.scale τ) ^ max N1 N2 :=
            le_mul_of_one_le_right hC3.le hone
        _ ≤ max (max ((C1 + C2 + 1) / 2) C3) 1 * (Work.Kernels.scale τ) ^ max N1 N2 :=
            mul_le_mul_of_nonneg_right hC3le hsp
    · have hH : max (max 3 H1) H2 ≤ τ.im := le_of_not_ge hcase
      have hH1 : H1 ≤ τ.im :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH
      have hH2 : H2 ≤ τ.im := le_trans (le_max_right _ _) hH
      have hK : Work.Kernels.Kfun ℓ 24 τ ζ
          = (Work.Kernels.KPlus 24 τ ζ + Work.Kernels.KMinus ℓ 24 τ ζ) / 2 := rfl
      rw [hK]
      refine le_trans (half_add_bound hC1 hC2 hN1 hN2
        (hb1 τ ζ hτ hζ hH1) (hb2 τ ζ hτ hζ hH2)) ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_left _ _) (le_max_left _ _)) hsp

end Work.Asymptotics.SpikeCircle
