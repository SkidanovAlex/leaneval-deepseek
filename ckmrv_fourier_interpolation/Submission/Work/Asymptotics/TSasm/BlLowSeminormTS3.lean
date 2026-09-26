import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.HFN.BlLowTS.Main
import Submission.Work.HFN.BlLow.window_bound
import Submission.Work.HFN.BlLow.offwindow_bound
import Submission.Work.Asymptotics.TSasm.cuspOneTileE_TS

namespace Work.Asymptotics

open UpperHalfPlane

theorem BlLowSeminormTS3 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
        (2 : ℝ) / 5 ≤ τ.im → τ.im ≤ 1 / 2 → 3 / 4 < |τ.re| →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨Cw, hCw, hwin⟩ := Work.HFN.BlLow.window_bound ℓ d hd
  obtain ⟨Co, hCo, hoff⟩ := Work.HFN.BlLow.offwindow_bound ℓ d hd
  obtain ⟨Cdec0, hCdec0, hdec1_0⟩ :=
    Work.HFN.BlLowTS.blLow_kernel_spike ℓ d hd hCw hCo hwin hoff
  set Cdec : ℝ := max Cdec0 Co with hCdecdef
  have hCdec : 0 ≤ Cdec := le_trans hCdec0 (le_max_left _ _)
  have hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec :=
    fun τ hτ t ht htT => le_trans (hdec1_0 τ t hτ ht htT) (le_max_left _ _)
  have hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec :=
    fun τ hτ t ht htT hsep => le_trans (hoff τ t hτ ht htT hsep) (le_max_right _ _)
  obtain ⟨C, hC, hb⟩ :=
    Work.HFN.BlLowTS.blLowLayer_transform_seminorm ℓ d hd hCdec hdec1 hdec2 k l
  refine ⟨C, hC, fun τ r hD him1 him2 hre => ?_⟩
  exact hb τ r (Work.HFN.BlLowTS.blLowSet_of_region hD him1 him2 hre)

end Work.Asymptotics
