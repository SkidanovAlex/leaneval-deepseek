import Mathlib
import Submission.Work.LayerCont.SmallTClosureLowBad
import Submission.Work.Asymptotics.HalfFunnel.tangTailExpansion

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

theorem Aexp_compact_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {T : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ K, ∀ t : ℝ, |t| ≤ T →
      ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C := by
  have hc : Continuous (fun p : ℍ × ℝ =>
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) p.1 p.2) :=
    Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun τ hτ t ht => ?_⟩
  refine le_trans (hC (τ, t) ⟨hτ, ?_⟩) (le_max_left _ _)
  rw [Set.mem_Icc]
  exact abs_le.mp ht

theorem hAexpLow_of_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) :
    ∃ Cae : ℝ, 0 ≤ Cae ∧ ∀ τ ∈ K, ∀ t : ℝ, 1 ≤ t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
        ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae := by
  obtain ⟨C, hC, hb⟩ := Aexp_compact_bound ℓ d hd hK (T := max Work.Asymptotics.HalfFunnel.lowT 1)
  refine ⟨C, hC, fun τ hτ t h1 h2 => hb τ hτ t ?_⟩
  rw [abs_of_nonneg (le_trans zero_le_one h1)]
  exact le_trans h2 (le_max_left _ _)

end Work.LayerCont
