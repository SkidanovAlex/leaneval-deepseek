import Submission.Work.WilE9G.Sard.morseCoverMain
import Submission.Work.WilE9G.Sard.morseCoverLevelSet

/-!
# Morse's criticality theorem

The main theorem `morseCriticality` is obtained from the inductive statement
`Work.WilE9G.Sard.morseCover_all` (in `morseCoverMain`) by supplying Morse's Lemma 3.3, which is
proved as `Work.WilE9G.Sard.levelSetParam_holds` (in `morseCoverLevelSet`).
-/

set_option autoImplicit false

namespace Work.WilE9G.Sard

open Set Metric

noncomputable section

theorem morseCriticality (s d : ℕ) (hs : 1 ≤ s) (B : Set (Fin d → ℝ)) :
    ∃ (ι : Type) (_ : Countable ι) (c : ι → ChartDatum d) (A : ι → Set (Fin d → ℝ)),
      (∀ i, A i ⊆ B) ∧
      (B ⊆ ⋃ i, A i) ∧
      (∀ i, A i ⊆ (c i).γ '' Metric.ball (c i).base (c i).rad) ∧
      (∀ (G : (Fin d → ℝ) → ℝ) (_ : ContDiff ℝ s G) (_ : ∀ x ∈ B, G x = 0) (i : ι),
        ∀ u ∈ Metric.ball (c i).base (c i).rad,
          (c i).γ u ∈ A i → FlatAt (fun v => G ((c i).γ v)) s u) := by
  obtain ⟨ι, hcnt, c, A, -, hsub, hcov, himg, hflat⟩ :=
    morseCover_all levelSetParam_holds s d univ B isOpen_univ (Set.subset_univ B)
  exact ⟨ι, hcnt, c, A, hsub, hcov, himg, fun G hG hG0 i u hu hgu =>
    hflat G ⟨hG.contDiffOn, hG0⟩ i u hu hgu⟩

end

end Work.WilE9G.Sard
