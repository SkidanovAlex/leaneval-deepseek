import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical
import Submission.Work.CoreStep.CrossDefs

namespace Work.WilE7.Endgame

/-- `verT` is the last coordinate projection, hence continuous. -/
theorem continuous_verT {n m : ℕ} :
    Continuous (fun z : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.CoreStep.verT z) := by
  show Continuous (fun z : Fin (0 + (n + (m + 1))) → ℝ =>
    z (Fin.natAdd 0 (Fin.natAdd n (Fin.last m))))
  exact continuous_apply _

/-- The composite `verT ∘ blockSndCLM` is continuous. -/
theorem continuous_verT_blockSnd (n m : ℕ) :
    Continuous (fun w : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ =>
      Work.WilE7.CoreStep.verT (Work.CoreStep.blockSndCLM n m w)) :=
  continuous_verT.comp (Work.CoreStep.blockSndCLM n m).continuous

theorem g2_block_nhds {n m : ℕ} (w₀ : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ) (O₁ O₂ : Set (Fin (0 + (n + (m + 1))) → ℝ)) (hO₁ : O₁ ∈ nhds (Work.CoreStep.blockFirstCLM n m w₀)) (hO₂ : O₂ ∈ nhds (Work.CoreStep.blockSndCLM n m w₀)) {ε : ℝ} (hε : 0 < ε) : ∃ U ∈ nhds w₀, ∀ w ∈ U, Work.CoreStep.blockFirstCLM n m w ∈ O₁ ∧ Work.CoreStep.blockSndCLM n m w ∈ O₂ ∧ |Work.WilE7.CoreStep.verT (Work.CoreStep.blockSndCLM n m w) - Work.WilE7.CoreStep.verT (Work.CoreStep.blockSndCLM n m w₀)| < ε := by
  refine ⟨(Work.CoreStep.blockFirstCLM n m) ⁻¹' O₁
      ∩ (Work.CoreStep.blockSndCLM n m) ⁻¹' O₂
      ∩ (fun w => Work.WilE7.CoreStep.verT (Work.CoreStep.blockSndCLM n m w)) ⁻¹'
          Set.Ioo (Work.WilE7.CoreStep.verT (Work.CoreStep.blockSndCLM n m w₀) - ε)
            (Work.WilE7.CoreStep.verT (Work.CoreStep.blockSndCLM n m w₀) + ε), ?_, ?_⟩
  · refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact ((Work.CoreStep.blockFirstCLM n m).continuous.continuousAt).preimage_mem_nhds hO₁
    · exact ((Work.CoreStep.blockSndCLM n m).continuous.continuousAt).preimage_mem_nhds hO₂
    · exact IsOpen.mem_nhds (IsOpen.preimage (continuous_verT_blockSnd n m) isOpen_Ioo)
        ⟨by linarith, by linarith⟩
  · rintro w ⟨⟨hw1, hw2⟩, hw3⟩
    exact ⟨hw1, hw2, by rw [abs_lt]; exact ⟨by linarith [hw3.1], by linarith [hw3.2]⟩⟩

end Work.WilE7.Endgame
