import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6.ProdAssembly6
import Submission.Work.FTS.StrongPersist.N6.Majorant6
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter


namespace Work.FTS.StrongPersist.N6

/-- **The `ℋ⁶` product rule of Elgindi in the open-quadrant class.** -/
theorem prod_field6 :
    ∃ Xi Cpow α₂ : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Xi * α ^ (-Cpow) * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨K, hK, hMaj⟩ := prod_majorant6
  obtain ⟨Ce, hCe, hExc⟩ := exc_bound6
  obtain ⟨C, hCpos, hC⟩ := prod_field_of6 ⟨K, hK, hMaj⟩ ⟨Ce, hCe, hExc⟩
  exact ⟨C, 1 / 2, 1, hCpos, by norm_num, by norm_num, fun α hα f g hf hg =>
    hC α hα.1 hα.2 f g hf hg⟩

end Work.FTS.StrongPersist.N6

