import Mathlib
import Submission.Work.CoreStep.SigmaFamDefs

namespace Work.WilE7.Endgame

theorem witness_mem_pairFrontierBaseFst {n m : ℕ}
    (V : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m))
    {p : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ}
    (hcl : p ∈ closure V.X.set) (hnot : p ∉ V.X.set) :
    Work.CoreStep.pairBaseFst n m (Work.WilE7.MainDesign.absPt p) ∈
      Work.CoreStep.pairFrontierBaseFst n m V := by
  unfold Work.CoreStep.pairFrontierBaseFst
  refine Set.mem_image_of_mem _ ⟨?_, ?_⟩
  · have h : Work.WilE7.MainDesign.absPt p ∈
        Work.WilE7.MainDesign.absPt '' closure V.X.set :=
      Set.mem_image_of_mem _ hcl
    rwa [Work.CoreStep.absPt_image_closure] at h
  · rintro ⟨q, hq, hqp⟩
    exact hnot (Work.CoreStep.absPt_injective _ hqp ▸ hq)

end Work.WilE7.Endgame
