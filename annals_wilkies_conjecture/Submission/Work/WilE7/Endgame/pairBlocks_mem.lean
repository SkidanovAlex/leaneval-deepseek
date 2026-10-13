import Mathlib
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.CoreStep.mem_absLevelPairSet_elim
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

theorem pairBlocks_mem {n m : ℕ} (S T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (V : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m))
    (hVsub : V.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet S T).set)
    {z : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ} (hz : z ∈ V.X.set) :
    (Work.CoreStep.blockFirstCLM n m z ∈ S.X.set) ∧
    (Work.CoreStep.blockSndCLM n m z ∈ T.X.set) ∧
    (Work.WilE7.CoreStep.projTop n m
        (Work.WilE7.MainDesign.absPt (Work.CoreStep.blockFirstCLM n m z))
      = Work.WilE7.CoreStep.projTop n m
        (Work.WilE7.MainDesign.absPt (Work.CoreStep.blockSndCLM n m z))) := by
  -- The pair point `z` lies in the level-pair set of `S` and `T`; `mem_absLevelPairSet_elim`
  -- unfolds this into membership of the two blocks in `absSet S`, `absSet T` together with a
  -- common base and a common last (vertical) fibre coordinate.
  obtain ⟨h1, h2, h3, h4, h5⟩ := Work.CoreStep.mem_absLevelPairSet_elim S T (hVsub hz)
  refine ⟨?_, ?_, ?_⟩
  · -- First block: `absPt` of it is `projFirst` of `absPt z`, which is in `absSet S`.
    have hbf : absPt (Work.CoreStep.blockFirstCLM n m z) ∈ absSet S := by
      rw [Work.CoreStep.absPt_blockFirstCLM]; exact h1
    have hs :=
      (Work.CoreStep.mem_absSet_iff S (absPt (Work.CoreStep.blockFirstCLM n m z))).mp hbf
    rwa [Work.WilE7.DimAPI.absPtInv_absPt] at hs
  · -- Second block: same, with `projSnd` and `absSet T`.
    have hbf : absPt (Work.CoreStep.blockSndCLM n m z) ∈ absSet T := by
      rw [Work.CoreStep.absPt_blockSndCLM]; exact h2
    have hs :=
      (Work.CoreStep.mem_absSet_iff T (absPt (Work.CoreStep.blockSndCLM n m z))).mp hbf
    rwa [Work.WilE7.DimAPI.absPtInv_absPt] at hs
  · -- `projTop` keeps the base (first `n` coordinates) and the last fibre coordinate: both
    -- agree, by the two agreement conditions of `mem_absLevelPairSet_elim`.
    have h4' :
        projSnd n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1)) (absPt z)) (Fin.last m)
          = projSnd n (m + 1) (projSnd (n + (m + 1)) (n + (m + 1)) (absPt z)) (Fin.last m) :=
      h4
    rw [Work.WilE7.CoreStep.projTop, Work.WilE7.CoreStep.projTop,
      Work.CoreStep.absPt_blockFirstCLM, Work.CoreStep.absPt_blockSndCLM, h3, h4']

end Work.WilE7.Endgame
