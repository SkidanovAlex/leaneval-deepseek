import Mathlib
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.MotV5.GenAux_relfinrank_bot_adjoin_genX

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotAS

theorem transcendental_twistFieldAS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    ∃ x : ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)), Transcendental (RatFunc 𝕜) x := by
  classical
  set F : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜) with hF
  have hG : D.Good := hD.1
  -- `genX` is transcendental over `RatFunc 𝕜`
  have hgenXtr : Transcendental (RatFunc 𝕜)
      (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) :=
    Work.MotV5.transcendental_genX_ratFunc 𝕜 D
  -- `genX` lies in the Klein field, hence in `asFieldL`
  have hgenXKlein : Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) ∈ Work.MotV5.kleinField D := by
    rw [Work.MotV5.kleinField_eq_adjoin_genXY 𝕜 D hG]
    exact IntermediateField.subset_adjoin (RatFunc 𝕜) _ (by simp)
  -- `asFieldL = F⟮asOM⟯`
  have hRestr : Work.MotV5.asFieldL D (Work.MotV.fAS 𝕜)
      = IntermediateField.restrictScalars (RatFunc 𝕜)
          (IntermediateField.adjoin ↥F {Work.MotAS.asOM D (Work.MotV.fAS 𝕜)}) :=
    Work.MotAS.asFieldL_eq_restrict D (Work.MotV.fAS 𝕜) hG
  -- hence `genX ∈ F⟮asOM⟯`
  have hgenXmem : Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))
      ∈ IntermediateField.adjoin ↥F {Work.MotAS.asOM D (Work.MotV.fAS 𝕜)} := by
    have h : Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))
        ∈ Work.MotV5.asFieldL D (Work.MotV.fAS 𝕜) :=
      (le_sup_left : Work.MotV5.kleinField D ≤ Work.MotV5.asFieldL D (Work.MotV.fAS 𝕜)) hgenXKlein
    rw [hRestr] at h
    simpa using h
  -- `asOM` is integral over `F`, so `F⟮asOM⟯ / F` is algebraic
  haveI hAlgAdjoin : Algebra.IsAlgebraic ↥F
      ↥(IntermediateField.adjoin ↥F {Work.MotAS.asOM D (Work.MotV.fAS 𝕜)}) :=
    IntermediateField.isAlgebraic_adjoin (S := {Work.MotAS.asOM D (Work.MotV.fAS 𝕜)})
      (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Work.MotAS.asOM_isIntegral D (Work.MotV.fAS 𝕜))
  -- hence `genX` is algebraic over `F`
  have hgenXalg : IsAlgebraic ↥F (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) := by
    have h := hAlgAdjoin.isAlgebraic
      (⟨Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)), hgenXmem⟩ :
        ↥(IntermediateField.adjoin ↥F {Work.MotAS.asOM D (Work.MotV.fAS 𝕜)}))
    simpa only [IntermediateField.algebraMap_apply] using
      (IsAlgebraic.algebraMap (R := ↥F)
        (S := ↥(IntermediateField.adjoin ↥F {Work.MotAS.asOM D (Work.MotV.fAS 𝕜)}))
        (A := Work.MotV.Om D) h)
  -- if `F` were algebraic over `RatFunc 𝕜`, so would `genX` be — contradiction
  by_contra hcon
  have hAlgF : Algebra.IsAlgebraic (RatFunc 𝕜) ↥F := ⟨fun x => by
    by_contra hx
    exact hcon ⟨x, hx⟩⟩
  haveI := hAlgF
  exact hgenXtr ((Algebra.IsAlgebraic.isAlgebraic_iff (RatFunc 𝕜) ↥F).mpr hgenXalg)

end Work.MotAS
