import Mathlib
import Submission.Work.Tubular.relKronH_relToAbs
import Submission.Work.Tubular.LocalDegree
import Submission.Work.Orient.Defs
import Submission.Work.ThomBordism.FrameSigns.chartCoh_compare
import Submission.Work.ThomBordism.coorFibre_fibreGeneratorAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.ThomBordism.KeyLocal

noncomputable section

open CategoryTheory

theorem admissible_pi_relToAbs {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (Work.ThomBordism.FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
          ((Work.Thom.CohMap
            (⟨Work.Tubular.NormalTotal.proj,
              Work.Tubular.NormalTotal.continuous_proj E⟩ :
                C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8).hom
            ((Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o)))
        V.c = 1 := by
  -- The projection `ν → V` is a retraction of the zero section `V → ν`, so on the absolute
  -- cohomology of `V` the two pullbacks cancel in the order `(proj)^* ∘ (zero)^* = id`.
  have hcomp : (⟨Work.Tubular.NormalTotal.proj,
        Work.Tubular.NormalTotal.continuous_proj E⟩ :
          C(Work.Tubular.NormalTotal E, V.pt)).comp (Work.Tubular.zeroSectionNormal E)
      = ContinuousMap.id V.pt := by
    ext y
    exact Work.Tubular.zeroSectionNormal_proj E y
  have hcancel : (Work.Thom.CohMap
        (⟨Work.Tubular.NormalTotal.proj,
          Work.Tubular.NormalTotal.continuous_proj E⟩ :
            C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8
      ≫ Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8) = 𝟙 _ := by
    rw [← Work.Thom.CohMap_comp (Work.Tubular.zeroSectionNormal E)
        (⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
          C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8, hcomp, Work.Thom.CohMap_id]
  rw [show ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (⟨Work.Tubular.NormalTotal.proj,
          Work.Tubular.NormalTotal.continuous_proj E⟩ :
            C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8).hom
        ((Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o)))
      = (Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o from by
    rw [← ModuleCat.comp_apply, hcancel]
    rfl]
  -- Transfer the absolute pairing back to the relative one at `{x}`; that is `ho`.
  rw [← Work.Tubular.relKronH_relToAbs_apply (Work.ThomBordism.FrameSigns.punct V x) 8 o V.c]
  exact ho

end
end Work.ThomBordism.KeyLocal
