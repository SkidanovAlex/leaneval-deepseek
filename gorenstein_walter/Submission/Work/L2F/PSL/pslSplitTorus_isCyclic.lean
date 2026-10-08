import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.PSL

/-- The split torus `pslSplitTorus F = torus F.map pslMap` is cyclic: it is the image of the
cyclic group `Fˣ` under the homomorphism `pslDiagHom F = pslMap ∘ diagHom`.  This holds for every
finite field, in particular in characteristic two where `Fˣ` is still cyclic. -/
theorem pslSplitTorus_isCyclic (F : Type*) [Field F] [Fintype F] :
    IsCyclic (Work.L2F.pslSplitTorus F) := by
  -- `pslSplitTorus F` is the range of `pslDiagHom F = pslMap ∘ diagHom`.
  have hrange : Work.L2F.pslSplitTorus F = (Work.PSL2.pslDiagHom F).range := by
    simp only [Work.L2F.pslSplitTorus, Work.L2F.torus, Work.PSL2.pslDiagHom]
    exact MonoidHom.map_range (Work.PSL2.pslMap F) (Work.PSL2.diagHom F)
  rw [hrange]
  -- the range of a homomorphism from the cyclic group `Fˣ` is cyclic.
  exact isCyclic_of_surjective (Work.PSL2.pslDiagHom F).rangeRestrict
    (Work.PSL2.pslDiagHom F).rangeRestrict_surjective

end Work.L2F.PSL
