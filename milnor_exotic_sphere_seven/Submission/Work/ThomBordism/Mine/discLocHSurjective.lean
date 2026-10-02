import Mathlib
import Submission.Work.ThomBordism.Mine.Vocab
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.exists_halfOrientationFamily_normalDiscSub
import Submission.Work.ThomBordism.normalTotal_locH_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Mine

/-- The surjectivity of the localisation of the top relative homology of the disc bundle at a point
of the zero section.  This is `Work.ThomBordism.disc_locH_surjective` (the general form, with the
inclusion of the point in the zero section taken as an explicit hypothesis), instantiated at the
canonical proof of membership of `0_x` in the zero section. -/
theorem discLocHSurjective {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (R : Work.Tubular.DiscManifold.HalfModelReindex k)
    (x : V.pt) :
    Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalDiscSub E ε))
      (7 + k + 1)
      (Set.singleton_subset_iff.mpr (Work.ThomBordism.Mine.mem_zeroSecSet (E := E) C.eps_pos x))) := by
  exact Work.ThomBordism.disc_locH_surjective E C R x
    (Set.singleton_subset_iff.mpr (mem_zeroSecSet (E := E) C.eps_pos x))

end Work.ThomBordism.Mine
