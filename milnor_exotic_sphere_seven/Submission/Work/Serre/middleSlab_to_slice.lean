import Mathlib
import Submission.Work.Serre.MiddleSlabAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

theorem middleSlab_to_slice (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(Work.Serre.pbPre p τ (Work.Serre.slabM n)))
        (Work.Serre.pbSub p τ (Work.Serre.slabM n)
          (Work.Serre.slabM n ∩ Work.Serre.cubeBdryS (n+1)))).homology m) ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(Work.Serre.pbPre p τ (Work.Serre.sliceZ n)))
        (Work.Serre.pbSub p τ (Work.Serre.sliceZ n)
          (Work.Serre.sliceZ n ∩ Work.Serre.cubeBdryS (n+1)))).homology m)) :=
  pbSL_SZ_iso n p hp τ m

end Work.Serre
