import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.thetaTop_cocycle
import Submission.Work.Pi6.MSSK.cap_theta_bdry_zero
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

theorem capThetaIsCycle (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s m : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + (m+1)))
    (y : (Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).X (s + m))
    (hy : (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (s + m) y
        = ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s + (m+1)) (s + m)).hom c) :
    ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (m+1) m).hom
        (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) (m+1) c) = 0 := by
  -- Boundary formula for the cap product with the cocycle `thetaTop`.
  have h := Work.Cohomology.cap_d R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (n := s) (m := m) (Work.Pi6.MSSK.thetaTop R p σ) c
  -- `thetaTop` is a cocycle, so the `cochainDiff` term drops out.
  rw [Work.Pi6.MSSK.thetaTop_cocycle R p σ] at h
  rw [Work.Cohomology.cap_zero] at h
  simp only [LinearMap.zero_apply, sub_zero] at h
  -- `dc` lies in the boundary subcomplex, where `thetaTop` vanishes.
  rw [← hy] at h
  rw [Work.Pi6.MSSK.cap_theta_bdry_zero R p σ y] at h
  simpa using h

end Work.Pi6.MSSK
