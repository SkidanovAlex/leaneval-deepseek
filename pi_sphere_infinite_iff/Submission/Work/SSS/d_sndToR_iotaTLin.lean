import Mathlib
import Submission.Work.SSS.serreE1CruxDefs
import Submission.Work.SSS.iotaTLin_boundary_explicit
import Submission.Work.SSS.sndToR_iotaTLinFace

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The boundary of the second projection of the lifted chain `Work.SSS.iotaTLin` is the
`incF`-image of the alternating sum `Work.SSS.faceSum` of the face chains `Work.SSS.faceB`.

Route: `Work.SSS.sndToR (sSingP p) σ` is a chain map
(`HomologicalComplex.Hom.comm`), so `d ((sCCMap (sndToR ...)).f (s+1+t) (iotaTLin ...))`
`= (sCCMap (sndToR ...)).f (s+t) (d (iotaTLin ...))`; expand `d (iotaTLin ...)` by
`Work.SSS.iotaTLin_boundary_explicit` and push the finite sum (`map_sum`, `map_zsmul`) through
`Work.SSS.sndToR_iotaTLinFace`; finally `Work.SSS.faceSum` is *defined* as that alternating sum. -/
theorem d_sndToR_iotaTLin (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s + 1))
    (h : Work.SSS.sigmaVert (Work.SSS.sigHat σ) = b) (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (((Work.SSS.Fc p).obj (s+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f (s+1+t)))
          (Work.SSS.iotaTLin p hfib s t b (Work.SSS.sigHat σ) h z))
      = (ModuleCat.Hom.hom ((Work.SSS.incF (Work.SSS.Fc p) s).f (s+t)))
          (Work.SSS.faceSum p hfib s t b (Work.SSS.sigHat σ) h z) := by
  -- Work in the `serreCC` presentation, where the differential and the inclusion have the
  -- syntactically matching chain-complex types needed by `rw`.
  have main : (ModuleCat.Hom.hom ((serreCC p (s+1+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((sCCMap (sndToR (sSingP p) σ)).f (s+1+t)))
          (iotaTLin p hfib s t b (sigHat σ) h z))
      = (ModuleCat.Hom.hom ((sCCMap (Subfunctor.homOfLe
            (Work.StemsB.serreSubcomplex_mono (sSingP p) (Nat.le_succ (s+1))))).f (s+t)))
          (faceSum p hfib s t b (sigHat σ) h z) := by
    -- `incF (Fc p) s` is, by definition, the chain map induced by the inclusion `R_{s+1} ⊆ R_{s+2}`.
    have hface : ∀ i : Fin (s+2),
        (ModuleCat.Hom.hom ((sCCMap (sndToR (sSingP p) σ)).f (s+t)))
          (iotaTLinFace p hfib s t b (sigHat σ) h i z)
        = (ModuleCat.Hom.hom ((sCCMap (Subfunctor.homOfLe
            (Work.StemsB.serreSubcomplex_mono (sSingP p) (Nat.le_succ (s+1))))).f (s+t)))
          (faceB p hfib s t b (sigHat σ) h z i) :=
      fun i => sndToR_iotaTLinFace p hfib s t b σ h i z
    -- The chain map `sCCMap (sndToR …)` commutes with the differentials.
    rw [chainMap_comm_apply_elem (sCCMap (sndToR (sSingP p) σ))
      (iotaTLin p hfib s t b (sigHat σ) h z)]
    -- The boundary of `iotaTLin` is the alternating sum of its face terms.
    rw [iotaTLin_boundary_explicit p hfib s t b (sigHat σ) h z hz]
    -- Distribute the (linear) face map over the alternating sum, on both sides.
    rw [faceSum]
    simp only [map_sum, map_zsmul]
    -- Each face term is the `incF`-image of the corresponding `faceB`.
    simp only [hface]
  exact main

end Work.SSS
