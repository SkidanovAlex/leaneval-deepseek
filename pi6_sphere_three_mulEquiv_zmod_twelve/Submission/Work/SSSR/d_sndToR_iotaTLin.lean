import Mathlib
import Submission.Work.SSSR.serreE1CruxDefs
import Submission.Work.SSSR.iotaTLin_boundary_explicit
import Submission.Work.SSSR.sndToR_iotaTLinFace
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The boundary of the second projection of the lifted chain `Work.SSSR.iotaTLin` is the
`incF`-image of the alternating sum `Work.SSSR.faceSum` of the face chains `Work.SSSR.faceB`.

Route: `Work.SSSR.sndToR (sSingP p) σ` is a chain map
(`HomologicalComplex.Hom.comm`), so `d ((sCCMap R (sndToR ...)).f (s+1+t) (iotaTLin ...))`
`= (sCCMap R (sndToR ...)).f (s+t) (d (iotaTLin ...))`; expand `d (iotaTLin ...)` by
`Work.SSSR.iotaTLin_boundary_explicit` and push the finite sum (`map_sum`, `map_zsmul`) through
`Work.SSSR.sndToR_iotaTLinFace`; finally `Work.SSSR.faceSum` is *defined* as that alternating sum. -/
theorem d_sndToR_iotaTLin (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (h : Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) = b) (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (((Work.SSSR.Fc p).obj (s+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (s+1+t)))
          (Work.SSSR.iotaTLin p hfib s t b (Work.SSSR.sigHat σ) h z))
      = (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.Fc p) s).f (s+t)))
          (Work.SSSR.faceSum p hfib s t b (Work.SSSR.sigHat σ) h z) := by
  -- Work in the `serreCC` presentation, where the differential and the inclusion have the
  -- syntactically matching chain-complex types needed by `rw`.
  have main : (ModuleCat.Hom.hom ((serreCC p (s+1+1)).d ((s+1)+t) (s+t)))
        ((ModuleCat.Hom.hom ((sCCMap R (sndToR (sSingP p) σ)).f (s+1+t)))
          (iotaTLin p hfib s t b (sigHat σ) h z))
      = (ModuleCat.Hom.hom ((sCCMap R (Subfunctor.homOfLe
            (Work.SSSR.StemsB.serreSubcomplex_mono (sSingP p) (Nat.le_succ (s+1))))).f (s+t)))
          (faceSum p hfib s t b (sigHat σ) h z) := by
    -- `incF (Fc p) s` is, by definition, the chain map induced by the inclusion `R_{s+1} ⊆ R_{s+2}`.
    have hface : ∀ i : Fin (s+2),
        (ModuleCat.Hom.hom ((sCCMap R (sndToR (sSingP p) σ)).f (s+t)))
          (iotaTLinFace p hfib s t b (sigHat σ) h i z)
        = (ModuleCat.Hom.hom ((sCCMap R (Subfunctor.homOfLe
            (Work.SSSR.StemsB.serreSubcomplex_mono (sSingP p) (Nat.le_succ (s+1))))).f (s+t)))
          (faceB p hfib s t b (sigHat σ) h z i) :=
      fun i => sndToR_iotaTLinFace p hfib s t b σ h i z
    -- The chain map `sCCMap R (sndToR …)` commutes with the differentials.
    rw [chainMap_comm_apply_elem (sCCMap R (sndToR (sSingP p) σ))
      (iotaTLin p hfib s t b (sigHat σ) h z)]
    -- The boundary of `iotaTLin` is the alternating sum of its face terms.
    rw [iotaTLin_boundary_explicit p hfib s t b (sigHat σ) h z hz]
    -- Distribute the (linear) face map over the alternating sum, on both sides.
    rw [faceSum]
    simp only [map_sum, map_zsmul]
    -- Each face term is the `incF`-image of the corresponding `faceB`.
    simp only [hface]
  exact main

end Work.SSSR
