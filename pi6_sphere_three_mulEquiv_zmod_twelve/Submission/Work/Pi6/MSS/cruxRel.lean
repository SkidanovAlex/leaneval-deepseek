import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.SSSR.IotaChain.basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

theorem cruxRel {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert σ)).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    Work.Pi6.MSS.CruxRel 𝕜 p hfib s q σ z :=
  Work.SSSR.IotaChain.iotaF_cycle (R := 𝕜) p hfib s q (Work.SSS.sigmaVert σ) σ rfl z hz

end Work.Pi6.MSS
