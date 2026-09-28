import Mathlib
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.transport_eq_topEnd

/-!
# From the chain level to the transport statement

`Work.SSS.transport_eq_topEnd` proves, for a coherent family of lifts `Φ`, that the class of the top
end of the lift of a cycle `τ` is the transport of the class of `τ`.  Its proof only uses the
*chain-level* fact that the two end-fibres of the pullback agree on the relevant classes
(`Work.SSS.homologyMap_source_eq_target`).  This file records the corresponding reduction in the
form needed for the vertex-`1` restriction `v` of a coherent lift: if the homology classes of the
images of a cycle `τ` under `sourceChainMap` and `targetChainMap` agree, then the transport of the
class of `τ` is the class of the target cycle.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.SSS

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The chain-level input implies the transport statement.**  If the homology classes of the
images of the cycle `τ` (over `b₀`) and of a cycle `w` (over `b₁`) under the two end-fibre
inclusions of the pullback along `γ` agree, then the transport of the class of `τ` along `γ` is the
class of `w`. -/
theorem transportIsoPath_hom_eq_of_chain {p : C(E, B)} (hp : Work.StemsB.IsSerreFibration p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ)
    (τ : C(edgeSimp t, Work.StemsB.fibre p b₀))
    (hτ : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d t
        ((ComplexShape.down ℕ).next t)))
        (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
          (Work.RatHurewicz.Bridge.simplexOf t τ)) = 0)
    (w : (Work.Stems.hChain (Work.StemsB.fibre p b₁)).X t)
    (hw : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d t
        ((ComplexShape.down ℕ).next t))) w = 0)
    (h : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
            (Work.Stems.hChain (Work.StemsB.fibre p b₀)) t))
            (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₀))
              (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
                (Work.RatHurewicz.Bridge.simplexOf t τ)) ((ComplexShape.down ℕ).next t) rfl hτ))
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (targetChainMap p γ) t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
            (Work.Stems.hChain (Work.StemsB.fibre p b₁)) t))
            (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₁))
              w ((ComplexShape.down ℕ).next t) rfl hw))) :
    (Work.SSS.transportIsoPath p hp γ t).hom
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
          (Work.Stems.hChain (Work.StemsB.fibre p b₀)) t))
          (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₀))
            (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
              (Work.RatHurewicz.Bridge.simplexOf t τ)) ((ComplexShape.down ℕ).next t) rfl hτ))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
          (Work.Stems.hChain (Work.StemsB.fibre p b₁)) t))
          (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₁))
            w ((ComplexShape.down ℕ).next t) rfl hw) := by
  rw [transportIsoPath_apply p hp γ t, h, transportPost_apply p hp γ t]

end

end Work.SSS
