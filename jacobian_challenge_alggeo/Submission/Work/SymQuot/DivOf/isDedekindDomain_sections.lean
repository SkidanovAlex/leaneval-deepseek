import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one
import Submission.Work.Normality.hasIntegrallyClosedStalks_of_smooth
import Submission.Work.Domain.Engine.isIntegrallyClosed_section

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

theorem isDedekindDomain_sections {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V) :
    IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V)) := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  haveI hIC : IsIntegrallyClosed Γ(C.left, V) :=
    Work.Domain.Engine.isIntegrallyClosed_section
      (Work.Normality.hasIntegrallyClosedStalks_of_smooth C.hom) hV
  have hK : Ring.KrullDimLE 1 Γ(C.left, V) :=
    Work.CurveBasics.BaseChange.krullDimLE_sections C V hV
  haveI hD : Ring.DimensionLEOne Γ(C.left, V) :=
    ⟨fun {p} hp hprime => (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hK) p hp hprime⟩
  haveI hN : IsNoetherianRing Γ(C.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsDomain Γ(C.left, V) := inferInstance
  haveI : IsDedekindRing Γ(C.left, V) := IsDedekindRing.mk
  exact inferInstance

end Work.SymQuot.DivOf
