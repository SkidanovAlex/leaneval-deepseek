import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute

/-- `inflHIn` is `extHMap` along the restriction `Gal(L'/k) →* Gal(L/k)` with coefficient map
`resResHom`; `extHMap` in turn is a composition of `Ext.comp` with the images of `mk₀`, and both
`Ext.comp` (in its second argument) and `Ext.mapExactFunctor` are additive. -/
theorem inflHIn_add {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) {L L' : IntermediateField K Ω} [NumberField L]
    [NumberField L'] [FiniteDimensional k L] [FiniteDimensional k L'] [IsGalois k L]
    [IsGalois k L'] (h : L ≤ L') {n : ℕ}
    (x y : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) n) :
    SSGRoute.PTExt.inflHIn (k := k) (K := K) h (x + y)
      = SSGRoute.PTExt.inflHIn (k := k) (K := K) h x
        + SSGRoute.PTExt.inflHIn (k := k) (K := K) h y := by
  simp only [SSGRoute.PTExt.inflHIn, SSGRoute.PTExt.inflHLevel, SSGRoute.PTExt.extHMap,
    SSGRoute.PTExt.extRes, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp,
    Abelian.Ext.comp_add]

end Work.SSGRoute
