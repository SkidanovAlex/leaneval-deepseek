import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.vfShared
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-pairing push of a localisation (light-weight copy)

`Work.SSGRoute.levelPair_extLoc_eq_push` (in `local_phi_realization_in`) is the identity
"the `w'`-component of a level pairing is the local pairing of the localisations".  This module
re-proves it against the light-weight import cone of `PT.vfShared` (which already contains
`E9c.Core`'s `extLoc_levelPair_idleRepMap_eq` and `E7cOmega`'s `extLoc_push_ideleMap`).
-/

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

set_option linter.unusedSectionVars false

theorem levelPairPushLocal (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) 1)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1)
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w) :
    SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k K L w w' hw')
        (Work.SSGRoute.localUnitsMap k K L w w' hw')
        (SSGRoute.PTExt.extLoc (k := k) (K := K) w z)
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := L) w') h)
      = SSGRoute.PTExt.extLoc (k := k) (K := L) w'
          (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K L)
            (Work.SSGRoute.idleRepMap k K L) z h) := by
  rw [Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := L) M z h w']
  rw [Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := K) (L := L) z w w' hw'
    (Work.SSGRoute.localUnitsMap k K L w w' hw') (Work.SSGRoute.localUnitsMap_spec k K L w w' hw')]
  rfl

end Work.SSGRoute.PT.G1plusOwn
