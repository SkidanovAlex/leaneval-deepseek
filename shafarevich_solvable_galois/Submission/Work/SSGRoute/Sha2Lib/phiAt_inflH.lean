import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.e6_util
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level pairing of an inflation is the inflation of the level pairing

For a tower of number fields `k ⊆ K ⊆ L`, a class `x ∈ Extʳ_{Gal(K/k)}(M, C_K)` and a cohomology
class `h ∈ H¹(Gal(K/k), M)`, the level-`L` pairing `φ` of the *inflation* of `h` is the inflation
of the level-`K` pairing (the Yoneda pairing):

  `phiAt x (inflH h) = inflC (yonedaPair x h)`.

This is the compatibility that lets a vanishing hypothesis on the *level-`K`* pairings
`yonedaPair x h` (the form in which the node `E9` most naturally receives its hypothesis) be
tested at every level `L ≥ K`: combined with the Hasse/Bauer descent of local triviality
(`Sha2Lib.exists_isLocTrivial_inflH`) it shows that the level-`K` and the all-levels forms of E9's
hypothesis are inter-derivable.
-/

namespace Work.SSGRoute.Sha2Lib

open SSGRoute.PTExt

/-- **The level pairing commutes with inflation.**  For `x : Ext^r_{Gal(K/k)}(M, C_K)` and
`h : H¹(Gal(K/k), M)`, the value of `φ` at the level `L ≥ K` on the inflation of `h` is the
inflation of the level-`K` value. -/
theorem phiAt_inflH {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.classesK k K) r)
    (h : SSGRoute.PTExt.extH M 1) :
    SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L) x
        (SSGRoute.PTExt.inflH (k := k) (K := K) (L := L) h)
      = SSGRoute.PTExt.inflC (k := k) (K := K) (L := L)
          (SSGRoute.PTExt.yonedaPair x h) := by
  simp only [SSGRoute.PTExt.phiAt, SSGRoute.PTExt.inflH, SSGRoute.PTExt.inflC]
  exact Work.SSGRoute.E6Util.levelPair_extHMap (SSGRoute.PTExt.galRes k K L)
    (SSGRoute.PTExt.classIncl k K L) x h

end Work.SSGRoute.Sha2Lib
