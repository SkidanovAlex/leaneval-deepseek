import Mathlib
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

/-- The vanishing form of the Galois equivariance of localisation at a place:
if the `u`-component of `z` vanishes then so does its `(σ • u)`-component.

This is the statement `Work.SSGRoute.e9c_extLoc_conj_zero`, phrased with the
universe-pinned abbreviations `SSGRoute.PTExt.idelesK`/`SSGRoute.PTExt.extLoc`
(which are definitionally the ones used there, `Work.SSGRoute.idelesRepP`). -/
theorem extLoc_conj_eq_zero {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) r)
    (u : NK.GlobalCFT.Place K) (σ : K ≃ₐ[k] K)
    (h : SSGRoute.PTExt.extLoc (k := k) (K := K) u z = 0) :
    SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • u) z = 0 :=
  e9c_extLoc_conj_zero (k := k) (K := K) z σ u h

end Work.SSGRoute.E7cOmega
