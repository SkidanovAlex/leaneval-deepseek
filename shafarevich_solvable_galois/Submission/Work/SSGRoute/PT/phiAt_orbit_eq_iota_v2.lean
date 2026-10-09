import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.E7cOmega.zfun_pairing_extLoc
import Submission.Work.SSGRoute.E7cOmega.mem_orbit_of_liesOver_conj
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory

set_option maxHeartbeats 1600000

theorem phiAt_orbit_eq_iota_v2 (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (w : NK.GlobalCFT.Place K)
    (z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) 1)
    (hsupp : ∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ u) →
      SSGRoute.PTExt.extLoc (k := k) u z = 0)
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1) :
    SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L) (SSGRoute.PTExt.extToClasses (k := k) z) h =
      Work.SSGRoute.PT.iota (k := k) (L := L) w'
        (SSGRoute.PTExt.extLoc (k := k) w'
          (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K L) (Work.SSGRoute.idleRepMap k K L) z h)) := by
  classical
  -- The pushed idèle-valued pairing value `Y = levelPair galRes idleRepMap z h` vanishes off
  -- the `Gal(L/k)`-orbit of `w'`.  Indeed the places of `L` over the `Gal(K/k)`-orbit of `w`
  -- are exactly that orbit (`E7cOmega.mem_orbit_of_liesOver_conj`), and off the orbit of `w`
  -- the local component of `z` vanishes (`hsupp`).
  have hYvan : ∀ v : NK.GlobalCFT.Place L,
      (∀ σ : L ≃ₐ[k] L, σ • w' ≠ v) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) v
        (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K L)
          (Work.SSGRoute.idleRepMap k K L) z h) = 0 := by
    intro v hv
    obtain ⟨u, hu⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) v
    rw [Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := L) M z h v]
    rw [Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := K) (L := L) (z := z)
      u v hu (Work.SSGRoute.localUnitsMap k K L u v hu)
      (Work.SSGRoute.localUnitsMap_spec k K L u v hu)]
    have huz : SSGRoute.PTExt.extLoc (k := k) (K := K) u z = 0 := by
      refine hsupp u (fun σ hσ => ?_)
      obtain ⟨ρ, hρ⟩ := Work.SSGRoute.E7cOmega.mem_orbit_of_liesOver_conj
        (k := k) (K := K) L w w' hw' v σ (by rw [hσ]; exact hu)
      exact hv ρ hρ
    simp only [huz, SSGRoute.PTExt.extRes, Abelian.Ext.mapExactFunctor_zero,
      Abelian.Ext.zero_comp, SSGRoute.PTExt.yonedaPair]
    exact Abelian.Ext.comp_zero _ _ _ _ _
  -- Uniqueness of the orbit-supported lift: `Y` *is* `iotaLift` of its own `w'`-component.
  have hYeq := eq_iotaLift_of_spec (k := k) (L := L) w'
      (SSGRoute.PTExt.extLoc (k := k) (K := L) w'
        (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K L)
          (Work.SSGRoute.idleRepMap k K L) z h))
      (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K L)
          (Work.SSGRoute.idleRepMap k K L) z h) rfl hYvan
  rw [Work.SSGRoute.phiAt_extToClasses_eq_idleRepMap k K L M z h]
  conv_lhs => rw [hYeq]
  rfl

end Work.SSGRoute.PT
