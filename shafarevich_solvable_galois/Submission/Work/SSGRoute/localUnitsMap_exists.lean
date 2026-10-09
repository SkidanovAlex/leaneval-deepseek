import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local units map `K_wˣ → L_{w'}ˣ` as a morphism of decomposition group representations

For a tower `k ⊆ K ⊆ L` of number fields with `L/k` and `K/k` finite Galois, places `w' | w`, the
canonical local embedding of unit groups `K_wˣ →* L_{w'}ˣ` (the completion of the inclusion
`K → L` at `w' | w`, `NK.GlobalCFT.Place.localAlgebraMapUnits`) is equivariant for the action of
the decomposition groups: the decomposition group `Γ_{w'} ≤ Gal(L/k)` acts on `L_{w'}ˣ`, and maps
to `Γ_w ≤ Gal(K/k)` by restriction, which acts on `K_wˣ`.

This file packages that equivariance into the statement that the local units map is a morphism of
`Rep`-representations `Rep.res f (K_wˣ) ⟶ L_{w'}ˣ` for any monoid homomorphism `f` of decomposition
groups which is the restriction (hypothesis `hf`), and records its value on `Additive.ofMul u`.

The mathematical content is the equivariance
`NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict`, packaged at the level of
`localUnitsEquiv`-actions already in `NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower`.
-/

open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute

theorem localUnitsMap_exists (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (K ≃ₐ[k] K) w)
    (hf : ∀ σ, ((f σ : MulAction.stabilizer (K ≃ₐ[k] K) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L)) :
    ∃ ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w)
        ⟶ NK.HassePrinciple.localUnitsRep k L w',
      ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι.hom (Additive.ofMul u)
          = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) := by
  refine ⟨Rep.ofHom
    { toFun := ⇑(NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw').toAdditive
      map_add' := fun x y =>
        map_add (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw').toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul
          (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw').toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw'
              (NK.HassePrinciple.localUnitsEquiv (K := k) w (f σ) (Additive.toMul x)))
          = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w' σ
              (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' (Additive.toMul x)))
        congr 1
        have hstab : f σ = NK.NUV2.LC.RouteB.localStabilizerMapTower
            (F := k) (L := K) (M := L) hw' σ := by
          apply Subtype.ext
          rw [NK.NUV2.LC.RouteB.localStabilizerMapTower_coe]
          exact hf σ
        rw [hstab]
        exact NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
          (F := k) (L := K) (M := L) hw' σ (Additive.toMul x) }, ?_⟩
  intro u
  rfl

end Work.SSGRoute
