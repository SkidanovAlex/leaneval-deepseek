import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.extHMap_gammaHom_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Group-naturality of the degree-one bridge `H¹(G,M) ≅ Ext¹_G(ℤ,M)`.**

For a group homomorphism `r : H →* G` and a `G`-module `M` (viewed as an `H`-module by pulling the
action back along `r`), restriction of the `Ext¹`-class of a `1`-cocycle `ψ` along `r` is the
`Ext¹`-class of the pulled-back cocycle `ψ ∘ r`.  Both sides are elements of
`Ext¹_H(ℤ, M) = ExtH (modRep H M) 1` (with the pulled-back action); the coefficient module on the
right of `extHMap` is `Rep.res r (modRep G M)`, which is *definitionally* `modRep H M` for the
`compHom` action.

PROOF STRATEGY (all ingredients are on disk):
* `ExtH1.gammaZ1_apply` / `gammaHom_H1π`: `gammaHom G M hS (H1π ψ) = hS.extClass.comp (mk₀ (cocycleHom ψ))`
  where `hS = augSES_shortExact G`.
* The cocycle identity: with `θ : k[H] →ₐ[Coeff] k[G]`, `γ ↦ r γ`, the maps
  `cocycleHom_H (ψ∘r)` and `θ|_{I_H} ≫ cocycleHom_G ψ` agree on `augDiff γ = ebas γ - ebas 1`
  (`cocycleHom_augDiff`), hence are equal by `ExtH1.hom_ext_augDiff`.
* `θ` restricted to the augmentation ideals gives a morphism of short complexes
  `Φ : augSES H ⟶ Rep.resFunctor r (augSES G)` (τ₁ = θ|, τ₂ = θ, τ₃ = 𝟙, the two squares by
  `Rep.hom_ext` + `LinearMap.ext` + `augHom_ebas`).
* `ShortComplex.ShortExact.extClass_naturality` then gives
  `(augSES H).extClass.comp (mk₀ θ|) = (mk₀ 𝟙).comp ((Rep.resFunctor r (augSES G)).extClass)`,
  and `Abelian.Ext.mapExactFunctor_extClass` identifies
  `(Rep.resFunctor r (augSES G)).extClass = mapExactFunctor (Rep.resFunctor r) hS.extClass`.
* Finish with `mk₀_comp_mk₀`, `comp_assoc`, `mapExactFunctor_comp`, `mapExactFunctor_mk₀` and
  `unitRes r = 𝟙` (`Rep.hom_ext`).
ALTERNATIVE SHORTCUT worth checking first: the workspace already has a *proved* naturality
`E0bClean.eBridge_natural` for the general `groupCohomology ↔ Ext` comparison; if `gammaHom` can be
identified with `eBridge` (nothing is recorded either way), the present statement follows from it. -/
theorem extHMap_gammaHom_eq {G H : Type} [Group G] [Group H] (r : H →* G)
    (M : Type) [AddCommGroup M] [Module SSGRoute.PTExt.Coeff M] [DistribMulAction G M]
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    letI : DistribMulAction H M := DistribMulAction.compHom M r
    SSGRoute.PTExt.extHMap r
        (CategoryTheory.CategoryStruct.id (Rep.res r (SSGRoute.PTExt.modRep G M)))
        (Work.SSGRoute.ExtH1.gammaHom G M (Work.SSGRoute.augSES_shortExact G)
          (Work.GroupCohomology.H1π G M ψ))
      = Work.SSGRoute.ExtH1.gammaHom H M (Work.SSGRoute.augSES_shortExact H)
          (Work.GroupCohomology.H1π H M
            ⟨fun h => ψ.1 (r h), (Work.GroupCohomology.mem_Z1_iff H M _).mpr
              (fun a b => by
                rw [map_mul]
                exact (Work.GroupCohomology.mem_Z1_iff G M ψ.1).mp ψ.2 (r a) (r b))⟩) := by
  letI : DistribMulAction H M := DistribMulAction.compHom M r
  rw [Work.SSGRoute.ExtH1.gammaHom_H1π (G := G) (M := M) (Work.SSGRoute.augSES_shortExact G) ψ,
    Work.SSGRoute.ExtH1.gammaHom_H1π (G := H) (M := M) (Work.SSGRoute.augSES_shortExact H),
    Work.SSGRoute.ExtH1.gammaZ1_apply (G := G) (M := M) (Work.SSGRoute.augSES_shortExact G) ψ,
    Work.SSGRoute.ExtH1.gammaZ1_apply (G := H) (M := M) (Work.SSGRoute.augSES_shortExact H)]
  simp only [Work.SSGRoute.ExtH1.phiMap]
  exact Work.SSGRoute.ExtHMapAux.extHMap_extClass_cocycle r ψ.1
    ((Work.SSGRoute.ExtH1.crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2) _

end Work.SSGRoute
