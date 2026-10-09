import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Compatibility of the canonical inclusion of idèle class groups with a tower of levels

For number fields `K ⊆ L ⊆ L₂`, the composite `C_K → C_L → C_{L₂}` of the canonical inclusions
(`classIncl`, i.e. the maps induced by the local embeddings) is the canonical inclusion
`C_K → C_{L₂}`, elementwise.  This is the "`λ` is natural under inflation" ingredient of the
dévissage `E5s` (`Work.SSGRoute.phi1_mono_step_in`); it is also what the `E6Ω` route
(`Work.SSGRoute.phi1_mono_sylow_in`) needs.

The proof avoids comparing the *place* maps of the two exhibited inclusions: it exhibits the
composite idèle map `φ₂ ∘ φ₁` (with place map `u₁ ∘ u₂`, transitive by
`place_liesOver_trans`, local components composing by `localAlgebraMapUnits_comp`), descends it to
the class groups (`globalCFT_ideleClassGroup_inclusion_exists`), packages the result as a
`Gal(L₂/k)`-morphism (equivariance from `ideleInclusion_smul_restrict`) and concludes with the
*uniqueness* of the canonical inclusion (`isCanonicalClassIncl_unique`).
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory NK.GlobalCFT

/-- **The composite `C_K → C_L → C_{L₂}` of canonical inclusions is `C_K → C_{L₂}`.** -/
theorem classIncl_compat_apply {k K L L₂ : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Field L₂] [NumberField L₂]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional k K]
    [IsGalois k K] [Algebra L L₂] [Algebra K L₂] [Algebra k L₂] [IsScalarTower k L L₂]
    [IsScalarTower K L L₂] [IsScalarTower k K L₂] [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional L L₂] [IsGalois L L₂] [FiniteDimensional k L₂] [IsGalois k L₂]
    (y : ↥(classesK k K)) :
    (classIncl k L L₂).hom ((classIncl k K L).hom y) = (classIncl k K L₂).hom y := by
  obtain ⟨u₁, hu₁, φ₁, hφ₁, hι₁⟩ := classIncl_isCanonical (k := k) (K := K) (L := L)
  obtain ⟨u₂, hu₂, φ₂, hφ₂, hι₂⟩ := classIncl_isCanonical (k := k) (K := L) (L := L₂)
  -- the composite data
  let uc : Place L₂ → Place K := fun w => u₁ (u₂ w)
  have huc : ∀ w : Place L₂, w.LiesOver (uc w) := fun w =>
    place_liesOver_trans (hu₂ w) (hu₁ (u₂ w))
  let φc : Idele K →* Idele L₂ := φ₂.comp φ₁
  have hφc : ∀ (x : Idele K) (w : Place L₂),
      φc x w = (Place.localAlgebraMapUnits w (uc w) (huc w)) (x (uc w)) := by
    intro x w
    show (φ₂ (φ₁ x)) w = _
    rw [hφ₂ (φ₁ x) w, hφ₁ x (u₂ w)]
    exact congrArg (fun f : (Place.localField K (u₁ (u₂ w)))ˣ →* (Place.localField L₂ w)ˣ =>
        f (x (u₁ (u₂ w))))
      (localAlgebraMapUnits_comp (hu₂ w) (hu₁ (u₂ w)) (huc w))
  -- the induced map on idèle class groups
  obtain ⟨psi, hpsi⟩ := Inclusion.globalCFT_ideleClassGroup_inclusion_exists
    (K := K) (L := L₂) uc huc φc hφc
  -- equivariance of `psi` (from the equivariance of the composite idèle map)
  have hpsieq : ∀ (σ : L₂ ≃ₐ[k] L₂) (y : IdeleClassGroup K),
      psi ((galRes k K L₂ σ) • y) = σ • psi y := by
    intro σ y
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K y
    rw [IdeleClassGroup.smul_mk, hpsi, hpsi, IdeleClassGroup.smul_mk]
    exact congrArg (IdeleClassGroup.mk L₂)
      (NK.HassePrinciple.ideleInclusion_smul_restrict (K := k) (F := K) (L := L₂)
        uc huc φc hφc σ x).symm
  -- package `psi` as a morphism of `Gal(L₂/k)`-modules
  let psiT : Rep.res (galRes k K L₂) (classesK k K) ⟶ classesK k L₂ :=
    Rep.ofHom { toFun := fun y => Additive.ofMul (psi (Additive.toMul y)),
                map_add' := fun a b => classIncl_ofMul_monoidHom_add psi a b
                map_smul' := fun n x => classIncl_ofMul_monoidHom_smul psi n x
                isIntertwining' := fun σ => by
                  apply LinearMap.ext
                  intro y
                  exact congrArg Additive.ofMul (hpsieq σ (Additive.toMul y)) }
  -- `psiT` is canonical
  have hcan : IsCanonicalClassIncl k K L₂ psiT := by
    refine ⟨uc, huc, φc, ?_, ?_⟩
    · intro x w
      exact hφc x w
    · intro x
      show (Rep.Hom.hom psiT) (Additive.ofMul (IdeleClassGroup.mk K x))
        = (Additive.ofMul (IdeleClassGroup.mk L₂ (φc x)) : ↥(classesK k L₂))
      show (Additive.ofMul (psi (IdeleClassGroup.mk K x)) : ↥(classesK k L₂)) = _
      exact congrArg (fun t => (Additive.ofMul t : ↥(classesK k L₂))) (hpsi x)
  have hpsiT : psiT = classIncl k K L₂ :=
    isCanonicalClassIncl_unique _ _ hcan (classIncl_isCanonical (k := k) (K := K) (L := L₂))
  -- conclude elementwise
  obtain ⟨z, hz⟩ : ∃ z : Idele K, y = Additive.ofMul (IdeleClassGroup.mk K z) := by
    obtain ⟨z, hz⟩ := IdeleClassGroup.mk_surjective K (Additive.toMul y)
    exact ⟨z, by change Additive.toMul y = IdeleClassGroup.mk K z; exact hz.symm⟩
  have hA : (Rep.Hom.hom (classIncl k K L)) (Additive.ofMul (IdeleClassGroup.mk K z))
      = (Additive.ofMul (IdeleClassGroup.mk L (φ₁ z)) : ↥(classesK k L)) := hι₁ z
  have hB : (Rep.Hom.hom (classIncl k L L₂)) (Additive.ofMul (IdeleClassGroup.mk L (φ₁ z)))
      = (Additive.ofMul (IdeleClassGroup.mk L₂ (φ₂ (φ₁ z))) : ↥(classesK k L₂)) := hι₂ (φ₁ z)
  have hC : (Rep.Hom.hom psiT) (Additive.ofMul (IdeleClassGroup.mk K z))
      = (Additive.ofMul (IdeleClassGroup.mk L₂ (φ₂ (φ₁ z))) : ↥(classesK k L₂)) := by
    show (Additive.ofMul (psi (IdeleClassGroup.mk K z)) : ↥(classesK k L₂)) = _
    exact congrArg (fun t => (Additive.ofMul t : ↥(classesK k L₂))) (hpsi z)
  have hD : (Rep.Hom.hom (classIncl k K L₂)) (Additive.ofMul (IdeleClassGroup.mk K z))
      = (Additive.ofMul (IdeleClassGroup.mk L₂ (φ₂ (φ₁ z))) : ↥(classesK k L₂)) := by
    rw [← hpsiT]
    exact hC
  have h1 : (Rep.Hom.hom (classIncl k L L₂))
        ((Rep.Hom.hom (classIncl k K L)) (Additive.ofMul (IdeleClassGroup.mk K z)))
      = (Additive.ofMul (IdeleClassGroup.mk L₂ (φ₂ (φ₁ z))) : ↥(classesK k L₂)) :=
    (congrArg (fun t => (Rep.Hom.hom (classIncl k L L₂)) t) hA).trans hB
  rw [hz]
  exact h1.trans hD.symm

/-! ## `resResHom` acts as the identity on elements -/

/-- **`eqToHom` in `Rep k G` acts by transport along the underlying-type equality.** -/
theorem Rep.eqToHom_hom_apply {k G : Type*} [Semiring k] [Monoid G] {A B : Rep k G}
    (h : A = B) (y : A.V) :
    (Rep.Hom.hom (CategoryTheory.eqToHom h)) y = (h ▸ y : B.V) := by
  cases h
  rfl

/-- **The canonical transport `resResHom` acts as the identity on elements.**  The two
representations have the same underlying type, so the transport underlying `eqToHom` is a
transport along a self-equality of a type. -/
theorem resResHom_hom_apply {k K L L₂ : Type} [Field k] [Field K] [Field L] [Field L₂]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k L₂]
    [Algebra K L₂] [IsScalarTower k K L₂] [Algebra L L₂] [IsScalarTower k L L₂]
    [IsScalarTower K L L₂] [IsGalois k K] [IsGalois k L] (M : Rep Coeff (K ≃ₐ[k] K))
    (y : ↥(Rep.res (galRes k L L₂) (Rep.res (galRes k K L) M))) :
    (Rep.Hom.hom (resResHom (k := k) (K := K) (L := L) (L' := L₂) M)) y = y := by
  rw [resResHom, Rep.eqToHom_hom_apply]
  exact eq_of_heq (rec_heq_of_heq _ (HEq.refl y))

/-! ## The morphism-level form (one step away, not yet verified here)

With `classIncl_compat_apply` (above) and `resResHom_hom_apply` (above), the morphism-level form

```lean
((Rep.resFunctor (galRes k L L₂)).map (classIncl k K L) ≫ classIncl k L L₂)
  = resResHom (k := k) (K := K) (L := L) (L' := L₂) (classesK k K) ≫ classIncl k K L₂
```

is obtained by `Rep.hom_ext` + `LinearMap.ext`: for `y` in the common underlying type, the left-hand
side is `π₂ (π₁ y)` (by `Rep.comp_apply` and `Rep.resMap_hom_apply`), which is `π₃ y` by
`classIncl_compat_apply`, while the right-hand side is `π₃ ((resResHom _) y) = π₃ y` by
`resResHom_hom_apply`.  (The `change` to the `ConcreteCategory`-coercion form of the two sides is
needed before the `Rep.comp_apply` rewrites; this last adaptation was not re-verified under the
fleet's memory budget at the end of the session.) -/

end Work.SSGRoute
