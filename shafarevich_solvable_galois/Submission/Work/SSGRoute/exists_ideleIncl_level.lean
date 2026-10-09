import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.classIncl_isCanonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!

# The idèle inclusion `𝕀_K → 𝕀_L` at the level `k ⊆ K ⊆ L`, as a map of `Gal(L/k)`-modules

This node makes explicit the *idèle-level* map underlying the canonical inclusion of idèle class
groups `C_K → C_L` of `Submission/Work/SSGRoute/classIncl_isCanonical.lean` (node `E0c`):

* `Work.SSGRoute.exists_ideleIncl_level`: there is a morphism of `Gal(L/k)`-representations
  `J : res 𝕀_K ⟶ 𝕀_L` whose `w`-component (for `w` a place of `L` lying over a place `v` of `K`)
  is the canonical local algebra map `K_vˣ →* L_wˣ`, and which is compatible with the class-group
  maps: `res(classGroupMap k K) ≫ classIncl k K L = J ≫ classGroupMap k L`.

The map `J` is obtained by choosing, for every place `w` of `L`, a place `u w` of `K` below it
(`NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder`) and taking `φ : 𝕀_K →* 𝕀_L` with
`φ x w = (localAlgebraMapUnits w (u w) ·) (x (u w))`
(`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists`).  Two inputs make `φ` a morphism of
representations and connect it with the (choice-based) `classIncl`:

* the Galois-equivariance of the idèle inclusion, i.e. the naturality of `φ` under base change
  (`NK.HassePrinciple.ideleInclusion_smul_restrict`);
* the uniqueness of the place of `K` below a given place of `L`
  (`NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`), which shows that *any* map satisfying the
  local description agrees componentwise with `φ`, hence in particular the one chosen to define
  `classIncl`.

-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

/-- Two idèle maps whose local descriptions are given with respect to two place maps `u` and `u'`
which agree, agree componentwise.  The proof is a transport along `u' = u` together with the fact
that `Place.localAlgebraMapUnits` does not depend on the proof of `Place.LiesOver`. -/
private lemma localComponent_eq_of_eq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {u u' : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K}
    (hu : ∀ w, NK.GlobalCFT.Place.LiesOver w (u w))
    (hu' : ∀ w, NK.GlobalCFT.Place.LiesOver w (u' w)) (h : u' = u)
    (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L) :
    NK.GlobalCFT.Place.localAlgebraMapUnits w (u' w) (hu' w) (x (u' w)) =
      NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)) := by
  cases h
  exact congrArg (fun f => f (x (u w)))
    (NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_congr w (u w) (hu' w) (hu w))

/-- For an idèle map `φ : 𝕀_K → 𝕀_L` whose `w`-component is the local algebra map attached to a
place `u w` below `w`, the `w'`-component of `φ x` is computed by the local algebra map attached to
*any* place `w` of `K` below `w'`: the place below is unique
(`NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`). -/
private lemma localComponent_eq_of_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K}
    (hu : ∀ w, NK.GlobalCFT.Place.LiesOver w (u w)) (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (x : NK.GlobalCFT.Idele K) {w' : NK.GlobalCFT.Place L} {w : NK.GlobalCFT.Place K}
    (hw : NK.GlobalCFT.Place.LiesOver w' w) :
    φ x w' = NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw (x w) := by
  have h : u w' = w := NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu w') hw
  subst h
  rw [hφ x w']

/-- **The `classIncl` of the class formation is the map induced by *any* idèle inclusion with the
canonical local description.**  `classIncl` is defined by choice out of the existence statement
`classIncl_isCanonical`; the witness `φ'` of that canonical structure has the same local
description, and the place below a place of `L` being unique it agrees with `φ`. -/
private lemma classIncl_hom_mk (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    {u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K}
    (hu : ∀ w, NK.GlobalCFT.Place.LiesOver w (u w))
    (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (x : NK.GlobalCFT.Idele K) :
    (classIncl k K L).hom (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk K x)) =
      Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk L (φ x)) := by
  obtain ⟨u', hu', φ', hφ', hψ'⟩ := classIncl_isCanonical k K L
  have hφφ' : φ' x = φ x := by
    apply NK.GlobalCFT.Idele.ext
    intro w
    rw [hφ' x w, hφ x w]
    exact localComponent_eq_of_eq hu hu'
      (funext fun w => NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu' w) (hu w)) x w
  rw [hψ' x, hφφ']

theorem exists_ideleIncl_level (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L] :
    ∃ J : Rep.res (galRes k K L) (idelesK k K) ⟶ idelesK k L,
      (∀ (x : NK.GlobalCFT.Idele K) (w' : NK.GlobalCFT.Place L) (w : NK.GlobalCFT.Place K)
        (hw : NK.GlobalCFT.Place.LiesOver w' w),
        (Additive.toMul (J.hom (Additive.ofMul x) : Additive (NK.GlobalCFT.Idele L)) : NK.GlobalCFT.Idele L) w' =
          NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw (x w)) ∧
      Rep.resMap (galRes k K L) (NK.HassePrinciple.classGroupMap k K) ≫ classIncl k K L =
        J ≫ NK.HassePrinciple.classGroupMap k L := by
  classical
  -- the class-group maps, with their universes pinned down
  let gK : idelesK k K ⟶ classesK k K := NK.HassePrinciple.classGroupMap k K
  let gL : idelesK k L ⟶ classesK k L := NK.HassePrinciple.classGroupMap k L
  -- a place of `K` below every place of `L`
  let u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K := fun w =>
    Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)
  have hu : ∀ w : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w (u w) := fun w =>
    Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)
  -- the idèle inclusion with the canonical local components
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := L) u hu
  -- naturality of the idèle inclusion under base change
  have hsmul : ∀ (σ : L ≃ₐ[k] L) (x : NK.GlobalCFT.Idele K),
      φ (galRes k K L σ • x) = σ • φ x := fun σ x =>
    (NK.HassePrinciple.ideleInclusion_smul_restrict (K := k) (F := K) (L := L) u hu φ hφ σ x).symm
  -- the underlying additive group homomorphism `𝕀_K → 𝕀_L`
  let lin : Additive (NK.GlobalCFT.Idele K) →ₗ[Coeff] Additive (NK.GlobalCFT.Idele L) :=
    { toFun := fun y => Additive.ofMul (φ (Additive.toMul y))
      map_add' := fun a b => by rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        change Additive.ofMul (φ (Additive.toMul ((n.down : ℤ) • x))) =
          n.down • Additive.ofMul (φ (Additive.toMul x))
        rw [toMul_zsmul, map_zpow, ofMul_zpow] }
  -- packaged as a morphism of `Gal(L/k)`-representations
  let J : Rep.res (galRes k K L) (idelesK k K) ⟶ idelesK k L :=
    Rep.ofHom
      { toLinearMap := lin
        isIntertwining' := by
          intro σ
          apply LinearMap.ext
          intro y
          obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = y := ⟨Additive.toMul y, rfl⟩
          change lin (((idelesK k K).ρ (galRes k K L σ)) (Additive.ofMul x)) =
            ((idelesK k L).ρ σ) (Additive.ofMul (φ x))
          rw [NK.HassePrinciple.ideleRep_ρ_apply k K (galRes k K L σ) x,
              NK.HassePrinciple.ideleRep_ρ_apply k L σ (φ x)]
          exact congrArg Additive.ofMul (hsmul σ x) }
  -- computation rules
  have hJ : ∀ x : NK.GlobalCFT.Idele K, J.hom (Additive.ofMul x) = Additive.ofMul (φ x) :=
    fun x => rfl
  have hgmK : ∀ x : NK.GlobalCFT.Idele K, gK.hom (Additive.ofMul x) =
      Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk K x) :=
    fun x => NK.HassePrinciple.classGroupMap_apply k K x
  have hgmL : ∀ x : NK.GlobalCFT.Idele L, gL.hom (Additive.ofMul x) =
      Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk L x) :=
    fun x => NK.HassePrinciple.classGroupMap_apply k L x
  refine ⟨J, ?_, ?_⟩
  · -- the local description of `J`
    intro x w' w hw
    change (φ x) w' = NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw (x w)
    exact localComponent_eq_of_liesOver hu φ hφ x hw
  · -- compatibility with the class-group maps
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ : ∃ x : NK.GlobalCFT.Idele K, Additive.ofMul x = y :=
      ⟨Additive.toMul y, rfl⟩
    show (classIncl k K L).hom (gK.hom (Additive.ofMul x)) =
      gL.hom (J.hom (Additive.ofMul x))
    refine Eq.trans (b := Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk L (φ x))) ?_ (Eq.symm ?_)
    · exact (congrArg (fun z => (classIncl k K L).hom z) (hgmK x)).trans
        (classIncl_hom_mk k K L hu φ hφ x)
    · exact (congrArg (fun z => gL.hom z) (hJ x)).trans (hgmL (φ x))

end

end Work.SSGRoute
