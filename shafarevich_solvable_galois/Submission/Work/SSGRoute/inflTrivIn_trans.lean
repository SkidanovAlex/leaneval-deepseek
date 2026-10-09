import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.mapExactFunctor_id
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity of the level inflation maps `Work.SSGRoute.PTExt.inflTrivIn`

The colimit step of `Work.SSGRoute.phi1_mono_step_in` needs the level system
`L ↦ H^n(Gal(L/k), V)` (for a *trivial* coefficient module `V`, e.g. `V = ZMod p`) to be a directed
system with the inflation maps `inflTrivIn h` as transition maps.  Here we prove the `map_map`
axiom: inflating first along `L ≤ L'` and then along `L' ≤ L''` is inflating along the composite
inclusion `L ≤ L''` (`inflTrivIn_trans`).

The proof has three layers.

* `extHMap_comp_aux`: **composition of the change-of-group maps on `Ext`-cohomology**.  For group
  homomorphisms `f : H →* G`, `g : I →* H` and coefficient maps `ι₁ : Rep.res f A ⟶ B`,
  `ι₂ : Rep.res g B ⟶ C`, `ι : Rep.res (f.comp g) A ⟶ C` with
  `Rep.resMap g ι₁ ≫ ι₂ = ι` (the sources are definitionally equal, since `Rep.resFunctor` is an
  abbreviation), one has `extHMap g ι₂ (extHMap f ι₁ y) = extHMap (f.comp g) ι y`.  This is the
  bookkeeping of `extRes`, `Rep.resMap`, `Abelian.Ext.mk₀_comp_mk₀` and the associativity lemmas
  for `Abelian.Ext.comp`.
* `inflTriv_comp_aux`: the same for the trivial coefficient module `V`, where the three coefficient
  maps are `trivResInv f V`, `trivResInv g V`, `trivResInv (f.comp g) V`; the compatibility
  hypothesis is `resMap_trivResInv_comp`, which holds since all these maps are the identity on the
  underlying module.
* `inflTrivIn_trans`: `inflTrivIn` unfolds to `extHMap` of `galRes` and `trivResInv`, and
  `galRes k L L'' = (galRes k L L').comp (galRes k L' L'')` is
  `IsScalarTower.AlgEquiv.restrictNormalHom_comp` (`restriction to a normal subfield is compatible
  with the scalar tower`).
-/

set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt

section Comp

variable {G H I : Type} [Group G] [Group H] [Group I]

/-- `unitRes` is compatible with the restriction of a representation along a composite of group
homomorphisms: `unitRes g ≫ Rep.resMap g (unitRes f) = unitRes (f.comp g)`.  Both sides are the
identity of the coefficient ring, so this is `rfl` on underlying maps. -/
theorem unitRes_comp_resMap (f : H →* G) (g : I →* H) :
    unitRes g ≫ Rep.resMap g (unitRes f) = unitRes (f.comp g) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rfl

/-- `trivResInv` is compatible with the restriction of a representation along a composite of group
homomorphisms: `Rep.resMap g (trivResInv f V) ≫ trivResInv g V = trivResInv (f.comp g) V`.  Again
both sides are the identity of `V`. -/
theorem resMap_trivResInv_comp (f : H →* G) (g : I →* H) (V : Type) [AddCommGroup V]
    [Module Coeff V] :
    Rep.resMap g (trivResInv f V) ≫ trivResInv g V = trivResInv (f.comp g) V := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rfl

/-- **Composition of the change-of-group maps on `Ext`-cohomology.**  Inflating `y ∈ Hⁿ(G, A)`
along `f : H →* G` (with coefficient map `ι₁`) and then along `g : I →* H` (with coefficient map
`ι₂`) is inflating along `f.comp g` (with coefficient map `ι`), provided the coefficient maps
compose: `Rep.resMap g ι₁ ≫ ι₂ = ι`.  The sources of `ι` and `Rep.resMap g ι₁ ≫ ι₂` are
definitionally equal because `Rep.resFunctor` is an abbreviation. -/
theorem extHMap_comp_aux (f : H →* G) (g : I →* H) {A : Rep Coeff G} {B : Rep Coeff H}
    {C : Rep Coeff I} (ι₁ : Rep.res f A ⟶ B) (ι₂ : Rep.res g B ⟶ C)
    (ι : Rep.res (f.comp g) A ⟶ C) (hι : Rep.resMap g ι₁ ≫ ι₂ = ι) {n : ℕ} (y : extH A n) :
    extHMap g ι₂ (extHMap f ι₁ y) = extHMap (f.comp g) ι y := by
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor g)
      (Abelian.Ext.mapExactFunctor (Rep.resFunctor f) y)
      = Abelian.Ext.mapExactFunctor (Rep.resFunctor (f.comp g)) y :=
    ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor f)
      (Rep.resFunctor g) n (unitRep G) A y
  have hι₀ : (Abelian.Ext.mk₀ (unitRes g)).comp
        (Abelian.Ext.mk₀ (Rep.resMap g (unitRes f))) (add_zero 0)
      = Abelian.Ext.mk₀ (unitRes (f.comp g)) := by
    rw [Abelian.Ext.mk₀_comp_mk₀, unitRes_comp_resMap]
  have hι' : (Abelian.Ext.mk₀ (Rep.resMap g ι₁)).comp (Abelian.Ext.mk₀ ι₂) (add_zero 0)
      = Abelian.Ext.mk₀ ι := by
    rw [Abelian.Ext.mk₀_comp_mk₀, hι]
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hcomp]
  conv_lhs => rw [← Abelian.Ext.comp_assoc_of_third_deg_zero]
  conv_lhs => rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
  conv_lhs => rw [hι₀]
  conv_lhs => rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  conv_lhs => rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  conv_lhs => rw [hι']

end Comp

section Triv

variable {G H I : Type} [Group G] [Group H] [Group I]

/-- **Transitivity of `extHMap` for a trivial coefficient module.**  For a trivial module
`V` the change-of-group maps are `extHMap · (trivResInv · V)`, and these compose: inflating first
along `f` and then along `g` is inflating along `f.comp g`. -/
theorem inflTriv_comp_aux (f : H →* G) (g : I →* H) (V : Type) [AddCommGroup V]
    [Module Coeff V] {n : ℕ} (y : extH (Rep.trivial Coeff G V) n) :
    extHMap g (trivResInv g V) (extHMap f (trivResInv f V) y)
      = extHMap (f.comp g) (trivResInv (f.comp g) V) y :=
  extHMap_comp_aux f g (trivResInv f V) (trivResInv g V) (trivResInv (f.comp g) V)
    (resMap_trivResInv_comp f g V) y

end Triv

/-- **Transitivity of the level inflation maps** (the `map_map` axiom for the level system of the
colimit step of `Work.SSGRoute.phi1_mono_step_in`): inflating `H^n(Gal(L/k), V)` first to `L'` and
then to `L''` is inflating along the composite inclusion.  Equivalent to
`levelMap (L'') (levelMap (L') y) = levelMap (h₁.trans h₂) y` in
`Submission/Work/SSGRoute/phi1_level_system.lean`.

Ingredients (all proved in the workspace): `Work.SSGRoute.ext_mapExactFunctor_comp_functor_aux`
(`(x.mapExactFunctor F).mapExactFunctor G = x.mapExactFunctor (F ⋙ G)`),
`Work.SSGRoute.extRes_comp_aux` (`extRes (ψ.comp φ) x = extRes φ (extRes ψ x)`),
`galRes_trans` (PTDefs), `Abelian.Ext.mapExactFunctor_comp`, `mk₀_comp_mk₀`, `comp_assoc_*`; the
bookkeeping is that `unitRes`/`trivResInv` are identities on the coefficient type and that
`Rep.res f₂ (Rep.res f₁ M)` vs `Rep.res (f₂.comp f₁) M` are propositionally equal. -/
theorem inflTrivIn_trans {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {L L' L'' : IntermediateField K Ω} [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k L'] [IsGalois k L'] (h₁ : L ≤ L') (h₂ : L' ≤ L'')
    (V : Type) [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V] {n : ℕ}
    (y : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) V) n) :
    SSGRoute.PTExt.inflTrivIn h₂ V (SSGRoute.PTExt.inflTrivIn h₁ V y)
      = SSGRoute.PTExt.inflTrivIn (h₁.trans h₂) V y := by
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion h₁).toAlgebra
  letI : Algebra ↥L ↥L'' := (IntermediateField.inclusion (h₁.trans h₂)).toAlgebra
  letI : Algebra ↥L' ↥L'' := (IntermediateField.inclusion h₂).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k ↥L ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥L ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hgal : (galRes k ↥L ↥L'' : (↥L'' ≃ₐ[k] ↥L'') →* (↥L ≃ₐ[k] ↥L))
      = (galRes k ↥L ↥L').comp (galRes k ↥L' ↥L'') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k ↥L ↥L' ↥L''
  unfold inflTrivIn inflTriv
  rw [hgal]
  exact inflTriv_comp_aux (galRes k ↥L ↥L') (galRes k ↥L' ↥L'') V y

end Work.SSGRoute
