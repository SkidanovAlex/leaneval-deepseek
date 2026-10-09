import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.e6_util
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.phi1_ext_cor_transfer
import Submission.Work.SSGRoute.phi1_sylow_setup
import Submission.Work.SSGRoute.sylow_descend
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E6Ω: Sylow descent for `φ¹` (levels inside a fixed `Ω`)

See `Submission/Work/SSGRoute/DESIGN_FIX.md` and `Submission/Work/SSGRoute/E6OMEGA_STATUS.md`
(the route, the level issue, and the interface to the pieces already on disk).  Definitions:
`PTDefs.lean` + `PTDefsOmega.lean`; the Sylow setup is
`Submission/Work/SSGRoute/phi1_sylow_setup.lean` and the restriction/corestriction
infrastructure is `Submission/Work/SSGRoute/sylow_descend.lean` (`Work.SSGRoute.SylowDesc`).

Contents of this file:

* the fixed field `k' = K^P` of a Sylow subgroup `P` (`SylowIn.finrank_fixedField_eq_index`,
  `SylowIn.fixedFieldGalEquiv`, `SylowIn.isPGroup_fixedField`,
  `SylowIn.not_dvd_finrank_fixedField`, `SylowIn.isPrimitiveRoot_fixedField`);
* uniqueness of the canonical inclusion `C_K → C_L` (`SylowIn.isCanonicalClassIncl_unique`).

(The target `phi1_mono_sylow_in` (E6Ω) lives in `Submission/Work/SSGRoute/phi1_mono_sylow_in.lean`,
which imports this module.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

namespace SylowIn

/-! ## The fixed field `k' = K^P` of a Sylow subgroup -/

section FixedField

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] (P : Subgroup (K ≃ₐ[k] K))

/-- `[K^P : k] = P.index`. -/
theorem finrank_fixedField_eq_index :
    Module.finrank k ↥(IntermediateField.fixedField P) = P.index := by
  have h1 : Nat.card ↥P * P.index = Nat.card (K ≃ₐ[k] K) := Subgroup.card_mul_index P
  have h2 : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
  have h3 : Module.finrank ↥(IntermediateField.fixedField P) K = Nat.card ↥P :=
    IntermediateField.finrank_fixedField_eq_card P
  have h4 : Module.finrank k ↥(IntermediateField.fixedField P) *
      Module.finrank ↥(IntermediateField.fixedField P) K = Module.finrank k K :=
    Module.finrank_mul_finrank k ↥(IntermediateField.fixedField P) K
  have h5 : Module.finrank k ↥(IntermediateField.fixedField P) * Nat.card ↥P =
      Nat.card ↥P * P.index := by
    calc Module.finrank k ↥(IntermediateField.fixedField P) * Nat.card ↥P
        = Module.finrank k ↥(IntermediateField.fixedField P) *
            Module.finrank ↥(IntermediateField.fixedField P) K := by rw [h3]
      _ = Module.finrank k K := h4
      _ = Nat.card (K ≃ₐ[k] K) := h2.symm
      _ = Nat.card ↥P * P.index := h1.symm
  exact Nat.mul_left_cancel (Nat.card_pos (α := ↥P)) (by rw [mul_comm]; exact h5)

/-- `Gal(K/K^P) ≃* P`. -/
noncomputable def fixedFieldGalEquiv :
    (K ≃ₐ[↥(IntermediateField.fixedField P)] K) ≃* ↥P :=
  (IntermediateField.subgroupEquivAlgEquiv P).symm

/-- `Gal(K/K^P)` is a `p`-group when `P` is. -/
theorem isPGroup_fixedField {p : ℕ} (hP : IsPGroup p ↥P) :
    IsPGroup p (K ≃ₐ[↥(IntermediateField.fixedField P)] K) :=
  IsPGroup.of_equiv hP (IntermediateField.subgroupEquivAlgEquiv P)

/-- `p ∤ [K^P : k]` when `p ∤ P.index`. -/
theorem not_dvd_finrank_fixedField {p : ℕ} (hP : ¬ p ∣ P.index) :
    ¬ p ∣ Module.finrank k ↥(IntermediateField.fixedField P) := by
  rw [finrank_fixedField_eq_index P]; exact hP

/-- An element of `K` fixed by `P` lies in `K^P`. -/
theorem mem_fixedField_of_forall (x : K) (hx : ∀ σ ∈ P, σ x = x) :
    x ∈ IntermediateField.fixedField P :=
  (IntermediateField.mem_fixedField_iff P x).mpr hx

/-- A primitive `p`-th root of unity in `K` fixed by `P` is a primitive `p`-th root of unity in
`K^P`. -/
theorem isPrimitiveRoot_fixedField {p : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ σ ∈ P, σ ζ = ζ) :
    IsPrimitiveRoot (⟨ζ, mem_fixedField_of_forall P ζ hfix⟩ : ↥(IntermediateField.fixedField P))
      p :=
  IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(IntermediateField.fixedField P) K)
    hζ (fun x y h => Subtype.ext h)

end FixedField

/-! ## Uniqueness of the canonical inclusion `classIncl` -/

section ClassInclUnique

variable {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]

/-- **Uniqueness of the canonical inclusion of idèle class groups.**  `IsCanonicalClassIncl k K L ι`
says that `ι` is induced by an idèle map `𝕀_K → 𝕀_L` whose `w`-component is the local embedding
`K_{u w} → L_w`.  A place of `K` below a given place of `L` is unique
(`NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`), and the idèle map is then determined by the
formula, so there is at most one such `ι`.  (Existence is the node `E0c`,
`Work.SSGRoute.classIncl_isCanonical`.) -/
theorem isCanonicalClassIncl_unique {ι ι' : Rep.res (galRes k K L) (classesK k K) ⟶ classesK k L}
    (h : IsCanonicalClassIncl k K L ι) (h' : IsCanonicalClassIncl k K L ι') : ι = ι' := by
  obtain ⟨u, hu, φ, hφ, hι⟩ := h
  obtain ⟨u', hu', φ', hφ', hι'⟩ := h'
  have huu : u = u' := by
    funext w
    exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu w) (hu' w)
  subst huu
  have hφφ : φ = φ' := by
    refine MonoidHom.ext fun x => ?_
    refine DFunLike.ext _ _ fun w => ?_
    rw [hφ x w, hφ' x w]
  have hfun : ∀ q : NK.GlobalCFT.IdeleClassGroup K,
      ι.hom (Additive.ofMul q) = ι'.hom (Additive.ofMul q) := by
    intro q
    obtain ⟨x, rfl⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective K q
    rw [hι x, hι' x, hφφ]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  conv_lhs => rw [show y = Additive.ofMul (Additive.toMul y) from rfl]
  conv_rhs => rw [show y = Additive.ofMul (Additive.toMul y) from rfl]
  exact hfun (Additive.toMul y)

end ClassInclUnique

/-! ## The canonical inclusion does not depend on the choice of base field -/

section ClassInclBaseChange

variable {k k' K L : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field K]
  [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k' K] [Algebra k k']
  [IsScalarTower k k' K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k' L]
  [IsScalarTower k' K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K]
  [IsGalois k' K] [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k' L] [IsGalois k' L]

/-- **The canonical inclusion `C_K → C_L` does not depend on the base field.**  For
`k ⊆ k' ⊆ K ⊆ L` the two inclusions `classIncl k' K L` and `classIncl k K L` agree on the classes of
principal idèles: both are induced by the same idèle map `𝕀_K → 𝕀_L` whose `w`-component is the local
embedding, and the place of `K` below a place of `L` is unique. -/
theorem classIncl_apply_baseChange (x : NK.GlobalCFT.Idele K) :
    (classIncl k' K L).hom (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk K x)) =
      (classIncl k K L).hom (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk K x)) := by
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k' K L
  obtain ⟨u', hu', φ', hφ', hι'⟩ := classIncl_isCanonical k K L
  have huu : u = u' := by
    funext w
    exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu w) (hu' w)
  subst huu
  have hφφ : φ = φ' := by
    refine MonoidHom.ext fun x => ?_
    refine DFunLike.ext _ _ fun w => ?_
    rw [hφ x w, hφ' x w]
  rw [hι x, hι' x, hφφ]

end ClassInclBaseChange

/-! ## The level pairing under a further restriction of the group -/

section LevelPairRestrict

variable {G H H' : Type} [Group G] [Group H] [Group H']

/-- **Naturality of the level pairing under a further restriction of the group**: the
restriction-companion of `Work.SSGRoute.levelPair_extHMap` (which is the inflation-companion).  For a
level map `f : H →* G`, a coefficient class `x ∈ Ext^r_G(M, A)`, `h ∈ H^s(H, res f M)`, the
coefficient map `ι : res f A ⟶ B` and a further restriction `g : H' →* H` whose coefficient maps fit
as `Rep.resMap g ι ≫ ιg = ι'`, restricting the value of the level pairing along `g` gives the level
pairing at the composite level:
`extHMap g ιg (levelPair f ι x h) = levelPair (f.comp g) ι' x (extHMap g (𝟙 _) h)`.

For `k ⊆ k' ⊆ K ⊆ L` and `f := galRes k K L`, `g := resBaseHom` this is the base-change step of the
Sylow descent `E6Ω`: the `k'`-value of the pairing, restricted to `Gal(L/k) ≤ Gal(L/k')`, is the
`k`-value paired with the restricted class. -/
theorem levelPair_restrict (f : H →* G) (g : H' →* H) {M A : Rep Coeff G} {B : Rep Coeff H}
    {B' : Rep Coeff H'} (ι : Rep.res f A ⟶ B) (ιg : Rep.res g B ⟶ B')
    (ι' : Rep.res (f.comp g) A ⟶ B') {r s : ℕ} (x : Abelian.Ext M A r)
    (h : extH (Rep.res f M) s)
    (hι : Rep.resMap g ι ≫ ιg = ι') :
    extHMap g ιg (levelPair f ι x h)
      = levelPair (f.comp g) ι' x (extHMap g (𝟙 (Rep.res g (Rep.res f M))) h) := by
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor (k := Coeff) g)
        (Abelian.Ext.mapExactFunctor (Rep.resFunctor (k := Coeff) f) x) =
      Abelian.Ext.mapExactFunctor (Rep.resFunctor (k := Coeff) (f.comp g)) x := by
    simpa only [extRes] using
      (Work.SSGRoute.SylowDesc.extRes_comp_aux f g x).symm
  have hh : extHMap g (𝟙 (Rep.res g (Rep.res f M))) h
      = (Abelian.Ext.mk₀ (unitRes g)).comp (extRes g h) (zero_add s) := by
    simp only [extHMap, Abelian.Ext.comp_mk₀_id]
  rw [hh]
  simp only [levelPair, extHMap, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hcomp, Abelian.Ext.mk₀_comp_mk₀, hι,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Work.SSGRoute.E6Util.comp_assoc_of_first_deg_zero]

end LevelPairRestrict


/-! ## Base change at a level: the two restrictions of `Gal(L/k')` to `Gal(K/k)` agree -/

section BaseChangeLevel

/-- The restriction `Gal(K/k') →* Gal(K/k)` for `k ⊆ k'`, viewing a `k'`-automorphism as a
`k`-automorphism. -/
abbrev resBaseHom (k k' K : Type) [Field k] [Field k'] [Field K] [Algebra k K] [Algebra k' K]
    [Algebra k k'] [IsScalarTower k k' K] : (K ≃ₐ[k'] K) →* (K ≃ₐ[k] K) :=
  AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)

variable {k k' K L : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field K]
  [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k' K] [Algebra k k']
  [IsScalarTower k k' K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k' L]
  [IsScalarTower k' K L] [IsScalarTower k k' L] [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k' K] [IsGalois k' K] [FiniteDimensional k L] [IsGalois k L]
  [IsGalois k' L]

/-- **The two way-restrictions agree.**  For the tower `k ⊆ k' ⊆ K ⊆ L`, restricting a
`k'`-automorphism `σ` of `L` to `K` and then viewing the resulting `k'`-automorphism of `K` as a
`k`-automorphism agrees with viewing `σ` as a `k`-automorphism of `L` and then restricting to `K`:
both homs `Gal(L/k') →* Gal(K/k)` are `σ ↦ σ|_K`. -/
theorem resBaseHom_comp_galRes :
    (resBaseHom k k' K).comp (galRes k' K L) = (galRes k K L).comp (resBaseHom k k' L) := by
  refine MonoidHom.ext fun σ => AlgEquiv.ext fun x => ?_
  rfl

set_option maxHeartbeats 800000 in
/-- **The `hι` obligation of `levelPair_restrict` for the base change is `rfl`.**  Taking the
coefficient map at the composite level to be *by definition* the composite of the coefficient maps
(the canonical inclusion `classIncl k K L` transported along the base change of `C_L`), the
compatibility hypothesis of `SylowIn.levelPair_restrict` is discharged by `rfl`.  This is the
first step of the case-(i) transfer of `E6Ω`: the `k`-value of the level pairing, restricted along
the base change `Gal(L/k') →* Gal(L/k)`, is the level pairing at the composite level with the
restricted cohomology class. -/
theorem levelPair_restrict_baseChange {M : Rep Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x : Abelian.Ext M (classesK k K) r)
    (h : extH (Rep.res (galRes k K L) M) s) :
    extHMap (resBaseHom k k' L)
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom
        (levelPair (galRes k K L) (classIncl k K L) x h)
      = levelPair ((galRes k K L).comp (resBaseHom k k' L))
          (Rep.resMap (resBaseHom k k' L) (classIncl k K L)
            ≫ (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom)
          x (extHMap (resBaseHom k k' L) (𝟙 _) h) :=
  levelPair_restrict (galRes k K L) (resBaseHom k k' L) (classIncl k K L)
    (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom _ x h rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Item 2 of the case-(i) transfer, value form.**  The coefficient map at the composite level,
`Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫ (classesK_baseChangeIso k k' L).hom`, agrees on
the classes of principal idèles with the canonical inclusion `classIncl k' K L` at the base field
`k'`.  (The base-change isomorphism of `C_L` acts as the identity on the carrier — its `hom` is
`𝟙 _` definitionally — and `Rep.resMap` does not change the underlying function, so this is
`SylowIn.classIncl_apply_baseChange`.) -/
theorem classIncl_baseChange_apply (x : NK.GlobalCFT.Idele K) :
    ((Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom).hom
      (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk K x)))
    = (classIncl k' K L).hom (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk K x)) := by
  rw [ConcreteCategory.comp_apply, Rep.resMap_hom_apply]
  have hι : (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom = 𝟙 _ := rfl
  rw [hι]
  exact (classIncl_apply_baseChange (k := k) (k' := k') (K := K) (L := L) x).symm

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Item 2 of the case-(i) transfer, morphism level (in usable form).**  The coefficient map at the
composite level, `Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫ ιg`, and the canonical inclusion
`classIncl k' K L` at the base field `k'` have the same underlying function on the whole carrier
(not only on classes of principal idèles): every element of `C_K` is such a class
(`IdeleClassGroup.mk_surjective`), and on those the value form
`SylowIn.classIncl_baseChange_apply` applies.

This is the form in which the pairing consumes the identification: replacing `mk₀ ι'` by
`mk₀ (classIncl k' K L)` only needs the two underlying linear maps to agree, the domain difference
being the `rfl`-level/`resBaseHom_comp_galRes` transport of §8 item 1. -/
theorem classIncl_baseChange_hom_apply (y : Additive (NK.GlobalCFT.IdeleClassGroup K)) :
    (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom).hom y
      = (classIncl k' K L).hom y := by
  conv_lhs => rw [show y = Additive.ofMul (Additive.toMul y) from rfl]
  conv_rhs => rw [show y = Additive.ofMul (Additive.toMul y) from rfl]
  obtain ⟨q, hq⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective K (Additive.toMul y)
  rw [← hq]
  exact classIncl_baseChange_apply (k := k) (k' := k') (K := K) (L := L) q

/-- **The base-changed class.**  A class over `(k, K)` gives a class over `(k', K)`: restrict along
`resBaseHom` and transport the coefficients `C_K` to the base field `k'` by
`SylowDesc.classesK_baseChangeIso`. -/
noncomputable def baseChangeExt {k k' K : Type} [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k']
    [IsScalarTower k k' K] (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1) :
    Abelian.Ext (Rep.res (resBaseHom k k' K) M) (classesK k' K) 1 :=
  (extRes (resBaseHom k k' K) x).comp
    (Abelian.Ext.mk₀ (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom) (add_zero 1)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Item 3 of the case-(i) transfer.**  Restricting the base-changed class to the level `L` gives
the restriction of the original class along the composite homomorphism
`(resBaseHom k k' K).comp (galRes k' K L)` (= `(galRes k K L).comp (resBaseHom k k' L)` by
`resBaseHom_comp_galRes`), with the coefficient map `classesK_baseChangeIso k k' K` transported by
`Rep.resMap (galRes k' K L)`.  This is `SylowDesc.extRes_comp_aux` together with
`Abelian.Ext.mapExactFunctor_comp` / `mapExactFunctor_mk₀`. -/
theorem baseChangeExt_extRes {k k' K L : Type} [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K]
    [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [Algebra k' L] [IsScalarTower k' K L] [IsScalarTower k k' L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K] [IsGalois k' K]
    [FiniteDimensional k L] [IsGalois k L] [IsGalois k' L]
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1) :
    extRes (galRes k' K L) (baseChangeExt M x)
      = (extRes ((resBaseHom k k' K).comp (galRes k' K L)) x).comp
          (Abelian.Ext.mk₀ (Rep.resMap (galRes k' K L)
            (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom)) (add_zero 1) := by
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor (k := Coeff) (galRes k' K L))
        (Abelian.Ext.mapExactFunctor (Rep.resFunctor (k := Coeff) (resBaseHom k k' K)) x) =
      Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (k := Coeff) ((resBaseHom k k' K).comp (galRes k' K L))) x := by
    simpa only [extRes] using
      (Work.SSGRoute.SylowDesc.extRes_comp_aux (resBaseHom k k' K) (galRes k' K L) x).symm
  simp only [baseChangeExt, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hcomp]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The `Ext`-algebra bridge of the case-(i) transfer.**  Pairing the level-`L` restriction of the
base-changed class with a coefficient map at the `k'`-level is the same as pairing the `k`-level
restriction of `x` with the composite coefficient map
`Rep.resMap (galRes k' K L) (classesK_baseChangeIso k k' K).hom ≫ classIncl k' K L`
(`baseChangeExt_extRes` plus `Abelian.Ext.mk₀_comp_mk₀`; both sides are elements of
`Ext¹_{Gal(L/k')}(Rep.res (galRes k' K L) (Rep.res (resBaseHom k k' K) M), classesK k' L)`, so no
transport is needed). -/
theorem baseChangeExt_lift {k k' K L : Type} [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K]
    [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [Algebra k' L] [IsScalarTower k' K L] [IsScalarTower k k' L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K] [IsGalois k' K]
    [FiniteDimensional k L] [IsGalois k L] [IsGalois k' L]
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1) :
    (extRes (galRes k' K L) (baseChangeExt M x)).comp
        (Abelian.Ext.mk₀ (classIncl k' K L)) (add_zero 1)
      = (extRes ((resBaseHom k k' K).comp (galRes k' K L)) x).comp
          (Abelian.Ext.mk₀ (Rep.resMap (galRes k' K L)
            (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom
            ≫ classIncl k' K L)) (add_zero 1) := by
  rw [baseChangeExt_extRes]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Work.SSGRoute.E6Util.comp_assoc_of_first_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The two composite coefficient modules are equal.**  For `k ⊆ k' ⊆ K ⊆ L` both
`Rep.res (galRes k' K L) (Rep.res (resBaseHom k k' K) (classesK k K))` and
`Rep.res (resBaseHom k k' L) (Rep.res (galRes k K L) (classesK k K))` are `Rep.of` of the action of
`classesK k K` composed with a hom `Gal(L/k') →* Gal(K/k)`, and the two homs are equal by
`SylowIn.resBaseHom_comp_galRes` (`rfl`-level `Rep.res` nesting). -/
theorem baseChangeDomain_eq :
    Rep.res (galRes k' K L) (Rep.res (resBaseHom k k' K) (classesK k K)) =
      Rep.res (resBaseHom k k' L) (Rep.res (galRes k K L) (classesK k K)) := by
  have h : (classesK k K).ρ.comp ((resBaseHom k k' K).comp (galRes k' K L)) =
      (classesK k K).ρ.comp ((galRes k K L).comp (resBaseHom k k' L)) := by
    rw [resBaseHom_comp_galRes]
  show Rep.of ((classesK k K).ρ.comp ((resBaseHom k k' K).comp (galRes k' K L))) =
      Rep.of ((classesK k K).ρ.comp ((galRes k K L).comp (resBaseHom k k' L)))
  rw [h]

/-- **The domain transport `δ` of the case-(i) transfer**: the identity-on-carriers isomorphism
relating the two composite coefficient modules of `baseChangeDomain_eq`.  This is the
`SylowDesc.classesK_baseChangeIso` pattern applied to the domains (whose difference is the
`resBaseHom_comp_galRes` identification of the two homomorphisms `Gal(L/k') →* Gal(K/k)`). -/
noncomputable def baseChangeDomainIso :
    Rep.res (galRes k' K L) (Rep.res (resBaseHom k k' K) (classesK k K)) ≅
      Rep.res (resBaseHom k k' L) (Rep.res (galRes k K L) (classesK k K)) :=
  eqToIso baseChangeDomain_eq

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The two composite coefficient morphisms agree as functions.**  For every element `y` of the
carrier `C_K`,
`(Rep.resMap (galRes k' K L) ιK ≫ classIncl k' K L).hom y =
 (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫ ιg).hom y`
— both are the idèle-class inclusion `C_K → C_L` at the appropriate base field, and those agree by
`SylowIn.classIncl_apply_baseChange`.  The `Rep.resMap`s and the two base-change isomorphisms of `C_L`
are `rfl`-level identities on the carrier.  With `SylowIn.baseChangeDomainIso` this is the function
form of the morphism identity `hαβ` of §16. -/
theorem classIncl_baseChange_composite (y : Additive (NK.GlobalCFT.IdeleClassGroup K)) :
    (Rep.resMap (galRes k' K L)
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom ≫ classIncl k' K L).hom y
      = (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫
          (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom).hom y := by
  have h₁ : (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom = 𝟙 _ := rfl
  have h₂ : (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom = 𝟙 _ := rfl
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Rep.resMap_hom_apply,
    Rep.resMap_hom_apply, h₁, h₂]
  conv_lhs => rw [show y = Additive.ofMul (Additive.toMul y) from rfl]
  conv_rhs => rw [show y = Additive.ofMul (Additive.toMul y) from rfl]
  obtain ⟨q, hq⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective K (Additive.toMul y)
  rw [← hq]
  exact classIncl_apply_baseChange (k := k) (k' := k') (K := K) (L := L) q

theorem baseChangeDomainIso_hom_apply (y : Additive (NK.GlobalCFT.IdeleClassGroup K)) :
    ((baseChangeDomainIso (k := k) (k' := k') (K := K) (L := L)).hom).hom y = y := rfl

theorem baseChangeDomainIso_inv_apply (y : Additive (NK.GlobalCFT.IdeleClassGroup K)) :
    ((baseChangeDomainIso (k := k) (k' := k') (K := K) (L := L)).inv).hom y = y := rfl


set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The transported function identity of the `mk₀`-push.**  Applying `δ`'s transport (which acts as
the identity on the carrier, `baseChangeDomainIso_hom_apply`) reduces the composite coefficient
morphism at the composite level to `SylowIn.classIncl_baseChange_composite`. -/
theorem classIncl_baseChange_composite_delta (y : Additive (NK.GlobalCFT.IdeleClassGroup K)) :
    (Rep.resMap (galRes k' K L)
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom ≫ classIncl k' K L).hom y
      = ((baseChangeDomainIso (k := k) (k' := k') (K := K) (L := L)).hom ≫
        (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫
          (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom)).hom y := by
  conv_lhs => rw [ConcreteCategory.comp_apply]
  conv_rhs => rw [ConcreteCategory.comp_apply]
  rw [baseChangeDomainIso_hom_apply]
  exact classIncl_baseChange_composite (k := k) (k' := k') (K := K) (L := L) y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The `mk₀`-push across `δ`.**  The two composite coefficient morphisms are equal (their
underlying functions agree by `classIncl_baseChange_composite_delta` and `δ` acts as the identity on
the carrier), hence their `Ext⁰`-classes agree: `mk₀ (classIncl k' K L)` may be replaced by
`mk₀ (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫ ιg)`, the coefficient map of the
composite-level pairing — the last step of the case-(i) transfer. -/
theorem mk₀_classIncl_baseChange :
    Abelian.Ext.mk₀ (Rep.resMap (galRes k' K L)
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom ≫ classIncl k' K L)
      = Abelian.Ext.mk₀ ((baseChangeDomainIso (k := k) (k' := k') (K := K) (L := L)).hom ≫
        (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫
          (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom)) := by
  have hαβ : (Rep.resMap (galRes k' K L)
        (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' K).hom ≫ classIncl k' K L)
      = ((baseChangeDomainIso (k := k) (k' := k') (K := K) (L := L)).hom ≫
        (Rep.resMap (resBaseHom k k' L) (classIncl k K L) ≫
          (Work.SSGRoute.SylowDesc.classesK_baseChangeIso k k' L).hom)) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    exact classIncl_baseChange_composite_delta (k := k) (k' := k') (K := K) (L := L) y
  rw [hαβ]

end BaseChangeLevel

end SylowIn


end Work.SSGRoute
