import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.phi1_lambda_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Conjugating a short exact sequence of `Gal(K/k)`-modules by an isomorphism `S.X₁ ≅ 𝔽_p`

The realisation step `Work.SSGRoute.level_family_of_delta` is stated for a short exact sequence
`S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` together with an isomorphism `e : S.X₁ ≅ 𝔽_p` (the trivial
module).  The normalised version of the statement (for which the machinery of
`Submission/Work/SSGRoute/phi1_wcolim.lean` and of the level systems is built) concerns the
*conjugated* sequence `S'` whose first map is `e.inv ≫ S.f`, so that its degree-`1` term is
literally `𝔽_p`.

This file provides:

* `LF.conjS` — the conjugated short complex, and `LF.conjS_shortExact`, its short exactness
  (transported from `S` along the isomorphism `e` of short complexes);
* `LF.conjS_deltaHom` — the identification of the connecting maps: composing the connecting map of
  `S` with the degree-`0` coefficient map `e.hom` is the connecting map of `S'`;
* `LF.hy_conj` — the hypothesis `hy` transfers from `S` to `S'`.
-/

namespace Work.SSGRoute

namespace LF

open SSGRoute.PTExt CategoryTheory

/-! ## A general `Ext`-fact: postcomposition with the class of an isomorphism is injective -/

section General

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{0} C]

/-- **Postcomposition with the class of an isomorphism is injective.**  If `φ : Y ⟶ Z` is an
isomorphism in an abelian category and `x.comp (mk₀ φ) = 0`, then `x = 0` (compose with the class
of `φ⁻¹`). -/
lemma comp_mk₀_of_iso_eq_zero {X Y Z : C} {a : ℕ} (φ : Y ⟶ Z) [IsIso φ]
    (x : Abelian.Ext X Y a) (hx : x.comp (Abelian.Ext.mk₀ φ) (add_zero a) = 0) : x = 0 := by
  calc x = x.comp (Abelian.Ext.mk₀ (𝟙 Y)) (add_zero a) := (Abelian.Ext.comp_mk₀_id x).symm
    _ = x.comp (Abelian.Ext.mk₀ (φ ≫ inv φ)) (add_zero a) := by rw [IsIso.hom_inv_id]
    _ = x.comp ((Abelian.Ext.mk₀ φ).comp (Abelian.Ext.mk₀ (inv φ)) (add_zero 0))
          (add_zero a) := by rw [Abelian.Ext.mk₀_comp_mk₀]
    _ = (x.comp (Abelian.Ext.mk₀ φ) (add_zero a)).comp (Abelian.Ext.mk₀ (inv φ))
          (add_zero a) :=
        (Abelian.Ext.comp_assoc x (Abelian.Ext.mk₀ φ) (Abelian.Ext.mk₀ (inv φ))
          (add_zero a) (add_zero 0) (by norm_num)).symm
    _ = 0 := by rw [hx, Abelian.Ext.zero_comp]

end General

noncomputable section

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- The zero relation of the conjugated sequence. -/
theorem conjZero (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (e.inv ≫ S.f) ≫ S.g = 0 := by
  rw [Category.assoc, S.zero]
  simp

/-- **The conjugated short complex**: same `X₂`, `X₃`, but with `𝔽_p` in degree `1`. -/
noncomputable abbrev conjS (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)) :=
  ShortComplex.mk (e.inv ≫ S.f) S.g (conjZero p S e)

theorem conjS_X₁ (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (conjS p S e).X₁ = Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) := rfl

theorem conjS_X₂ (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (conjS p S e).X₂ = S.X₂ := rfl

theorem conjS_X₃ (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (conjS p S e).X₃ = S.X₃ := rfl

theorem conjS_f (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (conjS p S e).f = e.inv ≫ S.f := rfl

theorem conjS_g (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (conjS p S e).g = S.g := rfl

/-- **Short exactness of the conjugated sequence.** -/
theorem conjS_shortExact (p : ℕ) [Fact p.Prime]
    (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) :
    (conjS p S e).ShortExact := by
  haveI : IsIso e.hom := e.isIso_hom
  refine ShortComplex.shortExact_of_iso (S₁ := S) (S₂ := conjS p S e)
    (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ ?_) hS
  · show e.hom ≫ (e.inv ≫ S.f) = S.f ≫ (Iso.refl S.X₂).hom
    rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · show (Iso.refl S.X₂).hom ≫ S.g = S.g ≫ (Iso.refl S.X₃).hom
    rw [Iso.refl_hom, Category.id_comp, Iso.refl_hom, Category.comp_id]

/-- The morphism of short complexes `S.map F ⟶ S'.map F` given by `e.hom` in degree `1`. -/
noncomputable abbrev conjHom (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (L : IntermediateField K Ω) :
    (S.map (Rep.resFunctor (galRes k K L))) ⟶
      ((conjS p S e).map (Rep.resFunctor (galRes k K L))) :=
  { τ₁ := (Rep.resFunctor (galRes k K L)).map e.hom
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by
      show (Rep.resFunctor (galRes k K L)).map e.hom
            ≫ (Rep.resFunctor (galRes k K L)).map (e.inv ≫ S.f)
          = (Rep.resFunctor (galRes k K L)).map S.f ≫ 𝟙 _
      rw [← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
        Category.comp_id]
    comm₂₃ := by
      show (𝟙 _) ≫ (Rep.resFunctor (galRes k K L)).map S.g
          = (Rep.resFunctor (galRes k K L)).map S.g ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id] }

@[simp] theorem conjHom_τ₁ (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (L : IntermediateField K Ω) :
    (conjHom p S e L).τ₁ = (Rep.resFunctor (galRes k K L)).map e.hom := rfl

@[simp] theorem conjHom_τ₃ (p : ℕ) (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (L : IntermediateField K Ω) :
    (conjHom p S e L).τ₃ = 𝟙 _ := rfl

/-- **The connecting maps of `S` and of the conjugated sequence `S'`.**  Composing the connecting
map of `S` at the level `L` with the degree-`0` coefficient map `e.hom : S.X₁ ⟶ 𝔽_p` gives the
connecting map of `S'` (naturality of `ShortComplex.ShortExact.extClass` under the change of
sub-object). -/
theorem conjS_deltaHom (p : ℕ) [Fact p.Prime]
    (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) S.X₃) 1) :
    (deltaHom (k := k) (K := K) (L := L) S hS h).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2)
      = deltaHom (k := k) (K := K) (L := L) (conjS p S e) (conjS_shortExact p S hS e) h := by
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (hS.map_of_exact (Rep.resFunctor (galRes k K L)))
    ((conjS_shortExact p S hS e).map_of_exact (Rep.resFunctor (galRes k K L)))
    (conjHom p S e L)
  have hnat' : (extRes (galRes k K L) hS.extClass).comp
      (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 1)
      = extRes (galRes k K L) (conjS_shortExact p S hS e).extClass := by
    simp only [extRes]
    rw [Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor (galRes k K L)) hS,
      Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor (galRes k K L))
        (conjS_shortExact p S hS e)]
    exact hnat.trans (Abelian.Ext.mk₀_id_comp _)
  rw [deltaHom_apply, deltaHom_apply]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [hnat']

/-- **The vanishing hypothesis transfers to the conjugated sequence.** -/
theorem hy_conj (p : ℕ) [Fact p.Prime]
    (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    (hy : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (h : extH (Rep.res (galRes k K L) S.X₃) 1),
      deltaHom (k := k) (K := K) (L := L) S hS h = 0 →
        phiAt (k := k) (K := K) (L := L) y h = 0) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) (conjS p S e).X₃) 1),
      deltaHom (k := k) (K := K) (L := L) (conjS p S e) (conjS_shortExact p S hS e) h = 0 →
        phiAt (k := k) (K := K) (L := L) y h = 0 := by
  intro L _ _ _ h hh
  refine hy L h ?_
  have h2 : (deltaHom (k := k) (K := K) (L := L) S hS h).comp
      (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2) = 0 := by
    rw [conjS_deltaHom p S hS e L h]
    exact hh
  haveI : IsIso ((Rep.resFunctor (galRes k K L)).map e.hom) := Functor.map_isIso _ e.hom
  exact comp_mk₀_of_iso_eq_zero ((Rep.resFunctor (galRes k K L)).map e.hom)
    (deltaHom (k := k) (K := K) (L := L) S hS h) h2

end

end LF

end Work.SSGRoute
