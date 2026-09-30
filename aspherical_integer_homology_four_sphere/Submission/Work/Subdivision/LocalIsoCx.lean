/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.LocalIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The local complexes of locally isomorphic cells

An order isomorphism `φ : Iic e ≃o Iic f` of the face lattices of two cells
induces an isomorphism of the local complexes `locCx P e ≅ locCx P f`: the vertexwise
map `starLM φ` preserves `leSub` and `ltSub` and commutes with the differential, so
it descends to the local modules `locMod e k ⧸ ltSub ↦ locMod f k` and is inverted by
`starLM φ.symm`.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The induced map on the local modules -/

/-- The restriction of `starLM` to the chains supported below `e`. -/
noncomputable def starLMLeSub {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    ↥(leSub P e k) →ₗ[ℤ] ↥(leSub P f k) where
  toFun x := ⟨starLM P φ k (x : chainMod P.Cell k), starLM_mem_leSub P φ k x.2⟩
  map_add' x y := Subtype.ext (map_add (starLM P φ k) (x : chainMod P.Cell k) y)
  map_smul' a x := Subtype.ext (map_smul (starLM P φ k) a (x : chainMod P.Cell k))

@[simp] theorem starLMLeSub_coe {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ)
    (x : ↥(leSub P e k)) :
    ((starLMLeSub P φ k x : ↥(leSub P f k)) : chainMod P.Cell k) =
      starLM P φ k (x : chainMod P.Cell k) := rfl

/-- The induced map on the local modules `leSub e k ⧸ ltSub e k → leSub f k ⧸ ltSub f k`. -/
noncomputable def locModLM {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    locMod P e k →ₗ[ℤ] locMod P f k :=
  Submodule.mapQ (locRel P e k) (locRel P f k) (starLMLeSub P φ k) fun x hx => by
    refine Submodule.mem_comap.mpr ?_
    show ((starLMLeSub P φ k x : ↥(leSub P f k)) : chainMod P.Cell k) ∈ ltSub P f k
    rw [starLMLeSub_coe]
    exact starLM_mem_ltSub P φ k (Submodule.mem_comap.mp hx)

theorem locModLM_mk {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ)
    (y : ↥(leSub P e k)) :
    locModLM P φ k (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (starLMLeSub P φ k y) :=
  Submodule.mapQ_apply _ _ _ y

/-- The induced map on the local differentials. -/
theorem locModLM_comm {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    (locModLM P φ k).comp (locD P e k) = (locD P f k).comp (locModLM P φ (k + 1)) := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [locD_mk P e k, locModLM_mk, locModLM_mk, locD_mk P f k]
      congr 1
      apply Subtype.ext
      simp only [coe_leSubD_apply, starLMLeSub_coe]
      exact starLM_D P φ k y.2

/-- `locModLM` is inverted by the map of the inverse order isomorphism. -/
theorem locModLM_symm {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) (x : locMod P e k) :
    locModLM P φ.symm k (locModLM P φ k x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
      rw [locModLM_mk, locModLM_mk]
      congr 1
      apply Subtype.ext
      rw [starLMLeSub_coe, starLMLeSub_coe]
      exact starLM_symm_apply P φ k y.2

/-- **The local complexes of two cells with isomorphic face lattices are
isomorphic.** -/
noncomputable def locCxIso {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) :
    locCx P e ≅ locCx P f :=
  Iso.mk
    (ChainComplex.ofHom (fun k => ModuleCat.ofHom (locModLM P φ k))
      (fun k => by
        rw [locCx_d, locCx_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
        exact congrArg ModuleCat.ofHom (locModLM_comm P φ k).symm))
    (ChainComplex.ofHom (fun k => ModuleCat.ofHom (locModLM P φ.symm k))
      (fun k => by
        rw [locCx_d, locCx_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
        exact congrArg ModuleCat.ofHom (locModLM_comm P φ.symm k).symm))
    (by
      apply HomologicalComplex.hom_ext
      intro k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
      show locModLM P φ.symm k (locModLM P φ k x) = x
      exact locModLM_symm P φ k x)
    (by
      apply HomologicalComplex.hom_ext
      intro k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
      show locModLM P φ k (locModLM P φ.symm k x) = x
      exact locModLM_symm P φ.symm k x)

@[simp] theorem locCxIso_hom_f {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    (locCxIso P φ).hom.f k = ModuleCat.ofHom (locModLM P φ k) := rfl

@[simp] theorem locCxIso_inv_f {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    (locCxIso P φ).inv.f k = ModuleCat.ofHom (locModLM P φ.symm k) := rfl

end PolyCW

end

end Work.Subdivision
