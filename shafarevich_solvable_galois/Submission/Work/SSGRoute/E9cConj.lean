import Mathlib
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.comp_extCor
import Submission.Work.SSGRoute.local_duality_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conjugation twist of a `G`-representation, and its effect on `Ext`

For a group `G`, an element `σ : G` and a `G`-representation `X`, the *conjugation twist*
`X^σ := Rep.res (MulAut.conj σ) X` is `X` with the conjugated action `g • x = σ g σ⁻¹ • x`.
The map `x ↦ σ • x` is an isomorphism `X ⟶ X^σ`, natural in `X`; its inverse is `x ↦ σ⁻¹ • x`.

The main result of this file is `Work.SSGRoute.extRes_conjTwist`: for `x ∈ Extⁿ_G(X, Y)` the class
obtained by applying the exact functor `Rep.res (MulAut.conj σ)` is the transport of `x` along these
natural isomorphisms of the two variables.  It is a corollary of the general naturality lemma
`Work.SSGRoute.ext_mapExactFunctor_naturality_unit_aux` (from `comp_extCor.lean`).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

section Conj

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

variable {G : Type} [Group G]

/-- The conjugation twist of a representation by an element `σ`, as a natural transformation
`𝟭 ⟹ Rep.res (MulAut.conj σ)`. -/
noncomputable def conjTwist (σ : G) :
    NatTrans (𝟭 (Rep.{0, 0, 0} Coeff G))
      (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)) where
  app X := Rep.ofHom ⟨X.ρ σ, fun g => by
    apply LinearMap.ext
    intro x
    show X.ρ σ (X.ρ g x) = X.ρ ((MulAut.conj σ) g) (X.ρ σ x)
    have h1 : (X.ρ σ) ((X.ρ g) x) = (X.ρ (σ * g)) x := by rw [map_mul]; rfl
    have h2 : (X.ρ ((MulAut.conj σ) g)) ((X.ρ σ) x) = (X.ρ ((MulAut.conj σ) g * σ)) x := by
      rw [map_mul]; rfl
    have h3 : (MulAut.conj σ) g * σ = σ * g := by rw [MulAut.conj_apply]; group
    rw [h1, h2, h3]⟩
  naturality := fun {X Y} f => by
    ext x
    show Y.ρ σ (f.hom x) = f.hom (X.ρ σ x)
    exact (Rep.hom_comm_apply f σ x).symm

/-- The inverse of the conjugation twist: a natural transformation
`Rep.res (MulAut.conj σ) ⟹ 𝟭`. -/
noncomputable def conjTwistInv (σ : G) :
    NatTrans (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom))
      (𝟭 (Rep.{0, 0, 0} Coeff G)) where
  app X := Rep.ofHom ⟨X.ρ σ⁻¹, fun g => by
    apply LinearMap.ext
    intro x
    show X.ρ σ⁻¹ (X.ρ ((MulAut.conj σ) g) x) = X.ρ g (X.ρ σ⁻¹ x)
    have h1 : (X.ρ σ⁻¹) ((X.ρ ((MulAut.conj σ) g)) x) =
        (X.ρ (σ⁻¹ * (MulAut.conj σ) g)) x := by rw [map_mul]; rfl
    have h2 : (X.ρ g) ((X.ρ σ⁻¹) x) = (X.ρ (g * σ⁻¹)) x := by rw [map_mul]; rfl
    have h3 : σ⁻¹ * (MulAut.conj σ) g = g * σ⁻¹ := by rw [MulAut.conj_apply]; group
    rw [h1, h2, h3]⟩
  naturality := fun {X Y} f => by
    ext x
    show Y.ρ σ⁻¹ (f.hom x) = f.hom (X.ρ σ⁻¹ x)
    exact (Rep.hom_comm_apply f σ⁻¹ x).symm

@[simp]
theorem conjTwist_apply (σ : G) (X : Rep.{0, 0, 0} Coeff G) (x : X.V) :
    (conjTwist σ).app X x = X.ρ σ x := rfl

@[simp]
theorem conjTwistInv_apply (σ : G) (X : Rep.{0, 0, 0} Coeff G) (x : X.V) :
    (conjTwistInv σ).app X x = X.ρ σ⁻¹ x := rfl

theorem conjTwist_comp_inv (σ : G) (X : Rep.{0, 0, 0} Coeff G) :
    (conjTwist σ).app X ≫ (conjTwistInv σ).app X = 𝟙 X := by
  ext x
  show X.ρ σ⁻¹ (X.ρ σ x) = x
  have h1 : (X.ρ σ⁻¹) ((X.ρ σ) x) = (X.ρ (σ⁻¹ * σ)) x := by rw [map_mul]; rfl
  rw [h1, inv_mul_cancel, map_one]
  rfl

theorem conjTwist_inv_comp (σ : G) (X : Rep.{0, 0, 0} Coeff G) :
    (conjTwistInv σ).app X ≫ (conjTwist σ).app X
      = 𝟙 ((Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)).obj X) := by
  ext x
  show X.ρ σ (X.ρ σ⁻¹ x) = x
  have h1 : (X.ρ σ) ((X.ρ σ⁻¹) x) = (X.ρ (σ * σ⁻¹)) x := by rw [map_mul]; rfl
  rw [h1, mul_inv_cancel, map_one]
  rfl

/-- **The conjugation twist on `Ext`.**  For a class `x ∈ Extⁿ_G(X, Y)`, the class obtained by
applying the exact functor `Rep.res (MulAut.conj σ)` is the transport of `x` along the natural
isomorphisms `conjTwist σ` of the two variables. -/
theorem extRes_conjTwist {σ : G} {n : ℕ} {X Y : Rep.{0, 0, 0} Coeff G}
    (x : Abelian.Ext X Y n) :
    extRes ((MulAut.conj σ).toMonoidHom) x
      = (Abelian.Ext.mk₀ ((conjTwistInv σ).app X)).comp
          (x.comp (Abelian.Ext.mk₀ ((conjTwist σ).app Y)) (add_zero n)) (zero_add n) := by
  have h := ext_mapExactFunctor_naturality_unit_aux (C := Rep.{0, 0, 0} Coeff G)
    (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)) (conjTwist σ) n X Y x
  have hid := conjTwist_inv_comp σ X
  have hassoc : (Abelian.Ext.mk₀ ((conjTwistInv σ).app X)).comp
        ((Abelian.Ext.mk₀ ((conjTwist σ).app X)).comp
          (Abelian.Ext.mapExactFunctor
            (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)) x) (zero_add n))
        (zero_add n)
      = ((Abelian.Ext.mk₀ ((conjTwistInv σ).app X)).comp
          (Abelian.Ext.mk₀ ((conjTwist σ).app X)) (zero_add 0)).comp
          (Abelian.Ext.mapExactFunctor
            (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)) x) (zero_add n) :=
    (Abelian.Ext.comp_assoc
      (X := (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)).obj X)
      (Y := X)
      (Z := (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)).obj X)
      (T := (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)).obj Y)
      (a₁ := 0) (a₂ := 0) (a₃ := n) (a₁₂ := 0) (a₂₃ := n) (a := n)
      (Abelian.Ext.mk₀ ((conjTwistInv σ).app X))
      (Abelian.Ext.mk₀ ((conjTwist σ).app X))
      (Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (k := Coeff) ((MulAut.conj σ).toMonoidHom)) x)
      (zero_add 0) (zero_add n) (by omega)).symm
  rw [extRes]
  refine Eq.symm ?_
  rw [h, hassoc, Abelian.Ext.mk₀_comp_mk₀, hid]
  exact Abelian.Ext.mk₀_id_comp _

end Conj

/-! ## Conjugation of decomposition groups, and the pinned localisation map -/

section Stab

open NK.GlobalCFT (Place Idele)

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- Conjugation by `σ` as a homomorphism `D_v →* D_{σ v}` between decomposition groups. -/
noncomputable def conjStabHom (σ : K ≃ₐ[k] K) (v : Place K) :
    decompK (k := k) v →* decompK (k := k) (σ • v) where
  toFun h := ⟨σ * h.1 * σ⁻¹, by
    rw [MulAction.mem_stabilizer_iff]
    have h1 : σ⁻¹ • (σ • v) = v := by rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [mul_smul, mul_smul, h1, MulAction.mem_stabilizer_iff.mp h.2]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show σ * (↑a * ↑b) * σ⁻¹ = (σ * ↑a * σ⁻¹) * (σ * ↑b * σ⁻¹)
    group)

/-- Conjugation by `σ⁻¹` as a homomorphism `D_{σ v} →* D_v`. -/
noncomputable def conjStabHomInv (σ : K ≃ₐ[k] K) (v : Place K) :
    decompK (k := k) (σ • v) →* decompK (k := k) v where
  toFun h := ⟨σ⁻¹ * h.1 * σ, by
    rw [MulAction.mem_stabilizer_iff]
    rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp h.2, ← mul_smul, inv_mul_cancel,
      one_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show σ⁻¹ * (↑a * ↑b) * σ = (σ⁻¹ * ↑a * σ) * (σ⁻¹ * ↑b * σ)
    group)

/-- **The decomposition groups of conjugate places are conjugate**: conjugation by `σ` is an
isomorphism of groups `D_v ≃* D_{σ v}`. -/
noncomputable def conjStabEquiv (σ : K ≃ₐ[k] K) (v : Place K) :
    decompK (k := k) v ≃* decompK (k := k) (σ • v) where
  toFun := conjStabHom k K σ v
  invFun := conjStabHomInv k K σ v
  left_inv h := Subtype.ext (by
    show σ⁻¹ * (σ * ↑h * σ⁻¹) * σ = ↑h
    group)
  right_inv h := Subtype.ext (by
    show σ * (σ⁻¹ * ↑h * σ) * σ⁻¹ = ↑h
    group)
  map_mul' a b := map_mul (conjStabHom k K σ v) a b

end Stab
