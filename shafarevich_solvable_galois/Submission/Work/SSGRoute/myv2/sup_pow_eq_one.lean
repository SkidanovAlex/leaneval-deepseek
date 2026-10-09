import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois group of a compositum of extensions of exponent dividing `p`

If `E₁/↥K` and `E₂/↥K` are finite Galois extensions whose automorphism groups have exponent
dividing `p` (equivalently, every automorphism is a `p`-torsion element), then the same holds for
the compositum `E₁ ⊔ E₂`.

The proof restricts an automorphism `σ` of `L = E₁ ⊔ E₂` to `E₁` and to `E₂` (possible because both
are normal over `↥K`).  Since `σ ↦ (σ|E₁, σ|E₂)` is injective (`E₁` and `E₂` generate `L`), and
`σ^p` restricts to `(σ|E₁)^p` and `(σ|E₂)^p`, both of which are trivial, `σ^p` itself is trivial.
The injectivity is packaged as: `σ^p` lies in the fixing subgroup of both `E₁` and `E₂`, hence in
the fixing subgroup of `E₁ ⊔ E₂`, which is trivial because `E₁ ⊔ E₂` is the whole field.
-/

namespace Work.SSGRoute.myv2

theorem sup_pow_eq_one {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (E₁ E₂ : IntermediateField ↥K Ω)
    [FiniteDimensional ↥K E₁] [IsGalois ↥K E₁]
    [FiniteDimensional ↥K E₂] [IsGalois ↥K E₂] (p : ℕ)
    (h₁ : ∀ σ : (↥E₁ ≃ₐ[↥K] ↥E₁), σ ^ p = 1)
    (h₂ : ∀ σ : (↥E₂ ≃ₐ[↥K] ↥E₂), σ ^ p = 1) :
    ∀ σ : (↥(E₁ ⊔ E₂) ≃ₐ[↥K] ↥(E₁ ⊔ E₂)), σ ^ p = 1 := by
  set_option linter.style.haveILetI false in
  intro σ
  -- `E₁` and `E₂` as subfields of the compositum `E₁ ⊔ E₂`.
  have h₁le : E₁ ≤ E₁ ⊔ E₂ := le_sup_left
  have h₂le : E₂ ≤ E₁ ⊔ E₂ := le_sup_right
  -- View `E₁` and `E₂` as scalars of the compositum so that restriction of automorphisms
  -- (`AlgEquiv.restrictNormal`) can be applied to them.
  letI : Algebra ↥E₁ ↥(E₁ ⊔ E₂) :=
    (IntermediateField.inclusion h₁le).toRingHom.toAlgebra
  letI : Algebra ↥E₂ ↥(E₁ ⊔ E₂) :=
    (IntermediateField.inclusion h₂le).toRingHom.toAlgebra
  haveI : IsScalarTower ↥K ↥E₁ ↥(E₁ ⊔ E₂) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥K ↥E₂ ↥(E₁ ⊔ E₂) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `σ ^ p` restricts trivially to `E₁` (resp. `E₂`), because the restriction is
  -- `(σ|E₁)^p` and `Gal(E₁/↥K)` has exponent dividing `p`.
  have hfix₁ : ∀ y : ↥E₁,
      (σ ^ p) (algebraMap ↥E₁ ↥(E₁ ⊔ E₂) y) = algebraMap ↥E₁ ↥(E₁ ⊔ E₂) y := by
    intro y
    have hres : (σ ^ p).restrictNormal ↥E₁ = 1 := by
      rw [show (σ ^ p).restrictNormal ↥E₁ =
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥(E₁ ⊔ E₂)) ↥E₁) (σ ^ p) from rfl,
        map_pow]
      exact h₁ _
    have h := AlgEquiv.restrictNormal_commutes (χ := σ ^ p) (E := ↥E₁) y
    rw [hres, AlgEquiv.one_apply] at h
    exact h.symm
  have hfix₂ : ∀ y : ↥E₂,
      (σ ^ p) (algebraMap ↥E₂ ↥(E₁ ⊔ E₂) y) = algebraMap ↥E₂ ↥(E₁ ⊔ E₂) y := by
    intro y
    have hres : (σ ^ p).restrictNormal ↥E₂ = 1 := by
      rw [show (σ ^ p).restrictNormal ↥E₂ =
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥(E₁ ⊔ E₂)) ↥E₂) (σ ^ p) from rfl,
        map_pow]
      exact h₂ _
    have h := AlgEquiv.restrictNormal_commutes (χ := σ ^ p) (E := ↥E₂) y
    rw [hres, AlgEquiv.one_apply] at h
    exact h.symm
  -- Translating to membership in the fixing subgroups of `E₁`, `E₂` inside `E₁ ⊔ E₂`.
  have hmem₁ : σ ^ p ∈ (E₁.restrict h₁le).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_restrict] at hx
    have h := hfix₁ ⟨x.1, hx⟩
    have hxeq : algebraMap ↥E₁ ↥(E₁ ⊔ E₂) (⟨x.1, hx⟩ : ↥E₁) = x := Subtype.ext rfl
    rwa [hxeq] at h
  have hmem₂ : σ ^ p ∈ (E₂.restrict h₂le).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_restrict] at hx
    have h := hfix₂ ⟨x.1, hx⟩
    have hxeq : algebraMap ↥E₂ ↥(E₁ ⊔ E₂) (⟨x.1, hx⟩ : ↥E₂) = x := Subtype.ext rfl
    rwa [hxeq] at h
  -- The two restrictions generate the compositum, so no nontrivial automorphism fixes both.
  have hsup : E₁.restrict h₁le ⊔ E₂.restrict h₂le = ⊤ := by
    refine (IntermediateField.lift_inj (F := E₁ ⊔ E₂)
      (E₁.restrict h₁le ⊔ E₂.restrict h₂le) ⊤).mp ?_
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  have hbot : σ ^ p ∈ (⊥ : Subgroup (↥(E₁ ⊔ E₂) ≃ₐ[↥K] ↥(E₁ ⊔ E₂))) := by
    have hmem : σ ^ p ∈ (E₁.restrict h₁le ⊔ E₂.restrict h₂le).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hmem₁, hmem₂⟩
    rwa [hsup, IntermediateField.fixingSubgroup_top] at hmem
  exact Subgroup.mem_bot.mp hbot

end Work.SSGRoute.myv2
