import Mathlib
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The invariants and the norm of a restricted idèle-class-group representation

Let `Ω / K` be a finite Galois extension of number fields and let `N ≤ Gal(Ω/K)` be a *normal*
subgroup with fixed field `K' = Ω^N` (so that `N = Gal(Ω/K')`).  The idèle class group `C_Ω` is a
module over `Gal(Ω/K)` and hence, by restriction along `N ↪ Gal(Ω/K)`, a module over `N`; it is
also a module over `Gal(Ω/K')`.

The Galois action on `C_Ω` only depends on the automorphism *as an automorphism of `Ω`*, so the two
actions agree under the canonical identification `N ≅ Gal(Ω/K')`:
for `τ : Ω ≃ₐ[K'] Ω` one has
`(rep K Ω).ρ (AlgEquiv.restrictScalars K τ) = (rep K' Ω).ρ τ`
(lemma `rep_rho_restrictScalars`, proved by `rfl`).  Consequently

* the `N`-invariants of the restricted representation `Rep.res N.subtype (rep K Ω)` and the
  `Gal(Ω/K')`-invariants of `rep K' Ω` are the *same* submodule of `C_Ω` — this is the statement
  that "the invariants of the idèle class group are the idèle class group of the fixed field",
  in the H⁰ degree;
* the norm operators (the sums `∑_g ρ g`) coincide as well, the sums being indexed by the two
  canonically identified finite groups.

## Main result

* `NK.CFTLib.Existence.res_subtype_eq_rep_fixedField`.

## Implementation notes

The invariance statement is reduced with
`NK.HassePrinciple.forall_smul_eq_self_subgroup_iff` (which identifies the elements of `C_Ω`
fixed by `N` with those fixed by `Gal(Ω/K')`) and the definitional unfolding
`(rep K Ω).ρ g x = Additive.ofMul (g • Additive.toMul x)`.
The norm statement is `Fintype.sum_equiv` along the group isomorphism
`IntermediateField.subgroupEquivAlgEquiv N : N ≃* Gal(Ω/Ω^N)`, whose underlying map is the
restriction of scalars `AlgEquiv.restrictScalars K` (`subgroupEquivAlgEquiv_restrictScalars`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField

noncomputable section

namespace NK.CFTLib.Existence

/-! ### Unfolding the action on the idèle class group -/

/-- The representation `IdeleClassGroup.rep F L` acts by the multiplicative action on `C_L`: as a
function, `ρ g x = Additive.ofMul (g • Additive.toMul x)`. -/
lemma rep_rho_apply {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (g : L ≃ₐ[F] L) (x : Additive (NK.GlobalCFT.IdeleClassGroup L)) :
    (NK.GlobalCFT.IdeleClassGroup.rep F L).ρ g x
      = Additive.ofMul (g • Additive.toMul x) := rfl

/-- An element of `C_L` is fixed by `g : Gal(L/F)` for the representation `IdeleClassGroup.rep F L`
if and only if it is fixed by `g` for the underlying multiplicative action. -/
lemma rep_rho_eq_self_iff {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] (g : L ≃ₐ[F] L) (x : Additive (NK.GlobalCFT.IdeleClassGroup L)) :
    (NK.GlobalCFT.IdeleClassGroup.rep F L).ρ g x = x ↔
      g • Additive.toMul x = Additive.toMul x := by
  rw [rep_rho_apply]
  constructor
  · intro h
    have := congrArg Additive.toMul h
    simpa using this
  · intro h
    rw [h, ofMul_toMul]

/-! ### The action depends only on the automorphism of `L` -/

/-- **The action on `C_L` only depends on the automorphism of `L`.**  For an intermediate field
`F ≤ L` and an automorphism `τ` of `L` over `F`, the action of `τ` on `C_L` coincides with the
action of the same automorphism viewed over the base field. -/
lemma rep_rho_restrictScalars {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] (F : IntermediateField K Ω) (τ : Ω ≃ₐ[↥F] Ω) :
    (NK.GlobalCFT.IdeleClassGroup.rep ↥F Ω).ρ τ
      = (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (AlgEquiv.restrictScalars K τ) := by
  ext x; rfl

/-- The canonical isomorphism `N ≃* Gal(L/L^N)` (`IntermediateField.subgroupEquivAlgEquiv`) is, on
the underlying automorphisms, the restriction of scalars `AlgEquiv.restrictScalars`. -/
lemma subgroupEquivAlgEquiv_restrictScalars {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] (H : Subgroup Gal(Ω/K)) (h : H) :
    AlgEquiv.restrictScalars K ((IntermediateField.subgroupEquivAlgEquiv H) h) = h.1 := by
  ext x; rfl

/-! ### The invariants and the norm after restriction -/

theorem res_subtype_eq_rep_fixedField {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (Nsub : Subgroup Gal(Ω/K)) [Nsub.Normal] [Fintype Nsub] :
    (Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.invariants
        = (NK.GlobalCFT.IdeleClassGroup.rep ↥(IntermediateField.fixedField Nsub) Ω).ρ.invariants ∧
    (Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.norm
        = (NK.GlobalCFT.IdeleClassGroup.rep ↥(IntermediateField.fixedField Nsub) Ω).ρ.norm := by
  haveI : FiniteDimensional ↥(IntermediateField.fixedField Nsub) Ω := inferInstance
  haveI : IsGalois ↥(IntermediateField.fixedField Nsub) Ω := inferInstance
  constructor
  · -- the invariants
    ext x
    change (∀ g : ↥Nsub,
        ((Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ g) x = x) ↔
      (∀ τ : Gal(Ω/↥(IntermediateField.fixedField Nsub)),
        ((NK.GlobalCFT.IdeleClassGroup.rep ↥(IntermediateField.fixedField Nsub) Ω).ρ τ) x = x)
    let q : Additive (NK.GlobalCFT.IdeleClassGroup Ω) := x
    have key := NK.HassePrinciple.forall_smul_eq_self_subgroup_iff (K := K) (L := Ω) Nsub
      (Additive.toMul q)
    constructor
    · intro h τ
      have h' : ∀ σ : Nsub, σ.1 • Additive.toMul q = Additive.toMul q :=
        fun σ => (rep_rho_eq_self_iff (F := K) σ.1 q).mp (h σ)
      exact (rep_rho_eq_self_iff (F := ↥(IntermediateField.fixedField Nsub)) τ q).mpr (key.mp h' τ)
    · intro h σ
      have h' : ∀ τ : Gal(Ω/↥(IntermediateField.fixedField Nsub)),
          τ • Additive.toMul q = Additive.toMul q :=
        fun τ => (rep_rho_eq_self_iff (F := ↥(IntermediateField.fixedField Nsub)) τ q).mp (h τ)
      exact (rep_rho_eq_self_iff (F := K) σ.1 q).mpr (key.mpr h' σ)
  · -- the norm
    simp only [Representation.norm]
    refine Fintype.sum_equiv (IntermediateField.subgroupEquivAlgEquiv Nsub).toEquiv _ _ ?_
    intro h
    rw [show (Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ h
        = (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ h.1 from rfl]
    rw [← subgroupEquivAlgEquiv_restrictScalars (K := K) (Ω := Ω) Nsub h]
    exact (rep_rho_restrictScalars (K := K) (Ω := Ω)
      (IntermediateField.fixedField Nsub) ((IntermediateField.subgroupEquivAlgEquiv Nsub) h)).symm

end NK.CFTLib.Existence
