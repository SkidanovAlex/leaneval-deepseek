/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# §6 of arXiv:2601.01251 at an arbitrary universe

Universe-polymorphic copies of the §6 chain of `Submission/Work/UchidaKummer/Uchida/`:

* `NK.UniverseWeakNU.nonempty_ringEquiv_of_uchidaModuleData_and_perlisU` — the common-field
  form (copy of `NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis`,
  `Uchida/Assembly.lean`): for `L/ℚ` a finite Galois extension in `Type u` and `H₁, H₂ ≤ Gal(L/ℚ)`,
  Uchida's module data (at `Type u`) and the Perlis/Gassmann input (at `Type u`) produce
  `L^{H₁} ≃+* L^{H₂}`;
* `NK.UniverseWeakNU.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_absU` — the abstract
  form (copy of `NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs`,
  `Uchida/Abstract.lean`): two number fields in `Type u` with isomorphic absolute Galois groups and
  `μ_ℓ ⊆ K_i` are isomorphic.

## The one place where the universe matters

The original `Uchida/Abstract.lean` embeds the two number fields into `AlgebraicClosure ℚ`, which
is a `Type 0` field (`AlgebraicClosure : (k : Type u) → Type u` with `ℚ : Type 0`); the common
finite Galois extension it produces is therefore `Type 0`, and the module data would have to be
evaluated at a `Type 0` base field.  Here the ambient field is

`Ω = AlgebraicClosure (ULift.{u,0} ℚ)`,

which is a field in `Type u` (the `ULift` of `ℚ` is a `Type u` field, by `ULift.field`, and
Mathlib's `AlgebraicClosure` keeps the universe of its base).  It carries

* `IsAlgClosed Ω`, `Algebra (ULift ℚ) Ω`, `Algebra ℚ Ω` (the composite `ℚ → ULift ℚ → Ω`),
  `Algebra.IsAlgebraic (ULift ℚ) Ω` (`AlgebraicClosure.isAlgebraic`) and hence
  `Algebra.IsAlgebraic ℚ Ω` (`Algebra.IsAlgebraic.trans`);

so `IsAlgClosed.lift` embeds `K_i` into `Ω` and
`NK.UchidaKummer.Uchida.exists_isGalois_sup_le` (which is universe-polymorphic) produces a
common finite Galois extension of `ℚ` *in `Type u`*, as the common-field theorem requires.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UniverseWeakNU.IsomorphicAbsGaloisU
import Submission.NK.UchidaKummer.Uchida.ModuleData
import Submission.NK.UchidaKummer.Gassmann.FieldBridge
import Submission.NK.UchidaKummer.Uchida.exists_isGalois_sup_le
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField

namespace NK.UniverseWeakNU

open IntermediateField

noncomputable section

universe u

/-- **§6's weak theorem, from the module data and the Perlis/Gassmann input**, at an arbitrary
universe.  Copy of `NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis` with the
two `Prop`s replaced by their `Type u` versions and `L : Type` by `L : Type u`. -/
theorem nonempty_ringEquiv_of_uchidaModuleData_and_perlisU {ℓ : ℕ}
    (hU : IsUchidaModuleDataU.{u} ℓ) (hP : PerlisGassmannInputU.{u}) [Fact ℓ.Prime]
    {L : Type u} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (hμ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ)
    (H₁ H₂ : Subgroup Gal(L/ℚ))
    (hμ₁ : ∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ)
    (hμ₂ : ∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ)
    (hiso : HasIsomorphicAbsGaloisU ↥(IntermediateField.fixedField H₁)
      ↥(IntermediateField.fixedField H₂)) :
    Nonempty (↥(IntermediateField.fixedField H₁) ≃+* ↥(IntermediateField.fixedField H₂)) := by
  classical
  haveI : Fintype Gal(L/ℚ) := AlgEquiv.fintype ℚ L
  letI : Fintype ↥H₁ := (Set.toFinite (H₁ : Set Gal(L/ℚ))).fintype
  letI : Fintype ↥H₂ := (Set.toFinite (H₂ : Set Gal(L/ℚ))).fintype
  set n : ℕ := Fintype.card ↥H₁ + Fintype.card ↥H₂ with hn
  obtain ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂,
    hLM₁, hLM₂, harith, hspec₁, hspec₂⟩ := hU n L hμ H₁ H₂ hμ₁ hμ₂ hiso
  letI : Field N := hfN
  letI : NumberField N := hnfN
  letI : Algebra ℚ N := halgN
  letI : Algebra L N := halgLN
  letI : IsScalarTower ℚ L N := htower
  letI : IsGalois ℚ N := hgalN
  letI : FiniteDimensional L N := hfinLN
  haveI : Normal ℚ L := inferInstance
  -- The restriction `Gal(N/ℚ) →* Gal(L/ℚ)` and its kernel `Gal(N/L)`.
  let ρ : Gal(N/ℚ) →* Gal(L/ℚ) := AlgEquiv.restrictNormalHom (F := ℚ) L
  have hJ₁ : M₁.fixingSubgroup ≤ ρ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    ext y
    show (AlgEquiv.restrictNormalHom (F := ℚ) L) σ y = y
    have h1 : σ (algebraMap L N y) = algebraMap L N y :=
      (IntermediateField.mem_fixingSubgroup_iff M₁ σ).mp hσ _ (hLM₁ y)
    have h2 : algebraMap L N (((AlgEquiv.restrictNormalHom (F := ℚ) L) σ) y)
        = σ (algebraMap L N y) :=
      AlgEquiv.restrictNormal_commutes (F := ℚ) (E := L) (K₁ := N) (K₂ := N) σ y
    rw [h1] at h2
    exact (algebraMap L N).injective h2
  have hJ₂ : M₂.fixingSubgroup ≤ ρ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    ext y
    show (AlgEquiv.restrictNormalHom (F := ℚ) L) σ y = y
    have h1 : σ (algebraMap L N y) = algebraMap L N y :=
      (IntermediateField.mem_fixingSubgroup_iff M₂ σ).mp hσ _ (hLM₂ y)
    have h2 : algebraMap L N (((AlgEquiv.restrictNormalHom (F := ℚ) L) σ) y)
        = σ (algebraMap L N y) :=
      AlgEquiv.restrictNormal_commutes (F := ℚ) (E := L) (K₁ := N) (K₂ := N) σ y
    rw [h1] at h2
    exact (algebraMap L N).injective h2
  obtain ⟨hconj₁, hconj₂⟩ := hP N M₁ M₂ harith
  -- The transport, in both directions.
  have hG₁ : NK.UchidaKummer.IsGassmannEquivalentOf (ZMod ℓ) (Fin n) H₁ H₂ :=
    NK.UchidaKummer.isGassmannEquivalentOf_of_module_data ρ H₁ H₂ e (fun γ x => he γ x)
      M₁.fixingSubgroup M₂.fixingSubgroup hJ₁ hJ₂ hspec₁ hspec₂ hconj₁
  have hG₂ : NK.UchidaKummer.IsGassmannEquivalentOf (ZMod ℓ) (Fin n) H₂ H₁ :=
    NK.UchidaKummer.isGassmannEquivalentOf_of_module_data ρ H₂ H₁ e (fun γ x => he γ x)
      M₂.fixingSubgroup M₁.fixingSubgroup hJ₂ hJ₁ hspec₂ hspec₁ hconj₂
  -- Uchida's λ-argument in both directions.
  have hinj₁ : ↥H₁ ↪ Fin n :=
    (Fintype.equivFin ↥H₁).toEmbedding.trans (Fin.castLEEmb (by rw [hn]; exact Nat.le_add_right _ _))
  have hinj₂ : ↥H₂ ↪ Fin n :=
    (Fintype.equivFin ↥H₂).toEmbedding.trans (Fin.castLEEmb (by rw [hn]; exact Nat.le_add_left _ _))
  obtain ⟨g, hg⟩ := NK.UchidaKummer.conj_le_of_gassmannOf (ℓ := ℓ) hinj₁ hG₁
  obtain ⟨k, hk⟩ := NK.UchidaKummer.conj_le_of_gassmannOf (ℓ := ℓ) hinj₂ hG₂
  -- Hence the subgroups are conjugate.
  have hcard : Nat.card ↥H₂ ≤ Nat.card ↥H₁ := NK.UchidaKummer.card_le_of_map_conj_le H₁ H₂ hk
  have hcard' : Nat.card ↥H₂ ≤ Nat.card ↥(H₁.map (MulAut.conj g : Gal(L/ℚ) →* Gal(L/ℚ))) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g : Gal(L/ℚ) →* Gal(L/ℚ)))
      (MulAut.conj g).injective]
    exact hcard
  have heq : H₁.map (MulAut.conj g : Gal(L/ℚ) →* Gal(L/ℚ)) = H₂ :=
    Subgroup.eq_of_le_of_card_ge hg hcard'
  -- And conjugate subgroups have isomorphic fixed fields.
  have hfix : (IntermediateField.fixedField H₁).fixingSubgroup.map
      (MulAut.conj g : Gal(L/ℚ) →* Gal(L/ℚ)) = (IntermediateField.fixedField H₂).fixingSubgroup := by
    rwa [IntermediateField.fixingSubgroup_fixedField, IntermediateField.fixingSubgroup_fixedField]
  exact NK.UchidaKummer.nonempty_ringEquiv_of_fixingSubgroup_map_conj _ _ hfix

/-- **§6 of arXiv:2601.01251, without a chosen common field**, at an arbitrary universe.  Copy of
`NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs`; the ambient algebraically
closed field is `AlgebraicClosure (ULift.{u,0} ℚ)`, of universe `u`, so that the common finite
Galois extension it produces is the `Type u` field the polymorphic module data expects. -/
theorem nonempty_ringEquiv_of_uchidaModuleData_and_perlis_absU {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : IsUchidaModuleDataU.{u} ℓ) (hP : PerlisGassmannInputU.{u})
    (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hiso : HasIsomorphicAbsGaloisU K₁ K₂) :
    Nonempty (K₁ ≃+* K₂) := by
  classical
  let Ω := AlgebraicClosure (ULift.{u,0} ℚ)
  haveI : IsAlgClosed Ω := inferInstance
  haveI : Algebra.IsAlgebraic ℚ Ω :=
    Algebra.IsAlgebraic.trans ℚ (ULift.{u,0} ℚ) Ω
  let i : K₁ →ₐ[ℚ] Ω := IsAlgClosed.lift
  let j : K₂ →ₐ[ℚ] Ω := IsAlgClosed.lift
  haveI hi : FiniteDimensional ℚ ↥(i.fieldRange) := i.toLinearMap.finiteDimensional_range
  haveI hj : FiniteDimensional ℚ ↥(j.fieldRange) := j.toLinearMap.finiteDimensional_range
  obtain ⟨N, hN₁, hN₂, hfinN, hgalN⟩ :=
    NK.UchidaKummer.Uchida.exists_isGalois_sup_le i.fieldRange j.fieldRange
  haveI : FiniteDimensional ℚ ↥N := hfinN
  haveI : IsGalois ℚ ↥N := hgalN
  haveI : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ℚ) N
  let iN : K₁ →ₐ[ℚ] ↥N :=
    i.codRestrict N.toSubalgebra (fun x => hN₁ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let jN : K₂ →ₐ[ℚ] ↥N :=
    j.codRestrict N.toSubalgebra (fun x => hN₂ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let H₁ : Subgroup Gal(↥N/ℚ) := iN.fieldRange.fixingSubgroup
  let H₂ : Subgroup Gal(↥N/ℚ) := jN.fieldRange.fixingSubgroup
  -- The isomorphisms `K_i ≃+* ↥(fixedField H_i)`.
  have hiso₁ : Nonempty (K₁ ≃+* ↥(IntermediateField.fixedField H₁)) :=
    ⟨(AlgEquiv.ofInjective iN iN.injective).toRingEquiv.trans
      ((IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup iN.fieldRange)).symm.toRingEquiv)⟩
  have hiso₂ : Nonempty (K₂ ≃+* ↥(IntermediateField.fixedField H₂)) :=
    ⟨(AlgEquiv.ofInjective jN jN.injective).toRingEquiv.trans
      ((IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup jN.fieldRange)).symm.toRingEquiv)⟩
  obtain ⟨e₁⟩ := hiso₁
  obtain ⟨e₂⟩ := hiso₂
  have hμH₁ : ∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ₁
    exact ⟨e₁ ζ, hζ.map_of_injective e₁.injective⟩
  have hμH₂ : ∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ₂
    exact ⟨e₂ ζ, hζ.map_of_injective e₂.injective⟩
  obtain ⟨ζ, hζ⟩ := hμ₁
  obtain ⟨e⟩ := nonempty_ringEquiv_of_uchidaModuleData_and_perlisU hU hP (L := ↥N)
    ⟨iN ζ, hζ.map_of_injective iN.injective⟩ H₁ H₂ hμH₁ hμH₂
    (hasIsomorphicAbsGaloisU_congr e₁ e₂ hiso)
  exact ⟨e₁.trans (e.trans e₂.symm)⟩

end

end NK.UniverseWeakNU
