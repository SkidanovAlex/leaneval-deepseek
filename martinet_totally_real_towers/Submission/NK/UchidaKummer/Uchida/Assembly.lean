/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# §6: the weak Neukirch–Uchida theorem from the module data and the Perlis/Gassmann input

Reference: arXiv:2601.01251, §6, proof of `thm:uchida isomorphism`.

Combining

* `NK.UchidaKummer.IsUchidaModuleData` — §6's embedding problem in module form together with the
  arithmetic equivalence produced by `cor:arith equiv`;
* `NK.UchidaKummer.PerlisGassmannInput` — Perlis/Gassmann: arithmetically equivalent number
  fields have conjugate-into fixing subgroups in their common Galois closure;

with the purely group-theoretic transport (`NK.UchidaKummer.isGassmannEquivalentOf_of_module_data`)
and Uchida's λ-argument (`NK.UchidaKummer.conj_le_of_gassmannOf`), one obtains: the base fields
`K_i = L^{H_i}` are isomorphic.
-/

import Submission.NK.UchidaKummer.Uchida.ModuleData
import Submission.NK.UchidaKummer.Gassmann.FieldBridge

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

open IntermediateField

variable {ℓ : ℕ}

/-- **§6's weak theorem, from the module data and the Perlis/Gassmann input.**

`L/ℚ` is a finite Galois extension containing `μ_ℓ`, `H₁`, `H₂ ≤ Gal(L/ℚ)` are the Galois groups of
the two base fields `K_i = L^{H_i}` (both containing `μ_ℓ`), and the absolute Galois groups of the
`K_i` are isomorphic.  Then `K₁ ≅ K₂`. -/
theorem nonempty_ringEquiv_of_uchidaModuleData_and_perlis
    (hU : IsUchidaModuleData ℓ) (hP : PerlisGassmannInput) [Fact ℓ.Prime]
    {L : Type} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (hμ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ)
    (H₁ H₂ : Subgroup Gal(L/ℚ))
    (hμ₁ : ∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ)
    (hμ₂ : ∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ)
    (hiso : HasIsomorphicAbsGalois ↥(IntermediateField.fixedField H₁)
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
  have hG₁ : IsGassmannEquivalentOf (ZMod ℓ) (Fin n) H₁ H₂ :=
    isGassmannEquivalentOf_of_module_data ρ H₁ H₂ e (fun γ x => he γ x)
      M₁.fixingSubgroup M₂.fixingSubgroup hJ₁ hJ₂ hspec₁ hspec₂ hconj₁
  have hG₂ : IsGassmannEquivalentOf (ZMod ℓ) (Fin n) H₂ H₁ :=
    isGassmannEquivalentOf_of_module_data ρ H₂ H₁ e (fun γ x => he γ x)
      M₂.fixingSubgroup M₁.fixingSubgroup hJ₂ hJ₁ hspec₂ hspec₁ hconj₂
  -- Uchida's λ-argument in both directions.
  have hinj₁ : ↥H₁ ↪ Fin n :=
    (Fintype.equivFin ↥H₁).toEmbedding.trans (Fin.castLEEmb (by rw [hn]; exact Nat.le_add_right _ _))
  have hinj₂ : ↥H₂ ↪ Fin n :=
    (Fintype.equivFin ↥H₂).toEmbedding.trans (Fin.castLEEmb (by rw [hn]; exact Nat.le_add_left _ _))
  obtain ⟨g, hg⟩ := conj_le_of_gassmannOf (ℓ := ℓ) hinj₁ hG₁
  obtain ⟨k, hk⟩ := conj_le_of_gassmannOf (ℓ := ℓ) hinj₂ hG₂
  -- Hence the subgroups are conjugate.
  have hcard : Nat.card ↥H₂ ≤ Nat.card ↥H₁ := card_le_of_map_conj_le H₁ H₂ hk
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
  exact nonempty_ringEquiv_of_fixingSubgroup_map_conj _ _ hfix

end NK.UchidaKummer
