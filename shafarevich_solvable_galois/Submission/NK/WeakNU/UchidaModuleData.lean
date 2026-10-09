/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uchida's module data: the reduction to its Kummer part and its arithmetic clause

Reference: arXiv:2601.01251, §6, Lemma `lem:embedding problem` together with `cor:arith equiv`.

`NK.UchidaKummer.IsUchidaModuleData ℓ` is the input of §6 of the paper in module form.  Its
content splits into two independent halves:

* `NK.WeakNU.IsUchidaModuleDataKummer ℓ` — the **Kummer-theoretic embedding problem** of Lemma
  6.1: the existence of a finite Galois `N/L` (with `N/ℚ` Galois) whose Galois group `Gal(N/L)` is
  identified, equivariantly for the conjugation action of `Gal(L/ℚ)`, with `𝔽_ℓ[Gal(L/ℚ)]^n`, and of
  two subfields `M₁, M₂ ⊆ N` containing `L` whose fixing subgroups correspond to the submodules
  `I_{H₁}𝔽_ℓ[Gal(L/ℚ)]^n`, `I_{H₂}𝔽_ℓ[Gal(L/ℚ)]^n`;
* `NK.WeakNU.IsUchidaModuleDataArith ℓ` — the **arithmetic clause** `cor:arith equiv`: for such
  data the two fields `M₁`, `M₂` are arithmetically equivalent.

The Kummer half is the half whose *cardinality* form is already a theorem of this workspace
(`NK.UchidaKummer.isKummerEmbeddingProblem`); what is missing for the module form is the
formalisation of the `𝔽_ℓ[Gal(L/ℚ)]`-module structure of a compositum of Kummer radicals.  The
arithmetic half is the genuine residual input: it is the step in which the prime-splitting behaviour
of the fields `M_i` is read off from the module structure (and, in the paper, from the prime
bijection of input (A) of (12.1.9)).

The two lemmas below record the trivial-but-useful consequences: the Kummer half is *implied by*
`IsUchidaModuleData`, and `IsUchidaModuleData` is *equivalent to* the conjunction of the two halves.
-/

import Submission.NK.WeakNU.Defs
import Submission.NK.UchidaKummer.Uchida.ModuleData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.WeakNU

open IntermediateField

/-- **The Kummer-theoretic half of Uchida's module data** (§6, Lemma `lem:embedding problem`).

This is `NK.UchidaKummer.IsUchidaModuleData ℓ` with the arithmetic-equivalence clause
`ArithmeticallyEquivalent ↥M₁ ↥M₂` removed.  It asserts the existence of the extension `N/L`, of the
equivariant identification `e` of `Gal(N/L)` with `𝔽_ℓ[Gal(L/ℚ)]^n`, and of the two subfields `M_i`
whose fixing subgroups correspond to `I_{H_i}𝔽_ℓ[Gal(L/ℚ)]^n`. -/
def IsUchidaModuleDataKummer (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L],
    (∃ ζ : L, IsPrimitiveRoot ζ ℓ) →
    ∀ (H₁ H₂ : Subgroup Gal(L/ℚ)),
      (∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ) →
      (∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ) →
      NK.UchidaKummer.HasIsomorphicAbsGalois ↥(IntermediateField.fixedField H₁)
        ↥(IntermediateField.fixedField H₂) →
      ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra ℚ N) (_ : Algebra L N)
        (_ : IsScalarTower ℚ L N) (_ : IsGalois ℚ N) (_ : FiniteDimensional L N)
        (e : ↥((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker)
              ≃ (Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ))),
        (∀ (γ : Gal(N/ℚ))
            (x : ↥((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker)),
          e ((MulAut.conjNormal γ) x) = fun i =>
            MonoidAlgebra.single (AlgEquiv.restrictNormalHom (F := ℚ) L γ) (1 : ZMod ℓ) * e x i) ∧
        ∃ (M₁ M₂ : IntermediateField ℚ N),
          (∀ x : L, algebraMap L N x ∈ M₁) ∧ (∀ x : L, algebraMap L N x ∈ M₂) ∧
          (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
            f ∈ e '' ((M₁.fixingSubgroup.subgroupOf
              ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
              ∀ i, f i ∈ NK.UchidaKummer.IH (ZMod ℓ) H₁) ∧
          (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
            f ∈ e '' ((M₂.fixingSubgroup.subgroupOf
              ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
              ∀ i, f i ∈ NK.UchidaKummer.IH (ZMod ℓ) H₂)

/-- **The arithmetic clause of Uchida's module data** (§6, `cor:arith equiv`).

For any data satisfying the Kummer clauses — a finite Galois `N/ℚ` with `N/L` Galois, the
equivariant identification `e : Gal(N/L) ≃ 𝔽_ℓ[Gal(L/ℚ)]^n`, and subfields `M_i ⊆ N` containing `L`
whose fixing subgroups are the preimages of `I_{H_i}𝔽_ℓ[Gal(L/ℚ)]^n` — the two fields `M₁`, `M₂` are
arithmetically equivalent.  This is the statement that the prime-splitting behaviour of `M_i` is
determined by the `𝔽_ℓ[Gal(L/ℚ)]`-module structure of the Kummer extension. -/
def IsUchidaModuleDataArith (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L],
    ∀ (H₁ H₂ : Subgroup Gal(L/ℚ))
      (N : Type) [Field N] [NumberField N] [Algebra ℚ N] [Algebra L N] [IsScalarTower ℚ L N]
      [IsGalois ℚ N] [FiniteDimensional L N]
      (e : ↥((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker)
            ≃ (Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ)))
      (M₁ M₂ : IntermediateField ℚ N),
      (∀ (γ : Gal(N/ℚ))
          (x : ↥((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker)),
        e ((MulAut.conjNormal γ) x) = fun i =>
          MonoidAlgebra.single (AlgEquiv.restrictNormalHom (F := ℚ) L γ) (1 : ZMod ℓ) * e x i) →
      (∀ x : L, algebraMap L N x ∈ M₁) → (∀ x : L, algebraMap L N x ∈ M₂) →
      (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
        f ∈ e '' ((M₁.fixingSubgroup.subgroupOf
          ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
          ∀ i, f i ∈ NK.UchidaKummer.IH (ZMod ℓ) H₁) →
      (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
        f ∈ e '' ((M₂.fixingSubgroup.subgroupOf
          ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
          ∀ i, f i ∈ NK.UchidaKummer.IH (ZMod ℓ) H₂) →
      NK.UchidaKummer.ArithmeticallyEquivalent ↥M₁ ↥M₂

/-- **The Kummer half is implied by Uchida's module data** (projection of the existential). -/
theorem isUchidaModuleDataKummer_of_isUchidaModuleData {ℓ : ℕ}
    (h : NK.UchidaKummer.IsUchidaModuleData ℓ) : IsUchidaModuleDataKummer ℓ := by
  intro n L _ _ _ _ hμ H₁ H₂ hμ₁ hμ₂ hiso
  obtain ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    -, hspec₁, hspec₂⟩ := h n L hμ H₁ H₂ hμ₁ hμ₂ hiso
  exact ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    hspec₁, hspec₂⟩

/-- **Uchida's module data from its two halves.** -/
theorem isUchidaModuleData_of_kummer_and_arith {ℓ : ℕ}
    (hK : IsUchidaModuleDataKummer ℓ) (hA : IsUchidaModuleDataArith ℓ) :
    NK.UchidaKummer.IsUchidaModuleData ℓ := by
  intro n L _ _ _ _ hμ H₁ H₂ hμ₁ hμ₂ hiso
  obtain ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    hspec₁, hspec₂⟩ := hK n L hμ H₁ H₂ hμ₁ hμ₂ hiso
  refine ⟨N, hfN, hnfN, halgN, halgLN, htower, hgalN, hfinLN, e, he, M₁, M₂, hLM₁, hLM₂,
    ?_, hspec₁, hspec₂⟩
  exact hA n L H₁ H₂ N e M₁ M₂ he hLM₁ hLM₂ hspec₁ hspec₂

/-- **Uchida's module data from its two halves.**  This is the requested name
`NK.WeakNU.isUchidaModuleData`, in the "reduced" form: the two halves of
`NK.UchidaKummer.IsUchidaModuleData` are the residual catalogue. -/
theorem isUchidaModuleData {ℓ : ℕ}
    (hK : IsUchidaModuleDataKummer ℓ) (hA : IsUchidaModuleDataArith ℓ) :
    NK.UchidaKummer.IsUchidaModuleData ℓ :=
  isUchidaModuleData_of_kummer_and_arith hK hA

end NK.WeakNU
