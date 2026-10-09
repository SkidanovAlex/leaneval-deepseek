/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uchida's module data: the form of §6 Lemma 6.1 consumed by the transport step

Reference: arXiv:2601.01251, §6, Lemma `lem:embedding problem` together with `cor:arith equiv`.

The embedding problem of §6 produces, for a finite Galois extension `L/ℚ` containing `μ_ℓ` and a
subgroup `H ≤ Gal(L/ℚ)`, an extension `N/L` with `N/ℚ` Galois whose Galois group `Gal(N/L)` is — as
a `Gal(L/ℚ)`-module — isomorphic to `𝔽_ℓ[G]^n`, and a subfield `L K̃ ⊆ N` with
`Gal(N/LK̃) = I_H 𝔽_ℓ[G]^n`.

Because `K̃` is chosen as the fixed field of the subgroup `I_H Gal(N/L)` of `Gal(N/ℚ)`, the second
clause is exactly the statement that the image of `Gal(N/K̃)` under the explicit isomorphism `e` is
the submodule `(I_H 𝔽_ℓ[G])^n`, i.e. the set of `n`-tuples all of whose entries lie in `I_H 𝔽_ℓ[G]`.

This file states the data in the form the transport step
(`NK.UchidaKummer.isGassmannEquivalentOf_of_module_data`) consumes.  It is a `Prop`, so callers
state theorems conditionally on it; its content is Kummer theory (weak approximation, the local
Kummer dichotomy, completely split primes) together with the prime bijection `cor:arith equiv` — no
Dedekind zeta functions.
-/

import Submission.NK.UchidaKummer.Uchida.PerlisInput
import Submission.NK.UchidaKummer.Uchida.Transport
import Submission.NK.UchidaKummer.Embedding.isKummerEmbeddingProblem
import Mathlib.FieldTheory.Galois.Infinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

open IntermediateField

/-- **Having isomorphic absolute Galois groups**, stated for arbitrary separable closures. -/
def HasIsomorphicAbsGalois (K₁ K₂ : Type*) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] :
    Prop :=
  ∀ (K₁' : Type) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))

/-- **Uchida's module data** (§6, Lemma 6.1 together with `cor:arith equiv`). -/
def IsUchidaModuleData (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L],
    (∃ ζ : L, IsPrimitiveRoot ζ ℓ) →
    ∀ (H₁ H₂ : Subgroup Gal(L/ℚ)),
      (∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ) →
      (∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ) →
      HasIsomorphicAbsGalois ↥(IntermediateField.fixedField H₁) ↥(IntermediateField.fixedField H₂) →
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
          ArithmeticallyEquivalent ↥M₁ ↥M₂ ∧
          (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
            f ∈ e '' ((M₁.fixingSubgroup.subgroupOf
              ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
              ∀ i, f i ∈ IH (ZMod ℓ) H₁) ∧
          (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
            f ∈ e '' ((M₂.fixingSubgroup.subgroupOf
              ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
              ∀ i, f i ∈ IH (ZMod ℓ) H₂)

end NK.UchidaKummer
