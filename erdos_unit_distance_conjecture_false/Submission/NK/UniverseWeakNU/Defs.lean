/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.UniverseWeakNU`: the weak Neukirch–Uchida chain at an arbitrary universe

The challenge statement `Submission.neukirch_uchida` is universe-polymorphic
(`{K₁ K₂ K₁' K₂' : Type*}`), but the on-disk derivation of the endgame hypothesis
`NK.ReconstructField.LevelIsoInput ϕ hϕ` runs through the *universe-0* chain

`NK.UchidaKummer.IsUchidaModuleData 2 → NK.WeakNU.ChebotarevFrobeniusInput →
NK.UchidaKummer.IsWeakUchida 2 → NK.ReconstructField.LevelIsoInput ϕ hϕ`

whose `Prop`-valued definitions quantify over `Type` (the bottom universe).  Consequently the
derivation can only produce `LevelIsoInput.{0,0,0,0}`.

This directory re-runs the whole chain with `Type` replaced by `Type u` under a `universe u`
binder.  **Nothing outside this directory is modified**: every definition below is a *copy* of a
definition of `Submission/Work/WeakNU/` or `Submission/Work/UchidaKummer/` with the universe
changed (the suffix `U` marks the polymorphic copy).

## The definitions

| this file | copy of | file |
|---|---|---|
| `NK.UniverseWeakNU.ChebotarevFrobeniusInputU` | `NK.WeakNU.ChebotarevFrobeniusInput` | `WeakNU/Defs.lean` |
| `NK.UniverseWeakNU.PrimeCountOrbitInputU` | idem | `WeakNU/Defs.lean` |
| `NK.UniverseWeakNU.PerlisGassmannInputU` | `NK.UchidaKummer.PerlisGassmannInput` | `UchidaKummer/Uchida/PerlisInput.lean` |
| `NK.UniverseWeakNU.HasIsomorphicAbsGaloisU` | `NK.UchidaKummer.HasIsomorphicAbsGalois` | `UchidaKummer/Uchida/ModuleData.lean` |
| `NK.UniverseWeakNU.IsUchidaModuleDataU`, `IsUchidaModuleDataKummerU`, `IsUchidaModuleDataArithU` | idem | `UchidaKummer/Uchida/ModuleData.lean`, `WeakNU/UchidaModuleData.lean` |
| `NK.UniverseWeakNU.IsWeakUchidaU`, `IsWeakUchidaOfU` | `NK.UchidaKummer.IsWeakUchida`, `NK.WeakNU.IsWeakUchidaOf` | `UchidaKummer/Defs.lean`, `WeakNU/Defs.lean` |

At `u = 0` each of these is *definitionally equal* to the original
(`NK.UniverseWeakNU.ChebotarevFrobeniusInputU.{0} = NK.WeakNU.ChebotarevFrobeniusInput = rfl`,
etc., proved in `Submission/Work/UniverseWeakNU/Zero.lean`), so the polymorphic chapter is a
conservative extension of the universe-0 one.

The universe-polymorphic *proofs* live in the sibling files; see `README.md` for the inventory and
for the list of statements a future prover of the leaves should target.
-/

import Mathlib
import Submission.NK.WeakNU.Defs
import Submission.NK.Chebotarev.Basic
import Submission.NeukirchUchida.Local.DecompositionGroup
import Submission.NK.UchidaKummer.Uchida.PerlisInput
import Submission.NK.UchidaKummer.Uchida.ModuleData

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-! ## The arithmetic inputs -/

/-- **Čebotarev's theorem**, at an arbitrary universe.  Copy of
`NK.WeakNU.ChebotarevFrobeniusInput`. -/
def ChebotarevFrobeniusInputU : Prop :=
  ∀ (N : Type u) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (σ : Gal(N/ℚ)) (T : Finset ℕ),
    ∃ p : ℕ, p.Prime ∧ p ∉ T ∧
      (∀ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1) ∧
      ∃ P : NK.Chebotarev.PrimeIdeal N,
        P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) ∧ NK.Chebotarev.IsFrobAt P σ

/-- **The counting of the primes of a subfield by the orbits of a Frobenius**, at an arbitrary
universe.  Copy of `NK.WeakNU.PrimeCountOrbitInput`. -/
def PrimeCountOrbitInputU : Prop :=
  ∀ (N : Type u) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (M : IntermediateField ℚ N) (p : ℕ), p.Prime →
    (∀ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1) →
    ∀ σ : Gal(N/ℚ),
      (∃ P : NK.Chebotarev.PrimeIdeal N,
        P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) ∧ NK.Chebotarev.IsFrobAt P σ) →
      Nat.card (NK.UchidaKummer.primesOverRat ↥M p) =
        NK.WeakNU.orbitCount σ (Gal(N/ℚ) ⧸ M.fixingSubgroup)

/-- **The Perlis/Gassmann input**, at an arbitrary universe.  Copy of
`NK.UchidaKummer.PerlisGassmannInput`. -/
def PerlisGassmannInputU : Prop :=
  ∀ (N : Type u) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (M₁ M₂ : IntermediateField ℚ N),
    NK.UchidaKummer.ArithmeticallyEquivalent ↥M₁ ↥M₂ →
    (∀ x ∈ M₁.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ M₂.fixingSubgroup) ∧
    (∀ x ∈ M₂.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ M₁.fixingSubgroup)

/-! ## Uchida's module data and the weak theorem -/

/-- **Having isomorphic absolute Galois groups**, at an arbitrary universe.  Copy of
`NK.UchidaKummer.HasIsomorphicAbsGalois`; the requirement is that this hold for *every*
separable closure in `Type u`. -/
def HasIsomorphicAbsGaloisU (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] : Prop :=
  ∀ (K₁' : Type u) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))

/-- **Uchida's module data**, at an arbitrary universe.  Copy of
`NK.UchidaKummer.IsUchidaModuleData`. -/
def IsUchidaModuleDataU (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (L : Type u) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L],
    (∃ ζ : L, IsPrimitiveRoot ζ ℓ) →
    ∀ (H₁ H₂ : Subgroup Gal(L/ℚ)),
      (∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ) →
      (∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ) →
      HasIsomorphicAbsGaloisU ↥(IntermediateField.fixedField H₁)
        ↥(IntermediateField.fixedField H₂) →
      ∃ (N : Type u) (_ : Field N) (_ : NumberField N) (_ : Algebra ℚ N) (_ : Algebra L N)
        (_ : IsScalarTower ℚ L N) (_ : IsGalois ℚ N) (_ : FiniteDimensional L N)
        (e : ↥((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker)
              ≃ (Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ))),
        (∀ (γ : Gal(N/ℚ))
            (x : ↥((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker)),
          e ((MulAut.conjNormal γ) x) = fun i =>
            MonoidAlgebra.single (AlgEquiv.restrictNormalHom (F := ℚ) L γ) (1 : ZMod ℓ) * e x i) ∧
        ∃ (M₁ M₂ : IntermediateField ℚ N),
          (∀ x : L, algebraMap L N x ∈ M₁) ∧ (∀ x : L, algebraMap L N x ∈ M₂) ∧
          NK.UchidaKummer.ArithmeticallyEquivalent ↥M₁ ↥M₂ ∧
          (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
            f ∈ e '' ((M₁.fixingSubgroup.subgroupOf
              ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
              ∀ i, f i ∈ NK.UchidaKummer.IH (ZMod ℓ) H₁) ∧
          (∀ f : Fin n → MonoidAlgebra (ZMod ℓ) Gal(L/ℚ),
            f ∈ e '' ((M₂.fixingSubgroup.subgroupOf
              ((AlgEquiv.restrictNormalHom (F := ℚ) L : Gal(N/ℚ) →* Gal(L/ℚ)).ker) : Set _)) ↔
              ∀ i, f i ∈ NK.UchidaKummer.IH (ZMod ℓ) H₂)

/-- **The Kummer-theoretic half of Uchida's module data**, at an arbitrary universe.  Copy of
`NK.WeakNU.IsUchidaModuleDataKummer`. -/
def IsUchidaModuleDataKummerU (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (L : Type u) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L],
    (∃ ζ : L, IsPrimitiveRoot ζ ℓ) →
    ∀ (H₁ H₂ : Subgroup Gal(L/ℚ)),
      (∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ) →
      (∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ) →
      HasIsomorphicAbsGaloisU ↥(IntermediateField.fixedField H₁)
        ↥(IntermediateField.fixedField H₂) →
      ∃ (N : Type u) (_ : Field N) (_ : NumberField N) (_ : Algebra ℚ N) (_ : Algebra L N)
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

/-- **The arithmetic clause of Uchida's module data**, at an arbitrary universe.  Copy of
`NK.WeakNU.IsUchidaModuleDataArith`. -/
def IsUchidaModuleDataArithU (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (L : Type u) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L],
    ∀ (H₁ H₂ : Subgroup Gal(L/ℚ))
      (N : Type u) [Field N] [NumberField N] [Algebra ℚ N] [Algebra L N] [IsScalarTower ℚ L N]
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

/-- **The weak Neukirch–Uchida theorem**, at an arbitrary universe.  Copy of
`NK.UchidaKummer.IsWeakUchida`. -/
def IsWeakUchidaU (ℓ : ℕ) : Prop :=
  ∀ (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → Nonempty (K₁ ≃+* K₂)

/-- The weak Neukirch–Uchida theorem *with* the paper's cyclotomic hypothesis `μ_ℓ ⊆ K_i`, at an
arbitrary universe.  Copy of `NK.WeakNU.IsWeakUchidaOf`. -/
def IsWeakUchidaOfU (ℓ : ℕ) : Prop :=
  ∀ (K₁ K₂ : Type u) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    (∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) → (∃ ζ : K₂, IsPrimitiveRoot ζ ℓ) →
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → Nonempty (K₁ ≃+* K₂)

end

end NK.UniverseWeakNU
