/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Arithmetic equivalence of number fields

Reference: arXiv:2601.01251, §6, `cor:arith equiv` and the citation *arithmetic equivalence by
number of primes*: two number fields are **arithmetically equivalent** iff they have the same number
of primes above `p` for all but finitely many rational primes `p` (equivalently, iff their Dedekind
zeta functions coincide).

This is the number-theoretic hypothesis of the Perlis/Gassmann input of §6
(`NK.UchidaKummer.PerlisGassmannInput`).
-/

import Mathlib
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace NK.UchidaKummer

/-- The nonzero primes of `𝓞 K` above the rational prime `p`. -/
def primesOverRat (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Set (NK.Chebotarev.PrimeIdeal K) :=
  {𝔭 | 𝔭.asIdeal.LiesOver (Ideal.span {(p : ℤ)})}

/-- **Arithmetic equivalence** of number fields: the same number of primes above `p` for all but
finitely many rational primes `p`. -/
def ArithmeticallyEquivalent (K₁ K₂ : Type*) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] :
    Prop :=
  ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
    Nat.card (primesOverRat K₁ p) = Nat.card (primesOverRat K₂ p)

/-- Arithmetic equivalence is reflexive. -/
theorem arithmeticallyEquivalent_refl (K : Type*) [Field K] [NumberField K] :
    ArithmeticallyEquivalent K K :=
  ⟨∅, fun _ _ _ => rfl⟩

namespace ArithmeticallyEquivalent

/-- Arithmetic equivalence is symmetric. -/
theorem symm {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (h : ArithmeticallyEquivalent K₁ K₂) : ArithmeticallyEquivalent K₂ K₁ := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun p hp hpmem => (hT p hp hpmem).symm⟩

end ArithmeticallyEquivalent

end NK.UchidaKummer
