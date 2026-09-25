/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Perlis/Gassmann input of §6 is reduced to Čebotarev plus a prime count

Reference: arXiv:2601.01251, §6, proof of `thm:uchida isomorphism`, and Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, §12.2.

`NK.UchidaKummer.PerlisGassmannInput` is the classical Perlis/Gassmann step: two **arithmetically
equivalent** number fields `M₁`, `M₂` inside a common finite Galois extension `N/ℚ` have
conjugate-into fixing subgroups in `Gal(N/ℚ)`.  Classically this is proved with Dedekind zeta
functions (Perlis' theorem, via the equality of the Euler products).

This file proves it from two statements that mention **no** zeta function:

* `NK.WeakNU.ChebotarevFrobeniusInput` — Čebotarev's density theorem, in the weak form used here:
  every element of `Gal(N/ℚ)` is a Frobenius element at a prime above some rational prime outside
  any prescribed finite set, that prime being unramified in `N`;
* `NK.WeakNU.PrimeCountOrbitInput` — the number of primes of an intermediate field `M ⊆ N` above
  an unramified rational prime `p` is the number of orbits of `⟨σ⟩` on `Gal(N/ℚ) ⧸ Gal(N/M)`, where
  `σ` is a Frobenius at a prime above `p`.

The deduction has three steps:

1. **Arithmetic equivalence at a well-chosen prime.**  If `M₁` and `M₂` are arithmetically
   equivalent then, for every element `σ` of `Gal(N/ℚ)`, Čebotarev supplies an unramified prime `p`,
   outside the exceptional set of the arithmetic equivalence, at which `σ` is a Frobenius element.
   At that `p` the two counts of `PrimeCountOrbitInput` agree, so
   `orbitCount σ (Gal(N/ℚ) ⧸ H₁) = orbitCount σ (Gal(N/ℚ) ⧸ H₂)` for `H_i = Gal(N/M_i)`
   (`key` below).
2. **Inversion of the orbit-count function.**  `NK.WeakNU.fixedCount_eq_of_orbitCount_eq`, the
   group-theoretic core proved in this chapter: the orbit counts of the cyclic subgroups determine
   the fixed-point counts.  Hence
   `fixedCount σ (Gal(N/ℚ) ⧸ H₁) = fixedCount σ (Gal(N/ℚ) ⧸ H₂)` for every `σ`.
3. **Conjugacy into the fixing subgroup.**  `NK.WeakNU.exists_conj_mem_of_fixedCount_coset_eq`:
   an element of `H₁` fixes the coset `H₁` of `Gal(N/ℚ) ⧸ H₁`, so its fixed-point count there is
   positive; by step 2 it is positive on `Gal(N/ℚ) ⧸ H₂` as well, i.e. some conjugate of it lies in
   `H₂`.

This is the "arithmetic equivalence ⟹ Gassmann equivalence" direction of Perlis' theorem, in the
only form §6 consumes (the elementwise conjugate-into condition), and with the analytic input
replaced by Čebotarev.
-/

import Submission.NK.WeakNU.Defs
import Submission.NK.WeakNU.fixedCount_eq_of_orbitCount_eq
import Submission.NK.WeakNU.exists_conj_mem_of_fixedCount_coset_eq
import Submission.NK.UchidaKummer.Uchida.PerlisInput

namespace NK.WeakNU

noncomputable section

open IntermediateField

/-- **The Perlis/Gassmann input, reduced to Čebotarev and a prime count.**

Let `N/ℚ` be a finite Galois extension of number fields and `M₁`, `M₂ ⊆ N` arithmetically
equivalent.  Then every element of `Gal(N/M₁)` is conjugate in `Gal(N/ℚ)` into `Gal(N/M₂)`, and
conversely. -/
theorem perlisGassmannInput_of_chebotarev_and_primeCount
    (hC : ChebotarevFrobeniusInput) (hPC : PrimeCountOrbitInput) :
    NK.UchidaKummer.PerlisGassmannInput := by
  intro N _f _nf _alg _gal M₁ M₂ hAE
  -- Step 1: the orbit counts of the two coset spaces agree at every element of the Galois group.
  have key : ∀ (A B : IntermediateField ℚ N), NK.UchidaKummer.ArithmeticallyEquivalent ↥A ↥B →
      ∀ σ : Gal(N/ℚ), orbitCount σ (Gal(N/ℚ) ⧸ A.fixingSubgroup) =
        orbitCount σ (Gal(N/ℚ) ⧸ B.fixingSubgroup) := by
    intro A B hAB σ
    obtain ⟨T, hT⟩ := hAB
    obtain ⟨p, hp, hpT, hram, P, hP, hfrob⟩ := hC N σ T
    have h1 := hPC N A p hp hram σ ⟨P, hP, hfrob⟩
    have h2 := hPC N B p hp hram σ ⟨P, hP, hfrob⟩
    have h3 := hT p hp hpT
    exact h1.symm.trans (h3.trans h2)
  -- Step 2 and 3: the fixed-point counts agree, whence the conjugacy-into condition.
  have hfix : ∀ (A B : IntermediateField ℚ N), NK.UchidaKummer.ArithmeticallyEquivalent ↥A ↥B →
      ∀ x ∈ A.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ B.fixingSubgroup := by
    intro A B hAB x hx
    have hfixed : ∀ σ : Gal(N/ℚ), fixedCount σ (Gal(N/ℚ) ⧸ A.fixingSubgroup) =
        fixedCount σ (Gal(N/ℚ) ⧸ B.fixingSubgroup) := by
      intro σ
      exact fixedCount_eq_of_orbitCount_eq σ (fun i => key A B hAB (σ ^ i))
    exact exists_conj_mem_of_fixedCount_coset_eq A.fixingSubgroup B.fixingSubgroup hfixed x hx
  exact ⟨hfix M₁ M₂ hAE, hfix M₂ M₁ hAE.symm⟩

/-- The same, in the form of the classical statement that the fixing subgroups are Gassmann
equivalent: `NK.WeakNU.perlisGassmannInput_of_chebotarev_and_primeCount` composed with
`NK.UchidaKummer.exists_conj_mem_of_gassmann`-style extraction is not needed, but this corollary
records that the conclusion is symmetric in the two fields. -/
theorem perlisGassmannInput_of_chebotarev_and_primeCount_conj
    (hC : ChebotarevFrobeniusInput) (hPC : PrimeCountOrbitInput)
    (N : Type) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (M₁ M₂ : IntermediateField ℚ N)
    (h : NK.UchidaKummer.ArithmeticallyEquivalent ↥M₁ ↥M₂) :
    (∀ x ∈ M₁.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ M₂.fixingSubgroup) ∧
    (∀ x ∈ M₂.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ M₁.fixingSubgroup) :=
  perlisGassmannInput_of_chebotarev_and_primeCount hC hPC N M₁ M₂ h

end

end NK.WeakNU
