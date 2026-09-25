/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Basic
import Submission.NK.HeckeL.All
import Submission.NK.Chebotarev.Density

/-!
# The analytic vocabulary of the second inequality

This file sets up the abstract analytic objects in which the **second inequality** of global class
field theory is proved.  The mathematical content (Milne, *Class Field Theory*, Chapter VI,
Theorems 3.4 and 4.8–4.9) is:

for a finite abelian group `B`, a "class map" `b : PrimeIdeal K → B` recording the class of a prime
ideal, and, for every character `χ : B →* ℂˣ`, the Euler product
`L(χ,s) = ∏_{𝔭 ∉ S} (1 - χ(b 𝔭) N𝔭^{-s})⁻¹`,

the sum of the weights `N𝔭^{-s}` over the primes with **trivial** class is bounded by
`|B|⁻¹ · log (1/(s-1))` up to an additive constant, as `s → 1⁺`.  If in addition every prime
splitting completely in a Galois extension `L/K` has trivial class, and the completely split primes
have density `1/[L:K]` (which the shared library proves), then `|B| ≤ [L:K]`.

The point of the abstract formulation is that the analytic input needed — the *regularity* of the
`L`-series at `s = 1` for non-trivial `χ`, which is Hecke's theorem — is stated for the characters
of the quotient group `B = C_K ⧸ (K^× U N 𝕀_L)`, whose characters are precisely the Hecke
characters of the ray class group trivial on the norms; no Artin reciprocity is used.

## References

* J. S. Milne, *Class Field Theory*, Chapter VI, §3 (density of the primes splitting completely)
  and §4 (density of the primes in a congruence subgroup, and the analytic proof of the second
  inequality, Theorem 4.9).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped BigOperators Classical

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.HeckeL

/-- A prime ideal of `𝓞 K`, i.e. a finite place of `K` (`HeightOneSpectrum (𝓞 K)`). -/
abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

variable {K : Type*} [Field K] [NumberField K]

/-- The weight `N𝔭^{-s}` of a prime ideal `𝔭`, as a real number. -/
def primeWeight (s : ℝ) (𝔭 : PrimeIdeal K) : ℝ := (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)

@[simp] theorem primeWeight_def (s : ℝ) (𝔭 : PrimeIdeal K) :
    primeWeight s 𝔭 = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := rfl

theorem primeWeight_pos (s : ℝ) (𝔭 : PrimeIdeal K) : 0 < primeWeight s 𝔭 :=
  Real.rpow_pos_of_pos
    (Commons.NumberTheory.NumberField.DedekindZeta.absNorm_primeIdeal_pos 𝔭) _

theorem primeWeight_nonneg (s : ℝ) (𝔭 : PrimeIdeal K) : 0 ≤ primeWeight s 𝔭 :=
  (primeWeight_pos s 𝔭).le

/-- The "prime term" `χ(b 𝔭) N𝔭^{-s}` of the Euler factor at `𝔭`. -/
def primeTerm {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ) (s : ℝ)
    (𝔭 : PrimeIdeal K) : ℂ :=
  (χ (b 𝔭) : ℂ) * ((primeWeight s 𝔭 : ℝ) : ℂ)

@[simp] theorem primeTerm_def {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ) (s : ℝ)
    (𝔭 : PrimeIdeal K) :
    primeTerm b χ s 𝔭 = (χ (b 𝔭) : ℂ) * ((primeWeight s 𝔭 : ℝ) : ℂ) := rfl

/-- The Euler factor `(1 - χ(b 𝔭) N𝔭^{-s})⁻¹` at `𝔭`. -/
def eulerFactor {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ) (s : ℝ)
    (𝔭 : PrimeIdeal K) : ℂ :=
  (1 - primeTerm b χ s 𝔭)⁻¹

@[simp] theorem eulerFactor_def {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ) (s : ℝ)
    (𝔭 : PrimeIdeal K) :
    eulerFactor b χ s 𝔭 = (1 - primeTerm b χ s 𝔭)⁻¹ := rfl

/-- **The Euler product** of the character `χ` attached to the class map `b`, over the primes
outside the finite set `S`. -/
def eulerProduct {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K))
    (χ : B →* ℂˣ) (s : ℝ) : ℂ :=
  ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, eulerFactor b χ s 𝔭.1

@[simp] theorem eulerProduct_def {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K))
    (χ : B →* ℂˣ) (s : ℝ) :
    eulerProduct b S χ s =
      ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, eulerFactor b χ s 𝔭.1 := rfl

/-- The logarithm of the norm of the Euler factor at `𝔭`, with the sign that makes it positive:
`-log ‖1 - χ(b 𝔭) N𝔭^{-s}‖`.

The logarithmic form of the local factor identity is that the sum of these over all characters of
`B` is `(|B| / orderOf (b 𝔭)) · (-log (1 - N𝔭^{-s·orderOf (b 𝔭)}))`. -/
def negLogEulerFactor {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ) (s : ℝ)
    (𝔭 : PrimeIdeal K) : ℝ :=
  - Real.log ‖1 - primeTerm b χ s 𝔭‖

@[simp] theorem negLogEulerFactor_def {B : Type*} [Monoid B] (b : PrimeIdeal K → B) (χ : B →* ℂˣ) (s : ℝ)
    (𝔭 : PrimeIdeal K) :
    negLogEulerFactor b χ s 𝔭 = - Real.log ‖1 - primeTerm b χ s 𝔭‖ := rfl

/-- **The sum of the weights of the primes whose class is trivial.**  This is the partial Dirichlet
series of the set `{𝔭 : b 𝔭 = 1}`, over the primes outside `S`. -/
def trivialClassSum {B : Type*} [Monoid B] [DecidableEq B] (b : PrimeIdeal K → B)
    (S : Finset (PrimeIdeal K)) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, if b 𝔭.1 = 1 then primeWeight s 𝔭.1 else 0

@[simp] theorem trivialClassSum_def {B : Type*} [Monoid B] [DecidableEq B] (b : PrimeIdeal K → B)
    (S : Finset (PrimeIdeal K)) (s : ℝ) :
    trivialClassSum b S s =
      ∑' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
        if b 𝔭.1 = 1 then primeWeight s 𝔭.1 else 0 := rfl

/-- The partial Dirichlet series of the set `T` of prime ideals, `∑_{𝔭 ∈ T} N𝔭^{-s}` — the
`NumberField.Set.primeIdealZetaSum` of the shared library. -/
abbrev primeSum (T : Set (PrimeIdeal K)) (s : ℝ) : ℝ :=
  NumberField.Set.primeIdealZetaSum T s

/-- The set of prime ideals whose class under `b` is trivial. -/
def trivialClassSet {B : Type*} [One B] (b : PrimeIdeal K → B) : Set (PrimeIdeal K) := {𝔭 | b 𝔭 = 1}

@[simp] theorem trivialClassSet_def {B : Type*} [One B] (b : PrimeIdeal K → B) :
    trivialClassSet b = {𝔭 | b 𝔭 = 1} := rfl

/-- The set of primes of `K` that split completely in `L`, i.e. have `[L : K]` primes above them in
`L` (equivalently: are unramified with residue degree one).  This is the set whose Dirichlet
density the shared library computes as `1/[L:K]`. -/
def splitCompletelySet (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Set (PrimeIdeal K) :=
  {𝔭 | (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L}

theorem hasDirichletDensity_splitCompletelySet {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    NumberField.Set.HasDirichletDensity (splitCompletelySet K L) (1 / (Module.finrank K L : ℝ)) :=
  Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely

end NK.GlobalCFTdeep.SecondInequality
