import Mathlib
import Submission.NumberField.MaximalProPOutsideS
import Submission.Commons.FieldTheory.Galois.isGalois_iSup_of_charZero

/-!
# `Work.ShafarevichKoch.SupportedTower` -- the maximal pro-`p`-outside-`S` extension as a tower

This module fixes the **objects of the comparison** used by the counting (Hochschild--Serre) form of
the classical Shafarevich--Koch argument, *inside* the algebraic closure of the base field, so that
the whole comparison is an exercise in `IntermediateField` arithmetic with no class field theory.

* `kSupported F p S` -- the maximal pro-`p` extension of `F` unramified outside `S`, i.e. the
  supremum (in `AlgebraicClosure F`) of the finite Galois pro-`p` subextensions whose relative
  different is supported on `S` (the seed's `Submission.NumberField.SupportedPField`);
* `le_kSupported` -- every `SupportedPField` is a subfield of it;
* `isGalois_kSupported` -- it is Galois over `F` (characteristic zero, `isGalois_iSup_of_charZero`);
* `kSupported_empty_le` -- **the key containment `F_∅ ⊆ k_S`**: the maximal pro-`p` extension
  unramified everywhere is contained in the maximal pro-`p` extension unramified outside `S`.

The last statement is where the "unramified at every finite prime" condition is used: a
`SupportedPField F p ∅` has a relative different all of whose prime divisors lie over the *empty*
set of rational primes, i.e. it is unramified, hence it is also a `SupportedPField F p S`.

## Conventions

`S : Finset ℕ` is a set of *rational* primes; an ideal of `𝓞 F` is "above `S`" if it lies over
`Ideal.span {(q : ℤ)}` for some `q ∈ S` (`Submission.NumberField.SupportedPField`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- The maximal pro-`p` extension of `F` unramified outside the rational primes in `S`, realised as
an intermediate field of the algebraic closure: the supremum of the finite Galois pro-`p`
subextensions whose relative different is supported on `S`. -/
def kSupported (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (S : Finset ℕ) :
    IntermediateField F (AlgebraicClosure F) :=
  ⨆ i : Submission.NumberField.SupportedPField F p S, i.L

/-- Every finite Galois pro-`p` `S`-supported subextension is contained in `kSupported F p S`. -/
theorem le_kSupported {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    {S : Finset ℕ} (i : Submission.NumberField.SupportedPField F p S) :
    i.L ≤ kSupported F p S :=
  le_iSup (fun i : Submission.NumberField.SupportedPField F p S => i.L) i

/-- `kSupported F p S` is Galois over `F`. -/
theorem isGalois_kSupported {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (S : Finset ℕ) : IsGalois F ↥(kSupported F p S) := by
  haveI : ∀ i : Submission.NumberField.SupportedPField F p S, IsGalois F ↥(i.L) :=
    fun i => i.hgal
  exact Commons.FieldTheory.Galois.isGalois_iSup_of_charZero
    (F := F) (K := AlgebraicClosure F)
    (E := fun i : Submission.NumberField.SupportedPField F p S => i.L)

/-- **The containment `F_∅ ⊆ k_S`.**  A finite Galois pro-`p` extension of `F` which is unramified
at every finite prime (i.e. has trivial relative different) is in particular `S`-supported for every
`S`: its different has no prime divisors at all, so the support condition is vacuous.  Hence the
maximal everywhere-unramified pro-`p` extension is contained in the maximal `S`-supported one. -/
theorem kSupported_empty_le {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (S : Finset ℕ) :
    kSupported F p (∅ : Finset ℕ) ≤ kSupported F p S := by
  refine iSup_le fun i => ?_
  haveI : FiniteDimensional F ↥(i.L) := i.hfd
  haveI : IsGalois F ↥(i.L) := i.hgal
  haveI : NumberField ↥(i.L) := i.hnum
  have hsupp : ∀ (P : Ideal (NumberField.RingOfIntegers ↥(i.L))), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers ↥(i.L)) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    intro P hP hPne hPdvd
    obtain ⟨q, hq, -⟩ := i.hsupp P hP hPne hPdvd
    exact absurd hq (Finset.notMem_empty q)
  exact le_iSup (fun j : Submission.NumberField.SupportedPField F p S => j.L)
    { L := i.L, hpg := i.hpg, hsupp := hsupp }

end Work.ShafarevichKoch
