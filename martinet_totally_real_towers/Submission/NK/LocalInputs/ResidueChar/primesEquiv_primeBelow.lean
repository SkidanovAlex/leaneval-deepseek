/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The rational prime below a finite prime is its residue characteristic

For a number field `K` and a finite prime `𝔭` of `K` with completion `κ = K_𝔭`, the residue
characteristic of `κ` — the characteristic of the residue field of the valuation ring
`𝒪_κ = 𝔭.adicCompletionIntegers K` — is the rational prime `p` below `𝔭`, i.e. the generator of
the prime ideal `𝔭 ∩ ℤ` of `ℤ = 𝓞 ℚ`.

The proof is a chain of canonical identifications:

* the residue field of `𝒪_κ` is the residue field `𝓞 K / 𝔭` of the prime `𝔭`
  (`Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists`);
* `CharP (𝓞 K / 𝔭) p` says `(p : 𝓞 K) ∈ 𝔭`, hence, pulling back along `𝓞 ℚ → 𝓞 K`,
  `(p : 𝓞 ℚ) ∈ 𝔭 ∩ ℤ`;
* a nonzero prime ideal of `𝓞 ℚ` containing `p` is `(p)`
  (`Commons.NumberTheory.NumberField.Completion.asIdeal_eq_span_prime`), so the natural generator
  `natGenerator (primeBelow K 𝔭)` of `𝔭 ∩ ℤ` divides the prime `p`, and both being prime they are
  equal.
-/
import Mathlib
import Submission.NK.LocalInputs.Inputs

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs.ResidueChar

/-- **The rational prime below `𝔭` lies in `𝔭`.**  If the residue field of the completion at the
finite prime `𝔭` has characteristic the prime `p`, then `p ∈ 𝔭`. -/
theorem ratPrime_mem_asIdeal_of_charP {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    (p : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal := by
  -- The residue field of the completion at `𝔭` is the residue field `𝓞 K ⧸ 𝔭` of `𝔭`.
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists 𝔭
  -- `CharP` of a nontrivial ring at the prime `p` says `(p : R) = 0`.
  have h1 : (p : ↥(𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) = 0 :=
    (CharP.charP_iff_prime_eq_zero hp).mp hchar
  have hmap : e (p : ↥(𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) =
      (p : NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := map_natCast e.toRingHom p
  have hreq : (p : NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) = 0 := by
    rw [← hmap, h1, RingEquiv.map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hreq

/-- **`natGenerator` of the prime below `𝔭` divides any prime in `𝔭`.**  If the prime `p` lies in
the ideal `𝔭`, then the natural generator of the rational prime below `𝔭` divides `p`. -/
theorem natGenerator_primeBelow_dvd {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hpr : (p : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal) :
    Rat.HeightOneSpectrum.natGenerator (NK.LocalInputs.primeBelow K 𝔭) ∣ p := by
  -- Pull `p` back to `𝓞 ℚ`, where `𝔭 ∩ ℤ = (primeBelow K 𝔭).asIdeal`.
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ (NK.LocalInputs.primeBelow K 𝔭).asIdeal := by
    rw [NK.LocalInputs.primeBelow_asIdeal, Ideal.mem_under]
    simpa using hpr
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  have hf : (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
      (p : NumberField.RingOfIntegers ℚ) = (p : ℤ) := map_natCast _ p
  rw [← hf]
  exact (Ideal.apply_mem_of_equiv_iff
    (f := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))).mpr hmem

/-- **The rational prime below `𝔭` is the residue characteristic of the completion.**  If the
residue field of `𝒪_{K_𝔭}` has characteristic the prime `p`, then the height-one prime
`𝔭 ∩ ℤ` of `𝓞 ℚ` corresponds to `p` under `Rat.HeightOneSpectrum.primesEquiv`. -/
theorem primesEquiv_primeBelow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K 𝔭)).1 = p := by
  have hdiv := natGenerator_primeBelow_dvd (K := K) 𝔭 (ratPrime_mem_asIdeal_of_charP 𝔭 hp hchar)
  have hne : Rat.HeightOneSpectrum.natGenerator (NK.LocalInputs.primeBelow K 𝔭) ≠ 1 :=
    (Rat.HeightOneSpectrum.prime_natGenerator _).ne_one
  exact ((Nat.Prime.dvd_iff_eq hp hne).mp hdiv).symm

end NK.LocalInputs.ResidueChar
