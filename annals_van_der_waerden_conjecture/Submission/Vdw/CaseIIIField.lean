import Mathlib
import Submission.Vdw.CaseI
import Submission.Vdw.ResidueCompare
import Submission.Vdw.CaseIIIStability
import Submission.Vdw.CaseIIIRootCount
import Submission.Vdw.CaseIIIWrapper

open Polynomial
open scoped BigOperators NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III, subcase (ii): the field-side per-prime chain

The pure counting of `CaseIIIAssembly` / `CaseIIIWrapper` bounds the
*arithmetic* subcase-(ii) set `CaseIIIArithSet B n H`.  This module supplies
the field-side half of the plumbing that the eventual Case-III assembly needs:
for a bad irreducible `f` (monic, degree `n`) whose field discriminant
`D_f = fieldDisc f` is squarefull, every ramified prime `p` (`p | D_f`) with
`p > n` satisfies

* `p | DD(u_f)` — the Case-III divisibility, from the chain
  `p | D_f` & squarefull ⟹ `v_p(D_f) ≥ 2` ⟹ (Lemma 24 field)
  `polyIndex(f̄ mod p) ≥ 2` ⟹ (`CaseIIIStability`)
  `p | concDDZ n (upperCoeffs n f) =: DD(u_f)`;
* `p | Disc(f)` — automatic from `D_f | disc(f)` (`fieldDisc_dvd_polyDisc`).

and the squarefree-`A` assembly: if every prime divisor of a squarefree `A`
divides `DD(u)` (resp. `Disc f`) then `A | DD(u)` (resp. per-prime divisibility
for the arithmetic set).  The final theorem `mem_caseIIIArithSet_of_field`
packages this: box-bounded `f` with squarefull `D_f`, `DD(u_f) ≠ 0`, and a
squarefree `A > H` all of whose primes are `≥ B`, divide `D_f`, and exceed `n`,
lies in `CaseIIIArithSet B n H`.

Also recorded: `squarefull_fieldDisc_of_primitive_card_lt` — how squarefullness
of `D_f` arises in the eventual application (irreducible `f` whose Galois group
is primitive with `|Gal| < n!`, by Jordan + the Case-I valuation/step-(c)
analysis: `fieldDisc_squarefull_of_no_transposition`).
-/

namespace Submission.Vdw

section Padic

/-- A squarefull number `N` divisible by the prime `p` satisfies
`v_p(N) ≥ 2`. -/
lemma padicValNat_ge_two_of_squarefull_prime_dvd (p N : ℕ) [Fact (Nat.Prime p)]
    (hN : N ≠ 0) (hsq : Squarefull N) (hpD : p ∣ N) : 2 ≤ padicValNat p N := by
  have hsq2 : p ^ 2 ∣ N := hsq p (Fact.out) hpD
  exact (padicValNat_dvd_iff_le (p := p) (n := 2) (a := N) hN).mp hsq2

end Padic

section SquarefullSource

/-- **How `D_f` is squarefull in the application:** a monic irreducible `f`
whose Galois group (natural action on the roots, via `irrGalFinHom`) is
primitive and satisfies `|Gal| < n!` has squarefull absolute field
discriminant (Jordan: primitive proper ⟹ no transposition; then the Case-I
analysis `fieldDisc_squarefull_of_no_transposition`). -/
theorem squarefull_fieldDisc_of_primitive_card_lt (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hf : f.Monic)
    (hprim : MulAction.IsPreprimitive ((irrGalFinHom f).range)
        (Fin ((f.map φℚ).natDegree)))
    (hcard : Nat.card (f.map φℚ).Gal < ((f.map φℚ).natDegree).factorial) :
    Squarefull (fieldDisc f) := by
  exact fieldDisc_squarefull_of_no_transposition f hf
    (no_isSwap_of_primitive_proper_of_card_lt f hf hprim hcard)

end SquarefullSource

section PerPrime

/-- **Case-III per-prime divisibility.**  `p | D_f` with squarefull `D_f` and
`p > n` forces `p | DD(u_f)`: Lemma 24 (field) turns `v_p(D_f) ≥ 2` into
`polyIndex(f̄ mod p) ≥ 2`, and `prime_dvd_concDDZ_of_index_ge_two` (the
per-prime geometric-sieve input) gives `p | concDDZ n (upperCoeffs n f)`. -/
theorem prime_dvd_concDDZ_of_squarefull_fieldDisc (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) {n : ℕ} (hdeg : f.natDegree = n)
    (hn : 3 ≤ n) {p : ℕ} [Fact (Nat.Prime p)] (hpgt : n < p)
    (hpD : p ∣ fieldDisc f) (hsq : Squarefull (fieldDisc f)) :
    (p : ℤ) ∣ concDDZ n (upperCoeffs n f) := by
  classical
  have hnpos : 1 ≤ n := by omega
  have hD0 : fieldDisc f ≠ 0 := by
    unfold fieldDisc
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Kpoly f))
  have hge : 2 ≤ padicValNat p (fieldDisc f) :=
    padicValNat_ge_two_of_squarefull_prime_dvd p (fieldDisc f) hD0 hsq hpD
  have hind : 2 ≤ polyIndex (F := ZMod p) (f.map (Int.castRingHom (ZMod p))) := by
    exact le_trans hge (lemma24_field_Kpoly f hf n hdeg hnpos p hpgt)
  exact prime_dvd_concDDZ_of_index_ge_two p hn hpgt f hf hdeg hind

/-- **`p | Disc(f)` is automatic from `p | D_f`:** the field discriminant
divides the polynomial discriminant (`fieldDisc_dvd_polyDisc`). -/
theorem prime_dvd_polyDisc_of_dvd_fieldDisc (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) {p : ℕ} [Fact (Nat.Prime p)]
    (hpD : p ∣ fieldDisc f) : (p : ℤ) ∣ polyDisc f := by
  have h := fieldDisc_dvd_polyDisc f hf
  exact dvd_trans ((Int.natCast_dvd_natCast).mpr hpD) h

/-- A squarefree `A` whose every prime divisor divides the integer `b`
divides `b` itself (`A = ∏_{p | A} p`, pairwise-coprime CRT/induction). -/
lemma squarefree_prod_dvd_of_prime_dvd {A : ℕ} (b : ℤ) (hsq : Squarefree A)
    (h : ∀ p ∈ A.primeFactors, (p : ℤ) ∣ b) : (A : ℤ) ∣ b := by
  have h' : ∀ p ∈ A.primeFactors, p ∣ b.natAbs := by
    intro p hp
    exact (ofNat_dvd_iff_natAbs_dvd p b).mp (h p hp)
  have hA : A ∣ b.natAbs :=
    dvd_of_forall_primeFactors_dvd_of_squarefree A b.natAbs hsq h'
  exact (ofNat_dvd_iff_natAbs_dvd A b).mpr hA

/-- Squarefree-`A` assembly for the double discriminant: if every prime
divisor of the squarefree `A` divides `DD(u)` then `A | DD(u)`. -/
lemma squarefree_prod_dvd_concDDZ_of_prime_dvd {n : ℕ} (u : Fin (n - 1) → ℤ) {A : ℕ}
    (hsq : Squarefree A) (h : ∀ p ∈ A.primeFactors, (p : ℤ) ∣ concDDZ n u) :
    (A : ℤ) ∣ concDDZ n u :=
  squarefree_prod_dvd_of_prime_dvd (concDDZ n u) hsq h

end PerPrime

section Membership

/-- The arithmetic-side membership packaging: given the field data
(squarefree `A > H`, primes `≥ B`, `A | DD(u_f)`, `p | Disc(f)` for all
`p | A`) and `DD(u_f) ≠ 0`, the box polynomial `f` lies in the arithmetic
subcase-(ii) set `CaseIIIArithSet B n H`. -/
theorem mem_caseIIIArithSet_of_field_data (n H B : ℕ) (_hn : 3 ≤ n)
    (f : ℤ[X]) (hfbox : f ∈ Box n H)
    (hdd : concDDZ n (upperCoeffs n f) ≠ 0)
    {A : ℕ} (hAH : H < A) (hsqA : Squarefree A) (hBp : ∀ p ∈ A.primeFactors, B ≤ p)
    (hAd : (A : ℤ) ∣ concDDZ n (upperCoeffs n f))
    (hpD : ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr f) :
    f ∈ CaseIIIArithSet B n H := by
  classical
  unfold CaseIIIArithSet
  refine ⟨hfbox, hdd, ⟨A, ?_, ?_⟩⟩
  · exact ⟨hAH, hsqA, hBp, hAd⟩
  · intro p hp
    exact hpD p hp

/-- **Field-side subcase-(ii) membership.**  For a monic irreducible box
polynomial `f` (degree `n ≥ 3`) with squarefull `D_f` and `DD(u_f) ≠ 0`, and a
squarefree `A > H` such that every prime divisor of `A` is `≥ B`, divides
`D_f`, and exceeds `n`: every prime divisor of `A` divides `Disc(f)`
(`fieldDisc_dvd_polyDisc`) and divides `DD(u_f)` (the per-prime chain), so `A`
is admissible for `u_f` and `f ∈ CaseIIIArithSet B n H`. -/
theorem mem_caseIIIArithSet_of_field (n H B : ℕ) (hn : 3 ≤ n) (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hfbox : f ∈ Box n H)
    (hsq : Squarefull (fieldDisc f))
    (hdd : concDDZ n (upperCoeffs n f) ≠ 0)
    {A : ℕ} (hAH : H < A) (hsqA : Squarefree A) (hBp : ∀ p ∈ A.primeFactors, B ≤ p)
    (hpD : ∀ p ∈ A.primeFactors, p ∣ fieldDisc f)
    (hpgt : ∀ p ∈ A.primeFactors, n < p) :
    f ∈ CaseIIIArithSet B n H := by
  classical
  have hfmon : f.Monic := hfbox.1
  have hdeg : f.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hfbox.2.1
  have hprime (p : ℕ) (hp : p ∈ A.primeFactors) : Nat.Prime p :=
    Nat.prime_of_mem_primeFactors hp
  -- per prime p | A : p | DD(u_f)
  have hconc (p : ℕ) (hp : p ∈ A.primeFactors) : (p : ℤ) ∣ concDDZ n (upperCoeffs n f) := by
    haveI : Fact (Nat.Prime p) := ⟨hprime p hp⟩
    exact prime_dvd_concDDZ_of_squarefull_fieldDisc f hfmon hdeg hn (hpgt p hp) (hpD p hp) hsq
  have hAd : (A : ℤ) ∣ concDDZ n (upperCoeffs n f) :=
    squarefree_prod_dvd_concDDZ_of_prime_dvd (u := upperCoeffs n f) hsqA hconc
  -- per prime p | A : p | Disc(f)
  have hdisc (p : ℕ) (hp : p ∈ A.primeFactors) : (p : ℤ) ∣ Polynomial.discr f := by
    haveI : Fact (Nat.Prime p) := ⟨hprime p hp⟩
    simpa [polyDisc] using (prime_dvd_polyDisc_of_dvd_fieldDisc f hfmon (p := p) (hpD p hp))
  exact mem_caseIIIArithSet_of_field_data n H B hn f hfbox hdd hAH hsqA hBp hAd hdisc

end Membership

end Submission.Vdw
