import Mathlib
import Submission.Vdw.CaseIExact
import Submission.Vdw.CaseIDisc
import Submission.Vdw.RestrictedSieve
import Submission.Vdw.ResidueIndex
import Submission.Vdw.IndexBounded

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case-I direct regime: clean restricted per-`D` bound (the (α) exact form)

`CaseISieve.restrictedPerDiscriminant_box_le` bounds the restricted sieve set
of a discriminant value `D` (index conditions at the *large* primes `p | D`,
`p > n`) in raw form.  This module converts it into the exact
`O(c^(ω(D*))·H^n/D*)` form the squarefull summation consumes: writing
`D* := discLargePart n D = ∏_{p | D, p > n} p^(v_p(D))` (the large-prime
part, `CaseIDisc`), the restricted sieve of `D` IS the full per-discriminant
sieve of `D*` (its prime support is exactly `{p | D : p > n}`, and its
exponents equal `v_p(D)` — `RestrictedSieve.primeFactors_discLargePart`,
`RestrictedSieve.factorization_discLargePart`).  Hence, under the two
hypotheses that are automatic for a real `D = D_f = fieldDisc f`
(`rad D* ≤ rad D_f = C_f ≤ H`; and `v_p(D*) < n` for `p | D*`, since
`v_p(D_f) ≤ polyIndex(f̄) ≤ n − 1` by Lemma 24 field at primes `p > n`),
`perDiscriminant_exact_le` applied to `D*` gives the clean bound.
-/

namespace Submission.Vdw

/-- **Restricted per-`D` sieve bound, exact clean form (the (α) layer
output).**  For `1 ≤ n`, `1 ≤ H`, `D ≠ 0`, with the large-prime modulus
`C_{>n}(D) = radical (discLargePart n D) ≤ H` and all large-prime exponents
`v_p(D) < n`: the number of degree-`n` box polynomials whose residue index at
every large prime `p | D` (`p > n`) is at least `min (v_p(D)) n` is at most

    4^n · 2^(((n+1)^4)·ω(D*)) · H^n / D*,     D* := discLargePart n D

— Bhargava's Case-I per-`D` estimate in the elementary regime, restricted to
the primes that Lemma 24 (field) controls.  (For real `D = D_f`,
`D*.factorization p = D.factorization p = v_p(D)` by
`RestrictedSieve.factorization_discLargePart`, so the condition is exactly
`index_{F_p}(f̄) ≥ v_p(D)` at `p > n`, which every `f` with `fieldDisc f = D`
satisfies by `RestrictedSieve.restrictedSieve_entry`.) -/
theorem restrictedPerDiscriminant_exact_le (n H : ℕ) (_hn : 1 ≤ n) (hH : 1 ≤ H) (D : ℕ)
    (hD : D ≠ 0) (hC : radical (discLargePart n D) ≤ H)
    (hsmall : ∀ p ∈ (discLargePart n D).primeFactors,
      (discLargePart n D).factorization p < n) :
    (Nat.card {f : ↥(Box n H) // ∀ p : (discLargePart n D).primeFactors,
        indexClass (F := ZMod (p : ℕ)) n
          (min ((discLargePart n D).factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
      (4 : ℝ) ^ n *
        (2 : ℝ) ^ (((n + 1) ^ 4) * ((discLargePart n D).primeFactors).card) *
        (H : ℝ) ^ n / ((discLargePart n D : ℕ) : ℝ) := by
  classical
  let Dstar : ℕ := discLargePart n D
  have hDstar : Dstar ≠ 0 := by
    dsimp [Dstar]
    exact Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (discLargePart_dvd n D hD) (Nat.pos_of_ne_zero hD))
  have hsmallstar : ∀ p ∈ Dstar.primeFactors, Dstar.factorization p < n := by
    simpa [Dstar] using hsmall
  have hCstar : radical Dstar ≤ H := by
    simpa [Dstar] using hC
  -- the restricted sieve of D is exactly the full per-discriminant sieve of D*
  simpa [Dstar] using (perDiscriminant_exact_le n H (by omega : 1 ≤ n) hH Dstar hDstar hCstar hsmallstar)


/-- **Real-polynomial entry into the restricted sieve set.**  For a monic
irreducible box polynomial `f` (degree `n ≥ 1`), `f` itself satisfies every
restricted sieve condition of its own field discriminant `D = D_f = fieldDisc
f`: at each large prime `p | D` (`p > n`) the residue index of `f` mod `p` is
at least `min (v_p(D), n)` — per prime, `restrictedSieve_entry` (Lemma 24,
field) gives `index ≥ v_p(D) = D.factorization p = D*.factorization p`
(`factorization_discLargePart`), and `min (v_p(D), n) ≤ v_p(D)`.  Hence
`f` lies in the counted set of `restrictedPerDiscriminant_exact_le` at
`D = fieldDisc f`. -/
theorem mem_restrictedSieve_of_fieldDisc (n H : ℕ) (_hn : 1 ≤ n) (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfbox : f ∈ Box n H) :
    ∀ p : (discLargePart n (fieldDisc f)).primeFactors,
      indexClass (F := ZMod (p : ℕ)) n
        (min ((discLargePart n (fieldDisc f)).factorization (p : ℕ)) n)
        (boxResidue n H (p : ℕ) ⟨f, hfbox⟩) := by
  classical
  intro p
  have hD0 : fieldDisc f ≠ 0 := by
    unfold fieldDisc
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Kpoly f))
  have hltD : n < (p : ℕ) ∧ (p : ℕ) ∣ fieldDisc f :=
    mem_primeFactors_discLargePart hD0 p.2
  have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hpp⟩
  have hfac : (fieldDisc f).factorization (p : ℕ) =
      (discLargePart n (fieldDisc f)).factorization (p : ℕ) :=
    factorization_discLargePart hD0 p.2
  have hind0 : (fieldDisc f).factorization (p : ℕ) ≤
      boxIndex (p : ℕ) n H ⟨f, hfbox⟩ := by
    have he := restrictedSieve_entry f hf hdeg _hn (p := (p : ℕ)) hltD.1 hltD.2
    simpa [boxIndex, reductionPoly] using he
  have hineq : min ((discLargePart n (fieldDisc f)).factorization (p : ℕ)) n ≤
      boxIndex (p : ℕ) n H ⟨f, hfbox⟩ := by
    calc
      min ((discLargePart n (fieldDisc f)).factorization (p : ℕ)) n
          ≤ (discLargePart n (fieldDisc f)).factorization (p : ℕ) := Nat.min_le_left _ _
      _ = (fieldDisc f).factorization (p : ℕ) := hfac.symm
      _ ≤ boxIndex (p : ℕ) n H ⟨f, hfbox⟩ := hind0
  exact (boxIndex_iff_indexClass (p : ℕ) n H
    (min ((discLargePart n (fieldDisc f)).factorization (p : ℕ)) n) ⟨f, hfbox⟩).mp hineq


/-- **`v_p(D_f) < n` is automatic for real `f` at large primes.**  For a monic
irreducible box polynomial `f` (degree `n`) and a prime `p > n` dividing
`D_f = fieldDisc f`: the exponent `v_p(D_f) = D_f.factorization p` is `< n`,
because `restrictedSieve_entry` (Lemma 24, field) gives
`v_p(D_f) ≤ index_{F_p}(f̄)` and the index of a degree-`n` polynomial is at
most `n − 1` (`polyIndex_le_sub_one`).  This is exactly the `hsmall`
hypothesis of `restrictedPerDiscriminant_exact_le` (in the
`D*.factorization` spelling it is automatic for every real `D = D_f`). -/
theorem fieldDisc_factorization_lt_of_prime_gt (n H : ℕ) (_hn : 1 ≤ n) (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfbox : f ∈ Box n H) {p : ℕ} [Fact (Nat.Prime p)] (hpgt : n < p)
    (hpD : p ∣ fieldDisc f) :
    (fieldDisc f).factorization p < n := by
  classical
  have hind0 : (fieldDisc f).factorization p ≤ boxIndex p n H ⟨f, hfbox⟩ := by
    have he := restrictedSieve_entry f hf hdeg _hn (p := p) hpgt hpD
    simpa [boxIndex, reductionPoly] using he
  have hle1 : boxIndex p n H ⟨f, hfbox⟩ ≤ n - 1 := by
    have hmon : (reductionPoly p n H ⟨f, hfbox⟩).Monic := reductionPoly_monic p n H ⟨f, hfbox⟩
    have hdeg1 : 1 ≤ (reductionPoly p n H ⟨f, hfbox⟩).natDegree := by
      rw [reductionPoly_natDegree p n H ⟨f, hfbox⟩]
      exact _hn
    have hsub := polyIndex_le_sub_one (F := ZMod p) (reductionPoly p n H ⟨f, hfbox⟩) hmon hdeg1
    rw [reductionPoly_natDegree p n H ⟨f, hfbox⟩] at hsub
    simpa [boxIndex] using hsub
  omega

end Submission.Vdw
