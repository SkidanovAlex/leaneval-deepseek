import Mathlib
import Submission.Vdw.CaseIDisc
import Submission.Vdw.CaseISieve
import Submission.Vdw.CaseI
import Submission.Vdw.ResidueCompare
import Submission.Vdw.LocalField.WildGlobalTrace

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case-I small-prime exponent cap (the S1 output, unconditional)

With the S1 gate closed (`LocalField.WildGlobalTrace.discrVal_le_wild_unconditional`:
for every prime `p` and number field `K`,
`v_p(|disc K|) ≤ [K:ℚ]·(1 + ⌊log_p [K:ℚ]⌋)`), the exponent of every *small*
prime `p ≤ n` in the field discriminant `D_f = |Disc K_f|` of a monic
irreducible degree-`n` polynomial is bounded by a constant depending on `n`
alone:

    ∀ p ∈ (fieldDisc f).primeFactors, p ≤ n ⟹
      (fieldDisc f).factorization p ≤ n + n·⌊log_2 n⌋.

Consequently the small-prime part `discSmallPart n (fieldDisc f)` of the
discriminant is bounded by `S₀(n) := primorial n ^ (n + n·⌊log_2 n⌋)`
(`CaseIDisc.discSmallPart_le_primorial_pow`), the "constant in `n`" input of
the Case-I direct-regime summation.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- `Nat.log` is antitone on the base (`2 ≤ p`). -/
lemma nat_log_le_log_two (p n : ℕ) (hp : 2 ≤ p) : Nat.log p n ≤ Nat.log 2 n := by
  have hp1 : 1 < p := by omega
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have h2 : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
  have hle : 2 ^ (Nat.log 2 n).succ ≤ p ^ (Nat.log 2 n).succ := Nat.pow_le_pow_left hp _
  have h : n < p ^ (Nat.log 2 n).succ := lt_of_lt_of_le h2 hle
  have hlt : Nat.log p n < (Nat.log 2 n).succ :=
    (Nat.log_lt_iff_lt_pow hp1 (y := n) (x := (Nat.log 2 n).succ) (by omega)).mpr h
  omega

/-- **Small-prime exponent cap for the field discriminant**: a prime `p ≤ n`
dividing `D_f` divides it to exponent at most `n + n·⌊log_2 n⌋`. -/
theorem fieldDisc_factorization_le_of_small (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) (n : ℕ) (hdeg : f.natDegree = n) :
    ∀ p ∈ (fieldDisc f).primeFactors, p ≤ n →
      (fieldDisc f).factorization p ≤ n + n * Nat.log 2 n := by
  intro p hp hpn
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  have hfac : (fieldDisc f).factorization p = padicValNat p (fieldDisc f) :=
    Nat.factorization_def (fieldDisc f) hpp
  rw [hfac]
  have hmain := LocalField.discrVal_le_wild_unconditional (K := Kpoly f) p
  have hfr : Module.finrank ℚ (Kpoly f) = n := by
    rw [finrank_kpoly_eq_natDegree f hf, hdeg]
  rw [hfr] at hmain
  have hlog : Nat.log p n ≤ Nat.log 2 n := nat_log_le_log_two p n hpp.two_le
  calc padicValNat p (fieldDisc f)
      = padicValNat p (NumberField.discr (Kpoly f)).natAbs := by simp only [fieldDisc]
    _ ≤ n + n * Nat.log p n := hmain
    _ ≤ n + n * Nat.log 2 n := Nat.add_le_add_left (Nat.mul_le_mul_left n hlog) n

/-- **The small-prime part of a field discriminant is bounded in terms of `n`
alone**: `discSmallPart n (fieldDisc f) ≤ primorial n ^ (n + n·⌊log_2 n⌋)`. -/
theorem discSmallPart_fieldDisc_le (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) (n : ℕ) (hdeg : f.natDegree = n) :
    discSmallPart n (fieldDisc f) ≤ primorial n ^ (n + n * Nat.log 2 n) :=
  discSmallPart_le_primorial_pow n (n + n * Nat.log 2 n) (fieldDisc f)
    (fun p hp hpn => fieldDisc_factorization_le_of_small f hf n hdeg p hp hpn)

end Submission.Vdw
