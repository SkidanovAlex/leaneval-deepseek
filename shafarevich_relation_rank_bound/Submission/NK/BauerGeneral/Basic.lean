import Mathlib
import Submission.NK.ReconstructField.Basic
import Submission.NK.UchidaKummer.Defs
import Submission.NK.ReconstructField.sum_localDeg_primesOver
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_le_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one

/-!
# `Submission/Work/BauerGeneral/` — Bauer's theorem for arbitrary number fields

This chapter removes the `IsGalois ℚ K` hypotheses from the Galois case of Bauer's theorem
(`NK.ReconstructField.exists_ringEquiv_of_isGalois_of_splitsCompletely_iff`) and, more
importantly, records precisely what the completely split primes of a number field do and do not
determine.

## The convention

`NK.ReconstructField.SplitsCompletely K L p` is
`(p.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L`, i.e. *every* prime of `𝓞 L` above `p` is
unramified of residue degree one.  For an arbitrary (not necessarily normal) finite extension
`L/K` of number fields this is equivalent to "every prime above `p` has local degree one"
(`NK.BauerGeneral.splitsCompletely_iff_forall_localDeg_eq_one`), which is the operational form of
the predicate used throughout this chapter.

## The main structural results

* `NK.BauerGeneral.splitsCompletely_conjugateCompositum` (module
  `Submission.NK.BauerGeneral.splitsCompletely_conjugateCompositum`): for `N ⊆ L` a number field
  inside a finite Galois `L/ℚ`, a prime splits completely in `N` if and only if it splits completely
  in the compositum of the conjugates `NK.BauerGeneral.conjugateCompositum N` — the normal closure
  of `N` in `L`.
* `NK.BauerGeneral.conjugateCompositum_eq_of_splitsCompletely_iff` (module
  `Submission.NK.BauerGeneral.GaloisClosureDetermines`): two number fields with the same completely
  split primes have the same normal closure; and
  `NK.BauerGeneral.normalClosure_eq_of_splitsCompletely_iff` (module
  `Submission.NK.BauerGeneral.normalClosure_eq_of_splitsCompletely_iff`) is the same statement for
  the normal closure inside `AlgebraicClosure ℚ`.

The false statement which the *requested* form of the weak Neukirch–Uchida theorem would need — two
number fields with the same completely split primes are isomorphic — is refuted in
`Submission/Work/BauerGeneral/not_weakNeukirchUchida_of_splitsCompletely_iff.lean`
(`NK.BauerGeneral.not_weakNeukirchUchida_of_splitsCompletely_iff`, with the counterexample
`ℚ(∛2)` vs. `ℚ(∛2, ζ₃)` built from
`NK.BauerGeneral.exists_numberField_not_isGalois`).

Reference: J. Neukirch, *Algebraic Number Theory*, VII §8 (Bauer's theorem); J. Neukirch,
A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–12.2.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.BauerGeneral

open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The set of finite primes of `K` splitting completely in the number field `L`
(`NK.ReconstructField.SplitsCompletely`, in set form). -/
def splitPrimes (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
    [Algebra K L] : Set (NK.Chebotarev.PrimeIdeal K) :=
  {p | NK.ReconstructField.SplitsCompletely K L p}

@[simp] theorem mem_splitPrimes {p : NK.Chebotarev.PrimeIdeal K} :
    p ∈ splitPrimes K L ↔ NK.ReconstructField.SplitsCompletely K L p := Iff.rfl

/-- A finite sum of natural numbers, each at least `1`, which is equal to the number of terms, is a
sum of ones. -/
theorem eq_one_of_sum_eq_card {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h1 : ∀ i ∈ s, 1 ≤ f i) (h : ∑ i ∈ s, f i = s.card) : ∀ i ∈ s, f i = 1 := by
  classical
  have hsum : ∑ i ∈ s, ((f i : ℤ) - 1) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1' : ∑ i ∈ s, (f i : ℤ) = (s.card : ℤ) := by
      rw [← Nat.cast_sum, h]
    have h2' : ∑ i ∈ s, (1 : ℤ) = (s.card : ℤ) := by
      simp
    rw [h1', h2', sub_self]
  intro i hi
  have hzero : (f i : ℤ) - 1 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j hj =>
      sub_nonneg.mpr (by exact_mod_cast h1 j hj))).mp hsum i hi
  have : (f i : ℤ) = 1 := sub_eq_zero.mp hzero
  exact_mod_cast this

/-- **Splitting completely is "all local degrees are one"**, for an arbitrary finite extension of
number fields (no normality or Galois hypothesis).

This is the operational form of `SplitsCompletely`: it is the sum formula
`∑_{Q | p} e(Q|p) f(Q|p) = [L : K]` (`NK.ReconstructField.sum_localDeg_primesOver`) together
with the trivial bound `#{Q | p} ≤ [L : K]` (`Ideal.ncard_primesOver_le_finrank`). -/
theorem splitsCompletely_iff_forall_localDeg_eq_one (p : NK.Chebotarev.PrimeIdeal K) :
    NK.ReconstructField.SplitsCompletely K L p ↔
      ∀ Q : NK.Chebotarev.PrimeIdeal L, Q.asIdeal.LiesOver p.asIdeal →
        NK.UchidaKummer.localDeg Q p = 1 := by
  classical
  have hsum := NK.ReconstructField.sum_localDeg_primesOver (K := K) (L := L) p
  have hpos : ∀ Q : p.asIdeal.primesOver (NumberField.RingOfIntegers L),
      1 ≤ NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩ p := by
    intro Q
    haveI : Q.1.IsPrime := Q.2.1
    rw [NK.UchidaKummer.localDeg]
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero
        (Nat.pos_iff_ne_zero.mp (Ideal.ramificationIdx_pos
          (R := NumberField.RingOfIntegers K) (q := Q.1)))
        (Nat.pos_iff_ne_zero.mp (Ideal.inertiaDeg_pos
          (R := NumberField.RingOfIntegers K) (q := Q.1))))
  constructor
  · intro h Q hQ
    have hsum' : ∑ Q : p.asIdeal.primesOver (NumberField.RingOfIntegers L),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩ p =
        (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard := by
      rw [hsum, h]
    have hall := eq_one_of_sum_eq_card Finset.univ _ (fun Q _ => hpos Q) (by simpa using hsum')
    exact hall ⟨Q.asIdeal, Q.2, hQ⟩ (Finset.mem_univ _)
  · intro h
    rw [NK.ReconstructField.SplitsCompletely, ← hsum]
    have hone : ∀ Q : p.asIdeal.primesOver (NumberField.RingOfIntegers L),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩ p = 1 :=
      fun Q => h ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩ Q.2.2
    rw [Finset.sum_congr rfl (fun Q _ => hone Q), Finset.sum_const, Finset.card_univ,
      Set.fintypeCard_eq_ncard, smul_eq_mul, mul_one]

end NK.BauerGeneral
