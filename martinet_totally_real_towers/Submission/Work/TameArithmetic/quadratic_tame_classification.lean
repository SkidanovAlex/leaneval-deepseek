import Mathlib
import Submission.Work.TameArithmetic.Defs
import Submission.Work.QuadraticFields.exists_squarefree_sq_eq_of_finrank_eq_two
import Submission.Work.QuadraticFields.two_dvd_discr_iff_mod_four_ne_one

/-!
# `Work.TameArithmetic.quadratic_tame_classification`

**Namespace** `Work.TameArithmetic`.

## The statement

Let `L/ℚ` be a **totally real Galois number field of degree two** whose relative different is
supported over the set `S = primesS = {17, 41, 73, 89, 97}` (every prime of `𝓞 L` dividing the
different lies over a prime of `S`).  Then there is an integer `d` with

* `0 < d`, `d` squarefree, `d ≡ 1 (mod 4)`;
* every prime divisor of `d` lies in `S`;
* `d` is a square in `L`, and indeed `L = ℚ(√d)`: there is `x ∈ L` with `x * x = d` (the rational
  number `d`, viewed in `L`) and `ℚ[x] = L`.

Equivalently: the `S`-tame totally real quadratic fields are exactly the fields `ℚ(√d)` with `d`
squarefree, `d ≡ 1 (mod 4)`, positive and supported on `S`.

## The mathematics

Write `L = ℚ(√d)` with `d` squarefree and `x ∈ L` with `x² = d`, `ℚ[x] = L`, as provided by
`Work.QuadraticFields.exists_squarefree_sq_eq_of_finrank_eq_two`; the discriminant of `L` is
`disc L = d · (if d % 4 = 1 then 1 else 4)` (`Work.QuadraticFields.discr_eq_of_sq_eq_squarefree`).
Then:

* **`0 < d`.**  `L` being totally real, it has a real infinite place `w`
  (`NumberField.InfinitePlace.embedding_of_isReal`); any ring homomorphism `φ : L →+* ℝ` sends
  `x² = d` to `φ x² = d`, and `φ x² ≥ 0` while `d ≠ 0` (squarefreeness).  This is the only place
  where total reality is used.
* **`d ≡ 1 (mod 4)`.**  If `d % 4 ≠ 1` then `2 ∣ disc L`
  (`Work.QuadraticFields.two_dvd_discr_iff_mod_four_ne_one`), so `2` divides the norm of the
  different and hence some prime `P` above `(2)` divides the different
  (`NumberField.not_dvd_discr_iff_forall_liesOver`, contraposed: `2 ∣ disc L` is the negation of
  "every prime above `(2)` is unramified").  By hypothesis `P` lies over `(q)` for some
  `q ∈ primesS`, whence `(2) = (q)`, i.e. `q = 2` — contradicting `q % 8 = 1`.
* **the prime divisors of `d`.**  In the case `d ≡ 1 (mod 4)` the discriminant *is* `d`, so a
  prime `p ∣ d` divides `disc L`, and the same argument produces a prime `P` above `(p)` dividing
  the different; the hypothesis gives `P` above `(q)` with `q ∈ primesS`, so `p = q ∈ primesS`.

## Relation with the chapter

This is the "elementary quadratic classification" of the tame Golod--Shafarevich route
(`Defs.lean`, `Assembly.lean`): it identifies the quadratic `S`-tame totally real extensions of `ℚ`
as the fields `ℚ(√d)` with `d` as above, which is what makes the generator number `d(Γ) = |S|` of
the maximal tame pro-`2` extension `Γ` computable from below.

## Implementation notes

The `ℚ`-algebra structure on a `NumberField` is *not* determined by the typeclass search in a way
that is definitionally compatible with an arbitrary `Algebra ℚ L` instance: the two structures are
equal (`Subsingleton (Algebra ℚ L)`), but only propositionally.  All results of
`Work.QuadraticFields` are stated for the canonical `DivisionRing.toRatAlgebra` structure, so the
proofs below begin by replacing the ambient instance by the canonical one via `subst` on the
equality `Subsingleton.elim`. -/

open scoped NumberField
open NumberField

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.TameArithmetic

/-- The different ideal of `ℤ ⊆ 𝓞 ℚ` is trivial: the prime field `ℚ` is unramified over `ℤ`, and
`(differentIdeal ℤ (𝓞 ℚ)).absNorm = (disc ℚ).natAbs = 1`. -/
theorem differentIdeal_int_ringOfIntegers_rat :
    differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ),
    NumberField.discr_rat]
  norm_num

/-- For a number field `M`, the different ideal over `ℤ` and over `𝓞 ℚ = ℤ` agree: they differ by
the (trivial) different of `ℤ ⊆ 𝓞 ℚ`, by the transitivity formula
`differentIdeal_eq_differentIdeal_mul_differentIdeal`. -/
theorem differentIdeal_int_eq {M : Type} [Field M] [NumberField M] [Algebra ℚ M] :
    differentIdeal ℤ (𝓞 M) = differentIdeal (𝓞 ℚ) (𝓞 M) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ) (𝓞 M),
    differentIdeal_int_ringOfIntegers_rat, Ideal.map_top]
  simp

/-- **A rational prime dividing the discriminant is the prime below a prime dividing the
different.**  If `p` is a rational prime with `p ∣ disc L`, then there is a prime ideal `P` of
`𝓞 L` above `(p)` which divides the different ideal `differentIdeal (𝓞 ℚ) (𝓞 L)`.

The input is Mathlib's `NumberField.not_dvd_discr_iff_forall_liesOver`: `p ∤ disc L` iff every
prime above `(p)` is unramified over `ℤ`, i.e. (by `dvd_differentIdeal_iff`) does not divide the
different.  The different over `ℤ` is replaced by the different over `𝓞 ℚ` using
`differentIdeal_int_eq`. -/
theorem exists_prime_dvd_different_of_dvd_discr {L : Type} [Field L] [NumberField L]
    [Algebra ℚ L] {p : ℤ} (hp : Prime p) (hpdvd : p ∣ NumberField.discr L) :
    ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P ≠ ⊥ ∧ P.LiesOver (Ideal.span ({p} : Set ℤ)) ∧
      P ∣ differentIdeal (𝓞 ℚ) (𝓞 L) := by
  have hA : (inferInstance : Algebra ℚ L) = (DivisionRing.toRatAlgebra : Algebra ℚ L) :=
    Subsingleton.elim _ _
  subst hA
  have hnp : ¬ (∀ (P : Ideal (𝓞 L)) (_ : P.IsMaximal),
      P.LiesOver (Ideal.span ({p} : Set ℤ)) → Algebra.IsUnramifiedAt ℤ P) := by
    intro h
    exact (NumberField.not_dvd_discr_iff_forall_liesOver (K := L) (𝒪 := 𝓞 L) hp).mpr h hpdvd
  push Not at hnp
  obtain ⟨P, hPmax, hLies, hunr⟩ := hnp
  haveI : P.IsPrime := hPmax.isPrime
  have hdvdZ : P ∣ differentIdeal ℤ (𝓞 L) :=
    (dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 L)).mpr hunr
  exact ⟨P, hPmax.isPrime, Ideal.IsMaximal.ne_bot_of_isIntegral_int P, hLies,
    by rwa [differentIdeal_int_eq] at hdvdZ⟩

/-- **Membership in `primesS` from the support hypothesis.**  If `P` is a prime of `𝓞 L` of residue
characteristic `p` dividing the different, then `p ∈ primesS`: the support hypothesis produces
`q ∈ primesS` with `P` also above `(q)`, so `(p) = (q)` (two primes over the same prime ideal of
`ℤ` are equal) and `p = q` since both are prime. -/
theorem mem_primesS_of_liesOver {L : Type} [Field L] [NumberField L] [Algebra ℚ L]
    {p : ℕ} (hp : Nat.Prime p) {P : Ideal (𝓞 L)}
    (hPprime : P.IsPrime) (hPbot : P ≠ ⊥)
    (hdvd : P ∣ differentIdeal (𝓞 ℚ) (𝓞 L))
    (hover : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (hsupp : ∀ P : Ideal (𝓞 L), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 ℚ) (𝓞 L) →
      ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    p ∈ primesS := by
  obtain ⟨q, hqmem, hqover⟩ := hsupp P hPprime hPbot hdvd
  have hspan : Ideal.span ({(p : ℤ)} : Set ℤ) = Ideal.span ({(q : ℤ)} : Set ℤ) :=
    hover.over.trans hqover.over.symm
  have hdiv : (q : ℤ) ∣ (p : ℤ) := by
    rw [← Ideal.mem_span_singleton, ← hspan]
    exact Ideal.mem_span_singleton.mpr dvd_rfl
  have hqn : q ∣ p := Int.natCast_dvd_natCast.mp hdiv
  have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq (primesS_prime q hqmem) hp).mp hqn
  rw [← hqeq]
  exact hqmem

/-- **The quadratic tame classification.**  A totally real quadratic number field whose different
is supported over `primesS` is `ℚ(√d)` for a squarefree `d ≡ 1 (mod 4)` with all prime divisors in
`primesS`. -/
theorem quadratic_tame_classification {L : Type} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (hfr : Module.finrank ℚ L = 2)
    (htr : NumberField.IsTotallyReal L)
    (hsupp : ∀ P : Ideal (NumberField.RingOfIntegers L), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) →
      ∃ q ∈ Work.TameArithmetic.primesS,
        P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    ∃ d : ℤ, 0 < d ∧ Squarefree d ∧ d % 4 = 1 ∧
      (∀ p : ℕ, Nat.Prime p → (p : ℤ) ∣ d → p ∈ Work.TameArithmetic.primesS) ∧
      ∃ x : L, x * x = algebraMap ℚ L (d : ℚ) ∧ Algebra.adjoin ℚ ({x} : Set L) = ⊤ := by
  -- replace the ambient `ℚ`-algebra structure by the canonical one, so that the results of
  -- `Work.QuadraticFields` (stated for `DivisionRing.toRatAlgebra`) apply
  have hA : (inferInstance : Algebra ℚ L) = (DivisionRing.toRatAlgebra : Algebra ℚ L) :=
    Subsingleton.elim _ _
  subst hA
  -- every quadratic field is `ℚ(√d)` with `d` squarefree
  obtain ⟨d, hdsq, x, hx, hgen⟩ :=
    Work.QuadraticFields.exists_squarefree_sq_eq_of_finrank_eq_two (K := L) hfr
  haveI htrI : NumberField.IsTotallyReal L := htr
  -- (A) `0 < d`, from total reality
  have hdpos : 0 < d := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace L))
    have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
    set φ : L →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hw with hφ
    have hval : φ x ^ 2 = (d : ℝ) := by
      rw [← map_pow, hx]
      norm_num
    have hnonneg : (0 : ℝ) ≤ (d : ℝ) := by
      rw [← hval]
      exact sq_nonneg _
    have hne : (d : ℝ) ≠ 0 := by
      exact_mod_cast hdsq.ne_zero
    exact Int.cast_pos.mp (lt_of_le_of_ne hnonneg (Ne.symm hne))
  -- (B) `d % 4 = 1`, from the unramifiedness of `2`
  have hd4 : d % 4 = 1 := by
    by_contra hne
    have h2dvd : (2 : ℤ) ∣ NumberField.discr L :=
      (Work.QuadraticFields.two_dvd_discr_iff_mod_four_ne_one hdsq x hx hgen).mpr hne
    obtain ⟨P, hPprime, hPbot, hLies, hPdvd⟩ :=
      exists_prime_dvd_different_of_dvd_discr (L := L) Int.prime_two h2dvd
    have h2S : 2 ∈ primesS :=
      mem_primesS_of_liesOver (L := L) Nat.prime_two hPprime hPbot hPdvd hLies hsupp
    have h8 := primesS_mod_eight 2 h2S
    norm_num at h8
  -- (C) the discriminant is `d`, and its prime divisors are in `S`
  have hdisc : NumberField.discr L = d :=
    Work.QuadraticFields.discr_eq_of_sq_eq_squarefree_of_emod_one hdsq hd4 x hx hgen hfr
  refine ⟨d, hdpos, hdsq, hd4, ?_, x, ?_, hgen⟩
  · intro p hp hpd
    have hpd' : (p : ℤ) ∣ NumberField.discr L := by
      rw [hdisc]; exact hpd
    obtain ⟨P, hPprime, hPbot, hLies, hPdvd⟩ :=
      exists_prime_dvd_different_of_dvd_discr (L := L) (Nat.prime_iff_prime_int.mp hp) hpd'
    exact mem_primesS_of_liesOver hp hPprime hPbot hPdvd hLies hsupp
  · rw [← pow_two]
    exact hx

end Work.TameArithmetic
