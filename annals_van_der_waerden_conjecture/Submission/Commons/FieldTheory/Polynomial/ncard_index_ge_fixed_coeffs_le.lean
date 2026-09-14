import Mathlib
import Submission.Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le_algClosed
import Submission.Commons.FieldTheory.Polynomial.finite_inS_algClosed

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Polynomial

open Polynomial

/-- The degree of the radical of a polynomial does not increase when the polynomial is
pushed forward along a ring homomorphism of fields.

Equivalently: a polynomial over a field `K` acquires no new *distinct* roots after extending
scalars to a larger field `L`.  The proof uses
`p ∣ radical p ^ m` for some `m`, which transports to `p.map f ∣ (radical p).map f ^ m`, whence
`radical (p.map f) ∣ (radical p).map f`. -/
lemma radical_map_natDegree_le {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]
    (f : K →+* L) (p : Polynomial K) (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.radical (p.map f)).natDegree ≤
      (UniqueFactorizationMonoid.radical p).natDegree := by
  classical
  have hpf : p.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hp
  have hradne : UniqueFactorizationMonoid.radical p ≠ 0 := UniqueFactorizationMonoid.radical_ne_zero
  obtain ⟨m, hm⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hp
  have hdvd : p.map f ∣ ((UniqueFactorizationMonoid.radical p) ^ m).map f :=
    Polynomial.map_dvd f hm
  rw [Polynomial.map_pow] at hdvd
  have hrad_dvd : UniqueFactorizationMonoid.radical (p.map f) ∣
      (UniqueFactorizationMonoid.radical p).map f :=
    (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hpf).mp ⟨m, hdvd⟩
  have hne : (UniqueFactorizationMonoid.radical p).map f ≠ 0 :=
    (Polynomial.map_ne_zero_iff f.injective).mpr hradne
  calc (UniqueFactorizationMonoid.radical (p.map f)).natDegree
      ≤ ((UniqueFactorizationMonoid.radical p).map f).natDegree :=
        Polynomial.natDegree_le_of_dvd hrad_dvd hne
    _ = (UniqueFactorizationMonoid.radical p).natDegree :=
        Polynomial.natDegree_map_eq_of_injective f.injective _

/-- The number of monic degree `n` polynomials over a field `K` whose coefficients at the `n - k`
top positions `k, k+1, …, n-1` are prescribed and whose index (i.e. `n` minus the degree of the
radical) is at least `k` is at most `(n + 1) · n! · 2ⁿ`, provided `char K ∤ n!`.

This is proved by extending scalars to an algebraic closure `K̄`, where it is
`ncard_index_ge_fixed_coeffs_le_algClosed`; the map `P ↦ P.map (algebraMap K K̄)` is injective
and preserves all the defining conditions (the radical degree never increases by
`radical_map_natDegree_le`). -/
theorem ncard_index_ge_fixed_coeffs_le (K : Type) [Field K] [DecidableEq K] (n k : ℕ) (hk : k ≤ n)
    (hchar : (Nat.factorial n : K) ≠ 0) (a : Fin (n - k) → K) :
    Nat.card {P : Polynomial K // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = a i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} ≤
      (n + 1) * Nat.factorial n * 2 ^ n := by
  classical
  let L := AlgebraicClosure K
  let b : Fin (n - k) → L := fun i => algebraMap K L (a i)
  have hcharL : (Nat.factorial n : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L) (Nat.factorial n)]
    exact fun h => hchar ((algebraMap K L).injective (by rw [h, map_zero]))
  haveI : IsAlgClosed L := AlgebraicClosure.isAlgClosed K
  have hbound := ncard_index_ge_fixed_coeffs_le_algClosed L n k hk hcharL b
  haveI hfin : Finite {P : Polynomial L // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = b i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} :=
    finite_inS_algClosed n k hk hcharL b
  let g : {P : Polynomial K // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = a i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} →
      {P : Polynomial L // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = b i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} :=
    fun P => ⟨P.1.map (algebraMap K L),
      P.2.1.map _,
      (Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective P.1).trans P.2.2.1,
      fun i => by rw [Polynomial.coeff_map, P.2.2.2.1 i],
      by
        have h := radical_map_natDegree_le (algebraMap K L) P.1 P.2.1.ne_zero
        have hk' := P.2.2.2.2
        omega⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    have hh : P.1.map (algebraMap K L) = Q.1.map (algebraMap K L) := congrArg Subtype.val hPQ
    exact Polynomial.map_injective (f := algebraMap K L) (algebraMap K L).injective hh
  calc Nat.card {P : Polynomial K // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = a i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree}
      ≤ Nat.card {P : Polynomial L // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = b i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} :=
        Nat.card_le_card_of_injective g hg
    _ ≤ (n + 1) * Nat.factorial n * 2 ^ n := hbound

end Commons.FieldTheory.Polynomial
