import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.CFTLib.IdeleHasse.Descent

open NumberField IsDedekindDomain

/-- If a natural number `p` divides the (absolute value of the) value of the `k`-th cyclotomic
polynomial at `P`, then `P` is a root of `Φ_k` in `ZMod p`. -/
private lemma isRoot_cyclotomic_zmod_of_dvd_natAbs {k P p : ℕ}
    (hdiv : p ∣ ((Polynomial.cyclotomic k ℤ).eval (P : ℤ)).natAbs) :
    (Polynomial.cyclotomic k (ZMod p)).IsRoot (P : ZMod p) := by
  have hval : (((Polynomial.cyclotomic k ℤ).eval (P : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.mpr hdiv))
  refine Polynomial.IsRoot.def.mpr ?_
  rw [← Polynomial.map_cyclotomic_int k (ZMod p), Polynomial.eval_map,
    show (P : ZMod p) = Int.castRingHom (ZMod p) (P : ℤ) by simp,
    Polynomial.eval₂_hom, Int.coe_castRingHom]
  exact hval

/-- For `1 < n` and `0 < N` there is a prime `q` not dividing `n` whose multiplicative order of
`n` modulo `q` is divisible by `N`; here `orderOf` is taken in the multiplicative monoid
`ZMod q`, where `q ∤ n` makes `n` a unit.

PROOF PLAN (Zsigmondy-lite, no Zsigmondy in Mathlib; use the cyclotomic-product lemmas in
`Mathlib/RingTheory/Polynomial/Cyclotomic/Expand.lean`).

Write `Φ_e = Polynomial.cyclotomic e`.

Step 1 (`N = 1`): take any prime `q > n`; `1 ∣ orderOf` is trivial.

Step 2 (`2 ≤ N`): pick a prime `M > max N n` such that `orderOf ((n : ZMod M)) ∤ N`.
Such `M` exists: if `orderOf ((n:ZMod M)) ∣ N` for *every* prime `M > max N n`, then
`M ∣ n^N - 1` for all those `M` (note `M ∤ n`), while there are infinitely many such `M` but
only finitely many primes below `n^N`.  (Concretely: choose a prime `M > max (max N n) (n^N - 1)`.)

Step 3: put `e := N * M` and take a prime `q` dividing `(Φ_e.eval (n : ℤ)).natAbs`.  This is
`≥ 2` because `n - 1 < (Φ_e.eval n).natAbs` (`Polynomial.sub_one_lt_natAbs_cyclotomic_eval`,
needs `1 < e`).

Step 4: show `q ∤ e`.
* `q ∤ n`: otherwise `(Φ_e.eval (n:ℤ) : ZMod q) = 0`, but `Φ_e(0) = 1` for `e ≥ 2`
  (`Polynomial.cyclotomic_coeff_zero`), and `n ≡ 0` mod `q`, so `0 = 1`.
* `q ≠ M`: if `M ∣ Φ_e(n)` then `M ∣ n^e - 1` (from `cyclotomic.dvd_X_pow_sub_one`), so
  `orderOf ((n:ZMod M)) ∣ e = N*M`; and `orderOf ((n:ZMod M)) ∣ M - 1`
  (`ZMod.orderOf_dvd_card_sub_one`, since `M ∤ n`); hence it divides
  `Nat.gcd (N*M) (M-1) = Nat.gcd N (M-1)`, hence divides `N`, contradicting Step 2.
* `q ∤ N`: let `a := (N).factorization q ≥ 1` and `e' := e / q^a`, so `q ∤ e'` and
  `e' = (N/q^a) * M ≥ M`.  Working in `(ZMod q)[X]` (`CharP (ZMod q) q`), the identities
  `Polynomial.cyclotomic_mul_prime_dvd_eq_pow` (`q ∣ n ⟹ Φ_{n q} = Φ_n ^ q`) and
  `Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd` (`q ∤ n ⟹ Φ_{n q} = Φ_n ^ (q-1)`) give
  `Φ_e = Φ_{e'} ^ (q^a - q^(a-1))`; evaluating at `n` shows `q ∣ Φ_{e'}(n)`.
  Now `isRoot_cyclotomic_iff` yields `IsPrimitiveRoot ((n:ℕ) : ZMod q) e'`, hence
  `orderOf ((n : ZMod q)) = e'` (`IsPrimitiveRoot.eq_orderOf`).  But
  `orderOf ((n : ZMod q)) ∣ q - 1` (`ZMod.orderOf_dvd_card_sub_one`, using `q ∤ n`) and
  `q - 1 < q ≤ N < M ≤ e'`, contradiction.

Step 5: `q ∤ e` and `q | Φ_e(n)` give, again via `isRoot_cyclotomic_iff`,
`IsPrimitiveRoot ((n:ℕ) : ZMod q) e`, hence `orderOf ((n : ZMod q)) = e = N * M`, which is
divisible by `N`.  Done. -/
theorem exists_prime_dvd_orderOf (n N : ℕ) (hn : 1 < n) (hN : 0 < N) :
    ∃ q : ℕ, q.Prime ∧ ¬ q ∣ n ∧ N ∣ orderOf ((n : ZMod q)) := by
  have hn0 : 0 < n := by omega
  -- Step 2: the auxiliary prime `M`
  obtain ⟨M, hMge, hMprime⟩ := Nat.exists_infinite_primes (max (max N n) (n ^ N - 1) + 1)
  have hKN : N ≤ max (max N n) (n ^ N - 1) := le_trans (le_max_left N n) (le_max_left _ _)
  have hKn : n ≤ max (max N n) (n ^ N - 1) := le_trans (le_max_right N n) (le_max_left _ _)
  have hKlt : n ^ N - 1 ≤ max (max N n) (n ^ N - 1) := le_max_right _ _
  have hMN : N < M := by omega
  have hMn : n < M := by omega
  have hMlt : n ^ N - 1 < M := by omega
  have hMgood : ¬ orderOf ((n : ZMod M)) ∣ N := by
    intro hdvd
    have hpow : (n : ZMod M) ^ N = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    have hcast : ((n ^ N : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) := by
      rw [Nat.cast_pow, Nat.cast_one]; exact hpow
    have hmod : n ^ N ≡ 1 [MOD M] := (ZMod.natCast_eq_natCast_iff (n ^ N) 1 M).mp hcast
    have hone : 1 ≤ n ^ N := by
      calc 1 ≤ n := by omega
        _ = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ N := Nat.pow_le_pow_right hn0 (by omega)
    have hdvdN : M ∣ n ^ N - 1 := (Nat.modEq_iff_dvd' hone).mp hmod.symm
    have hpos : 0 < n ^ N - 1 := by
      have : 2 ≤ n ^ N := by
        calc 2 ≤ n := by omega
          _ = n ^ 1 := (pow_one n).symm
          _ ≤ n ^ N := Nat.pow_le_pow_right hn0 (by omega)
      omega
    have := Nat.le_of_dvd hpos hdvdN
    omega
  -- Step 3: the exponent `e = N * M` and a prime `q ∣ Φ_e(n)`
  set e : ℕ := N * M with he
  have he1 : 1 < e := by
    have h1 : M ≤ e := by rw [he]; exact Nat.le_mul_of_pos_left M hN
    have h2 : 2 ≤ M := hMprime.two_le
    omega
  set A : ℕ := ((Polynomial.cyclotomic e ℤ).eval (n : ℤ)).natAbs with hA
  have hbig : n - 1 < A := by
    rw [hA]; exact Polynomial.sub_one_lt_natAbs_cyclotomic_eval he1 (by omega)
  have hA2 : 2 ≤ A := by omega
  obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd (by omega : A ≠ 1)
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hq2 : 2 ≤ q := hqprime.two_le
  have hroot : (Polynomial.cyclotomic e (ZMod q)).IsRoot (n : ZMod q) :=
    isRoot_cyclotomic_zmod_of_dvd_natAbs (k := e) (P := n) (p := q) (by rw [← hA]; exact hqdiv)
  -- Step 4, first bullet: `q ∤ n`
  have hqn : ¬ q ∣ n := by
    intro hdvd
    have hn0' : (n : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff n q).mpr hdvd
    have h0 : (Polynomial.cyclotomic e (ZMod q)).eval (n : ZMod q) = 0 :=
      Polynomial.IsRoot.def.mp hroot
    rw [hn0'] at h0
    have hcoeff : (Polynomial.cyclotomic e (ZMod q)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]; exact h0
    have hone : (Polynomial.cyclotomic e (ZMod q)).coeff 0 = 1 :=
      Polynomial.cyclotomic_coeff_zero (ZMod q) he1
    rw [hone] at hcoeff
    exact one_ne_zero hcoeff
  -- Step 4, second bullet: `q ≠ M`
  have hqM : q ≠ M := by
    intro hqMeq
    haveI : Fact M.Prime := ⟨hMprime⟩
    have hMdvd : M ∣ A := hqMeq ▸ hqdiv
    have hrootM : (Polynomial.cyclotomic e (ZMod M)).IsRoot (n : ZMod M) :=
      isRoot_cyclotomic_zmod_of_dvd_natAbs (k := e) (P := n) (p := M)
        (by rw [← hA]; exact hMdvd)
    have hpow : (n : ZMod M) ^ e = 1 := by
      have h1 : (Polynomial.cyclotomic e (ZMod M)).eval (n : ZMod M) = 0 :=
        Polynomial.IsRoot.def.mp hrootM
      obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one e (ZMod M)
      have h2 : Polynomial.eval (n : ZMod M) (Polynomial.X ^ e - 1) = 0 := by
        rw [hg, Polynomial.eval_mul, h1, zero_mul]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h2
      exact sub_eq_zero.mp h2
    have hord1 : orderOf ((n : ZMod M)) ∣ e := (orderOf_dvd_iff_pow_eq_one).mpr hpow
    have hnM0 : (n : ZMod M) ≠ 0 := by
      intro h
      have hMn : M ∣ n := (ZMod.natCast_eq_zero_iff n M).mp h
      have := Nat.le_of_dvd hn0 hMn
      omega
    have hord2 : orderOf ((n : ZMod M)) ∣ M - 1 := ZMod.orderOf_dvd_card_sub_one hnM0
    refine hMgood ?_
    have hord1' : orderOf ((n : ZMod M)) ∣ N * M := he ▸ hord1
    have hM1 : 1 ≤ M := by have := hMprime.two_le; omega
    have hNm1 : N * (M - 1) = N * M - N := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    have hsub : N * M - N * (M - 1) = N := by
      rw [hNm1]
      exact Nat.sub_sub_self (by simpa using Nat.mul_le_mul_left N hM1)
    have hd : orderOf ((n : ZMod M)) ∣ N * M - N * (M - 1) :=
      Nat.dvd_sub hord1' (dvd_mul_of_dvd_right hord2 N)
    exact hsub ▸ hd
  -- `q ∤ M`
  have hqMdvd : ¬ q ∣ M := by
    intro h
    rcases hMprime.eq_one_or_self_of_dvd q h with h1 | h1
    · exact hqprime.ne_one h1
    · exact hqM h1
  -- Step 4, third bullet: `q ∤ N`
  have hqN : ¬ q ∣ N := by
    intro hqNdvd
    obtain ⟨a, m, hmnot, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hqprime.ne_one
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, pow_zero, one_mul] at hNm
      rw [hNm] at hqNdvd
      exact hmnot hqNdvd
    have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hNm
        omega
      · exact h
    have he_eq : e = q ^ a * (m * M) := by
      rw [he, hNm]; ring
    have hmm : ¬ q ∣ m * M := hqprime.not_dvd_mul hmnot hqMdvd
    haveI : NeZero (((m * M : ℕ) : ZMod q)) :=
      ⟨fun h => hmm ((ZMod.natCast_eq_zero_iff (m * M) q).mp h)⟩
    have hroot' : (Polynomial.cyclotomic (q ^ a * (m * M)) (ZMod q)).IsRoot (n : ZMod q) := by
      rw [← he_eq]; exact hroot
    have hpr : IsPrimitiveRoot ((n : ZMod q)) (m * M) :=
      (Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP
        (R := ZMod q) (p := q) (k := a) (m := m * M)).mp hroot'
    have hord : orderOf ((n : ZMod q)) = m * M := hpr.eq_orderOf.symm
    have hnq0 : (n : ZMod q) ≠ 0 := fun h => hqn ((ZMod.natCast_eq_zero_iff n q).mp h)
    have hq1 : orderOf ((n : ZMod q)) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hnq0
    have hle1 : orderOf ((n : ZMod q)) ≤ q - 1 := Nat.le_of_dvd (by omega) hq1
    have hle2 : M ≤ m * M := Nat.le_mul_of_pos_left M hmpos
    have hNq : q ≤ N := Nat.le_of_dvd hN hqNdvd
    omega
  -- Step 4, conclusion: `q ∤ e`
  have hqe : ¬ q ∣ e := by
    rw [he]
    exact hqprime.not_dvd_mul hqN hqMdvd
  -- Step 5
  refine ⟨q, hqprime, hqn, ?_⟩
  haveI : NeZero ((e : ℕ) : ZMod q) :=
    ⟨fun h => hqe ((ZMod.natCast_eq_zero_iff e q).mp h)⟩
  have hpr : IsPrimitiveRoot ((n : ZMod q)) e :=
    (Polynomial.isRoot_cyclotomic_iff (R := ZMod q) (n := e) (μ := (n : ZMod q))).mp hroot
  rw [← hpr.eq_orderOf, he]
  exact dvd_mul_right N M

end NK.CFTLib.IdeleHasse.Descent
