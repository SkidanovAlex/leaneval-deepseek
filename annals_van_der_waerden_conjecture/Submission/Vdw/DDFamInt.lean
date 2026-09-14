import Mathlib
import Submission.Vdw.DoubleDisc
import Submission.Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero
import Submission.Vdw.PrimeDiscr

open Polynomial

/-!
# The Case-III double discriminant over the integers (per-prime divisibility)

`DoubleDisc.lean` builds the double discriminant `DD(a₁,…,a_{n-1})` for the monic family
`X^n + a_{n-1}X^{n-1} + … + a₁X + a₀` as a polynomial in the upper coefficients over ℚ.
This module provides the *integer* objects (`concFamilyZ`, `concInnerZ`, `concDDZ`: the
same family / inner discriminant / double discriminant with upper coefficients
`u : Fin (n-1) → ℤ`, living in `ℤ[t]` / `ℤ`) and proves

- `concInnerZ_natDegree_coeff`: `P_u(t) = Disc_X(family)` is a `ℤ[t]`-polynomial of degree
  `n−1` with leading coefficient `± nⁿ` — transferred from the ℚ-side machinery of
  `DoubleDisc` along the injection `ℤ ↪ ℚ` (discriminants commute with this map);
- **`prime_dvd_concDDZ_of_modp_stable`**: if, for the prime `p` (`p ∤ n`), the value of
  `P_u` is divisible by `p²` on a whole residue class `a₀ (mod p)`
  (`∀ d, p² | P_u(a₀ + p·d)` — "`Disc(f)` is a multiple of `p²` for mod-`p` reasons" in the
  language of Bhargava's Case III), then `p | DD(u)` as an integer.

Together with `PrimeDiscr.prime_dvd_discr_of_modp_stable` this is the per-prime algebra
behind Case III of Theorem 1 of Bhargava (Annals of Math 2025): applied to every prime
`p | C` (in the eventual counting only `p > H^{δ/2}` occur, so `p ∤ n` for all large `H`)
it yields `A = ∏ p | DD(u)` — the geometric-sieve input of Case III subcase (ii).  The
leading-coefficient hypothesis of `prime_dvd_discr_of_double_root_modp` is verified from
`p ∤ n` via `concInnerZ_natDegree_coeff` (`lc(P_u) = ± nⁿ`).
-/

noncomputable section

namespace Submission.Vdw

/-- The monic degree-`n` family `X^n + Σ_j u_j·X^(j+1) + t` over `ℤ[t]` with concrete
upper integer coefficients `u`. -/
def concFamilyZ (n : ℕ) (u : Fin (n - 1) → ℤ) : (Polynomial ℤ)[X] :=
  X ^ n + (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (u j)) * X ^ ((j : ℕ) + 1)) +
    Polynomial.C (Polynomial.X : Polynomial ℤ)

/-- `P_u(t) = Disc_X` of the ℤ-concrete family: an element of `ℤ[t]`. -/
abbrev concInnerZ (n : ℕ) (u : Fin (n - 1) → ℤ) : Polynomial ℤ :=
  Polynomial.discr (concFamilyZ n u)

/-- `DD(u) := Disc_t(P_u)`, an integer (the Case-III double discriminant at `u`). -/
def concDDZ (n : ℕ) (u : Fin (n - 1) → ℤ) : ℤ := Polynomial.discr (concInnerZ n u)

/-- The upper coefficients `u` cast into `ℚ`. -/
def uQ {n : ℕ} (u : Fin (n - 1) → ℤ) : Fin (n - 1) → ℚ := fun j => (u j : ℚ)

-- ---------------------------------------------------------------
-- 1. the family is monic of degree n (ℤ analogue of the ℚ fact)
-- ---------------------------------------------------------------

/-- Coefficients of the ℤ-family at degrees `k ≥ n` vanish except `coeff n = 1`. -/
lemma concFamilyZ_coeff_ge (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : n ≤ k) (u : Fin (n - 1) → ℤ) :
    (concFamilyZ n u).coeff k = if k = n then 1 else 0 := by
  classical
  unfold concFamilyZ
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  have hX : (X ^ n : (Polynomial ℤ)[X]).coeff k = if k = n then 1 else 0 := by
    rw [Polynomial.coeff_X_pow]
  have hC : (Polynomial.C (Polynomial.X : Polynomial ℤ) : (Polynomial ℤ)[X]).coeff k = 0 := by
    rw [Polynomial.coeff_C]
    simp [show k ≠ 0 by omega]
  rw [coeff_finset_sum]
  have hsum : (∑ j : Fin (n - 1), (Polynomial.C (Polynomial.C (u j)) * X ^ ((j : ℕ) + 1)
        : (Polynomial ℤ)[X]).coeff k) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [Polynomial.coeff_C_mul_X_pow, show k ≠ (j : ℕ) + 1 by omega]
  rw [hX, hC, hsum]
  simp

/-- The ℤ-family is monic of degree `n` in `X` (for `1 ≤ n`). -/
lemma concFamilyZ_monic_natDegree (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) :
    (concFamilyZ n u).Monic ∧ (concFamilyZ n u).natDegree = n := by
  have hnd : (concFamilyZ n u).natDegree = n := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [concFamilyZ_coeff_ge n hn m (le_of_lt hm) u]
      simp [ne_of_gt hm]
    · by_contra hlt
      have hc0 : (concFamilyZ n u).coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hlt)
      have hc : (concFamilyZ n u).coeff n = 1 := by
        rw [concFamilyZ_coeff_ge n hn n (le_rfl) u]
        simp
      rw [hc] at hc0
      norm_num at hc0
  constructor
  · show (concFamilyZ n u).leadingCoeff = 1
    rw [Polynomial.leadingCoeff, hnd, concFamilyZ_coeff_ge n hn n (le_rfl) u]
    simp
  · exact hnd

-- ---------------------------------------------------------------
-- 2. mapping the ℤ-family to ℚ
-- ---------------------------------------------------------------

/-- Mapping the ℤ-family to ℚ (coefficient-wise) gives the ℚ-concrete family at the cast
upper coefficients. -/
lemma concFamilyZ_map_conc (n : ℕ) (u : Fin (n - 1) → ℤ) :
    Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) (concFamilyZ n u) =
      concFamily n (uQ u) := by
  classical
  let f : Polynomial ℤ →+* Polynomial ℚ := Polynomial.mapRingHom (Int.castRingHom ℚ)
  have hterm (j : Fin (n - 1)) :
      Polynomial.map f (Polynomial.C (Polynomial.C (u j)) * X ^ ((j : ℕ) + 1)
          : (Polynomial ℤ)[X]) = Polynomial.C (Polynomial.C ((u j : ℚ))) * X ^ ((j : ℕ) + 1) := by
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    congr 1
    rw [Polynomial.map_C]
    congr 1
    change Polynomial.map (Int.castRingHom ℚ) (Polynomial.C (u j)) = Polynomial.C ((u j : ℚ))
    simp
  unfold concFamilyZ concFamily uQ
  rw [Polynomial.map_add, Polynomial.map_add]
  rw [Polynomial.map_pow, Polynomial.map_X]
  rw [Polynomial.map_sum]
  rw [Polynomial.map_C]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j
  · congr 1
    change (Polynomial.mapRingHom (Int.castRingHom ℚ)) (Polynomial.X : Polynomial ℤ) = Polynomial.X
    simp

/-- `Disc_X` commutes with the coefficient map `ℤ ↪ ℚ`: the ℤ-inner maps to the
ℚ-concrete inner at the cast upper coefficients. -/
lemma concInnerZ_map_conc (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) :
    (concInnerZ n u).map (Int.castRingHom ℚ) = concInner n (uQ u) := by
  classical
  let f : Polynomial ℤ →+* Polynomial ℚ := Polynomial.mapRingHom (Int.castRingHom ℚ)
  have hm := (concFamilyZ_monic_natDegree n hn u).1
  have hdeg : (Polynomial.map f (concFamilyZ n u)).natDegree = (concFamilyZ n u).natDegree := by
    exact Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero f (p := concFamilyZ n u)
      (by rw [hm.leadingCoeff]; simp)
  have hR5 := Commons.RingTheory.Polynomial.discr_map_of_natDegree
    (R := Polynomial ℤ) (S := Polynomial ℚ) f (p := concFamilyZ n u) hdeg
  change (concInnerZ n u).map (Int.castRingHom ℚ) = concInner n (uQ u)
  change Polynomial.map (Int.castRingHom ℚ) (Polynomial.discr (concFamilyZ n u))
      = Polynomial.discr (concFamily n (uQ u))
  -- hR5: φ (discr p) = discr (p.map φ); rearrange
  change (Polynomial.mapRingHom (Int.castRingHom ℚ)) (Polynomial.discr (concFamilyZ n u))
      = Polynomial.discr (concFamily n (uQ u))
  rw [hR5]
  congr 1
  rw [concFamilyZ_map_conc n u]

-- ---------------------------------------------------------------
-- 3. degree and leading coefficient of P_u, over ℚ and then ℤ
-- ---------------------------------------------------------------

/-- Over ℚ: the concrete inner discriminant `P_u(t) = Disc_X(f_u)` at cast upper
coefficients has t-degree `n−1` and t-leading coefficient `± nⁿ`. -/
lemma concInner_natDegree_coeff_Q (n : ℕ) (hn : 2 ≤ n) (u : Fin (n - 1) → ℤ) :
    (concInner n (uQ u)).natDegree = n - 1 ∧
      (concInner n (uQ u)).coeff (n - 1) = (-1 : ℚ) ^ (n * (n - 1) / 2) * (n : ℚ) ^ n := by
  classical
  let ψ : ddParam n →+* ℚ := MvPolynomial.eval (uQ u)
  have hnd0 := (ddInner_natDegree_lc n hn).1
  have hlc0 := (ddInner_natDegree_lc n hn).2
  have hlcne : ψ ((ddInner n).leadingCoeff) ≠ 0 := by
    rw [Polynomial.leadingCoeff, hnd0, hlc0, MvPolynomial.eval_C]
    exact mul_ne_zero
      (pow_ne_zero (n * (n - 1) / 2) (by norm_num))
      (pow_ne_zero n (by exact_mod_cast (by omega : n ≠ 0)))
  have hdeg : (Polynomial.map ψ (ddInner n)).natDegree = (ddInner n).natDegree :=
    Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero ψ (p := ddInner n) hlcne
  have hmap : Polynomial.map ψ (ddInner n) = concInner n (uQ u) :=
    ddInner_map_conc n (by omega : 1 ≤ n) (uQ u)
  constructor
  · calc
      (concInner n (uQ u)).natDegree = (Polynomial.map ψ (ddInner n)).natDegree := by rw [hmap]
      _ = (ddInner n).natDegree := hdeg
      _ = n - 1 := hnd0
  · calc
      (concInner n (uQ u)).coeff (n - 1) = (Polynomial.map ψ (ddInner n)).coeff (n - 1) := by rw [hmap]
      _ = ψ ((ddInner n).coeff (n - 1)) := by rw [Polynomial.coeff_map]
      _ = ψ (MvPolynomial.C ((-1 : ℚ) ^ (n * (n - 1) / 2) * (n : ℚ) ^ n)) := by rw [hlc0]
      _ = (-1 : ℚ) ^ (n * (n - 1) / 2) * (n : ℚ) ^ n := by simp

/-- The inner `P_u(t) = Disc_X(f_u)` is an integer polynomial in `t` of degree `n−1` with
leading coefficient `± nⁿ`. -/
lemma concInnerZ_natDegree_coeff (n : ℕ) (hn : 2 ≤ n) (u : Fin (n - 1) → ℤ) :
    (concInnerZ n u).natDegree = n - 1 ∧
      (concInnerZ n u).coeff (n - 1) = (-1 : ℤ) ^ (n * (n - 1) / 2) * (n : ℤ) ^ n := by
  classical
  let ι : ℤ →+* ℚ := Int.castRingHom ℚ
  have hmap : (concInnerZ n u).map ι = concInner n (uQ u) :=
    concInnerZ_map_conc n (by omega : 1 ≤ n) u
  have hQ := concInner_natDegree_coeff_Q n hn u
  constructor
  · calc
      (concInnerZ n u).natDegree = ((concInnerZ n u).map ι).natDegree := by
          rw [← Polynomial.natDegree_map_eq_of_injective (f := ι) Int.cast_injective (concInnerZ n u)]
      _ = (concInner n (uQ u)).natDegree := by rw [hmap]
      _ = n - 1 := hQ.1
  · have hc : ι ((concInnerZ n u).coeff (n - 1)) =
        ι ((-1 : ℤ) ^ (n * (n - 1) / 2) * (n : ℤ) ^ n) := by
      calc
        ι ((concInnerZ n u).coeff (n - 1)) = ((concInnerZ n u).map ι).coeff (n - 1) := by
            rw [Polynomial.coeff_map]
        _ = (concInner n (uQ u)).coeff (n - 1) := by rw [hmap]
        _ = (-1 : ℚ) ^ (n * (n - 1) / 2) * (n : ℚ) ^ n := hQ.2
        _ = ι ((-1 : ℤ) ^ (n * (n - 1) / 2) * (n : ℤ) ^ n) := by
            simp
    exact Int.cast_injective hc

-- ---------------------------------------------------------------
-- 4. per-prime divisibility of DD(u)
-- ---------------------------------------------------------------

/-- Since the leading coefficient of `P_u` is `± nⁿ`, `p ∤ n` keeps the degree from
dropping upon reduction mod `p`. -/
lemma not_dvd_leadingCoeff_concInnerZ (p : ℕ) (hp : Nat.Prime p) {n : ℕ} (hn : 3 ≤ n)
    (hpn : ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    ¬ (p : ℤ) ∣ (concInnerZ n u).leadingCoeff := by
  classical
  have hnd := (concInnerZ_natDegree_coeff n (by omega : 2 ≤ n) u).1
  have hlc := (concInnerZ_natDegree_coeff n (by omega : 2 ≤ n) u).2
  intro hdiv
  rw [Polynomial.leadingCoeff, hnd] at hdiv
  rw [hlc] at hdiv
  have hsq : (-1 : ℤ) ^ (n * (n - 1) / 2) * (-1 : ℤ) ^ (n * (n - 1) / 2) = 1 := by
    calc
      (-1 : ℤ) ^ (n * (n - 1) / 2) * (-1 : ℤ) ^ (n * (n - 1) / 2)
          = ((-1 : ℤ) ^ (n * (n - 1) / 2)) ^ 2 := by rw [pow_two]
      _ = (-1 : ℤ) ^ ((n * (n - 1) / 2) * 2) := by rw [pow_mul]
      _ = ((-1 : ℤ) ^ 2) ^ (n * (n - 1) / 2) := by
        rw [← pow_mul]
        congr 1
        omega
      _ = 1 := by norm_num
  have hmul := dvd_mul_of_dvd_right hdiv ((-1 : ℤ) ^ (n * (n - 1) / 2))
  have hdivn : (p : ℤ) ∣ (n : ℤ) ^ n := by
    simpa [mul_assoc, mul_left_comm, mul_comm, hsq] using hmul
  have hnat : p ∣ n ^ n := by
    -- (p : ℤ) ∣ (n : ℤ)^n, with nats
    have h' : (p : ℤ) ∣ ((n : ℕ) : ℤ) ^ n := by
      simpa using hdivn
    have h'' : (p : ℤ) ∣ ((n ^ n : ℕ) : ℤ) := by
      rw [← Int.natCast_pow] at h'
      exact h'
    exact (Int.natCast_dvd_natCast).1 h''
  exact hpn (hp.dvd_of_dvd_pow hnat)

/-- **Case III, per prime:** if the value of `P_u(t) = Disc_X(f_t)` is divisible by `p²`
on a whole residue class `a₀ (mod p)` (i.e. `Disc` is a multiple of `p²` for mod-`p`
reasons), then `p` divides the double discriminant `DD(u) = Disc_t(P_u)` as an integer.
Here `u` are the upper coefficients of the monic family and `p ∤ n`. -/
lemma prime_dvd_concDDZ_of_modp_stable (p : ℕ) (hp : Nat.Prime p) {n : ℕ} (hn : 3 ≤ n)
    (hpn : ¬ p ∣ n) (u : Fin (n - 1) → ℤ) (a₀ : ℤ)
    (hstab : ∀ d : ℤ, ((p : ℤ) ^ 2) ∣ (concInnerZ n u).eval (a₀ + (p : ℤ) * d)) :
    (p : ℤ) ∣ concDDZ n u := by
  change (p : ℤ) ∣ Polynomial.discr (concInnerZ n u)
  exact prime_dvd_discr_of_modp_stable p hp (concInnerZ n u) a₀
    (by
      rw [(concInnerZ_natDegree_coeff n (by omega : 2 ≤ n) u).1]
      omega)
    (not_dvd_leadingCoeff_concInnerZ p hp hn hpn u)
    hstab

end Submission.Vdw
