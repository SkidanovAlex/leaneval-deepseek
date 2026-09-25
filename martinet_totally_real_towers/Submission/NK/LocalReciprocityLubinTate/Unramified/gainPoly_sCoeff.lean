import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.GainAux
import Submission.NK.LocalReciprocityLubinTate.Unramified.resultant_X_pow_sub_C_X
import Submission.NK.LocalReciprocityLubinTate.Unramified.LTGain

/-!
# The linear term in `s` of the gain polynomial vanishes modulo `P`

Let `A` be a commutative domain and `P ∈ A` such that the residue ring `A ⧸ (P)` is a domain, and
let `q ≥ 2` be a power of the residue characteristic (`IsFrobeniusPower P q`).  For the
`s`-parametrised norm operator

`gainPoly P q t = Res_X(f(X) - Y, 1 + s·t(X)) ∈ (A[s])[Y]`,   `f = LTpoly P q = P·X + X^q`,

the **linear term in `s`** of every `Y`-coefficient is divisible by `P`:

`[s] (gainPoly P q t).coeff j ∈ (P)`.

This is the first-order estimate entering the gain lemma `normOp_gain`: modulo `P` one has
`f(X) ≡ X^q`, so the resultant reduces to the Frobenius twist of `1 + s·t(X)`, which equals
`1 + s^q · (∑_j t_j^q Y^j)` because the residue ring has characteristic `p` and `q = p^k`; since
`q ≥ 2` its `s`-coefficient vanishes.  (The vanishing of the `s`-coefficient modulo `P` is what
makes `𝒩(1 + P^k t) ≡ 1 + P^{k+1}·(…)`, i.e. the norm operator gain one level of `P`.)

## Main results

* `coeff_sum_C_pow_mul_X_pow` — the `i`-th coefficient of `∑_j C (h_j ^ q) · Y^j` is `h_i ^ q`;
* `coeff_one_pow_C_add_X_mul` — in characteristic `p`, `[s]((C a + s·b)^{p^k}) = 0` for `p^k ≥ 2`;
* `hPoly_coeff` — the coefficients of `hPoly t = 1 + s·t(X)`;
* `gainPoly_sCoeff` — the statement above.
-/

open Polynomial

namespace NK.LocalReciprocityLubinTate.Unramified

/-- The `i`-th coefficient of the polynomial `∑_j C (h_j ^ q) · Y^j` is `h_i ^ q`. -/
theorem coeff_sum_C_pow_mul_X_pow {R : Type*} [CommSemiring R] (h : Polynomial R) {q : ℕ}
    (hq : q ≠ 0) (i : ℕ) :
    (∑ j ∈ h.support, Polynomial.C (h.coeff j ^ q) * Polynomial.X ^ j : Polynomial R).coeff i
      = h.coeff i ^ q := by
  rw [show (∑ j ∈ h.support, Polynomial.C (h.coeff j ^ q) * Polynomial.X ^ j : Polynomial R)
      = h.sum (fun j a => Polynomial.C (a ^ q) * Polynomial.X ^ j) from rfl]
  rw [Polynomial.coeff_sum, Polynomial.sum_def]
  trans (∑ a ∈ h.support, (if a = i then h.coeff a ^ q else 0))
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h' : a = i
    · simp [h']
    · simp [h', Ne.symm h']
  · rw [Finset.sum_ite_eq']
    split_ifs with hi
    · rfl
    · rw [Polynomial.mem_support_iff] at hi
      simp only [ne_eq, not_not] at hi
      rw [hi, zero_pow hq]

/-- In a ring of characteristic `p`, the `s`-coefficient of `(C a + s·b)^{p^k}` vanishes as soon
as `p^k ≥ 2`: by the Frobenius additivity `(x + y)^{p^k} = x^{p^k} + y^{p^k}` the `s`-coefficient
can only come from `(s·b)^{p^k}`, whose order in `s` is `p^k`. -/
theorem coeff_one_pow_C_add_X_mul {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {q k : ℕ} (hqk : q = p ^ k) (hq : 2 ≤ q) (a : R) (b : Polynomial R) :
    ((Polynomial.C a + Polynomial.X * b) ^ q : Polynomial R).coeff 1 = 0 := by
  rw [hqk, add_pow_char_pow, Polynomial.coeff_add]
  have hpk : 2 ≤ p ^ k := by rw [← hqk]; exact hq
  have h1 : ((Polynomial.C a : Polynomial R) ^ (p ^ k)).coeff 1 = 0 := by
    rw [← Polynomial.C_pow, Polynomial.coeff_C]; simp
  have h2 : ((Polynomial.X * b : Polynomial R) ^ (p ^ k)).coeff 1 = 0 := by
    rw [mul_pow]
    have hdvd : Polynomial.X ^ 2 ∣ (Polynomial.X : Polynomial R) ^ (p ^ k) * b ^ (p ^ k) := by
      have hX : (Polynomial.X : Polynomial R) ^ (p ^ k)
          = Polynomial.X ^ 2 * Polynomial.X ^ (p ^ k - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [hX]
      exact ⟨Polynomial.X ^ (p ^ k - 2) * b ^ (p ^ k), by rw [mul_assoc]⟩
    exact (Polynomial.X_pow_dvd_iff.mp hdvd) 1 (by norm_num)
  rw [h1, h2, add_zero]

/-- The coefficients of `hPoly t = 1 + s·t(X) ∈ (A[s])[X]`: the `j`-th coefficient is the
constant `1` (for `j = 0`) plus `s · (t.coeff j)`. -/
theorem hPoly_coeff {A : Type*} [CommRing A] (t : Polynomial A) (j : ℕ) :
    (hPoly t).coeff j
      = (if j = 0 then (1 : Polynomial A) else 0) + Polynomial.X * Polynomial.C (t.coeff j) := by
  rw [hPoly, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]

/-- **The `s`-linear coefficients of the gain polynomial vanish modulo `P`.**

Let `A` be a commutative domain, `P ∈ A` with `A ⧸ (P)` a domain, `q ≥ 2` a power of the residue
characteristic, and `t ∈ A[X]`.  Then for every `j` the linear-in-`s` coefficient of the `Y^j`-th
coefficient of `gainPoly P q t = Res_X(f(X) - Y, 1 + s·t(X))` is divisible by `P`.

Proof.  Base change to the residue ring `B = A ⧸ (P)` along `φ : A →+* B` and use
`map_gainPoly`: the image of `gainPoly P q t` is `Res_X(X^q - Y, 1 + s·t̄(X))` in `(B[s])[Y]`.
The Frobenius resultant formula (`resultant_X_pow_sub_C_X'`, applied over `B[s]`) turns this into
`∑_j C((1 + s·t̄(X)).coeff j ^ q) Y^j`; by `add_pow_char_pow` and `q = p^k` the `j`-th
coefficient is `1 + s^q·(t̄_j)^q` (for `j = 0`) resp. `s^q·(t̄_j)^q` (for `j ≠ 0`), whose linear
`s`-coefficient vanishes because `q ≥ 2`.  Hence the `s`-coefficient lies in the kernel of `φ`,
i.e. in `(P)`. -/
theorem gainPoly_sCoeff {A : Type*} [CommRing A] [IsDomain A] (P : A)
    [IsDomain (A ⧸ Ideal.span ({P} : Set A))] (q : ℕ) (hq : 2 ≤ q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower P q)
    (t : Polynomial A) :
    ∀ j, ((NK.LocalReciprocityLubinTate.Unramified.gainPoly P q t).coeff j).coeff 1
      ∈ Ideal.span ({P} : Set A) := by
  intro j
  set I := Ideal.span ({P} : Set A) with hI
  haveI : IsDomain (A ⧸ I) := by rw [hI]; infer_instance
  set φ : A →+* (A ⧸ I) := Ideal.Quotient.mk I with hφ
  obtain ⟨p, hp, hchar, k, hqk⟩ := hpow
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (A ⧸ I) p := hchar
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ, ← Polynomial.coeff_map]
  set hh : Polynomial (Polynomial (A ⧸ I)) :=
    Polynomial.map (Polynomial.mapRingHom φ) (NK.LocalReciprocityLubinTate.Unramified.hPoly t)
    with hhh
  -- the first argument of the resultant reduces to `X ^ q - C Y`
  have hA1 : (Polynomial.map Polynomial.C (Polynomial.map (Polynomial.mapRingHom φ)
        (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)))
      - Polynomial.C (Polynomial.X : Polynomial (Polynomial (A ⧸ I))))
      = Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial (Polynomial (A ⧸ I))) := by
    congr 1
    have h1 : ((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map
          (Polynomial.mapRingHom φ)
        = ((NK.LocalReciprocityLubinTate.LTpoly P q).map φ).map Polynomial.C := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext a
      simp [RingHom.comp_apply]
    rw [show Polynomial.map Polynomial.C (Polynomial.map (Polynomial.mapRingHom φ)
          (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)))
        = (((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map
            (Polynomial.mapRingHom φ)).map Polynomial.C from rfl,
      h1, NK.LocalReciprocityLubinTate.Unramified.LTpoly_map_quotient]
    simp only [Polynomial.map_pow, Polynomial.map_X]
  -- the Frobenius resultant formula over the residue ring
  have hres := NK.LocalReciprocityLubinTate.Unramified.resultant_X_pow_sub_C_X'
    (A := Polynomial (A ⧸ I)) (p := p) (q := q) (k := k) hqk hh
    (n := (NK.LocalReciprocityLubinTate.Unramified.hPoly t).natDegree)
    Polynomial.natDegree_map_le
  have hG' : Polynomial.map (Polynomial.mapRingHom φ)
        (NK.LocalReciprocityLubinTate.Unramified.gainPoly P q t)
      = ∑ i ∈ hh.support, Polynomial.C (hh.coeff i ^ q) * Polynomial.X ^ i := by
    rw [NK.LocalReciprocityLubinTate.Unramified.map_gainPoly, hA1]
    exact hres
  have e1 : Polynomial.map φ ((NK.LocalReciprocityLubinTate.Unramified.gainPoly P q t).coeff j)
      = (Polynomial.map (Polynomial.mapRingHom φ)
          (NK.LocalReciprocityLubinTate.Unramified.gainPoly P q t)).coeff j := by
    rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
  rw [e1, hG', coeff_sum_C_pow_mul_X_pow hh (by omega) j]
  -- the `j`-th coefficient of `hh` is `C (δ_j) + s · C (t̄_j)`
  have hh_coeff : hh.coeff j = Polynomial.C (if j = 0 then (1 : A ⧸ I) else 0)
      + Polynomial.X * Polynomial.C (φ (t.coeff j)) := by
    rw [hhh, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
      show Polynomial.map φ ((NK.LocalReciprocityLubinTate.Unramified.hPoly t).coeff j)
          = Polynomial.map φ ((if j = 0 then (1 : Polynomial A) else 0)
              + Polynomial.X * Polynomial.C (t.coeff j)) from by
        rw [hPoly_coeff]]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    congr 2
    split_ifs <;> simp
  rw [hh_coeff, coeff_one_pow_C_add_X_mul hqk hq]

end NK.LocalReciprocityLubinTate.Unramified
