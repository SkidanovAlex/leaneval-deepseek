import Mathlib
import Submission.Vdw.MultiPrime
import Submission.Vdw.CaseI
import Submission.Vdw.ResidueIndex

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Case-I data instantiation of the sieve: the per-discriminant bound

Bhargava §5, Case I: an irreducible degree-`n` box polynomial `f` with
`|Disc K_f| = D` (squarefull, `C = rad D`) satisfies, for every prime
`p | C` (`p > n`), a congruence condition of "index at least `v_p(D)`"
modulo `p`.  This module instantiates the multi-prime sieve
(`MultiPrime.main_multiPrime_box_le`) with the Case-I data over the prime
factors of `D`:

    ι := D.primeFactors,  q p := p,  e p := min (v_p(D)) n

and proves (`perDiscriminant_box_le`, `perDiscriminant_real_raw`,
`perDiscriminant_clean_le`):

    #{f ∈ Box n H : ∀ p | D, index (f mod p) ≥ min (v_p(D)) n}
        ≤ 2^(((n+1)^4)·ω(D)) · (∏_{p|D} p^(n − min (v_p(D)) n)) · ((2H+1)/C + 1)^n

with `C = ∏_{p | D} p` the radical of `D`, and — under the elementary
Case-I hypothesis `C ≤ H`, `H ≥ 1` — the clean form

    ≤ 4^n · 2^(((n+1)^4)·ω(D)) · H^n · ∏_{p | D} p^{−min (v_p(D)) n}.

(The exponents are capped at `n` because the index of a degree-`n` polynomial
is at most `n−1`; primes with `v_p(D) ≥ n` will be shown separately to make
the count vanish — see the CI-4 block in `Roadmap`.)  This is Bhargava's
`O(c^{ω(D)}·H^n/D)` congruence-density estimate in the elementary `C ≤ H`
regime, ready to be summed over squarefull `D > H^{2+2δ}` once the
`discindex` bridge (`|Disc K_f| = D ⟹ index (f mod p) ≥ v_p(D)`) is in place.
-/

namespace Submission.Vdw

noncomputable section

/-- A member of `n.primeFactors` (viewed as a type) is prime — as a `Fact`,
so that `ZMod p` is a field and all `ZMod` API applies. -/
instance primeFactors_fact_prime (n : ℕ) (p : n.primeFactors) :
    Fact (Nat.Prime (p : ℕ)) :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

/-- Product over the subtype type `s = {x // x ∈ s}` equals the product over
the finset `s`. -/
theorem prod_type_eq_finset {α : Type*} {β : Type*} [CommMonoid β] (s : Finset α) (g : α → β) :
    (∏ p : s, g (p : α)) = ∏ p ∈ s, g p := by
  exact Finset.prod_attach s g

/-- Product over the subtype type `s` of `2^c · g`:
`∏_p (2^c · g p) = 2^(c·card s) · ∏_{p ∈ s} g p` (finset form). -/
theorem prod_const_mul {α : Type*} (s : Finset α) (g : α → ℕ) (c : ℕ) :
    (∏ p : s, 2 ^ c * g (p : α)) =
      2 ^ (c * s.card) * (∏ p ∈ s, g p) := by
  classical
  calc
    (∏ p : s, 2 ^ c * g (p : α)) = ∏ p ∈ s, 2 ^ c * g p := prod_type_eq_finset s (fun p => 2 ^ c * g p)
    _ = (∏ p ∈ s, 2 ^ c) * (∏ p ∈ s, g p) := by rw [Finset.prod_mul_distrib]
    _ = 2 ^ (c * s.card) * (∏ p ∈ s, g p) := by
      rw [Finset.prod_const, pow_mul]

/-- **Case-I per-discriminant counting bound.**  The number of degree-`n`
box polynomials (`|a_i| ≤ H`, `i < n`) whose reduction modulo every prime
divisor `p` of `D` has index at least `min (v_p(D)) n` is at most

    2^(((n+1)^4)·ω(D)) · (∏_{p | D} p^(n − min (v_p(D)) n)) · ((2H+1)/C + 1)^n

with `C = ∏_{p | D} p` the radical of `D`.  This is
`main_multiPrime_box_le` instantiated with the Case-I data
`q p := p`, `e p := min (v_p(D)) n`. -/
theorem perDiscriminant_box_le (n H : ℕ) (D : ℕ) :
    Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} ≤
      2 ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
        (∏ p ∈ D.primeFactors, p ^ (n - min (D.factorization p) n)) *
        ((2 * H + 1) / (∏ p ∈ D.primeFactors, p) + 1) ^ n := by
  classical
  let ι := D.primeFactors
  let q : ι → ℕ := fun p => (p : ℕ)
  let e : ι → ℕ := fun p => min (D.factorization (p : ℕ)) n
  have he : ∀ p : ι, e p ≤ n := by
    intro p
    exact Nat.min_le_right _ _
  have hqFact : ∀ p : ι, Fact (Nat.Prime (q p)) := fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hcop : ∀ p j : ι, p ≠ j → Nat.Coprime (q p) (q j) := by
    intro p j hpj
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
      (Nat.prime_of_mem_primeFactors j.2)).mpr (Subtype.coe_ne_coe.mpr hpj)
  have hinst := main_multiPrime_box_le (ι := ι) (q := q) (hqFact := hqFact) hcop n H e he
  have hmain : Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} ≤
      (∏ p : D.primeFactors, 2 ^ ((n + 1) ^ 4) * (p : ℕ) ^ (n - min (D.factorization (p : ℕ)) n)) *
        ((2 * H + 1) / (∏ p : D.primeFactors, (p : ℕ)) + 1) ^ n := by
    simpa [ι, q, e] using hinst
  have hfac1 :
      (∏ p : D.primeFactors, 2 ^ ((n + 1) ^ 4) * (p : ℕ) ^ (n - min (D.factorization (p : ℕ)) n)) =
        2 ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
          (∏ p ∈ D.primeFactors, p ^ (n - min (D.factorization p) n)) := by
    exact prod_const_mul D.primeFactors (fun p => p ^ (n - min (D.factorization p) n)) ((n + 1) ^ 4)
  calc
    Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} ≤
        (∏ p : D.primeFactors, 2 ^ ((n + 1) ^ 4) * (p : ℕ) ^ (n - min (D.factorization (p : ℕ)) n)) *
          ((2 * H + 1) / (∏ p : D.primeFactors, (p : ℕ)) + 1) ^ n := hmain
    _ ≤ 2 ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
          (∏ p ∈ D.primeFactors, p ^ (n - min (D.factorization p) n)) *
            ((2 * H + 1) / (∏ p ∈ D.primeFactors, p) + 1) ^ n := by
      have hden : (∏ p : D.primeFactors, (p : ℕ)) = ∏ p ∈ D.primeFactors, p :=
        prod_type_eq_finset D.primeFactors id
      rw [hden]
      rw [hfac1]

/-- The count of the Case-I per-`D` set, as a real bound (no `C ≤ H`
hypothesis): casts the natural bound to `ℝ`, replacing the natural division
`(2H+1)/C` by genuine real division. -/
theorem perDiscriminant_real_raw (n H : ℕ) (D : ℕ) :
    (Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
      (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
        (∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ (n - min (D.factorization p) n)) *
        ((((2 * H + 1 : ℕ) : ℝ) / (∏ p ∈ D.primeFactors, (p : ℕ) : ℕ)) + 1) ^ n := by
  classical
  have h := perDiscriminant_box_le n H D
  let C : ℕ := ∏ p ∈ D.primeFactors, p
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact Finset.one_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le)
  have hdiv : (((2 * H + 1) / C : ℕ) : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) / C := by
    have hCpos : (0 : ℝ) < C := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC1)
    rw [le_div_iff₀ hCpos]
    exact_mod_cast (Nat.div_mul_le_self (2 * H + 1) C)
  calc
    (Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
        ((2 ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
            (∏ p ∈ D.primeFactors, p ^ (n - min (D.factorization p) n)) *
            (((2 * H + 1) / C + 1) ^ n : ℕ)) : ℝ) := by
      exact_mod_cast h
    _ = (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
          (∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ (n - min (D.factorization p) n)) *
          ((((2 * H + 1) / C : ℕ) : ℝ) + 1) ^ n := by
      simp [C]
    _ ≤ (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
          (∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ (n - min (D.factorization p) n)) *
          (((2 * H + 1 : ℕ) : ℝ) / C + 1) ^ n := by
      let A : ℝ := (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card)
      let B : ℝ := ∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ (n - min (D.factorization p) n)
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hB : 0 ≤ B := by
        dsimp [B]
        exact Finset.prod_nonneg (fun p hp => pow_nonneg (by positivity) _)
      have hbase : 0 ≤ (((2 * H + 1) / C : ℕ) : ℝ) + 1 := by positivity
      have hu : (((2 * H + 1) / C : ℕ) : ℝ) + 1 ≤ ((2 * H + 1 : ℕ) : ℝ) / C + 1 := by
        linarith [hdiv]
      have hpow := pow_le_pow_left₀ hbase hu n
      -- A · B · u^n ≤ A · B · v^n
      simpa [A, B, mul_assoc] using
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hB) hA)
    _ = (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) *
          (∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ (n - min (D.factorization p) n)) *
          ((((2 * H + 1 : ℕ) : ℝ) / (∏ p ∈ D.primeFactors, (p : ℕ) : ℕ)) + 1) ^ n := by
      simp [C]

/-- The product identity behind the `C ≤ H` cleanup:
`(∏_p p^(n−k_p)) / C^n = ∏_p 1/p^(k_p)` with `C = ∏_p p` (real division),
valid when `0 ≠ p` and `k_p ≤ n` for every `p ∈ s`. -/
theorem prod_index_power_div (n : ℕ) (s : Finset ℕ) (k : ℕ → ℕ)
    (hp0 : ∀ p ∈ s, p ≠ 0) (hk : ∀ p ∈ s, k p ≤ n) :
    (∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)) /
        ((∏ p ∈ s, (p : ℕ) : ℕ) : ℝ) ^ n =
      ∏ p ∈ s, 1 / ((p : ℕ) : ℝ) ^ (k p) := by
  classical
  have hC : ((∏ p ∈ s, (p : ℕ) : ℕ) : ℝ) = ∏ p ∈ s, ((p : ℕ) : ℝ) := by
    simp [Nat.cast_prod]
  have hCpow : (((∏ p ∈ s, (p : ℕ) : ℕ) : ℝ) ^ n) = ∏ p ∈ s, ((p : ℕ) : ℝ) ^ n := by
    rw [hC]
    rw [Finset.prod_pow]
  calc
    (∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)) /
        ((∏ p ∈ s, (p : ℕ) : ℕ) : ℝ) ^ n
        = (∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)) / (∏ p ∈ s, ((p : ℕ) : ℝ) ^ n) := by
            rw [hCpow]
    _ = ∏ p ∈ s, (((p : ℕ) : ℝ) ^ (n - k p)) / (((p : ℕ) : ℝ) ^ n) := by
            rw [Finset.prod_div_distrib]
    _ = ∏ p ∈ s, 1 / ((p : ℕ) : ℝ) ^ (k p) := by
            apply Finset.prod_congr rfl
            intro p hp
            have hp0r : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hp0 p hp)
            have hkp : k p ≤ n := hk p hp
            have hsplit : n = k p + (n - k p) := by omega
            have hpow : ((p : ℕ) : ℝ) ^ n =
                ((p : ℕ) : ℝ) ^ (k p) * ((p : ℕ) : ℝ) ^ (n - k p) := by
              nth_rw 1 [hsplit]
              rw [pow_add]
            have ha1 : ((p : ℕ) : ℝ) ^ (n - k p) ≠ 0 := pow_ne_zero _ hp0r
            have ha2 : ((p : ℕ) : ℝ) ^ (k p) ≠ 0 := pow_ne_zero _ hp0r
            calc
              ((p : ℕ) : ℝ) ^ (n - k p) / ((p : ℕ) : ℝ) ^ n
                  = ((p : ℕ) : ℝ) ^ (n - k p) /
                      (((p : ℕ) : ℝ) ^ (k p) * ((p : ℕ) : ℝ) ^ (n - k p)) := by rw [hpow]
              _ = 1 / ((p : ℕ) : ℝ) ^ (k p) := by field_simp [ha1, ha2]

/-- **Case-I per-discriminant bound, `C ≤ H` clean form.**  Under
`C := radical D ≤ H` and `H ≥ 1` (and `n ≥ 1`) the count of degree-`n` box
polynomials satisfying the per-prime index conditions of `D` is at most

    4^n · 2^(((n+1)^4)·ω(D)) · H^n · ∏_{p | D} p^{−min (v_p(D)) n}

— Bhargava's `O(c^{ω(D)}·H^n/D)`-shaped estimate in the elementary `C ≤ H`
regime (exponents capped at `n`; primes with `v_p(D) ≥ n` will later be shown
to contribute nothing, since the index of a degree-`n` polynomial is `< n`). -/
theorem perDiscriminant_clean_le (n H : ℕ) (_hn : 1 ≤ n) (hH : 1 ≤ H) (D : ℕ)
    (hC : radical D ≤ H) :
    (Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
      (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) * (H : ℝ) ^ n *
        (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ min (D.factorization p) n) := by
  classical
  let s := D.primeFactors
  let C : ℕ := ∏ p ∈ s, p
  let k : ℕ → ℕ := fun p => min (D.factorization p) n
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact Finset.one_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC1)
  have hCnat : C ≤ H := by
    simpa [C, s, radical] using hC
  have hCnat' : (C : ℝ) ≤ (H : ℝ) := by exact_mod_cast hCnat
  have hH' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hraw := perDiscriminant_real_raw n H D
  -- bound the base (((2H+1)/C) + 1) by (4H)/C
  have hwle : ((((2 * H + 1 : ℕ) : ℝ) / C) + 1) ≤ (4 * (H : ℝ)) / C := by
    have hnum : ((2 * H + 1 : ℕ) : ℝ) + C ≤ 4 * (H : ℝ) := by
      have hc2 : ((2 * H + 1 : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by norm_num
      rw [hc2]
      nlinarith
    have heq : ((((2 * H + 1 : ℕ) : ℝ) / C) + 1) = (((2 * H + 1 : ℕ) : ℝ) + C) / C := by
      field_simp [hCpos.ne']
    rw [heq]
    exact div_le_div_of_nonneg_right hnum (le_of_lt hCpos)
  have hwbase : 0 ≤ ((((2 * H + 1 : ℕ) : ℝ) / C) + 1) := by positivity
  have hwpow : ((((2 * H + 1 : ℕ) : ℝ) / C) + 1) ^ n ≤
      (4 : ℝ) ^ n * (H : ℝ) ^ n / (C : ℝ) ^ n := by
    have hmid : ((((2 * H + 1 : ℕ) : ℝ) / C) + 1) ^ n ≤ ((4 * (H : ℝ)) / C) ^ n :=
      pow_le_pow_left₀ hwbase hwle n
    have hdiv : ((4 * (H : ℝ)) / C) ^ n = (4 : ℝ) ^ n * (H : ℝ) ^ n / (C : ℝ) ^ n := by
      rw [div_pow, mul_pow]
    exact le_trans hmid (le_of_eq hdiv)
  -- product identity
  have hId : (∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)) / (C : ℝ) ^ n =
      ∏ p ∈ s, 1 / ((p : ℕ) : ℝ) ^ (k p) := by
    have hkn : ∀ p ∈ s, k p ≤ n := by
      intro p hp
      dsimp [k]
      exact Nat.min_le_right _ _
    have hpn : ∀ p ∈ s, p ≠ 0 := by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).ne_zero
    simpa [C, s, k] using (prod_index_power_div n s k hpn hkn)
  calc
    (Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
        (2 : ℝ) ^ (((n + 1) ^ 4) * s.card) *
          (∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)) *
          ((((2 * H + 1 : ℕ) : ℝ) / C) + 1) ^ n := by
      simpa [s, C, k] using hraw
    _ ≤ (2 : ℝ) ^ (((n + 1) ^ 4) * s.card) *
          (∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)) *
          ((4 : ℝ) ^ n * (H : ℝ) ^ n / (C : ℝ) ^ n) := by
      let A : ℝ := (2 : ℝ) ^ (((n + 1) ^ 4) * s.card)
      let B : ℝ := ∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hB : 0 ≤ B := by
        dsimp [B]
        exact Finset.prod_nonneg (fun p hp => pow_nonneg (by positivity) _)
      have hAB : 0 ≤ A * B := mul_nonneg hA hB
      simpa [A, B, mul_assoc] using (mul_le_mul_of_nonneg_left hwpow hAB)
    _ = (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * s.card) * (H : ℝ) ^ n *
          (∏ p ∈ s, 1 / ((p : ℕ) : ℝ) ^ (k p)) := by
      let A : ℝ := (2 : ℝ) ^ (((n + 1) ^ 4) * s.card)
      let B : ℝ := ∏ p ∈ s, ((p : ℕ) : ℝ) ^ (n - k p)
      have hden : (C : ℝ) ^ n ≠ 0 := pow_ne_zero n hCpos.ne'
      have hre : A * B * ((4 : ℝ) ^ n * (H : ℝ) ^ n / (C : ℝ) ^ n) =
          (4 : ℝ) ^ n * A * (H : ℝ) ^ n * (B / (C : ℝ) ^ n) := by
        field_simp [hden]
      rw [hre]
      rw [hId]
    _ = (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * s.card) * (H : ℝ) ^ n *
          (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ min (D.factorization p) n) := by
      simp [s, k]



/-- **Restricted per-`D` sieve bound (raw), Case-I direct regime.**  The
direct-regime assembly (S1) counts `{f : fieldDisc f = D}` through index
conditions at the *large* primes `p | D` (`p > n`) only — at those primes
Lemma 24 (field) gives `index ≥ v_p(D)` (`RestrictedSieve.restrictedSieve_entry`),
while the small primes `p ≤ n | D` are excluded (their index conditions can
fail) and absorbed later as the bounded factor `discSmallPart n D ≤ S₀(n)`
(wild different bound).  This is the (α) layer: the per-`D` count of the
restricted sieve set

    RestSieve(D) := {f ∈ Box n H : ∀ p | D with p > n,
                        index_{F_p}(f̄) ≥ min (v_p(D), n)}

is bounded by the `MultiPrime` sieve over the family
`ι := {q : D.primeFactors // n < q}` (each prime factor of `D` exceeding `n`):
per-prime factor `2^((n+1)^4)·p^(n − min(v_p(D),n))` and box-residue modulus
`C_{>n}(D) := ∏_{p | D, p > n} p` — the raw form (no `C ≤ H` hypothesis; the
clean `O(c^(ω)H^n/D*)`-form with `D* = discLargePart n D` needs `C_{>n}(D) ≤ H`
and the exponent-cap `v_p(D) < n` at large primes, both automatic for real
`D = D_f`, and is a mechanical corollary via the `perDiscriminant_clean_le`
chain). -/
theorem restrictedPerDiscriminant_box_le (n H : ℕ) (D : ℕ) :
    Nat.card {f : ↥(Box n H) // ∀ p : {q : D.primeFactors // n < (q : ℕ)},
        indexClass (F := ZMod (p.1 : ℕ)) n (min (D.factorization (p.1 : ℕ)) n)
          (boxResidue n H (p.1 : ℕ) f)} ≤
      (∏ p : {q : D.primeFactors // n < (q : ℕ)},
          2 ^ ((n + 1) ^ 4) * (p.1 : ℕ) ^ (n - min (D.factorization (p.1 : ℕ)) n)) *
        ((2 * H + 1) / (∏ p : {q : D.primeFactors // n < (q : ℕ)}, (p.1 : ℕ)) + 1) ^ n := by
  classical
  let ι := {q : D.primeFactors // n < (q : ℕ)}
  let q : ι → ℕ := fun p => (p.1 : ℕ)
  let e : ι → ℕ := fun p => min (D.factorization (p.1 : ℕ)) n
  have he : ∀ p : ι, e p ≤ n := by
    intro p
    exact Nat.min_le_right _ _
  have hqFact : ∀ p : ι, Fact (Nat.Prime (q p)) := fun p =>
    ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
  have hcop : ∀ p j : ι, p ≠ j → Nat.Coprime (q p) (q j) := by
    intro p j hpj
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.1.2)
      (Nat.prime_of_mem_primeFactors j.1.2)).mpr (by
        intro hq
        apply hpj
        apply Subtype.ext
        apply Subtype.ext
        exact hq)
  have hinst := main_multiPrime_box_le (ι := ι) (q := q) (hqFact := hqFact) hcop n H e he
  simpa [ι, q, e] using hinst

end
end Submission.Vdw
