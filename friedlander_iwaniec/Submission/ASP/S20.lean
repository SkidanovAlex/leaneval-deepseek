/-
  **The elementary verification of the companion-sieve hypothesis (1.6)/(2.8) for X² + Y⁴.**

  The companion's crude bound (1.6) reads `A_d(x) ≪ d^{-1}τ(d)^8 A(x)` uniformly for `d ≤ x^{1/3}`.
  For the Friedlander–Iwaniec sequence that pointwise bound is *false* (the local density at
  `d = p^4` is `≍ p^{-3}`, which exceeds `5^8 p^{-4}` for `p ≳ 5^8`); what the main paper actually
  uses (p. 962 of the paper) is the **elementary** estimate

      `A_d(x) ≪ d^{-1} τ(d) A(x)`   uniformly for `d ≤ x^{1/2-ε}`,

  which *is* true (and here, with `τ(d)²` in place of `τ(d)`, for `d ≤ x^{1/2}`).  The proof is a
  direct lattice count: for each `c` the `a`'s with `a² ≡ −c⁴ (mod d)` form `ρ(c²,d)` residue
  classes, and (for cubefree `d`) `ρ(c²,d) ≤ 2^{ω(d)}·∏_{p² ∣ d, p ∣ c} p`, whose sum over
  `|c| ≤ x^{1/4}` is `≪ x^{1/4}τ(d)`.
-/
import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_eq_sum_c
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega_mul_of_cubefree
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos
import Submission.Commons.NumberTheory.Divisors.prod_factorization_div_two_eq_sqPart
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_filter_dvd_sq_add_pow_four_le

namespace Submission.ASP

open Finset

noncomputable section

/-- The **square part** `∏_{p² ∣ d} p` of `d`. -/
def sqPart (d : ℕ) : ℕ := ∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d), p

/-- A positive integer has `sqPart ≥ 1`. -/
lemma sqPart_pos (d : ℕ) (hd : 1 ≤ d) : 0 < sqPart d := by
  refine Finset.prod_pos (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  exact (Nat.prime_of_mem_primeFactors hp.1).pos

/-- A product of pairwise coprime divisors of `d` divides `d`. -/
lemma prod_dvd_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {d : ℕ}
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → (f p).Coprime (f q))
    (hdvd : ∀ p ∈ s, f p ∣ d) : ∏ p ∈ s, f p ∣ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_dvd d
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : f a ∣ d := hdvd a (Finset.mem_insert_self a s)
    have h2 : (∏ p ∈ s, f p) ∣ d :=
      ih (fun p hp q hq hpq => hcop p (Finset.mem_insert_of_mem hp) q
            (Finset.mem_insert_of_mem hq) hpq)
        (fun p hp => hdvd p (Finset.mem_insert_of_mem hp))
    have h3 : (f a).Coprime (∏ p ∈ s, f p) :=
      Nat.Coprime.prod_right (fun p hp => hcop a (Finset.mem_insert_self a s) p
        (Finset.mem_insert_of_mem hp) (fun h => ha (h ▸ hp)))
    exact h3.mul_dvd_of_dvd_of_dvd h1 h2

/-- `sqPart d ∣ d`. -/
lemma sqPart_dvd (d : ℕ) : sqPart d ∣ d := by
  rw [sqPart]
  refine prod_dvd_of_pairwise_coprime ?_ ?_
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1)
      (Nat.prime_of_mem_primeFactors hq.1)).mpr hpq
  · intro p hp
    have h2 : p ^ 2 ∣ d := (Finset.mem_filter.mp hp).2
    exact dvd_trans (by rw [pow_two]; exact dvd_mul_right p p) h2

/-- `(sqPart d) ^ 2 ∣ d`. -/
lemma sqPart_sq_dvd (d : ℕ) : sqPart d ^ 2 ∣ d := by
  rw [sqPart, ← Finset.prod_pow]
  refine prod_dvd_of_pairwise_coprime ?_ ?_
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1)
      (Nat.prime_of_mem_primeFactors hq.1)).mpr hpq |>.pow 2 2
  · intro p hp
    exact (Finset.mem_filter.mp hp).2

/-- `sqPart d ≤ √d` for `d > 0`. -/
lemma sqPart_le_sqrt (d : ℕ) (hd : 0 < d) : sqPart d ≤ Nat.sqrt d := by
  rw [Nat.le_sqrt]
  rw [← pow_two]
  exact Nat.le_of_dvd hd (sqPart_sq_dvd d)

/-- `τ(sqPart d) ≤ τ(d)`. -/
lemma card_divisors_sqPart_le (d : ℕ) (hd : 1 ≤ d) :
    (sqPart d).divisors.card ≤ d.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega) (sqPart_dvd d))

/-- `gcd` distributes over a product of pairwise coprime factors. -/
lemma gcd_prod_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {c : ℕ}
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → (f p).Coprime (f q)) :
    Nat.gcd c (∏ p ∈ s, f p) = ∏ p ∈ s, Nat.gcd c (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h3 : (f a).Coprime (∏ p ∈ s, f p) :=
      Nat.Coprime.prod_right (fun p hp => hcop a (Finset.mem_insert_self a s) p
        (Finset.mem_insert_of_mem hp) (fun h => ha (h ▸ hp)))
    rw [h3.gcd_mul]
    congr 1
    exact ih (fun p hp q hq hpq =>
      hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq)

/-- The square part is exactly the product of the primes `p` with `p² ∣ d`. -/
lemma sqPart_eq_prod_filter (d : ℕ) :
    sqPart d = ∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d), p := rfl

/-- **The `c`-sum of the root counts.**  For cubefree `d ≥ 1`:
`∑_{c = 1}^{N} ρ(c², d) ≤ 2^{ω(d)}·N·τ(d)`.

The point is that `ρ(c²,d) ≤ 2^{ω(d)}·gcd(c, sqPart d)` (the first factor `2^{ω(d)}` counts the
roots of `ν² + 1`, the `gcd` the prime powers `p² ∣ d` with `p ∣ c`), and
`∑_{c ≤ N} gcd(c, m) ≤ N·τ(m)`. -/
lemma sum_rho_le (d N : ℕ) (hd : 1 ≤ d) (hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) :
    ∑ c ∈ Finset.Icc 1 N, Submission.rho (c ^ 2) d
      ≤ 2 ^ d.primeFactors.card * (N * d.divisors.card) := by
  classical
  have hd0 : 0 < d := by omega
  set S : Finset ℕ := d.primeFactors.filter (fun p => p ^ 2 ∣ d) with hS
  have hSsub : S ⊆ d.primeFactors := Finset.filter_subset _ _
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hSsub hp)
  have hScop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.Coprime q := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hSprime p hp) (hSprime q hq)).mpr hpq
  -- per-`c` bound
  have hper : ∀ c ∈ Finset.Icc 1 N,
      Submission.rho (c ^ 2) d ≤ 2 ^ d.primeFactors.card * Nat.gcd c (sqPart d) := by
    intro c _
    refine le_trans (Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega_mul_of_cubefree (c := c) hd0 hcb) ?_
    have hprod : (∏ p ∈ d.primeFactors.filter (fun p => p ^ 2 ∣ d ∧ p ∣ c), p)
        = ∏ p ∈ S, (if p ∣ c then p else 1) := by
      have hfil : d.primeFactors.filter (fun p => p ^ 2 ∣ d ∧ p ∣ c)
          = S.filter (fun p => p ∣ c) := by
        rw [hS, Finset.filter_filter]
      rw [hfil, Finset.prod_filter]
    rw [hprod]
    have hgcd : Nat.gcd c (sqPart d) = ∏ p ∈ S, Nat.gcd c p := by
      rw [sqPart_eq_prod_filter]
      exact gcd_prod_of_pairwise_coprime hScop
    rw [hgcd]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) ?_)
      (by positivity)
    intro p hp
    have hp' := hSprime p hp
    have hgp : Nat.gcd c p = if p ∣ c then p else 1 := by
      by_cases h : p ∣ c
      · rw [if_pos h, Nat.gcd_eq_right h]
      · rw [if_neg h]
        exact Nat.coprime_iff_gcd_eq_one.mp ((hp'.coprime_iff_not_dvd.mpr h).symm)
    rw [hgp]
  calc ∑ c ∈ Finset.Icc 1 N, Submission.rho (c ^ 2) d
      ≤ ∑ c ∈ Finset.Icc 1 N, 2 ^ d.primeFactors.card * Nat.gcd c (sqPart d) :=
        Finset.sum_le_sum hper
    _ = 2 ^ d.primeFactors.card * ∑ c ∈ Finset.Icc 1 N, Nat.gcd c (sqPart d) := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ d.primeFactors.card * (N * (sqPart d).divisors.card) :=
        mul_le_mul_of_nonneg_left
          (Commons.NumberTheory.Divisors.sum_gcd_le_of_pos N (sqPart d) (sqPart_pos d hd)) (by positivity)
    _ ≤ 2 ^ d.primeFactors.card * (N * d.divisors.card) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (card_divisors_sqPart_le d hd) (Nat.zero_le N))
          (by positivity)

/-- The root count for `c = 0`: `ρ(0,d) ≤ 2 ^ ω(d) · sqPart d`. -/
lemma rho_zero_le (d : ℕ) (hd : 0 < d) (hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) :
    Submission.rho 0 d ≤ 2 ^ d.primeFactors.card * sqPart d := by
  have h := Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega_mul_of_cubefree
    (d := d) (c := 0) hd hcb
  have hfil : d.primeFactors.filter (fun p => p ^ 2 ∣ d ∧ p ∣ 0)
      = d.primeFactors.filter (fun p => p ^ 2 ∣ d) := by
    apply Finset.filter_congr
    intro p _
    simp
  rw [hfil] at h
  exact h

/-- `2 ^ ω(d) ≤ τ(d)` for `d ≥ 1`. -/
lemma two_pow_card_primeFactors_le_card_divisors (d : ℕ) (hd : 1 ≤ d) :
    2 ^ d.primeFactors.card ≤ d.divisors.card := by
  rw [Nat.card_divisors (by omega : d ≠ 0),
    ← Finset.prod_const (s := d.primeFactors) (2 : ℕ)]
  refine Finset.prod_le_prod₀ (fun p _ => by norm_num) ?_
  intro p hp
  have h1 : 1 ≤ d.factorization p := (Nat.Prime.dvd_iff_one_le_factorization
    (Nat.prime_of_mem_primeFactors hp) (by omega : d ≠ 0)).mp (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- For an even power, `(c : ℤ) ^ 4 = ((c.natAbs) ^ 4 : ℕ)`. -/
lemma int_pow_four_eq_natAbs (c : ℤ) : c ^ 4 = (((c.natAbs) ^ 4 : ℕ) : ℤ) := by
  rw [← Int.natAbs_pow, Int.natCast_natAbs, abs_of_nonneg (by positivity)]

/-- The inner counting function of the decomposition `X2Y4_Ad_eq_sum_c`: the number of `a ∈ ℤ`
with `a ∈ [-⌊√(x-c⁴)⌋-1, ⌊√(x-c⁴)⌋+1]`, `|a| ≤ √(x-c⁴)` and `d ∣ a² + c⁴`. -/
def innerCount (d x : ℕ) (c : ℤ) : ℕ :=
  (Finset.filter (fun a : ℤ =>
      |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) ∧
        ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
    (Finset.Icc (-(⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))
      (⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))).card

/-- **The lattice count for `A_d(x)`.**  For `d ≥ 1` and `x ≥ 1`,
`A_d(x) ≤ (2·⌊√x⌋/d + 2)·∑_{|c| ≤ ⌊x^{1/4}⌋} ρ(c², d)`.

For each `c` the `a`'s with `d ∣ a² + c⁴` form `ρ(c²,d)` residue classes modulo `d`, and each
class meets `[-⌊√x⌋, ⌊√x⌋]` at most `2⌊√x⌋/d + 2` times. -/
theorem Ad_le_sum_rho (d x : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) :
    (Submission.Ad d x : ℝ)
      ≤ (2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2) *
          ∑ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
              (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)),
            (Submission.rho (c.natAbs ^ 2) d : ℝ) := by
  classical
  have hd0 : 0 < d := by omega
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast hx
  -- the decomposition of `A_d(x)` as a sum over `c`
  have hdecomp : (Submission.Ad d x : ℤ)
      = ∑ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
          (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)), (innerCount d x c : ℤ) := by
    have h1 : (Submission.Ad d x : ℤ)
        = (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)
            ∧ (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4}).ncard : ℤ) := by
      rw [Submission.Ad]
      simp only [Submission.an]
      rw [ncard_eq_Ad_sum]
    rw [h1]
    exact Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_eq_sum_c x d hd hx
  -- the per-`c` bound
  have hper : ∀ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
        (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)),
      (innerCount d x c : ℝ)
        ≤ (2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2) *
            (Submission.rho (c.natAbs ^ 2) d : ℝ) := by
    intro c _
    have h4 : (c : ℤ) ^ 4 = (((c.natAbs) ^ 4 : ℕ) : ℤ) := int_pow_four_eq_natAbs c
    -- the `c`-fibre is contained in the `⌊√x⌋`-interval with the same congruence condition
    have hsub : innerCount d x c
        ≤ ((Finset.Icc (-(((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℤ)))
              (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℤ))).filter
            (fun a : ℤ => (d : ℤ) ∣ a ^ 2 + ((c.natAbs : ℕ) : ℤ) ^ 4)).card := by
      refine Finset.card_le_card ?_
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      obtain ⟨hint, habs, hdvd⟩ := ha
      rw [h4] at hdvd
      refine ⟨?_, hdvd⟩
      have habsR : |(a : ℝ)| ≤ Real.sqrt (x : ℝ) :=
        le_trans habs (Real.sqrt_le_sqrt (by
          have h : (0 : ℝ) ≤ (c : ℝ) ^ 4 := by positivity
          linarith))
      have hle : (a.natAbs : ℕ) ≤ ⌊Real.sqrt (x : ℝ)⌋₊ := by
        refine Nat.le_floor ?_
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact habsR
      have hZ : (|a| : ℤ) ≤ (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ)) : ℤ) := by
        rw [← Int.natCast_natAbs a]
        exact_mod_cast hle
      exact Finset.mem_Icc.mpr (abs_le.mp hZ)
    refine le_trans (Nat.cast_le.mpr hsub) ?_
    have hb := Commons.NumberTheory.FriedlanderIwaniec.card_filter_dvd_sq_add_pow_four_le
      (A := ⌊Real.sqrt (x : ℝ)⌋₊) (d := d) (c := c.natAbs) hd0
    refine le_trans (Nat.cast_le.mpr hb) ?_
    have h1 : 2 * (((⌊Real.sqrt (x : ℝ)⌋₊ / d : ℕ)) : ℝ) + 2
        ≤ 2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2 := by
      have h2 : (((⌊Real.sqrt (x : ℝ)⌋₊ / d : ℕ)) : ℝ)
          ≤ ((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
      linarith
    push_cast
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  -- sum the per-`c` bounds
  have hcast : (Submission.Ad d x : ℝ)
      = ∑ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
          (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)), (innerCount d x c : ℝ) := by
    exact_mod_cast hdecomp
  rw [hcast]
  calc ∑ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
          (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)), (innerCount d x c : ℝ)
      ≤ ∑ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
          (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)),
          (2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2) *
            (Submission.rho (c.natAbs ^ 2) d : ℝ) := Finset.sum_le_sum hper
    _ = (2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2) *
          ∑ c ∈ Finset.Icc (-(((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)))
            (((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℤ)),
            (Submission.rho (c.natAbs ^ 2) d : ℝ) := by rw [Finset.mul_sum]

/-- Splitting a symmetric `ℤ`-sum: `∑_{c ∈ [-N,N]} g |c| = g 0 + 2 ∑_{c ∈ [1,N]} g c`. -/
lemma sum_Icc_abs_eq (g : ℤ → ℝ) (N : ℕ) :
    ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g ((c.natAbs : ℕ) : ℤ)
      = g 0 + 2 * ∑ c ∈ Finset.Icc 1 N, g ((c : ℕ) : ℤ) := by
  classical
  have hsplit : Finset.Icc (-(N : ℤ)) (N : ℤ)
      = Finset.Icc (-(N : ℤ)) (-1 : ℤ) ∪ Finset.Icc 0 (N : ℤ) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (-(N : ℤ)) (-1 : ℤ)) (Finset.Icc 0 (N : ℤ)) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hneg : ∑ c ∈ Finset.Icc (-(N : ℤ)) (-1 : ℤ), g ((c.natAbs : ℕ) : ℤ)
      = ∑ c ∈ Finset.Icc 1 N, g ((c : ℕ) : ℤ) := by
    refine Finset.sum_bij' (fun c (_ : c ∈ Finset.Icc (-(N : ℤ)) (-1 : ℤ)) => (-c).natAbs)
      (fun k (_ : k ∈ Finset.Icc 1 N) => -(k : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_Icc] at hc ⊢
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro c hc
      rw [Finset.mem_Icc] at hc
      have h : ((-c).natAbs : ℤ) = -c := by
        rw [Int.natCast_natAbs, abs_of_pos (by omega : (0 : ℤ) < -c)]
      rw [h]
      ring
    · intro k _
      simp only [neg_neg, Int.natAbs_natCast]
    · intro c _
      congr 1
      exact_mod_cast (Int.natAbs_neg c).symm
  have hpos : ∑ c ∈ Finset.Icc 0 (N : ℤ), g ((c.natAbs : ℕ) : ℤ)
      = g 0 + ∑ c ∈ Finset.Icc 1 N, g ((c : ℕ) : ℤ) := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp
    · have h2 : Finset.Icc (0 : ℤ) (N : ℤ)
          = insert 0 (Finset.image (fun c : ℕ => (c : ℤ)) (Finset.Icc 1 N)) := by
        ext c
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image]
        constructor
        · intro hc
          rcases eq_or_lt_of_le hc.1 with h | h
          · exact Or.inl h.symm
          · right
            refine ⟨c.natAbs, ?_, ?_⟩
            · omega
            · rw [Int.natCast_natAbs, abs_of_nonneg (le_of_lt h)]
        · rintro (rfl | ⟨k, hk, rfl⟩)
          · exact ⟨le_rfl, Nat.cast_nonneg _⟩
          · omega
      rw [h2, Finset.sum_insert (by
        simp only [Finset.mem_image]
        rintro ⟨k, hk, hk0⟩
        rw [Finset.mem_Icc] at hk
        omega), Finset.sum_image]
      · simp only [Int.natAbs_natCast, Int.natAbs_zero, Nat.cast_zero]
      · intro a _ b _ hab
        exact Nat.cast_injective hab
  rw [hneg, hpos]
  ring

/-- **(2.8)-type bound for X² + Y⁴, elementary.**  For **cubefree** `d` with `d² ≤ x`,
`A_d(x) ≤ 12·τ(d)²·x^{3/4}/d`.

This replaces the companion's `(1.6)` (`A_d(x) ≪ d^{-1}τ(d)^8A(x)` for `d ≤ x^{1/3}`) — which is
*false* for this sequence at `d = p^4` — by the elementary bound the paper actually uses. -/
theorem Ad_le_tau_sq_mul_rpow (d x : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x)
    (hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) (hdx : d ^ 2 ≤ x) :
    (Submission.Ad d x : ℝ) ≤ 12 * ((d.divisors.card : ℝ)) ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 4) / (d : ℝ) := by
  classical
  have hd0 : 0 < d := by omega
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast hx
  set N : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ with hN
  set T : ℕ := d.divisors.card with hT
  -- the `ρ`-sum
  have hsum : ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (Submission.rho (c.natAbs ^ 2) d : ℝ)
      ≤ 2 ^ d.primeFactors.card *
          ((sqPart d : ℝ) + 2 * (N : ℝ) * (T : ℝ)) := by
    have hsplit := sum_Icc_abs_eq (fun k : ℤ => (Submission.rho (k.toNat ^ 2) d : ℝ)) N
    have hL : ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (Submission.rho (c.natAbs ^ 2) d : ℝ)
        = ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (Submission.rho (((c.natAbs : ℤ)).toNat ^ 2) d : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Int.toNat_natCast]
    have h01 : (Submission.rho ((0 : ℤ).toNat ^ 2) d : ℝ) = (Submission.rho 0 d : ℝ) := by
      simp
    have hpos : ∀ c : ℕ, (Submission.rho (((c : ℤ)).toNat ^ 2) d : ℝ)
        = (Submission.rho (c ^ 2) d : ℝ) := by
      intro c
      rw [Int.toNat_natCast]
    rw [hL, hsplit, h01, Finset.sum_congr rfl (fun c _ => hpos c)]
    have h1 : ((Submission.rho 0 d : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ d.primeFactors.card * (sqPart d : ℝ) := by
      have := rho_zero_le d hd0 hcb
      exact_mod_cast this
    have h2 : (∑ c ∈ Finset.Icc 1 N, (Submission.rho (c ^ 2) d : ℝ))
        ≤ (2 : ℝ) ^ d.primeFactors.card * ((N : ℝ) * (T : ℝ)) := by
      have := sum_rho_le d N hd hcb
      rw [hT]
      exact_mod_cast this
    calc ((Submission.rho 0 d : ℕ) : ℝ)
          + 2 * ∑ c ∈ Finset.Icc 1 N, (Submission.rho (c ^ 2) d : ℝ)
        ≤ 2 ^ d.primeFactors.card * (sqPart d : ℝ)
            + 2 * (2 ^ d.primeFactors.card * ((N : ℝ) * (T : ℝ))) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 2 ^ d.primeFactors.card *
            ((sqPart d : ℝ) + 2 * (N : ℝ) * (T : ℝ)) := by ring
  -- real-number bookkeeping
  have hsqrt : ((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    refine le_trans (Nat.floor_le (Real.sqrt_nonneg _)) ?_
    rw [Real.sqrt_eq_rpow]
  have hNle : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hN]
    exact Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hdsqrt : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le ?_
    simpa [pow_two] using (by exact_mod_cast hdx : ((d : ℝ)) ^ 2 ≤ (x : ℝ))
  have hsqPart : (sqPart d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (sqPart d : ℝ) ≤ Real.sqrt (d : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      have h2 : (sqPart d : ℝ) ^ 2 ≤ (d : ℝ) := by
        have h3 : sqPart d * sqPart d ≤ d := by
          rw [← pow_two]
          exact Nat.le_of_dvd hd0 (sqPart_sq_dvd d)
        rw [pow_two]
        exact_mod_cast h3
      exact h2
    refine le_trans h1 ?_
    have h3 : Real.sqrt (d : ℝ) ≤ Real.sqrt (Real.sqrt (x : ℝ)) :=
      Real.sqrt_le_sqrt (by rwa [Real.sqrt_eq_rpow] : (d : ℝ) ≤ Real.sqrt (x : ℝ))
    refine le_trans h3 ?_
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le,
      show ((1 : ℝ) / 2) * (1 / 2) = 1 / 4 by norm_num]
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by
    rw [hT]
    have h : 0 < d.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, by omega⟩⟩
    exact_mod_cast h
  have h2ω : (2 : ℝ) ^ d.primeFactors.card ≤ (T : ℝ) := by
    rw [hT]
    exact_mod_cast two_pow_card_primeFactors_le_card_divisors d hd
  have hx4 : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  have hx12 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  -- the `ρ`-sum is `≤ 3 τ(d)² x^{1/4}`
  have hsum3 : ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (Submission.rho (c.natAbs ^ 2) d : ℝ)
      ≤ 3 * (T : ℝ) ^ 2 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    refine le_trans hsum ?_
    have hinner : (sqPart d : ℝ) + 2 * (N : ℝ) * (T : ℝ)
        ≤ 3 * (T : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 : (sqPart d : ℝ) ≤ (T : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4) :=
        le_trans hsqPart (le_mul_of_one_le_left (le_of_lt hx4) hT1)
      have h2 : 2 * (N : ℝ) * (T : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 4) * (T : ℝ) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNle (by norm_num :
          (0:ℝ) ≤ 2)) (Nat.cast_nonneg T)
        linarith [this]
      nlinarith [h1, h2, hx4, hT1]
    have h2ωnn : (0 : ℝ) ≤ 2 ^ d.primeFactors.card := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hinner h2ωnn) ?_
    have hb := mul_le_mul_of_nonneg_left h2ω
      (show (0 : ℝ) ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 4) by positivity)
    calc 2 ^ d.primeFactors.card * (3 * (T : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4))
        = (3 * (x : ℝ) ^ ((1 : ℝ) / 4)) * 2 ^ d.primeFactors.card * (T : ℝ) := by ring
      _ ≤ (3 * (x : ℝ) ^ ((1 : ℝ) / 4)) * (T : ℝ) * (T : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg T)
          exact mul_le_mul_of_nonneg_left h2ω (by positivity)
      _ = 3 * (T : ℝ) ^ 2 * (x : ℝ) ^ ((1 : ℝ) / 4) := by ring
  -- assemble
  refine le_trans (Ad_le_sum_rho d x hd hx) ?_
  have hsum2 : (0 : ℝ) ≤ ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (Submission.rho (c.natAbs ^ 2) d : ℝ) := Finset.sum_nonneg (fun c _ => Nat.cast_nonneg _)
  have hfac : (2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2)
      ≤ 4 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (d : ℝ)) := by
    have h1 : ((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) / (d : ℝ) :=
      div_le_div_of_nonneg_right hsqrt hdR.le
    have h2 : (2 : ℝ) ≤ 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (d : ℝ)) := by
      rw [le_mul_iff_one_le_right (by norm_num : (0:ℝ) < 2), one_le_div hdR]
      exact hdsqrt
    linarith [h1, h2]
  have hfac2 : (0 : ℝ) ≤ 2 * (((⌊Real.sqrt (x : ℝ)⌋₊ : ℕ) : ℝ) / (d : ℝ)) + 2 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right hfac hsum2) ?_
  refine le_trans (mul_le_mul_of_nonneg_left hsum3 (by positivity)) ?_
  have hx34 : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 4)
      = (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hf : 4 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (d : ℝ)) * (3 * (T : ℝ) ^ 2 * (x : ℝ) ^ ((1 : ℝ) / 4))
      = 12 * (T : ℝ) ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 4) / (d : ℝ) := by
    rw [show 4 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (d : ℝ))
          * (3 * (T : ℝ) ^ 2 * (x : ℝ) ^ ((1 : ℝ) / 4))
        = 12 * (T : ℝ) ^ 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 4)) / (d : ℝ) by ring]
    rw [hx34]
  exact le_of_eq hf

/-- `A_d(x) ≤ A(x)` (the congruence condition only removes lattice points). -/
lemma Ad_le_Aseq (d x : ℕ) : Submission.Ad d x ≤ Submission.Aseq x := by
  rw [Submission.Ad, Submission.Aseq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun n _ _ => Nat.zero_le _)

/-- **The elementary verification of the sieve input `(2.8)` for `X² + Y⁴`.**  For **cubefree**
`d` with `d² ≤ x`, `A_d(x) ≤ C·τ(d)²·A(x)/d`.

(The companion's `(1.6)` — `A_d(x) ≪ d^{-1}τ(d)^8A(x)` for `d ≤ x^{1/3}` — is *false* for this
sequence at `d = p^4`, where the local density is `≍ p^{-3}`; the main paper (p. 962) uses the
present elementary bound instead, with `τ(d)` in place of `τ(d)^8` and the range `d ≤ x^{1/2-ε}`
here sharpened to `d ≤ x^{1/2}` and `τ(d)²`.) -/
theorem Ad_le_tau_sq_div_of_cubefree : ∃ C : ℝ, 0 < C ∧ ∀ d x : ℕ, 1 ≤ d →
    (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) → d ^ 2 ≤ x →
    (Submission.Ad d x : ℝ)
      ≤ C * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ)) * (Submission.Aseq x : ℝ) := by
  obtain ⟨c₀, hc₀pos, X₀, hAseq⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
  refine ⟨max (12 / c₀) ((X₀ : ℝ) + 1), ?_, ?_⟩
  · refine lt_of_lt_of_le (by positivity) (le_max_left _ _)
  · intro d x hd hcb hdx
    have hd0 : 0 < d := by omega
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hT : (0 : ℝ) ≤ ((d.divisors.card : ℝ)) ^ 2 / (d : ℝ) := by positivity
    have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
    rcases lt_or_ge X₀ x with hX | hX
    · have h1 : (Submission.Ad d x : ℝ)
          ≤ 12 * ((d.divisors.card : ℝ)) ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 4) / (d : ℝ) :=
        Ad_le_tau_sq_mul_rpow d x hd (by omega) hcb hdx
      have h2 : c₀ * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAseq x (le_of_lt hX)
      have h3 : (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) / c₀ := by
        rw [le_div_iff₀ hc₀pos]
        rw [mul_comm]
        exact h2
      calc (Submission.Ad d x : ℝ)
          ≤ 12 * ((d.divisors.card : ℝ)) ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 4) / (d : ℝ) := h1
        _ ≤ 12 * ((d.divisors.card : ℝ)) ^ 2 * ((Submission.Aseq x : ℝ) / c₀) / (d : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hdR.le
            refine mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (12 / c₀) * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ)) * (Submission.Aseq x : ℝ) := by
            ring
        _ ≤ max (12 / c₀) ((X₀ : ℝ) + 1) * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
              * (Submission.Aseq x : ℝ) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (le_max_left _ _) hT) hA0
    · have h1 : (Submission.Ad d x : ℝ) ≤ (Submission.Aseq x : ℝ) := by
        exact_mod_cast Ad_le_Aseq d x
      have hx1 : 1 ≤ x :=
        le_trans hd (le_trans (Nat.le_self_pow (by norm_num) d) hdx)
      have hdX : (d : ℝ) ≤ (X₀ : ℝ) := by
        have hdx' : d ≤ x :=
          le_trans (Nat.le_self_pow (by norm_num) d) hdx
        exact_mod_cast le_trans hdx' hX
      have hX0 : (1 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast le_trans hx1 hX
      have hbd : (1 : ℝ) ≤ max (12 / c₀) ((X₀ : ℝ) + 1)
          * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ)) := by
        have hT1 : (1 : ℝ) ≤ (d.divisors.card : ℝ) := by
          have h : 0 < d.divisors.card :=
            Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, by omega⟩⟩
          exact_mod_cast h
        have hτ : (1 : ℝ) ≤ ((d.divisors.card : ℝ)) ^ 2 := one_le_pow₀ hT1
        have h6 : (X₀ : ℝ) + 1 ≤ max (12 / c₀) ((X₀ : ℝ) + 1) := le_max_right _ _
        have h7 : (1 : ℝ) / (d : ℝ) ≤ ((d.divisors.card : ℝ)) ^ 2 / (d : ℝ) :=
          div_le_div_of_nonneg_right hτ hdR.le
        have h8 : ((X₀ : ℝ) + 1) * ((1 : ℝ) / (d : ℝ))
            ≤ max (12 / c₀) ((X₀ : ℝ) + 1) * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ)) :=
          mul_le_mul h6 h7 (by positivity) (by linarith [hX0])
        have h4 : (1 : ℝ) ≤ ((X₀ : ℝ) + 1) * ((1 : ℝ) / (d : ℝ)) := by
          rw [mul_one_div, le_div_iff₀ hdR]
          linarith [hdX]
        linarith [h8, h4]
      calc (Submission.Ad d x : ℝ) ≤ (Submission.Aseq x : ℝ) := h1
        _ ≤ max (12 / c₀) ((X₀ : ℝ) + 1) * (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
              * (Submission.Aseq x : ℝ) := le_mul_of_one_le_left hA0 hbd

end

end Submission.ASP
