import Submission.ZagierHoffmanProof.ThakurDeg4
import Submission.Commons.Data.Nat.noCarry_iff_digits_le
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.CharP.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Prime `q`: the digit theory of the least good shift `jMin`
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The digitwise "no carry" predicate in base `q`. -/
def noCarry (q a b : ℕ) : Prop := ∀ i : ℕ, a / q ^ i % q + b / q ^ i % q < q

section CharP

/-- A finite field whose cardinality is a prime `p` has characteristic `p`. -/
lemma charP_of_card_prime (hp : (Nat.card F).Prime) : CharP F (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpchar, _n, hprime, hcard⟩ := FiniteField.card' F
  have hcard' : p ^ (_n : ℕ) = Nat.card F := by rw [← hcard, Fintype.card_eq_nat_card]
  have hdvd : p ∣ Nat.card F := hcard' ▸ dvd_pow_self p (Nat.pos_iff_ne_zero.mp _n.pos)
  have hpeq : p = Nat.card F := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hdvd
  exact hpeq ▸ hpchar

end CharP

section Kummer

/-- Kummer/Lucas at the level of `ZMod p`: `C(a+b,a)` is invertible modulo the prime `p`
exactly when adding `a` and `b` in base `p` produces no carry. -/
lemma zmod_choose_add_ne_zero_iff {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ((Nat.choose (a + b) a : ℕ) : ZMod p) ≠ 0 ↔
      ∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < p := hp.pos
  have hge : 2 ≤ p := hp.two_le
  set N := a + b + 2 with hN
  have hlt1 : a + b < p ^ N := by
    have h1 : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ (a + b) ≤ p ^ N := by
      have h3a : (2 : ℕ) ^ (a + b) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3b : (2 : ℕ) ^ N ≤ p ^ N := Nat.pow_le_pow_left hge N
      omega
    omega
  have hlt2 : a < p ^ N := lt_of_le_of_lt (Nat.le_add_right a b) hlt1
  have hL := Choose.choose_modEq_prod_range_choose_nat (p := p) (n := a + b) (k := a)
    (a := N) hlt1 hlt2
  have hL' : (((a + b).choose a : ℕ) : ZMod p) =
      ((∏ i ∈ Finset.range N, ((a + b) / p ^ i % p).choose (a / p ^ i % p) : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hL
  have hfac : ∀ i ∈ Finset.range N,
      ((((a + b) / p ^ i % p).choose (a / p ^ i % p) : ℕ) : ZMod p) ≠ 0 ↔
        a / p ^ i % p ≤ (a + b) / p ^ i % p := by
    intro i _
    have h3 : (a + b) / p ^ i % p < p := Nat.mod_lt _ hpos
    by_cases hle' : a / p ^ i % p ≤ (a + b) / p ^ i % p
    · exact Iff.intro (fun _ => hle') (fun _ => by
        intro h0
        have hne' : p ∣ (((a + b) / p ^ i % p).choose (a / p ^ i % p)) :=
          (CharP.cast_eq_zero_iff (ZMod p) p _).mp h0
        exact (hp.coprime_iff_not_dvd).mp (hp.coprime_choose_of_lt h3 hle') hne')
    · rw [not_le] at hle'
      have hzero : (((a + b) / p ^ i % p).choose (a / p ^ i % p) : ℕ) = 0 :=
        Nat.choose_eq_zero_of_lt hle'
      exact Iff.intro (fun hc => absurd (by rw [hzero]; simp : ((((a+b) / p ^ i % p).choose (a / p ^ i % p) : ℕ) : ZMod p) = 0) hc)
        (fun hc => absurd hc (not_le.mpr hle'))
  have hbig : ∀ i ≥ N, (a + b) / p ^ i = 0 := fun i hi =>
    Nat.div_eq_of_lt (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right hpos hi))
  rw [Commons.Data.Nat.noCarry_iff_digits_le hp a b]
  constructor
  · intro h i
    by_cases hi : i < N
    · have h1 : ((∏ i ∈ Finset.range N,
            ((a + b) / p ^ i % p).choose (a / p ^ i % p) : ℕ) : ZMod p) ≠ 0 := by
        rw [← hL']; exact h
      rw [Nat.cast_prod] at h1
      exact (hfac i (Finset.mem_range.mpr hi)).mp
        ((Finset.prod_ne_zero_iff.mp h1) i (Finset.mem_range.mpr hi))
    · have hz : a / p ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hlt2
        (Nat.pow_le_pow_right hpos (by omega)))
      rw [hz, hbig i (by omega)]
  · intro h
    rw [hL', Nat.cast_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => (hfac i hi).mpr ?_
    by_cases hi' : i < N
    · exact h i
    · exact absurd (Finset.mem_range.mp hi) hi'

end Kummer

section GoodJ

/-- Kummer in a field of prime cardinality: `C(a+b,a)` is nonzero iff there is no
base-`p` carry in `a + b`. -/
lemma choose_add_ne_zero_iff_field (hp : (Nat.card F).Prime) (a b : ℕ) :
    (((Nat.choose (a + b) a : ℕ)) : F) ≠ 0 ↔ noCarry (Nat.card F) a b := by
  haveI : CharP F (Nat.card F) := charP_of_card_prime F hp
  have hiff : (((Nat.choose (a + b) a : ℕ)) : F) ≠ 0 ↔
      (((Nat.choose (a + b) a : ℕ)) : ZMod (Nat.card F)) ≠ 0 := by
    rw [Ne, Ne, CharP.cast_eq_zero_iff F (Nat.card F),
      CharP.cast_eq_zero_iff (ZMod (Nat.card F)) (Nat.card F)]
  rw [hiff, noCarry]
  exact zmod_choose_add_ne_zero_iff hp a b

/-- **The digit characterisation of a good shift** for `q = Nat.card F` prime:
`j` is good at `k` iff it is positive, divisible by `q-1`, and adding it to `k-1`
in base `q` produces no carry. -/
lemma isGoodJ_iff_noCarry (hp : (Nat.card F).Prime) (k j : ℕ) (hk : 1 ≤ k) :
    IsGoodJ F k j ↔ 1 ≤ j ∧ (Nat.card F - 1) ∣ j ∧ noCarry (Nat.card F) j (k - 1) := by
  have hj : k + j - 1 = j + (k - 1) := by omega
  rw [IsGoodJ, binF, mul_ne_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [hj] at h3
    exact (choose_add_ne_zero_iff_field F hp j (k - 1)).mp h3.2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, pow_ne_zero _ (by norm_num), ?_⟩
    rw [hj]
    exact (choose_add_ne_zero_iff_field F hp j (k - 1)).mpr h3

end GoodJ

section JMinDigits

variable {F}

/-- The least good shift produces no carry with `k-1` (for `q` prime). -/
lemma jMin_noCarry (hp : (Nat.card F).Prime) (k : ℕ+) :
    noCarry (Nat.card F) (jMin F k) ((k : ℕ) - 1) :=
  ((isGoodJ_iff_noCarry F hp (k : ℕ) (jMin F k) k.pos).mp (jMin_spec F k)).2.2

/-- Digitwise bound for the least good shift. -/
lemma jMin_digit_le (hp : (Nat.card F).Prime) (k : ℕ+) (i : ℕ) :
    jMin F k / (Nat.card F) ^ i % (Nat.card F) ≤
      (Nat.card F - 1) - (((k : ℕ) - 1) / (Nat.card F) ^ i % (Nat.card F)) := by
  have h := jMin_noCarry (F := F) hp k i
  omega

/-- The lowest digit of the least good shift is the full capacity. -/
lemma jMin_mod_le (hp : (Nat.card F).Prime) (k : ℕ+) :
    jMin F k % (Nat.card F) ≤
      (Nat.card F - 1) - (((k : ℕ) - 1) % (Nat.card F)) := by
  simpa using jMin_digit_le (F := F) hp k 0

/-- `q - 1` divides `q^t - 1` for `t ≥ 1`. -/
lemma dvd_pow_sub_one (q t : ℕ) (hq : 1 ≤ q) (ht : 1 ≤ t) : (q - 1) ∣ q ^ t - 1 := by
  have key : ∀ s : ℕ, (q - 1) ∣ q ^ (s + 1) - 1 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        have h1 : q ^ (s + 1 + 1) - 1 = q * (q ^ (s + 1) - 1) + (q - 1) := by
          have h3 : 1 ≤ q ^ (s + 1) := Nat.one_le_pow _ _ (by omega)
          have h4 : q ≤ q * q ^ (s + 1) := by
            calc q = q * 1 := (mul_one q).symm
              _ ≤ q * q ^ (s + 1) := Nat.mul_le_mul_left _ h3
          rw [pow_succ, Nat.mul_comm (q ^ (s+1)) q, Nat.mul_sub_left_distrib, Nat.mul_one]
          omega
        rw [h1]
        exact Nat.dvd_add (dvd_mul_of_dvd_right ih q) (dvd_refl (q - 1))
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le ht
  rw [hs]
  simpa [Nat.add_comm] using key s

/-- The `i`-th quotient of `q ^ t * b` for `i ≤ t`. -/
lemma mul_pow_div_pow (q t i b : ℕ) (hq : 0 < q) (hi : i ≤ t) :
    q ^ t * b / q ^ i = q ^ (t - i) * b := by
  have h : q ^ t = q ^ i * q ^ (t - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [h, mul_assoc, Nat.mul_div_cancel_left (q ^ (t - i) * b) (Nat.pow_pos (n := i) hq)]

/-- Subtracting one from a number whose last digit is nonzero decreases the last digit. -/
lemma sub_one_mod (q a : ℕ) (h : 1 ≤ a % q) (hq : 0 < q) : (a - 1) % q = a % q - 1 := by
  have h1 : a = q * (a / q) + a % q := (Nat.div_add_mod a q).symm
  have h2 : q * (a / q) + a % q - 1 = q * (a / q) + (a % q - 1) := by omega
  have h3 : (q * (a / q) + a % q) % q = a % q := by
    rw [Nat.mul_add_mod_self_left q (a / q) (a % q), Nat.mod_eq_of_lt (Nat.mod_lt a hq)]
  rw [h1, h2, h3, Nat.mul_add_mod_self_left q (a / q) (a % q - 1),
    Nat.mod_eq_of_lt (by have := Nat.mod_lt a hq; omega)]

/-- If every quotient of `a` by a power of `q` is divisible by `q`, then `a = 0`. -/
lemma eq_zero_of_all_dvd (q : ℕ) (hq2 : 2 ≤ q) : ∀ a : ℕ, (∀ s : ℕ, q ∣ a / q ^ s) → a = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro h
    have hq : 0 < q := by omega
    have h0 : q ∣ a := by simpa using h 0
    rcases Nat.eq_zero_or_pos a with hz | hpos
    · exact hz
    · exfalso
      obtain ⟨m, hm⟩ := h0
      have hmlt : m < a := by
        rcases Nat.eq_zero_or_pos m with hz | hpos'
        · rw [hz, mul_zero] at hm
          omega
        · have h2 : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq2
          have h3 : m < 2 * m := by omega
          rw [hm]
          exact lt_of_lt_of_le h3 h2
      have hm2 : ∀ s : ℕ, q ∣ m / q ^ s := by
        intro s
        have h1 : a / q ^ (s + 1) = m / q ^ s := by
          rw [hm, pow_succ', ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left m hq]
        have := h (s + 1)
        rwa [h1] at this
      have hm0 := ih m hmlt hm2
      rw [hm0, mul_zero] at hm
      omega

end JMinDigits

end ZagierHoffmanPositiveChar
