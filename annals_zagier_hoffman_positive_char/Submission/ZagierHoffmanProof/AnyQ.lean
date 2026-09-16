/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.PrimeQ
import Submission.ZagierHoffmanProof.DegLin
import Submission.Commons.Data.Nat.div_pow_add_mul_mod
import Submission.Commons.Data.Nat.div_pow_pow_sub_one_mod
import Submission.Commons.Data.Nat.noCarry_pow_mul_shift
import Submission.Commons.Data.Nat.noCarry_pred_mul_pow
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The level-one digit theory of `jMin` over an arbitrary finite field

For a finite field `F` of cardinality `q = p ^ f` (`p = ringChar F`) the least good shift
`jMin F x` is characterised by *base-`p`* digits (Kummer's theorem in characteristic `p`):
`j` is good at `k` iff `1 ≤ j`, `(q-1) ∣ j` and adding `j` to `k-1` in base `p` produces no
carry.  The main result is the closed form

  `jMin F x = (q-1) * x`  for `1 ≤ x ≤ q`,

for **every** finite field `F` (the prime case `q = p` is `DegLin.jMin_eq_pred_mul`, where the
base and the modulus coincide).  Consequently the map `T x = x + jMin F x` is linear on `[1,q]`:

  `T^i x = q^i * x`,

and the depth-one power sums have the exact degree `v (P F 1 (q^i x)) = exp (-(q ^ (i+1) * x))`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section CardPrime

/-- The characteristic of `F` together with a power description of the cardinality. -/
lemma exists_ringChar_pow : ∃ (p f : ℕ), p.Prime ∧ CharP F p ∧ ringChar F = p ∧
    Nat.card F = p ^ f ∧ 1 ≤ f := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hchar, n, hprime, hcard⟩ := FiniteField.card' F
  refine ⟨p, (n : ℕ), hprime, hchar, ?_, ?_, n.pos⟩
  · exact ringChar.eq F p
  · rw [← Fintype.card_eq_nat_card, hcard]

end CardPrime

section KummerAny

/-- **Kummer's theorem for an arbitrary finite field**: the binomial coefficient `C(a+b,a)` is
nonzero in `F` iff adding `a` and `b` in base `p = ringChar F` produces no carry. -/
theorem choose_add_ne_zero_iff_char (a b : ℕ) :
    (((Nat.choose (a + b) a : ℕ)) : F) ≠ 0 ↔ noCarry (ringChar F) a b := by
  obtain ⟨p, f, hprime, hchar, hring, -, -⟩ := exists_ringChar_pow F
  haveI : CharP F p := hchar
  haveI : Fact p.Prime := ⟨hprime⟩
  rw [hring]
  have hiff : (((Nat.choose (a + b) a : ℕ)) : F) ≠ 0 ↔
      (((Nat.choose (a + b) a : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, Ne, CharP.cast_eq_zero_iff F p, CharP.cast_eq_zero_iff (ZMod p) p]
  rw [hiff, noCarry]
  exact zmod_choose_add_ne_zero_iff hprime a b

/-- **The digit characterisation of a good shift** for an arbitrary finite field:
`j` is good at `k` iff it is positive, divisible by `q-1`, and adding it to `k-1` in base
`p = ringChar F` produces no carry. -/
theorem isGoodJ_iff_noCarry_char (k j : ℕ) (hk : 1 ≤ k) :
    IsGoodJ F k j ↔ 1 ≤ j ∧ (Nat.card F - 1) ∣ j ∧ noCarry (ringChar F) j (k - 1) := by
  have hj : k + j - 1 = j + (k - 1) := by omega
  rw [IsGoodJ, binF, mul_ne_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [hj] at h3
    exact (choose_add_ne_zero_iff_char F j (k - 1)).mp h3.2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, pow_ne_zero _ (by norm_num), ?_⟩
    rw [hj]
    exact (choose_add_ne_zero_iff_char F j (k - 1)).mpr h3

end KummerAny



section JMinLeCardAny

/-- **The shift `(q-1) * x` is good at `x`** for `1 ≤ x ≤ q`, over an arbitrary finite field. -/
theorem isGoodJ_pred_mul_char {x : ℕ} (hx : 1 ≤ x) (hxq : x ≤ Nat.card F) :
    IsGoodJ F x ((Nat.card F - 1) * x) := by
  obtain ⟨p, f, hprime, hchar, hring, hcard, hf⟩ := exists_ringChar_pow F
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hqne : Nat.card F - 1 ≠ 0 := by omega
  have hxne : x ≠ 0 := by omega
  rw [isGoodJ_iff_noCarry_char F x ((Nat.card F - 1) * x) hx, hring]
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hqne hxne),
    dvd_mul_right _ _, ?_⟩
  intro i
  have hxq' : x ≤ p ^ f := hcard ▸ hxq
  have h := Commons.Data.Nat.noCarry_pred_mul_pow p f x hprime.two_le hf hx hxq' i
  simpa only [hcard] using h

/-- **`jMin` on `[1,q]` for an arbitrary finite field**: `jMin F x = (q-1) * x`. -/
theorem jMin_eq_pred_mul_char {x : ℕ} (hx : 1 ≤ x) (hxq : x ≤ Nat.card F) :
    jMin F ⟨x, hx⟩ = (Nat.card F - 1) * x := by
  obtain ⟨p, f, hprime, hchar, hring, hcard, hf⟩ := exists_ringChar_pow F
  have hq1 : 1 ≤ Nat.card F := by have := two_le_card F; omega
  refine le_antisymm (jMin_le F (isGoodJ_pred_mul_char F hx hxq)) ?_
  by_contra hcon
  have hlt : jMin F ⟨x, hx⟩ < (Nat.card F - 1) * x := not_le.mp hcon
  have hj1 : 1 ≤ jMin F ⟨x, hx⟩ := jMin_pos F _
  have hgood := jMin_spec F ⟨x, hx⟩
  have hnc : ∀ m : ℕ, (jMin F ⟨x, hx⟩) / p ^ m % p + (x - 1) / p ^ m % p < p := by
    have h := ((isGoodJ_iff_noCarry_char F x (jMin F ⟨x, hx⟩) hx).mp hgood).2.2
    rw [hring] at h
    exact h
  have hdvd : (Nat.card F - 1) ∣ jMin F ⟨x, hx⟩ := hgood.2.1
  have hms := (Commons.Data.Nat.noCarry_iff_mod_sum (p := p) hprime.two_le).mp hnc f
  have hms' : jMin F ⟨x, hx⟩ % Nat.card F + (x - 1) % Nat.card F < Nat.card F := by
    rw [hcard]
    exact hms
  have hx1 : (x - 1) % Nat.card F = x - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hx1] at hms'
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  by_cases hmq : m ≤ Nat.card F
  · have hmod := Commons.Data.Nat.pred_mul_mod (q := Nat.card F) hq1 hmpos hmq
    rw [hm] at hms'
    rw [hmod] at hms'
    have hmx : x ≤ m := by omega
    have hchain : (Nat.card F - 1) * x ≤ (Nat.card F - 1) * m := Nat.mul_le_mul_left _ hmx
    rw [← hm] at hchain
    omega
  · have hmq' : Nat.card F ≤ m := by omega
    have hmul : (Nat.card F - 1) * Nat.card F ≤ (Nat.card F - 1) * m := by
      have h1 : (Nat.card F) * (Nat.card F - 1) ≤ m * (Nat.card F - 1) :=
        Nat.mul_le_mul_right _ hmq'
      rwa [mul_comm (Nat.card F) (Nat.card F - 1), mul_comm m (Nat.card F - 1)] at h1
    have h3 : (Nat.card F - 1) * x ≤ (Nat.card F - 1) * Nat.card F :=
      Nat.mul_le_mul_left _ hxq
    have hchain : (Nat.card F - 1) * x ≤ (Nat.card F - 1) * m := le_trans h3 hmul
    rw [← hm] at hchain
    omega

/-- The `ℕ+`-variable form of `jMin_eq_pred_mul_char`. -/
theorem jMin_eq_pred_mul_char_pnat (k : ℕ+) (hk : (k : ℕ) ≤ Nat.card F) :
    jMin F k = (Nat.card F - 1) * (k : ℕ) :=
  jMin_eq_pred_mul_char F k.pos hk

end JMinLeCardAny

section JMinPowAny

/-- `jMin` only depends on the value of its argument. -/
lemma jMin_congr {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a = b) :
    jMin F ⟨a, ha⟩ = jMin F ⟨b, hb⟩ := by
  subst h
  rfl

/-- **`q ^ i * ((q-1) * x)` is good at `q ^ i * x`** for `1 ≤ x ≤ q`. -/
theorem isGoodJ_pow_mul_char (i : ℕ) (k : ℕ+) (hk : (k : ℕ) ≤ Nat.card F) :
    IsGoodJ F (Nat.card F ^ i * (k : ℕ)) (Nat.card F ^ i * ((Nat.card F - 1) * (k : ℕ))) := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi
  · subst hi0
    simpa using isGoodJ_pred_mul_char F k.pos hk
  obtain ⟨p, f, hprime, hchar, hring, hcard, hf⟩ := exists_ringChar_pow F
  have hp : 2 ≤ p := hprime.two_le
  have hp0 : 0 < p := by omega
  have hfi : 1 ≤ f * i := Nat.mul_pos hf hi
  have hq0 : 0 < Nat.card F := by have := two_le_card F; omega
  have hqne : Nat.card F - 1 ≠ 0 := by have := two_le_card F; omega
  have hxne : (k : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp k.pos
  have hx1 : 1 ≤ (k : ℕ) := k.pos
  have hk1 : 1 ≤ Nat.card F ^ i * (k : ℕ) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero i hq0.ne') hxne)
  rw [isGoodJ_iff_noCarry_char F (Nat.card F ^ i * (k : ℕ)) _ hk1, hring]
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero i hq0.ne')
      (Nat.mul_ne_zero hqne hxne)), dvd_mul_of_dvd_right (dvd_mul_right _ _) _, ?_⟩
  have hpow : Nat.card F ^ i = p ^ (f * i) := by rw [hcard, pow_mul]
  have hdec : p ^ (f * i) * (k : ℕ) - 1 = p ^ (f * i) * ((k : ℕ) - 1) + (p ^ (f * i) - 1) :=
    pow_mul_sub_one_decomp (q := p) (i := f * i) (x := (k : ℕ)) hp0 hx1
  have hxq' : (k : ℕ) ≤ p ^ f := hcard ▸ hk
  unfold noCarry
  rw [hpow, hdec, Commons.Data.Nat.noCarry_pow_mul_shift p (f * i) hp
    ((Nat.card F - 1) * (k : ℕ)) ((k : ℕ) - 1)]
  intro m
  have h := Commons.Data.Nat.noCarry_pred_mul_pow p f (k : ℕ) hp hf hx1 hxq' m
  simpa only [hcard] using h

/-- **`jMin (q ^ i * x) = q ^ i * ((q-1) * x)`** for `1 ≤ x ≤ q`, stated with the value as a
variable so that it can be applied to opaque positive naturals. -/
theorem jMin_pow_mul_char_value (i x n : ℕ) (hx : 1 ≤ x) (hxq : x ≤ Nat.card F)
    (hn : 0 < n) (hv : n = Nat.card F ^ i * x) :
    jMin F ⟨n, hn⟩ = Nat.card F ^ i * ((Nat.card F - 1) * x) := by
  subst hv
  rcases Nat.eq_zero_or_pos i with hi0 | hi
  · subst hi0
    have h0 : Nat.card F ^ 0 * x = x := by rw [pow_zero, one_mul]
    rw [show jMin F ⟨Nat.card F ^ 0 * x, hn⟩ = jMin F ⟨x, hx⟩ from
      jMin_congr F hn hx h0]
    rw [jMin_eq_pred_mul_char F hx hxq]
    rw [pow_zero, one_mul]
  obtain ⟨p, f, hprime, hchar, hring, hcard, hf⟩ := exists_ringChar_pow F
  have hp : 2 ≤ p := hprime.two_le
  have hp0 : 0 < p := by omega
  have hfi : 1 ≤ f * i := Nat.mul_pos hf hi
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hq0 : 0 < Nat.card F := by omega
  have hq1 : 1 ≤ Nat.card F := by omega
  have hpk : 0 < p ^ (f * i) := pow_pos hp0 _
  have hfkp : p ^ (f * i) = Nat.card F ^ i := by rw [hcard, pow_mul]
  refine le_antisymm (jMin_le F (isGoodJ_pow_mul_char F i ⟨x, hx⟩ hxq)) ?_
  by_contra hcon
  have hlt : jMin F ⟨Nat.card F ^ i * x, hn⟩ < Nat.card F ^ i * ((Nat.card F - 1) * x) :=
    not_le.mp hcon
  have hgood := jMin_spec F ⟨Nat.card F ^ i * x, hn⟩
  have hj1 : 1 ≤ jMin F ⟨Nat.card F ^ i * x, hn⟩ := jMin_pos F _
  have hdvdq : (Nat.card F - 1) ∣ jMin F ⟨Nat.card F ^ i * x, hn⟩ := hgood.2.1
  have hqix : Nat.card F ^ i * x = p ^ (f * i) * x := by rw [hfkp]
  have hnc : ∀ m : ℕ, (jMin F ⟨Nat.card F ^ i * x, hn⟩) / p ^ m % p +
      (Nat.card F ^ i * x - 1) / p ^ m % p < p := by
    have h := ((isGoodJ_iff_noCarry_char F (Nat.card F ^ i * x)
      (jMin F ⟨Nat.card F ^ i * x, hn⟩)
      (Nat.one_le_iff_ne_zero.mpr hn.ne')).mp hgood).2.2
    rw [hring] at h
    exact h
  have hdec : p ^ (f * i) * x - 1 = p ^ (f * i) * (x - 1) + (p ^ (f * i) - 1) :=
    pow_mul_sub_one_decomp (q := p) (i := f * i) (x := x) hp0 hx
  have hjmod : jMin F ⟨Nat.card F ^ i * x, hn⟩ % p ^ (f * i) = 0 := by
    have hms := (Commons.Data.Nat.noCarry_iff_mod_sum (p := p) hprime.two_le).mp hnc (f * i)
    have h1 : (p ^ (f * i) * x - 1) % p ^ (f * i) = p ^ (f * i) - 1 :=
      pow_mul_sub_one_mod (q := p) (i := f * i) (x := x) hp0 hx
    have h0 : Nat.card F ^ i * x - 1 = p ^ (f * i) * x - 1 := by rw [hqix]
    have hM : p ^ (f * i) - 1 + 1 = p ^ (f * i) := Nat.sub_add_cancel (by omega)
    have hl0 : 0 ≤ jMin F ⟨Nat.card F ^ i * x, hn⟩ % p ^ (f * i) := Nat.zero_le _
    rw [h0, h1] at hms
    omega
  have hdvd : Nat.card F ^ i ∣ jMin F ⟨Nat.card F ^ i * x, hn⟩ := by
    have h' : jMin F ⟨Nat.card F ^ i * x, hn⟩ % Nat.card F ^ i = 0 := by
      simpa only [hfkp] using hjmod
    exact Nat.dvd_of_mod_eq_zero h'
  set j' := jMin F ⟨Nat.card F ^ i * x, hn⟩ / Nat.card F ^ i with hj'def
  have hjval : Nat.card F ^ i * j' = jMin F ⟨Nat.card F ^ i * x, hn⟩ :=
    Nat.mul_div_cancel' hdvd
  have hj'pos : 1 ≤ j' := Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    rw [hzero, mul_zero] at hjval
    omega)
  have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F ^ i) := by
    have h1 : Nat.Coprime (Nat.card F - 1) (Nat.card F) := by
      have h := Nat.coprime_self_add_right (m := Nat.card F - 1) (n := 1)
      rw [Nat.sub_add_cancel hq1] at h
      exact h.mpr (Nat.coprime_one_right _)
    exact h1.pow_right i
  have hdvd0 : (Nat.card F - 1) ∣ j' := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [hj'def, hjval]
    exact hdvdq
  have hnc0 : noCarry p j' (x - 1) := by
    have hpform : (∀ m : ℕ, (p ^ (f * i) * j') / p ^ m % p +
        (p ^ (f * i) * (x - 1) + (p ^ (f * i) - 1)) / p ^ m % p < p) := by
      intro m
      have h1 := hnc m
      have e1 : jMin F ⟨Nat.card F ^ i * x, hn⟩ / p ^ m = (p ^ (f * i) * j') / p ^ m := by
        rw [← hjval, ← hfkp]
      have e2 : (Nat.card F ^ i * x - 1) / p ^ m =
          (p ^ (f * i) * (x - 1) + (p ^ (f * i) - 1)) / p ^ m := by
        rw [hqix, hdec]
      rw [e1, e2] at h1
      exact h1
    unfold noCarry
    exact (Commons.Data.Nat.noCarry_pow_mul_shift p (f * i) hp j' (x - 1)).mp hpform
  have hgood0 : IsGoodJ F x j' := by
    rw [isGoodJ_iff_noCarry_char F x j' hx, hring]
    exact ⟨hj'pos, hdvd0, hnc0⟩
  have hle : (Nat.card F - 1) * x ≤ j' := by
    have h := jMin_le F (k := ⟨x, hx⟩) hgood0
    rw [jMin_eq_pred_mul_char F hx hxq] at h
    exact h
  have hfin : Nat.card F ^ i * ((Nat.card F - 1) * x) ≤
      jMin F ⟨Nat.card F ^ i * x, hn⟩ := by
    rw [← hjval]
    exact Nat.mul_le_mul_left _ hle
  omega

/-- **`jMin (q ^ i * x) = q ^ i * ((q-1) * x)`** for `1 ≤ x ≤ q`. -/
theorem jMin_pow_mul_char (i x : ℕ) (hx : 1 ≤ x) (hxq : x ≤ Nat.card F)
    (hpos : 0 < Nat.card F ^ i * x) :
    jMin F ⟨Nat.card F ^ i * x, hpos⟩ = Nat.card F ^ i * ((Nat.card F - 1) * x) :=
  jMin_pow_mul_char_value F i x (Nat.card F ^ i * x) hx hxq hpos rfl

end JMinPowAny

section TNAny

/-- The general-`q` Thakur map `T x = x + jMin F x` on naturals (with `T 0 = 0`). -/
noncomputable def TN (n : ℕ) : ℕ :=
  if h : 0 < n then n + jMin F ⟨n, h⟩ else 0

lemma TN_eq {n : ℕ} (hn : 0 < n) : TN F n = n + jMin F ⟨n, hn⟩ := by
  unfold TN
  rw [dif_pos hn]

/-- On a positive natural (a `ℕ+`) the definition of `TN` is the expected one. -/
lemma TN_eq' (k : ℕ+) : TN F (k : ℕ) = (k : ℕ) + jMin F k := by
  rw [TN_eq F k.pos]
  rfl

/-- **`T x = q * x` on `[1,q]`** for an arbitrary finite field. -/
theorem TN_eq_mul (k : ℕ+) (hk : (k : ℕ) ≤ Nat.card F) :
    TN F (k : ℕ) = Nat.card F * (k : ℕ) := by
  have hq1 : 1 ≤ Nat.card F := by have := two_le_card F; omega
  rw [TN_eq' F k, jMin_eq_pred_mul_char_pnat F k hk]
  calc (k : ℕ) + (Nat.card F - 1) * (k : ℕ)
      = 1 * (k : ℕ) + (Nat.card F - 1) * (k : ℕ) := by rw [one_mul]
    _ = (1 + (Nat.card F - 1)) * (k : ℕ) := by rw [Nat.add_mul]
    _ = Nat.card F * (k : ℕ) := by rw [Nat.add_comm, Nat.sub_add_cancel hq1]

/-- **`T ^ i x = q ^ i * x` on `[1,q]`** for an arbitrary finite field. -/
theorem TN_iter_eq_mul (k : ℕ+) (hk : (k : ℕ) ≤ Nat.card F) (i : ℕ) :
    (((TN F)^[i]) (k : ℕ)) = Nat.card F ^ i * (k : ℕ) := by
  have hq0 : 0 < Nat.card F := by have := two_le_card F; omega
  have hq1 : 1 ≤ Nat.card F := by omega
  induction i with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      have hpos : 0 < Nat.card F ^ i * (k : ℕ) := Nat.mul_pos (pow_pos hq0 i) k.pos
      rw [TN_eq F hpos, jMin_pow_mul_char F i (k : ℕ) k.pos hk hpos]
      have hnat : Nat.card F ^ i * (k : ℕ) + Nat.card F ^ i * ((Nat.card F - 1) * (k : ℕ))
          = Nat.card F ^ (i + 1) * (k : ℕ) := by
        have h2 : (k : ℕ) + (Nat.card F - 1) * (k : ℕ) = Nat.card F * (k : ℕ) := by
          calc (k : ℕ) + (Nat.card F - 1) * (k : ℕ)
              = 1 * (k : ℕ) + (Nat.card F - 1) * (k : ℕ) := by rw [one_mul]
            _ = (1 + (Nat.card F - 1)) * (k : ℕ) := by rw [Nat.add_mul]
            _ = Nat.card F * (k : ℕ) := by rw [Nat.add_comm, Nat.sub_add_cancel hq1]
        calc Nat.card F ^ i * (k : ℕ) + Nat.card F ^ i * ((Nat.card F - 1) * (k : ℕ))
            = Nat.card F ^ i * ((k : ℕ) + (Nat.card F - 1) * (k : ℕ)) := by ring
          _ = Nat.card F ^ i * (Nat.card F * (k : ℕ)) := by rw [h2]
          _ = Nat.card F ^ (i + 1) * (k : ℕ) := by rw [pow_succ]; ring
      rw [hnat]

/-- **The linearised degree exponent `∑_{i<d} T^{i+1} x = x · q · (q^d - 1)/(q-1)`** on `[1,q]`,
for an arbitrary finite field (the general-`q` form of `DegLin.sExpG_eq_lin`). -/
theorem Tsum_eq_mul (k : ℕ+) (hk : (k : ℕ) ≤ Nat.card F) (d : ℕ) :
    ((Nat.card F - 1 : ℕ) : ℤ) * (∑ i ∈ Finset.range d, ((((TN F)^[i + 1]) (k : ℕ) : ℕ) : ℤ))
      = (k : ℤ) * (Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ d - 1) := by
  have hq1 : 1 ≤ Nat.card F := by have := two_le_card F; omega
  have hterm : ∀ i ∈ Finset.range d,
      (((((TN F)^[i + 1]) (k : ℕ) : ℕ) : ℤ)) = (k : ℤ) * (Nat.card F : ℤ) ^ (i + 1) := by
    intro i _
    rw [TN_iter_eq_mul F k hk (i + 1)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : (∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ (i + 1))
      = (Nat.card F : ℤ) * (∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_comm]
  rw [hsum]
  have hg := mul_geom_sum (Nat.card F : ℤ) d
  have hcast : ((Nat.card F - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  rw [hcast]
  calc ((Nat.card F : ℤ) - 1)
        * ((k : ℤ) * ((Nat.card F : ℤ) * ∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ i))
      = ((k : ℤ) * (Nat.card F : ℤ))
        * (((Nat.card F : ℤ) - 1) * ∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ i) := by ring
    _ = ((k : ℤ) * (Nat.card F : ℤ)) * ((Nat.card F : ℤ) ^ d - 1) := by rw [hg]
    _ = (k : ℤ) * (Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ d - 1) := by ring

end TNAny

section DepthOneDegree

/-- **The degree of the depth-one power sum at `x ∈ [1,q]`** over an arbitrary finite field. -/
theorem val_P_one_le_card (k : ℕ+) (hk : (k : ℕ) ≤ Nat.card F) :
    Valued.v (P F 1 k) = WithZero.exp (-((Nat.card F : ℤ) * (k : ℕ))) := by
  have hq1 : 1 ≤ Nat.card F := by have := two_le_card F; omega
  have hnat : (k : ℕ) + (Nat.card F - 1) * (k : ℕ) = Nat.card F * (k : ℕ) := by
    calc (k : ℕ) + (Nat.card F - 1) * (k : ℕ)
        = 1 * (k : ℕ) + (Nat.card F - 1) * (k : ℕ) := by rw [one_mul]
      _ = (1 + (Nat.card F - 1)) * (k : ℕ) := by rw [Nat.add_mul]
      _ = Nat.card F * (k : ℕ) := by rw [Nat.add_comm, Nat.sub_add_cancel hq1]
  rw [val_P_one F k, jMin_eq_pred_mul_char_pnat F k hk, ← Nat.cast_add, hnat]
  push_cast
  rfl

end DepthOneDegree

section Regression

attribute [local instance 100] Classical.decEq

/-- Over the prime field `F₂`: `jMin 2 = (2-1)·2 = 2`. -/
example : jMin (ZMod 2) (⟨2, by norm_num⟩ : ℕ+) = 2 := by
  have h := jMin_eq_pred_mul_char (ZMod 2) (x := 2) (by norm_num) (by
    norm_num [Nat.card_eq_fintype_card, ZMod.card])
  simpa [Nat.card_eq_fintype_card, ZMod.card] using h

/-- Over the prime field `F₃`: `T 3 = 3 · 3 = 9`. -/
example : TN (ZMod 3) 3 = 9 := by
  have h := TN_eq_mul (ZMod 3) (⟨3, by norm_num⟩ : ℕ+) (by
    norm_num [Nat.card_eq_fintype_card, ZMod.card])
  norm_num [Nat.card_eq_fintype_card, ZMod.card] at h
  exact h

/-- Over `F₄ = GaloisField 2 2` (a non-prime field): `jMin 3 = (4-1)·3 = 9`. -/
example : jMin (GaloisField 2 2) (⟨3, by norm_num⟩ : ℕ+) = 9 := by
  have h := jMin_eq_pred_mul_char (GaloisField 2 2) (x := 3) (by norm_num) (by
    rw [GaloisField.card (p := 2) (n := 2) (by norm_num)]; norm_num)
  rw [GaloisField.card (p := 2) (n := 2) (by norm_num)] at h
  norm_num at h
  exact h

end Regression

end ZagierHoffmanPositiveChar
