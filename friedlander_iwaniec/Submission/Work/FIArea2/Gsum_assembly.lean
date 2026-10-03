import Mathlib
import Submission.Work.FIArea2.TsumDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Assembly of the global estimate `‖T(n,a,h₁,h₂)‖ ≤ 4τ(n)³(h₁²-a h₂²,n)`

This is the *assembly* step of Lemma 8.1: from the local estimate at every prime power and the CRT
multiplicativity of `T` one obtains the estimate at every modulus, by strong induction peeling off
the full `p`-part of `n`.  The argument (strong induction, `Nat.ordProj_dvd`,
`Nat.coprime_ordCompl`, Bézout via `Nat.gcd_eq_gcd_ab`, and the cancellation of the units `c₁, c₂`
in the gcds) was worked out and proved by the colleague who proved
`Submission/Work/FIArea2/Tsum_bound_of_pieces`; it is reproduced here under private names so that it
can be imported next to the prime-power developments without a name clash.
-/

set_option linter.style.haveILetI false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `T(1,a,h₁,h₂) = 1`. -/
lemma gsumAsm_Tsum_one (i : NeZero 1) (a h1 h2 : ℤ) : @Tsum 1 i a h1 h2 = 1 := by
  unfold Tsum
  rw [Fintype.sum_unique]
  rw [Fintype.sum_unique]
  rw [← Unique.eq_default (0 : ZMod 1)]
  norm_num [E]

/-- The `NeZero`-free version of `Tsum` (its value at `n = 0` is irrelevant and set to `0`). -/
def gsumAsm_TsumU (n : ℕ) (a h1 h2 : ℤ) : ℂ :=
  if h : n = 0 then 0 else @Tsum n ⟨h⟩ a h1 h2

/-- `gsumAsm_TsumU` agrees with `Tsum` at every nonzero modulus. -/
lemma gsumAsm_TsumU_eq {n : ℕ} [NeZero n] (a h1 h2 : ℤ) : gsumAsm_TsumU n a h1 h2 = Tsum n a h1 h2 := by
  unfold gsumAsm_TsumU
  rw [dif_neg (NeZero.ne n)]

/-- `gsumAsm_TsumU 1 a h₁ h₂ = 1`. -/
lemma gsumAsm_TsumU_one (a h1 h2 : ℤ) : gsumAsm_TsumU 1 a h1 h2 = 1 := by
  rw [gsumAsm_TsumU_eq]
  exact gsumAsm_Tsum_one _ a h1 h2

/-- A unit modulo `n` restricts to a unit modulo any divisor of `n`. -/
lemma gsumAsm_isUnit_cast_of_dvd {m n : ℕ} (hdvd : m ∣ n) (a : ℤ) (ha : IsUnit (a : ZMod n)) :
    IsUnit (a : ZMod m) := by
  have h := IsUnit.map (ZMod.castHom hdvd (ZMod m)) ha
  simpa [ZMod.castHom_apply, ZMod.cast_intCast hdvd a] using h

/-- Multiplying `Y` by the square of a unit modulo `N` does not change `Nat.gcd N ·.natAbs`. -/
lemma gsumAsm_gcd_natAbs_mul_sq (N : ℕ) (c Y : ℤ) (hc : IsUnit (c : ZMod N)) :
    Nat.gcd N ((c ^ 2 * Y).natAbs) = Nat.gcd N Y.natAbs := by
  have hcop : Nat.Coprime c.natAbs N := by
    have key : (c : ZMod N) = ((c.natAbs : ℕ) : ZMod N) ∨
        (c : ZMod N) = -((c.natAbs : ℕ) : ZMod N) := by
      rcases Int.natAbs_eq c with hh | hh
      · left; rw [hh]; simp
      · right; rw [hh]; simp
    have h2 : IsUnit (((c.natAbs : ℕ) : ZMod N)) := by
      rcases key with k | k
      · rw [k] at hc; exact hc
      · rw [k] at hc; simpa using hc.neg
    exact (ZMod.isUnit_iff_coprime c.natAbs N).mp h2
  have hcop2 : Nat.Coprime (c.natAbs ^ 2) N := hcop.pow_left 2
  rw [Int.natAbs_mul, Int.natAbs_pow]
  rw [mul_comm (c.natAbs ^ 2) Y.natAbs]
  exact Nat.Coprime.gcd_mul_right_cancel_right Y.natAbs hcop2

/-- `(p^e).divisors.card = e + 1` for `p` prime. -/
lemma gsumAsm_card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp e, Finset.card_map, Finset.card_range]

/-- **Assembly of the global estimate from the local (prime-power) bound and CRT multiplicativity.**
Two inputs are assumed: the local estimate `Hloc` at every prime power `p^ν` (`ν ≥ 1`), and the CRT
factorisation `Hmul` of `T` across coprime moduli.  The conclusion is the global form of *FI* Lemma
8.1 (8.5) for the reduced sum `T`:

  `‖T(n,a,h₁,h₂)‖ ≤ 4 τ(n)³ · (h₁² - a h₂², n)`  for `a` a unit modulo `n`.

Route: strong induction on `n`.  For `n = 1`, `T(1,a,h₁,h₂) = 1 ≤ 4`.  For `n ≥ 2`, take a prime
`p ∣ n`, `e = n.factorization p`, `m = n / p^e`, so `n = p^e·m`, `(p^e,m) = 1`, `m < n`,
`m ≠ 0`.  Bézout (`Nat.gcd_eq_gcd_ab`) for `(p^e,m)` gives `c₁,c₂` with
`c₁·m ≡ 1 (mod p^e)`, `c₂·p^e ≡ 1 (mod m)`, and `Hmul` gives
`T(n,a,h₁,h₂) = T(p^e, a, h₁c₁, h₂c₁)·T(m, a, h₁c₂, h₂c₂)`.  Bound the first factor by `Hloc`
(using that `a` is a unit modulo `p^e` because it is one modulo `n` and `p^e ∣ n`, and that a unit
`c₁` modulo `p^e` can be cancelled in `(p^e, (h₁c₁)² - a(h₂c₁)²) = (p^e, h₁²-a h₂²)`), and the
second by the induction hypothesis (same cancellation with `c₂`).  Finally multiply and use
`τ(p^e m) = (e+1)τ(m)` and `(p^e m, X) = (p^e, X)·(m, X)` for coprime moduli, together with
`(e+1) = (p^e).divisors.card`. -/
theorem gsumAsm_Tsum_bound
    (Hloc : ∀ (p : ℕ), p.Prime → ∀ (ν : ℕ) [NeZero (p ^ ν)], 1 ≤ ν → ∀ (a h1 h2 : ℤ),
      IsUnit (a : ZMod (p ^ ν)) →
      ‖Tsum (p ^ ν) a h1 h2‖
        ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ))
    (Hmul : ∀ {m n : ℕ} [NeZero m] [NeZero n], Nat.Coprime m n → ∀ (c1 c2 : ℤ),
      (c1 : ZMod m) * (n : ZMod m) = 1 → (c2 : ZMod n) * (m : ZMod n) = 1 → ∀ (a h1 h2 : ℤ),
      Tsum (m * n) a h1 h2
        = Tsum m a (h1 * c1) (h2 * c1) * Tsum n a (h1 * c2) (h2 * c2))
    (n : ℕ) [NeZero n] (a h1 h2 : ℤ) (ha : IsUnit (a : ZMod n)) :
    ‖Tsum n a h1 h2‖
      ≤ 4 * ((n.divisors.card : ℝ) ^ 3) * (Nat.gcd n ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
  have main : ∀ n : ℕ, n ≠ 0 → ∀ a h1 h2 : ℤ, IsUnit (a : ZMod n) →
      ‖gsumAsm_TsumU n a h1 h2‖
        ≤ 4 * ((n.divisors.card : ℝ) ^ 3) *
            (Nat.gcd n ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnz a h1 h2 ha
      rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hnz) with hlt | heq
      · -- 1 < n
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
        set e : ℕ := n.factorization p with he_def
        set q : ℕ := n / p ^ e with hq_def
        have he : 1 ≤ e := by
          rw [he_def]; exact (hp.dvd_iff_one_le_factorization hnz).mp hpdvd
        have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
        have hn_eq : n = p ^ e * q := by
          rw [hq_def, mul_comm]; exact (Nat.div_mul_cancel hpe_dvd).symm
        have hq_ne : q ≠ 0 := by
          rintro hq0; rw [hq0, mul_zero] at hn_eq; exact hnz hn_eq
        have hq_pos : 0 < q := Nat.pos_of_ne_zero hq_ne
        have hcop_pq : Nat.Coprime p q := by
          rw [hq_def, he_def]; exact Nat.coprime_ordCompl hp hnz
        have hcop : Nat.Coprime (p ^ e) q := hcop_pq.pow_left e
        have hgcd1 : Nat.gcd (p ^ e) q = 1 := hcop
        have hq_lt : q < n := by
          rw [hn_eq]
          exact lt_mul_of_one_lt_left hq_pos (one_lt_pow₀ hp.one_lt (by omega))
        have hq_dvd : q ∣ n := ⟨p ^ e, by rw [hn_eq, mul_comm]⟩
        haveI hpNe : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
        haveI hqNe : NeZero q := ⟨hq_ne⟩
        -- Bézout
        have hbez : (p ^ e : ℤ) * (Nat.gcdA (p ^ e) q) +
            (q : ℤ) * (Nat.gcdB (p ^ e) q) = 1 := by
          have h := Nat.gcd_eq_gcd_ab (p ^ e) q
          rw [hgcd1] at h
          norm_num at h
          exact h.symm
        have hc1 : ((Nat.gcdB (p ^ e) q : ℤ) : ZMod (p ^ e)) * (q : ZMod (p ^ e)) = 1 := by
          have h := congrArg (fun k : ℤ => (k : ZMod (p ^ e))) hbez
          push_cast at h
          rw [← Nat.cast_pow] at h
          simp only [ZMod.natCast_self, zero_mul, zero_add] at h
          rw [mul_comm] at h
          exact h
        have hc2 : ((Nat.gcdA (p ^ e) q : ℤ) : ZMod q) * ((p ^ e : ℕ) : ZMod q) = 1 := by
          have h := congrArg (fun k : ℤ => (k : ZMod q)) hbez
          push_cast at h
          simp only [ZMod.natCast_self, zero_mul, add_zero] at h
          rw [← Nat.cast_pow, mul_comm] at h
          exact h
        have hmulT := Hmul (m := p ^ e) (n := q) hcop (Nat.gcdB (p ^ e) q : ℤ)
          (Nat.gcdA (p ^ e) q : ℤ) hc1 hc2 a h1 h2
        have hmulU : gsumAsm_TsumU (p ^ e * q) a h1 h2
            = gsumAsm_TsumU (p ^ e) a (h1 * (Nat.gcdB (p ^ e) q : ℤ))
                (h2 * (Nat.gcdB (p ^ e) q : ℤ))
              * gsumAsm_TsumU q a (h1 * (Nat.gcdA (p ^ e) q : ℤ))
                (h2 * (Nat.gcdA (p ^ e) q : ℤ)) := by
          rw [gsumAsm_TsumU_eq (n := p ^ e * q) a h1 h2,
              gsumAsm_TsumU_eq (n := p ^ e) a (h1 * (Nat.gcdB (p ^ e) q : ℤ))
                (h2 * (Nat.gcdB (p ^ e) q : ℤ)),
              gsumAsm_TsumU_eq (n := q) a (h1 * (Nat.gcdA (p ^ e) q : ℤ))
                (h2 * (Nat.gcdA (p ^ e) q : ℤ))]
          exact hmulT
        -- local factor
        have hUnit_pe : IsUnit (a : ZMod (p ^ e)) := gsumAsm_isUnit_cast_of_dvd hpe_dvd a ha
        have hloc := Hloc p hp e he a (h1 * (Nat.gcdB (p ^ e) q : ℤ))
          (h2 * (Nat.gcdB (p ^ e) q : ℤ)) hUnit_pe
        have hc1unit : IsUnit ((Nat.gcdB (p ^ e) q : ℤ) : ZMod (p ^ e)) :=
          isUnit_iff_exists_inv.mpr ⟨(q : ZMod (p ^ e)), hc1⟩
        have hgcdpe : Nat.gcd (p ^ e) (((h1 * (Nat.gcdB (p ^ e) q : ℤ)) ^ 2 -
              a * (h2 * (Nat.gcdB (p ^ e) q : ℤ)) ^ 2).natAbs)
            = Nat.gcd (p ^ e) ((h1 ^ 2 - a * h2 ^ 2).natAbs) := by
          rw [show (h1 * (Nat.gcdB (p ^ e) q : ℤ)) ^ 2 -
                a * (h2 * (Nat.gcdB (p ^ e) q : ℤ)) ^ 2
              = (Nat.gcdB (p ^ e) q : ℤ) ^ 2 * (h1 ^ 2 - a * h2 ^ 2) by ring]
          exact gsumAsm_gcd_natAbs_mul_sq (p ^ e) ((Nat.gcdB (p ^ e) q : ℤ))
            (h1 ^ 2 - a * h2 ^ 2) hc1unit
        have hA : ‖gsumAsm_TsumU (p ^ e) a (h1 * (Nat.gcdB (p ^ e) q : ℤ))
              (h2 * (Nat.gcdB (p ^ e) q : ℤ))‖
            ≤ ((e : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ e) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
          rw [gsumAsm_TsumU_eq]
          rw [hgcdpe] at hloc
          exact hloc
        -- induction factor
        have hUnit_q : IsUnit (a : ZMod q) := gsumAsm_isUnit_cast_of_dvd hq_dvd a ha
        have hih := ih q hq_lt hq_ne a (h1 * (Nat.gcdA (p ^ e) q : ℤ))
          (h2 * (Nat.gcdA (p ^ e) q : ℤ)) hUnit_q
        have hc2unit : IsUnit ((Nat.gcdA (p ^ e) q : ℤ) : ZMod q) :=
          isUnit_iff_exists_inv.mpr ⟨((p ^ e : ℕ) : ZMod q), hc2⟩
        have hgcdq : Nat.gcd q (((h1 * (Nat.gcdA (p ^ e) q : ℤ)) ^ 2 -
              a * (h2 * (Nat.gcdA (p ^ e) q : ℤ)) ^ 2).natAbs)
            = Nat.gcd q ((h1 ^ 2 - a * h2 ^ 2).natAbs) := by
          rw [show (h1 * (Nat.gcdA (p ^ e) q : ℤ)) ^ 2 -
                a * (h2 * (Nat.gcdA (p ^ e) q : ℤ)) ^ 2
              = (Nat.gcdA (p ^ e) q : ℤ) ^ 2 * (h1 ^ 2 - a * h2 ^ 2) by ring]
          exact gsumAsm_gcd_natAbs_mul_sq q ((Nat.gcdA (p ^ e) q : ℤ))
            (h1 ^ 2 - a * h2 ^ 2) hc2unit
        have hB : ‖gsumAsm_TsumU q a (h1 * (Nat.gcdA (p ^ e) q : ℤ))
              (h2 * (Nat.gcdA (p ^ e) q : ℤ))‖
            ≤ 4 * ((q.divisors.card : ℝ) ^ 3)
                * (Nat.gcd q ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
          rw [hgcdq] at hih
          exact hih
        -- rewrite the goal modulus
        rw [hn_eq]
        -- final assembly
        have htau : (((p ^ e * q).divisors.card : ℝ))
            = ((e : ℝ) + 1) * (q.divisors.card : ℝ) := by
          rw [hcop.card_divisors_mul, gsumAsm_card_divisors_prime_pow hp e]
          push_cast; ring
        have hgcdn : Nat.gcd (p ^ e * q) ((h1 ^ 2 - a * h2 ^ 2).natAbs)
            = Nat.gcd (p ^ e) ((h1 ^ 2 - a * h2 ^ 2).natAbs)
              * Nat.gcd q ((h1 ^ 2 - a * h2 ^ 2).natAbs) := by
          rw [Nat.gcd_comm (p ^ e * q) _, hcop.gcd_mul,
            Nat.gcd_comm (p ^ e) _, Nat.gcd_comm q _]
        calc ‖gsumAsm_TsumU (p ^ e * q) a h1 h2‖
            = ‖gsumAsm_TsumU (p ^ e) a (h1 * (Nat.gcdB (p ^ e) q : ℤ))
                (h2 * (Nat.gcdB (p ^ e) q : ℤ))
              * gsumAsm_TsumU q a (h1 * (Nat.gcdA (p ^ e) q : ℤ))
                (h2 * (Nat.gcdA (p ^ e) q : ℤ))‖ := by rw [hmulU]
          _ = ‖gsumAsm_TsumU (p ^ e) a (h1 * (Nat.gcdB (p ^ e) q : ℤ))
                (h2 * (Nat.gcdB (p ^ e) q : ℤ))‖
              * ‖gsumAsm_TsumU q a (h1 * (Nat.gcdA (p ^ e) q : ℤ))
                (h2 * (Nat.gcdA (p ^ e) q : ℤ))‖ := norm_mul _ _
          _ ≤ (((e : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ e) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ))
              * (4 * ((q.divisors.card : ℝ) ^ 3)
                * (Nat.gcd q ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ)) :=
                mul_le_mul hA hB (norm_nonneg _) (by positivity)
          _ = 4 * (((p ^ e * q).divisors.card : ℝ) ^ 3)
              * (Nat.gcd (p ^ e * q) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
                rw [htau, hgcdn]; push_cast; ring
      · -- n = 1
        subst heq
        rw [gsumAsm_TsumU_one]
        norm_num [Nat.divisors_one]
  have hmain := main n (NeZero.ne n) a h1 h2 ha
  rwa [gsumAsm_TsumU_eq] at hmain

end

end Work.FIArea2
