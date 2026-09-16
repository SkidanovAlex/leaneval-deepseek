import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Kummer / Lucas: `p ∤ (a+b).choose a` iff adding `a` and `b` in base `p` has no carries

For a prime `p` and natural numbers `a b`, the binomial coefficient `(a+b).choose a`
is not divisible by `p` if and only if adding the base-`p` digits of `a` and `b` never
produces a carry, i.e. `a / p ^ i % p + b / p ^ i % p < p` for every `i`.

The proof proceeds by strong induction on `a`, using Lucas's theorem
(`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) to peel off the lowest base-`p`
digit.  (Kummer's theorem would give the same statement via the number of carries.)
-/

set_option linter.style.haveILetI false

open Nat

namespace Commons.Data.Nat

namespace ChooseNoCarry

/-- The `(j+1)`-st base-`p` digit of `a` is the `j`-th base-`p` digit of `a / p`. -/
lemma div_pow_succ_mod (a p j : ℕ) : a / p ^ (j + 1) % p = a / p / p ^ j % p := by
  rw [Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- **Lucas, one digit at a time.**  If the lowest base-`p` digits of `a` and `b` add up
without a carry, then `(a+b).choose a` factors modulo `p` into the binomial coefficient
of the lowest digits and the binomial coefficient of the quotients by `p`. -/
lemma lucas_step {p : ℕ} (hp : p.Prime) (a b : ℕ) (hlt : a % p + b % p < p) :
    (((a + b).choose a : ℕ) : ZMod p) =
      (((a % p + b % p).choose (a % p) : ℕ) : ZMod p) *
        (((a / p + b / p).choose (a / p) : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hab : a + b = (a % p + b % p) + p * (a / p + b / p) := by
    have h1 : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
    have h2 : b = p * (b / p) + b % p := (Nat.div_add_mod b p).symm
    calc a + b = (p * (a / p) + a % p) + (p * (b / p) + b % p) := by rw [← h1, ← h2]
      _ = (a % p + b % p) + p * (a / p + b / p) := by ring
  have hmod : (a + b) % p = a % p + b % p := by
    rw [hab, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hdiv : (a + b) / p = a / p + b / p := by
    rw [hab, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := a + b) (k := a) (p := p)
  rw [hmod, hdiv] at hluc
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  exact hluc

/-- If the lowest base-`p` digits of `a` and `b` produce a carry, then `(a+b).choose a`
vanishes modulo `p`. -/
lemma lucas_step_zero {p : ℕ} (hp : p.Prime) (a b : ℕ) (hge : p ≤ a % p + b % p) :
    (((a + b).choose a : ℕ) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha : a % p < p := Nat.mod_lt a hp.pos
  have hb : b % p < p := Nat.mod_lt b hp.pos
  have hmod : (a + b) % p = a % p + b % p - p := by
    rw [Nat.add_mod, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  have hzero : (a % p + b % p - p).choose (a % p) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := a + b) (k := a) (p := p)
  rw [hmod, hzero, zero_mul] at hluc
  exact (ZMod.natCast_eq_zero_iff _ p).mpr (Nat.modEq_zero_iff_dvd.mp hluc)

/-- If there is no carry in the lowest base-`p` digit, divisibility of `(a+b).choose a`
by `p` is equivalent to divisibility of `(a/p + b/p).choose (a/p)` by `p`. -/
lemma dvd_choose_iff_dvd_choose_div {p : ℕ} (hp : p.Prime) (a b : ℕ)
    (hlt : a % p + b % p < p) :
    p ∣ (a + b).choose a ↔ p ∣ (a / p + b / p).choose (a / p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz := lucas_step hp a b hlt
  have hc : (((a % p + b % p).choose (a % p) : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp
      (Nat.Prime.coprime_choose_of_lt hp hlt (Nat.le_add_right _ _))
  rw [← ZMod.natCast_eq_zero_iff ((a + b).choose a) p,
      ← ZMod.natCast_eq_zero_iff ((a / p + b / p).choose (a / p)) p, hz, _root_.mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hc
    · exact h
  · exact Or.inr

/-- Splitting off the lowest base-`p` digit of the condition `∃ i, p ≤ a/p^i % p + b/p^i % p`. -/
lemma exists_digit_shift (a b p : ℕ) :
    (∃ i, p ≤ a / p ^ i % p + b / p ^ i % p) ↔
      (p ≤ a % p + b % p) ∨ (∃ j, p ≤ a / p / p ^ j % p + b / p / p ^ j % p) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | zero => exact Or.inl (by simpa using hi)
    | succ j =>
      refine Or.inr ⟨j, ?_⟩
      simpa only [div_pow_succ_mod] using hi
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨0, by simpa using h⟩
    · refine ⟨j + 1, ?_⟩
      simpa only [div_pow_succ_mod] using hj

/-- **Kummer's theorem, divisibility form.**  A prime `p` divides `(a+b).choose a` if and
only if some base-`p` digit of `a` plus the corresponding digit of `b` is at least `p`
(equivalently, adding `a` and `b` in base `p` produces a carry). -/
lemma prime_dvd_choose_iff {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    p ∣ (a + b).choose a ↔ ∃ i, p ≤ a / p ^ i % p + b / p ^ i % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  revert b
  refine Nat.strongRecOn a ?_
  intro n ih b
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · constructor
    · intro h
      exact (hp.not_dvd_one (by simpa using h)).elim
    · rintro ⟨i, hi⟩
      have h := Nat.mod_lt (b / p ^ i) hp.pos
      simp only [Nat.zero_div, Nat.zero_mod, zero_add] at hi
      omega
  · rcases lt_or_ge (n % p + b % p) p with hlt | hge
    · have h1 := dvd_choose_iff_dvd_choose_div hp n b hlt
      have h2 := ih (n / p) (Nat.div_lt_self hn hp.one_lt) (b / p)
      simp only [h1, h2, exists_digit_shift n b p, hlt.not_ge, false_or]
    · constructor
      · intro _
        exact ⟨0, by simpa using hge⟩
      · intro _
        rw [← ZMod.natCast_eq_zero_iff ((n + b).choose n) p, lucas_step_zero hp n b hge]

end ChooseNoCarry

open ChooseNoCarry

/-- For a prime `p`, `(a+b).choose a` is nonzero modulo `p` if and only if adding `a` and `b`
in base `p` never produces a carry. -/
theorem choose_add_ne_zero_iff_noCarry {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ((Nat.choose (a + b) a : ℕ) : ZMod p) ≠ 0 ↔
      ∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff, prime_dvd_choose_iff hp a b, not_exists]
  simp only [not_le]

end Commons.Data.Nat