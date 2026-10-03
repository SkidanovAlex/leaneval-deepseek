import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Squares in `ZMod (2 ^ ν)` congruent to `1` mod `8`

An odd integer `a` is a square modulo `2 ^ ν` if and only if `a ≡ 1 (mod 8)`.
Here we prove the direction needed for the Friedlander–Iwaniec development:
every `a` with `a % 8 = 1` is a square in `ZMod (2 ^ ν)`.

The proof is a Hensel-type lifting argument in the integers: given `b` with
`b ^ 2 ≡ a (mod 2 ^ ν)`, write `b ^ 2 - a = 2 ^ ν * c` and correct `b` by
`t * 2 ^ (ν - 1)` with `t = c % 2`, which makes `c + b * t` even (using that
`b` is odd, since `a ≡ 1 (mod 2)`). This lifts the congruence to `2 ^ (ν + 1)`.
-/

namespace Work.FIArea2

/-- `2` divides `2 ^ n` for `n ≥ 1` (in `ℤ`). -/
lemma two_dvd_two_pow (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ∣ (2 : ℤ) ^ n := by
  cases n with
  | zero => omega
  | succ k =>
    rw [pow_succ]
    exact dvd_mul_left (2 : ℤ) _

/-- `2` divides `b ^ 2 - b` for every integer `b`. -/
lemma two_dvd_sq_sub_self (b : ℤ) : (2 : ℤ) ∣ b ^ 2 - b := by
  rw [← even_iff_two_dvd]
  rw [show b ^ 2 - b = b * (b - 1) by ring]
  rcases Int.even_or_odd b with hb | hb
  · exact Even.mul_right hb (b - 1)
  · have h1 : Even (b - 1) := hb.sub_odd (by norm_num : Odd (1 : ℤ))
    rw [mul_comm]
    exact Even.mul_right h1 b

/-- Hensel lifting step: if `b ^ 2 ≡ a (mod 2 ^ (ν + 3))` and `a ≡ 1 (mod 8)`,
then the congruence can be lifted to `2 ^ (ν + 4)`. -/
lemma lift_step (ν : ℕ) (a b : ℤ) (ha8 : (8 : ℤ) ∣ a - 1)
    (hb : (2 : ℤ) ^ (ν + 3) ∣ b ^ 2 - a) :
    ∃ b' : ℤ, (2 : ℤ) ^ (ν + 4) ∣ b' ^ 2 - a := by
  obtain ⟨c, hc⟩ := hb
  have h2a1 : (2 : ℤ) ∣ a - 1 := dvd_trans (by norm_num : (2 : ℤ) ∣ 8) ha8
  have h2ba : (2 : ℤ) ∣ b ^ 2 - a :=
    dvd_trans (two_dvd_two_pow (ν + 3) (by omega)) ⟨c, hc⟩
  have h2bb : (2 : ℤ) ∣ b ^ 2 - b := two_dvd_sq_sub_self b
  -- `b` is odd, i.e. `2 ∣ b - 1`
  have hbe : (2 : ℤ) ∣ b - 1 := by
    have h1 : (2 : ℤ) ∣ (b ^ 2 - a) - (b ^ 2 - b) := dvd_sub h2ba h2bb
    have h2 : (b ^ 2 - a) - (b ^ 2 - b) + (a - 1) = b - 1 := by ring
    rw [← h2]
    exact dvd_add h1 h2a1
  set D : ℤ := (2 : ℤ) ^ (ν + 2) with hDdef
  set t : ℤ := c % 2 with htdef
  have hD1 : 2 * D = (2 : ℤ) ^ (ν + 3) := by
    rw [hDdef, ← pow_succ']
  have hD2 : D ^ 2 = (2 : ℤ) ^ (2 * ν + 4) := by
    rw [hDdef, ← pow_mul]
    congr 1
    ring
  have hexp : (b + t * D) ^ 2 - a = (2 : ℤ) ^ (ν + 3) * (c + b * t) + t ^ 2 * D ^ 2 := by
    have h1 : b ^ 2 = a + (2 : ℤ) ^ (ν + 3) * c := by linarith [hc]
    have h3 : 2 * b * t * D = b * t * (2 : ℤ) ^ (ν + 3) := by
      rw [← hD1]; ring
    calc (b + t * D) ^ 2 - a = b ^ 2 - a + 2 * b * t * D + t ^ 2 * D ^ 2 := by ring
      _ = (a + (2 : ℤ) ^ (ν + 3) * c) - a + 2 * b * t * D + t ^ 2 * D ^ 2 := by rw [h1]
      _ = (2 : ℤ) ^ (ν + 3) * c + 2 * b * t * D + t ^ 2 * D ^ 2 := by ring
      _ = (2 : ℤ) ^ (ν + 3) * c + b * t * (2 : ℤ) ^ (ν + 3) + t ^ 2 * D ^ 2 := by rw [h3]
      _ = (2 : ℤ) ^ (ν + 3) * (c + b * t) + t ^ 2 * D ^ 2 := by ring
  refine ⟨b + t * D, ?_⟩
  rw [hexp]
  have ht : t = 0 ∨ t = 1 := by
    rw [htdef]; exact Int.emod_two_eq_zero_or_one c
  -- `c + b * t` is even
  have hmain : (2 : ℤ) ∣ c + b * t := by
    rcases ht with ht0 | ht1
    · rw [ht0, mul_zero, add_zero]
      apply Int.dvd_of_emod_eq_zero
      rw [htdef] at ht0
      exact ht0
    · rw [ht1, mul_one]
      have hodd : Odd c := by rw [Int.odd_iff]; rw [htdef] at ht1; exact ht1
      have hce : Even (c - 1) := hodd.sub_odd (by norm_num : Odd (1 : ℤ))
      have hc1 : (2 : ℤ) ∣ c - 1 := even_iff_two_dvd.mp hce
      have : c + b = (c - 1) + (b - 1) + 2 := by ring
      rw [this]
      exact dvd_add (dvd_add hc1 hbe) (by norm_num)
  apply dvd_add
  · have hh : (2 : ℤ) ^ (ν + 3) * 2 ∣ (2 : ℤ) ^ (ν + 3) * (c + b * t) :=
      mul_dvd_mul_left _ hmain
    rwa [← pow_succ] at hh
  · rcases ht with ht0 | ht1
    · rw [ht0]; simp
    · rw [ht1, one_pow, one_mul, hD2]
      exact pow_dvd_pow (2 : ℤ) (by omega : ν + 4 ≤ 2 * ν + 4)

set_option linter.unusedVariables false in
/-- Every natural number `a ≡ 1 (mod 8)` is a square in `ZMod (2 ^ ν)`. -/
theorem sq_eq_zmod_two_pow (ν a : ℕ) (hν : 1 ≤ ν) (ha : a % 8 = 1) :
    ∃ b : ZMod (2 ^ ν), b ^ 2 = (a : ZMod (2 ^ ν)) := by
  -- Work in the integers: it suffices to solve `b ^ 2 ≡ a (mod 2 ^ ν)` there.
  have ha8 : (8 : ℤ) ∣ (a : ℤ) - 1 := by
    have h2 : (a : ℤ) = 8 * (a / 8 : ℕ) + 1 := by
      have := Nat.div_add_mod a 8
      omega
    refine ⟨(a / 8 : ℕ), ?_⟩
    linarith
  have key : ∀ n : ℕ, ∃ b : ℤ, ((2 : ℤ) ^ n) ∣ b ^ 2 - (a : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases lt_or_ge n 4 with hn | hn
      · -- small moduli: `b = 1` works since `2 ^ n ∣ 8 ∣ a - 1`
        refine ⟨1, ?_⟩
        have h1 : ((2 : ℤ) ^ n) ∣ (8 : ℤ) := by
          have h := pow_dvd_pow (2 : ℤ) (by omega : n ≤ 3)
          simpa using h
        have h2 : (8 : ℤ) ∣ 1 - (a : ℤ) := by
          obtain ⟨k, hk⟩ := ha8
          exact ⟨-k, by linarith⟩
        simpa using dvd_trans h1 h2
      · -- lift the congruence for `n - 1` to `n`
        obtain ⟨b, hb⟩ := ih (n - 1) (by omega)
        obtain ⟨b', hb'⟩ := lift_step (n - 4) (a : ℤ) b ha8 (by
          simpa [show (n - 4) + 3 = n - 1 by omega] using hb)
        exact ⟨b', by simpa [show (n - 4) + 4 = n by omega] using hb'⟩
  obtain ⟨b, hb⟩ := key ν
  refine ⟨(b : ZMod (2 ^ ν)), ?_⟩
  have hz : ((b ^ 2 - (a : ℤ) : ℤ) : ZMod (2 ^ ν)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [Nat.cast_pow] using hb
  have hz2 : (b : ZMod (2 ^ ν)) ^ 2 - (a : ZMod (2 ^ ν)) = 0 := by
    have hh := hz
    push_cast at hh
    exact hh
  exact sub_eq_zero.mp hz2

end Work.FIArea2
