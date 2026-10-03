import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mul_of_coprime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local-density product formula for `X ^ 2 + Y ^ 4` on `d₁ * d₂ ^ 2`

For `d = d₁ * d₂ ^ 2` with `d₁`, `d₂` squarefree and coprime and `4 ∤ d`, the
normalised count of solutions of `x ^ 2 + y ^ 4 = 0` in `ZMod d × ZMod d` factors
as an Euler product over the primes dividing `d₁` (exponent `1`) and `d₂`
(exponent `2`).
-/

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- The number of pairs `(x, y)` in `ZMod n × ZMod n` with `x ^ 2 + y ^ 4 = 0`. -/
private noncomputable def X2Y4cnt (n : ℕ) : ℕ :=
  ({x : ZMod n × ZMod n | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard

private lemma X2Y4cnt_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    X2Y4cnt (m * n) = X2Y4cnt m * X2Y4cnt n :=
  X2Y4_pair_roots_mul_of_coprime h

private lemma X2Y4cnt_one : X2Y4cnt 1 = 1 := by
  have h : ({x : ZMod 1 × ZMod 1 | x.1 ^ 2 + x.2 ^ 4 = 0} : Set (ZMod 1 × ZMod 1)) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have h1 : x.1 = 0 := Subsingleton.elim _ _
      have h2 : x.2 = 0 := Subsingleton.elim _ _
      simp [h1, h2]
  rw [X2Y4cnt, h, Set.ncard_univ, Nat.card_prod, Nat.card_zmod]

private lemma X2Y4cnt_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (g a) (g b)) :
    X2Y4cnt (∏ a ∈ s, g a) = ∏ a ∈ s, X2Y4cnt (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X2Y4cnt_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hca : Nat.Coprime (g a) (∏ b ∈ s, g b) :=
        Nat.Coprime.prod_right (fun b hb =>
          hcop a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
            (fun h => ha (h ▸ hb)))
      rw [X2Y4cnt_mul_of_coprime hca,
        ih (fun a' ha' b' hb' hne =>
          hcop a' (Finset.mem_insert_of_mem ha') b' (Finset.mem_insert_of_mem hb') hne)]

private lemma squarefree_ne_zero {m : ℕ} (hs : Squarefree m) : m ≠ 0 := by
  rintro rfl
  have h : IsUnit (2 : ℕ) := hs 2 (by norm_num)
  have h2 : (2 : ℕ) ∣ 1 := isUnit_iff_dvd_one.mp h
  omega

private lemma eq_prod_primeFactors_of_squarefree {m : ℕ} (hs : Squarefree m) :
    m = ∏ p ∈ m.primeFactors, p := by
  have hm0 : m ≠ 0 := squarefree_ne_zero hs
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
  apply Finset.prod_congr rfl
  intro p hp
  have hle : m.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hm0).mp hs p
  have hpos : 0 < m.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
  rw [show m.factorization p = 1 by omega, pow_one]

private lemma prime_mod_four_eq_one_or_three {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left h2
  have hmod2 : (p % 4) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]; exact hodd
  have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
  interval_cases p % 4 <;> simp_all

/-- The number of solutions of `x ^ 2 + y ^ 4 = 0` in `ZMod p × ZMod p` for a
prime `p`, in closed form as a rational number. -/
private lemma X2Y4cnt_prime_rat {p : ℕ} (hp : p.Prime) :
    (X2Y4cnt p : ℚ) = ((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + 1 := by
  rw [X2Y4cnt]
  by_cases h43 : p % 4 = 3
  · rw [X2Y4_pair_card_mod_four_three hp h43, ZMod.χ₄_nat_three_mod_four h43]
    push_cast
    ring
  · by_cases h2 : p = 2
    · subst h2
      rw [X2Y4_pair_card_eq_two Nat.prime_two rfl, ZMod.χ₄_nat_eq_if_mod_four]
      norm_num
    · rcases prime_mod_four_eq_one_or_three hp h2 with h41 | h43'
      · rw [X2Y4_pair_card_mod_four_one hp h41, ZMod.χ₄_nat_one_mod_four h41]
        have hle : 1 ≤ 2 * p := by omega
        rw [Nat.cast_sub hle]
        push_cast
        ring
      · exact absurd h43' h43

/-- The number of solutions of `x ^ 2 + y ^ 4 = 0` in `ZMod (p ^ 2) × ZMod (p ^ 2)`
for an odd prime `p`, in closed form as a rational number. -/
private lemma X2Y4cnt_prime_sq_rat {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (X2Y4cnt (p ^ 2) : ℚ) =
      (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + (p : ℚ)) * (p : ℚ) := by
  have hcard : X2Y4cnt (p ^ 2) =
      if p = 2 then 4 else if p % 4 = 1 then 3 * p ^ 2 - 2 * p else p ^ 2 := by
    rw [X2Y4cnt]; exact X2Y4_pair_roots_mod_prime_sq_card hp
  rw [hcard, if_neg h2]
  rcases prime_mod_four_eq_one_or_three hp h2 with h41 | h43
  · rw [if_pos h41, ZMod.χ₄_nat_one_mod_four h41]
    have hle : 2 * p ≤ 3 * p ^ 2 := by nlinarith [hp.two_le]
    rw [Nat.cast_sub hle]
    push_cast
    ring
  · rw [if_neg (by omega : ¬ p % 4 = 1), ZMod.χ₄_nat_three_mod_four h43]
    push_cast
    ring

private lemma X2Y4cnt_eq_prod_primeFactors_of_squarefree {m : ℕ} (hs : Squarefree m) :
    X2Y4cnt m = ∏ p ∈ m.primeFactors, X2Y4cnt p := by
  have hm : m = ∏ p ∈ m.primeFactors, p := eq_prod_primeFactors_of_squarefree hs
  conv_lhs => rw [hm]
  exact X2Y4cnt_prod m.primeFactors (fun p => p) (fun a ha b hb hne =>
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
      (Nat.prime_of_mem_primeFactors hb)).mpr hne)

private lemma X2Y4cnt_sq_eq_prod_primeFactors_of_squarefree {m : ℕ} (hs : Squarefree m) :
    X2Y4cnt (m ^ 2) = ∏ p ∈ m.primeFactors, X2Y4cnt (p ^ 2) := by
  have hm : m = ∏ p ∈ m.primeFactors, p := eq_prod_primeFactors_of_squarefree hs
  have hsq : m ^ 2 = ∏ p ∈ m.primeFactors, p ^ 2 := by
    conv_lhs => rw [hm]
    rw [← Finset.prod_pow]
  rw [hsq]
  exact X2Y4cnt_prod m.primeFactors (fun p => p ^ 2) (fun a ha b hb hne =>
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
      (Nat.prime_of_mem_primeFactors hb)).mpr hne))

private lemma X2Y4cnt_primeFactors_div_sq {m : ℕ} (hs : Squarefree m) :
    (X2Y4cnt m : ℚ) / (m : ℚ) ^ 2
      = ∏ p ∈ m.primeFactors,
          (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + 1) / (p : ℚ) ^ 2 := by
  have hF : X2Y4cnt m = ∏ p ∈ m.primeFactors, X2Y4cnt p :=
    X2Y4cnt_eq_prod_primeFactors_of_squarefree hs
  have hm : (m : ℚ) = ∏ p ∈ m.primeFactors, (p : ℚ) := by
    conv_lhs => rw [eq_prod_primeFactors_of_squarefree hs]
    push_cast
    rfl
  have hnum : (X2Y4cnt m : ℚ) = ∏ p ∈ m.primeFactors, (X2Y4cnt p : ℚ) := by
    rw [hF]; push_cast; rfl
  rw [hnum, hm, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [X2Y4cnt_prime_rat (Nat.prime_of_mem_primeFactors hp)]

private lemma X2Y4cnt_primeFactors_sq_div {m : ℕ} (hs : Squarefree m)
    (hodd : ∀ p ∈ m.primeFactors, p ≠ 2) :
    (X2Y4cnt (m ^ 2) : ℚ) / (m : ℚ) ^ 4
      = ∏ p ∈ m.primeFactors,
          (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + (p : ℚ))
            / (p : ℚ) ^ 3 := by
  have hF : X2Y4cnt (m ^ 2) = ∏ p ∈ m.primeFactors, X2Y4cnt (p ^ 2) :=
    X2Y4cnt_sq_eq_prod_primeFactors_of_squarefree hs
  have hm : (m : ℚ) = ∏ p ∈ m.primeFactors, (p : ℚ) := by
    conv_lhs => rw [eq_prod_primeFactors_of_squarefree hs]
    push_cast
    rfl
  have hnum : (X2Y4cnt (m ^ 2) : ℚ) = ∏ p ∈ m.primeFactors, (X2Y4cnt (p ^ 2) : ℚ) := by
    rw [hF]; push_cast; rfl
  rw [hnum, hm, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [X2Y4cnt_prime_sq_rat (Nat.prime_of_mem_primeFactors hp) (hodd p hp)]
  have hp0 : (p : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [div_eq_div_iff (pow_ne_zero 4 hp0) (pow_ne_zero 3 hp0)]
  ring

theorem X2Y4_gdens_cubefree_eq_prod {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    (({p : ZMod (d₁ * d₂ ^ 2) × ZMod (d₁ * d₂ ^ 2) | p.1 ^ 2 + p.2 ^ 4 = 0}).ncard : ℚ)
        / (((d₁ * d₂ ^ 2 : ℕ)) : ℚ) ^ 2
      = (∏ p ∈ d₁.primeFactors,
            (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + 1) / (p : ℚ) ^ 2)
        * (∏ p ∈ d₂.primeFactors,
            (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + (p : ℚ))
              / (p : ℚ) ^ 3) := by
  classical
  change (X2Y4cnt (d₁ * d₂ ^ 2) : ℚ) / ((d₁ * d₂ ^ 2 : ℕ) : ℚ) ^ 2
      = (∏ p ∈ d₁.primeFactors,
            (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + 1) / (p : ℚ) ^ 2)
        * (∏ p ∈ d₂.primeFactors,
            (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + (p : ℚ))
              / (p : ℚ) ^ 3)
  have hodd : ∀ p ∈ d₂.primeFactors, p ≠ 2 := by
    intro p hp hp2
    have hpd2 : p ∣ d₂ := Nat.dvd_of_mem_primeFactors hp
    have hp2d : p ^ 2 ∣ d₂ ^ 2 := pow_dvd_pow_of_dvd hpd2 2
    have hpd : p ^ 2 ∣ d₁ * d₂ ^ 2 := dvd_mul_of_dvd_right hp2d d₁
    rw [hp2] at hpd
    exact h4 hpd
  have h1 := X2Y4cnt_primeFactors_div_sq hs₁
  have h2 := X2Y4cnt_primeFactors_sq_div hs₂ hodd
  have hF : X2Y4cnt (d₁ * d₂ ^ 2) = X2Y4cnt d₁ * X2Y4cnt (d₂ ^ 2) :=
    X2Y4cnt_mul_of_coprime (hcop.pow_right 2)
  have hnum : (X2Y4cnt (d₁ * d₂ ^ 2) : ℚ) = (X2Y4cnt d₁ : ℚ) * (X2Y4cnt (d₂ ^ 2) : ℚ) := by
    rw [hF]; push_cast; rfl
  rw [hnum, show ((d₁ * d₂ ^ 2 : ℕ) : ℚ) = (d₁ : ℚ) * (d₂ : ℚ) ^ 2 by push_cast; ring]
  rw [mul_pow, ← div_mul_div_comm]
  rw [h1]
  rw [show ((d₂ : ℚ) ^ 2) ^ 2 = (d₂ : ℚ) ^ 4 by ring]
  rw [h2]

end Commons.NumberTheory.FriedlanderIwaniec
