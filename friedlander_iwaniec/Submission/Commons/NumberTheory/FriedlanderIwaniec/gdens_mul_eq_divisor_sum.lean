import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_cubefree_eq_prod
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mul_of_coprime
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_eq_one_add_chi4
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

noncomputable section

/-- Number of solutions of `x ^ 2 + y ^ 4 = 0` in `ZMod n × ZMod n`. -/
private def Xcnt (n : ℕ) : ℕ := ({x : ZMod n × ZMod n | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard

/-- Number of square roots of `-1` modulo `n`. -/
private def rcnt (n : ℕ) : ℕ := ({α : ZMod n | α ^ 2 = -1}).ncard

private lemma Xcnt_mul {m n : ℕ} (h : Nat.Coprime m n) :
    Xcnt (m * n) = Xcnt m * Xcnt n :=
  X2Y4_pair_roots_mul_of_coprime h

private lemma rcnt_mul {m n : ℕ} (h : Nat.Coprime m n) :
    rcnt (m * n) = rcnt m * rcnt n :=
  sq_roots_neg_one_mul_of_coprime h

private lemma Xcnt_one : Xcnt 1 = 1 := by
  have h : ({x : ZMod 1 × ZMod 1 | x.1 ^ 2 + x.2 ^ 4 = 0} : Set (ZMod 1 × ZMod 1)) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have h1 : x.1 = 0 := Subsingleton.elim _ _
      have h2 : x.2 = 0 := Subsingleton.elim _ _
      simp [h1, h2]
  rw [Xcnt, h, Set.ncard_univ, Nat.card_prod, Nat.card_zmod]

private lemma rcnt_one : rcnt 1 = 1 := by
  have h : ({α : ZMod 1 | α ^ 2 = -1} : Set (ZMod 1)) = Set.univ := by
    ext α
    constructor
    · intro _; trivial
    · intro _
      exact Subsingleton.elim _ _
  rw [rcnt, h, Set.ncard_univ, Nat.card_zmod]

private lemma Xcnt_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (g a) (g b)) :
    Xcnt (∏ a ∈ s, g a) = ∏ a ∈ s, Xcnt (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Xcnt_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hca : Nat.Coprime (g a) (∏ b ∈ s, g b) :=
        Nat.Coprime.prod_right (fun b hb =>
          hcop a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
            (fun h => ha (h ▸ hb)))
      rw [Xcnt_mul hca,
        ih (fun a' ha' b' hb' hne =>
          hcop a' (Finset.mem_insert_of_mem ha') b' (Finset.mem_insert_of_mem hb') hne)]

private lemma rcnt_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (g a) (g b)) :
    rcnt (∏ a ∈ s, g a) = ∏ a ∈ s, rcnt (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rcnt_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hca : Nat.Coprime (g a) (∏ b ∈ s, g b) :=
        Nat.Coprime.prod_right (fun b hb =>
          hcop a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
            (fun h => ha (h ▸ hb)))
      rw [rcnt_mul hca,
        ih (fun a' ha' b' hb' hne =>
          hcop a' (Finset.mem_insert_of_mem ha') b' (Finset.mem_insert_of_mem hb') hne)]

private lemma Xcnt_eq_prod_primeFactors {m : ℕ} (hs : Squarefree m) :
    Xcnt m = ∏ p ∈ m.primeFactors, Xcnt p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hs]
  exact Xcnt_prod m.primeFactors (fun p => p) (fun a ha b hb hne =>
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
      (Nat.prime_of_mem_primeFactors hb)).mpr hne)

private lemma rcnt_eq_prod_primeFactors {m : ℕ} (hs : Squarefree m) :
    rcnt m = ∏ p ∈ m.primeFactors, rcnt p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hs]
  exact rcnt_prod m.primeFactors (fun p => p) (fun a ha b hb hne =>
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
      (Nat.prime_of_mem_primeFactors hb)).mpr hne)

private lemma Xcnt_sq_eq_prod_primeFactors {m : ℕ} (hs : Squarefree m) :
    Xcnt (m ^ 2) = ∏ p ∈ m.primeFactors, Xcnt (p ^ 2) := by
  have hm : m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hs).symm
  have hsq : m ^ 2 = ∏ p ∈ m.primeFactors, p ^ 2 := by
    conv_lhs => rw [hm]
    rw [← Finset.prod_pow]
  rw [hsq]
  exact Xcnt_prod m.primeFactors (fun p => p ^ 2) (fun a ha b hb hne =>
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
      (Nat.prime_of_mem_primeFactors hb)).mpr hne))

private lemma prime_mod_four_eq_one_or_three {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left h2
  have hmod2 : (p % 4) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]; exact hodd
  have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
  interval_cases p % 4 <;> simp_all

private lemma rcnt_prime_chi {p : ℕ} (hp : p.Prime) :
    ((rcnt p : ℕ) : ℤ) = 1 + ZMod.χ₄ (p : ZMod 4) :=
  sq_roots_neg_one_mod_prime_eq_one_add_chi4 hp

private lemma rcnt_prime_rat {p : ℕ} (hp : p.Prime) :
    ((rcnt p : ℕ) : ℚ) = 1 + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ) := by
  have h := rcnt_prime_chi hp
  have : ((rcnt p : ℕ) : ℚ) = ((1 + ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ) := by
    rw [← h]; push_cast; ring
  rw [this]; push_cast; ring

private lemma Xcnt_prime_rat {p : ℕ} (hp : p.Prime) :
    (Xcnt p : ℚ) = (1 + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + 1 := by
  rw [Xcnt]
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

private lemma Xcnt_prime {p : ℕ} (hp : p.Prime) :
    (Xcnt p : ℚ) = ((rcnt p : ℕ) : ℚ) * ((p : ℚ) - 1) + 1 := by
  rw [Xcnt_prime_rat hp, rcnt_prime_rat hp]

private lemma Xcnt_prime_sq_rat {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (Xcnt (p ^ 2) : ℚ) =
      ((1 + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + (p : ℚ)) * (p : ℚ) := by
  rw [Xcnt]
  have hcard : ({x : ZMod (p ^ 2) × ZMod (p ^ 2) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard =
      if p = 2 then 4 else if p % 4 = 1 then 3 * p ^ 2 - 2 * p else p ^ 2 :=
    X2Y4_pair_roots_mod_prime_sq_card hp
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

/-- For an odd prime `p`, `Xcnt (p ^ 2) / p ^ 2 = 1 + rcnt p * φ(p) / p`. -/
private lemma Xcnt_prime_sq_div {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (Xcnt (p ^ 2) : ℚ) / (p : ℚ) ^ 2
      = 1 + ((rcnt p : ℕ) : ℚ) * (Nat.totient p : ℚ) / (p : ℚ) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hp.ne_zero
  have hφ : (Nat.totient p : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.totient_prime hp]
    have h1 : 1 ≤ p := hp.one_le
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [Xcnt_prime_sq_rat hp h2, hφ, rcnt_prime_rat hp]
  field_simp
  ring

private lemma rcnt_mul_cast {m n : ℕ} (h : Nat.Coprime m n) :
    ((rcnt (m * n) : ℕ) : ℚ) = ((rcnt m : ℕ) : ℚ) * ((rcnt n : ℕ) : ℚ) := by
  rw [rcnt_mul h]; push_cast; ring

private lemma totient_mul_cast {m n : ℕ} (h : Nat.Coprime m n) :
    (Nat.totient (m * n) : ℚ) = (Nat.totient m : ℚ) * (Nat.totient n : ℚ) := by
  rw [Nat.totient_mul h]; push_cast; ring

private lemma squarefree_zero_false : ¬ Squarefree (0 : ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]; push Not
  exact ⟨2, Nat.prime_two, by norm_num⟩

/-- Divisor sum equals Euler product for a multiplicative function, over a
squarefree argument. -/
private lemma sum_divisors_eq_prod_primeFactors_of_sqfree {α : Type*} [CommRing α]
    (f : ℕ → α) (n : ℕ) (hsq : Squarefree n) (hf1 : f 1 = 1)
    (hfm : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ d ∈ n.divisors, f d) = ∏ p ∈ n.primeFactors, (1 + f p) := by
  have hn : n ≠ 0 := hsq.ne_zero
  let g : ℕ → α := fun d => if Squarefree d then f d else 0
  have hg1 : g 1 = 1 := by simp [g, hf1]
  have hgm : ∀ a b, Nat.Coprime a b → g (a * b) = g a * g b := by
    intro a b hab
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
      subst hb
      have h1 : g 1 = 1 := hg1
      have h0 : g 0 = 0 := by dsimp only [g]; rw [if_neg squarefree_zero_false]
      rw [h0, h1]; ring
    · rcases eq_or_ne b 0 with hb | hb
      · subst hb
        have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
        subst ha1
        have h1 : g 1 = 1 := hg1
        have h0 : g 0 = 0 := by dsimp only [g]; rw [if_neg squarefree_zero_false]
        rw [h0, h1]; ring
      · by_cases hsa : Squarefree a
        · by_cases hsb : Squarefree b
          · have hab' : Squarefree (a * b) := (Nat.squarefree_mul hab).mpr ⟨hsa, hsb⟩
            simp only [g, if_pos hab', if_pos hsa, if_pos hsb, hfm a b ha hb hab]
          · have hab' : ¬ Squarefree (a * b) := fun h => hsb ((Nat.squarefree_mul hab).mp h).2
            simp only [g, if_neg hab', if_pos hsa, if_neg hsb, mul_zero]
        · have hab' : ¬ Squarefree (a * b) := fun h => hsa ((Nat.squarefree_mul hab).mp h).1
          simp only [g, if_neg hab', if_neg hsa, zero_mul]
  have hgs : ∀ p k, p.Prime → 2 ≤ k → g (p ^ k) = 0 := by
    intro p k hp hk
    have hns : ¬ Squarefree (p ^ k) := by
      rw [Nat.squarefree_iff_prime_squarefree]; push Not
      exact ⟨p, hp, by simpa [pow_two] using (pow_dvd_pow p hk)⟩
    simp only [g, if_neg hns]
  have hprod :=
    Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors g n hn hg1 hgm hgs
  have h1 : (∏ p ∈ n.primeFactors, (1 + f p)) = ∏ p ∈ n.primeFactors, (1 + g p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hsp : Squarefree p := (Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)).squarefree
    simp only [g, if_pos hsp]
  have h2 : (∑ d ∈ n.divisors, f d) = ∑ d ∈ n.divisors, g d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hsd : Squarefree d := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    simp only [g, if_pos hsd]
  rw [h2, ← hprod, ← h1]

private lemma sum_divisors_comp_div {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    (∑ d ∈ m.divisors, g (m / d)) = ∑ d ∈ m.divisors, g d := by
  classical
  refine Finset.sum_bij (fun d _ => m / d) ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
  · intro a ha b hb hab
    have hm : m ≠ 0 := (Nat.mem_divisors.mp ha).2
    rw [← Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hm, hab,
      Nat.div_div_self (Nat.dvd_of_mem_divisors hb) hm]
  · intro b hb
    refine ⟨m / b, ?_, ?_⟩
    · exact Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hb), (Nat.mem_divisors.mp hb).2⟩
    · exact Nat.div_div_self (Nat.dvd_of_mem_divisors hb) (Nat.mem_divisors.mp hb).2
  · intro a ha
    rfl

/-- `∑_{d | m} rcnt d · φ(d) = Xcnt m` for squarefree `m`. -/
private lemma A_eq {m : ℕ} (hs : Squarefree m) :
    (∑ d ∈ m.divisors, ((rcnt d : ℕ) : ℚ) * (Nat.totient d : ℚ)) = (Xcnt m : ℚ) := by
  have hf1 : ((rcnt 1 : ℕ) : ℚ) * (Nat.totient 1 : ℚ) = 1 := by
    rw [rcnt_one, Nat.totient_one]; norm_num
  have hfm : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → Nat.Coprime a b →
      ((rcnt (a * b) : ℕ) : ℚ) * (Nat.totient (a * b) : ℚ)
        = (((rcnt a : ℕ) : ℚ) * (Nat.totient a : ℚ))
            * (((rcnt b : ℕ) : ℚ) * (Nat.totient b : ℚ)) := by
    intro a b _ _ hab
    rw [rcnt_mul_cast hab, totient_mul_cast hab]; ring
  rw [sum_divisors_eq_prod_primeFactors_of_sqfree _ m hs hf1 hfm,
    Xcnt_eq_prod_primeFactors hs]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [Xcnt_prime hpp]
  have hφ : (Nat.totient p : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.totient_prime hpp]
    have h1 : 1 ≤ p := hpp.one_le
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [hφ]; ring

/-- `∑_{d | m} rcnt d · φ(d) / d = Xcnt (m^2) / m^2` for squarefree odd `m`. -/
private lemma B_eq {m : ℕ} (hs : Squarefree m) (hodd : ∀ p ∈ m.primeFactors, p ≠ 2) :
    (∑ d ∈ m.divisors, ((rcnt d : ℕ) : ℚ) * (Nat.totient d : ℚ) / (d : ℚ))
      = (Xcnt (m ^ 2) : ℚ) / (m : ℚ) ^ 2 := by
  have hf1 : ((rcnt 1 : ℕ) : ℚ) * (Nat.totient 1 : ℚ) / (1 : ℚ) = 1 := by
    rw [rcnt_one, Nat.totient_one]; norm_num
  have hfm : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → Nat.Coprime a b →
      ((rcnt (a * b) : ℕ) : ℚ) * (Nat.totient (a * b) : ℚ) / ((a * b : ℕ) : ℚ)
        = (((rcnt a : ℕ) : ℚ) * (Nat.totient a : ℚ) / (a : ℚ))
            * (((rcnt b : ℕ) : ℚ) * (Nat.totient b : ℚ) / (b : ℚ)) := by
    intro a b ha hb hab
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    rw [rcnt_mul_cast hab, totient_mul_cast hab, Nat.cast_mul]
    field_simp
  rw [sum_divisors_eq_prod_primeFactors_of_sqfree _ m hs hf1 hfm]
  have hnum : (Xcnt (m ^ 2) : ℚ) = ∏ p ∈ m.primeFactors, (Xcnt (p ^ 2) : ℚ) := by
    rw [Xcnt_sq_eq_prod_primeFactors hs]; push_cast; rfl
  have hmcast : (m : ℚ) = ∏ p ∈ m.primeFactors, (p : ℚ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hs]
    push_cast; rfl
  have hden : (m : ℚ) ^ 2 = ∏ p ∈ m.primeFactors, (p : ℚ) ^ 2 := by
    rw [hmcast, Finset.prod_pow]
  rw [hnum, hden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Xcnt_prime_sq_div (Nat.prime_of_mem_primeFactors hp) (hodd p hp)]

/-- `∑_{ν | m} rcnt (m/ν) · φ(m/ν) = Xcnt m` for squarefree `m`. -/
private lemma P1_eq {m : ℕ} (hs : Squarefree m) :
    (∑ ν ∈ m.divisors, ((rcnt (m / ν) : ℕ) : ℚ) * (Nat.totient (m / ν) : ℚ))
      = (Xcnt m : ℚ) := by
  rw [sum_divisors_comp_div m (fun d => ((rcnt d : ℕ) : ℚ) * (Nat.totient d : ℚ))]
  exact A_eq hs

/-- `∑_{ν | m} ν · rcnt (m/ν) · φ(m/ν) = Xcnt (m^2) / m` for squarefree odd `m`. -/
private lemma P2_eq {m : ℕ} (hs : Squarefree m) (hodd : ∀ p ∈ m.primeFactors, p ≠ 2) :
    (∑ ν ∈ m.divisors, (ν : ℚ) * ((rcnt (m / ν) : ℕ) : ℚ) * (Nat.totient (m / ν) : ℚ))
      = (Xcnt (m ^ 2) : ℚ) / (m : ℚ) := by
  have hm : m ≠ 0 := hs.ne_zero
  rw [← sum_divisors_comp_div m
    (fun d => (d : ℚ) * ((rcnt (m / d) : ℕ) : ℚ) * (Nat.totient (m / d) : ℚ))]
  have hstep : (∑ d ∈ m.divisors,
        ((m / d : ℕ) : ℚ) * ((rcnt (m / (m / d)) : ℕ) : ℚ) * (Nat.totient (m / (m / d)) : ℚ))
      = (m : ℚ) * ∑ d ∈ m.divisors,
          ((rcnt d : ℕ) : ℚ) * (Nat.totient d : ℚ) / (d : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm hdvd
    have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    have hdd : m / (m / d) = d := Nat.div_div_self hdvd hm
    rw [hdd]
    have hcast : ((m / d : ℕ) : ℚ) = (m : ℚ) / (d : ℚ) := Nat.cast_div hdvd hd0'
    rw [hcast]
    field_simp
  rw [hstep, B_eq hs hodd]
  field_simp

private lemma sum_sum_mul_div {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → ℚ) (g : κ → ℚ) (c : ℚ) :
    (∑ i ∈ s, ∑ j ∈ t, f i * g j / c) = (∑ i ∈ s, f i) * (∑ j ∈ t, g j) / c := by
  simp_rw [← Finset.sum_div]
  rw [← Finset.sum_mul_sum]

theorem gdens_mul_eq_divisor_sum {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    ((d₁ * d₂ ^ 2 : ℕ) : ℚ)
        * ((∏ p ∈ d₁.primeFactors,
              (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + 1) / (p : ℚ) ^ 2)
          * (∏ p ∈ d₂.primeFactors,
              (((1 : ℚ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℚ)) * ((p : ℚ) - 1) + (p : ℚ))
                / (p : ℚ) ^ 3))
      = ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
          (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ)
            * (Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℚ) / ((d₁ * d₂ : ℕ) : ℚ) := by
  have hd₁0 : d₁ ≠ 0 := hs₁.ne_zero
  have hd₂0 : d₂ ≠ 0 := hs₂.ne_zero
  have hodd : ∀ p ∈ d₂.primeFactors, p ≠ 2 := by
    intro p hp hp2
    have hpd2 : p ∣ d₂ := Nat.dvd_of_mem_primeFactors hp
    have hp2d : p ^ 2 ∣ d₂ ^ 2 := pow_dvd_pow_of_dvd hpd2 2
    have hpd : p ^ 2 ∣ d₁ * d₂ ^ 2 := dvd_mul_of_dvd_right hp2d d₁
    rw [hp2] at hpd
    exact h4 hpd
  have hd₁' : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁0
  have hd₂' : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂0
  -- RHS computation
  have hRHS : (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
        (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ)
          * (Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℚ) / ((d₁ * d₂ : ℕ) : ℚ))
      = (Xcnt d₁ : ℚ) / (d₁ : ℚ) * ((Xcnt (d₂ ^ 2) : ℚ) / (d₂ : ℚ) ^ 2) := by
    have hpt : ∀ ν₁ ∈ Nat.divisors d₁, ∀ ν₂ ∈ Nat.divisors d₂,
        (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ)
          * (Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℚ) / ((d₁ * d₂ : ℕ) : ℚ)
        = (((rcnt (d₁ / ν₁) : ℕ) : ℚ) * (Nat.totient (d₁ / ν₁) : ℚ))
            * ((ν₂ : ℚ) * ((rcnt (d₂ / ν₂) : ℕ) : ℚ) * (Nat.totient (d₂ / ν₂) : ℚ))
            / ((d₁ : ℚ) * (d₂ : ℚ)) := by
      intro ν₁ hν₁ ν₂ hν₂
      have h1 : ν₁ ∣ d₁ := Nat.dvd_of_mem_divisors hν₁
      have h2 : ν₂ ∣ d₂ := Nat.dvd_of_mem_divisors hν₂
      have hd₁'' : (d₁ : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.mem_divisors.mp hν₁).2
      have hd₂'' : (d₂ : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.mem_divisors.mp hν₂).2
      have hN : (d₁ * d₂) / (ν₁ * ν₂) = (d₁ / ν₁) * (d₂ / ν₂) :=
        (Nat.div_mul_div_comm h1 h2).symm
      have hcop' : Nat.Coprime (d₁ / ν₁) (d₂ / ν₂) :=
        (hcop.coprime_dvd_left (Nat.div_dvd_of_dvd h1)).coprime_dvd_right
          (Nat.div_dvd_of_dvd h2)
      show (ν₂ : ℚ) * ((rcnt ((d₁ * d₂) / (ν₁ * ν₂)) : ℕ) : ℚ)
          * (Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℚ) / ((d₁ * d₂ : ℕ) : ℚ)
        = (((rcnt (d₁ / ν₁) : ℕ) : ℚ) * (Nat.totient (d₁ / ν₁) : ℚ))
            * ((ν₂ : ℚ) * ((rcnt (d₂ / ν₂) : ℕ) : ℚ) * (Nat.totient (d₂ / ν₂) : ℚ))
            / ((d₁ : ℚ) * (d₂ : ℚ))
      rw [hN, rcnt_mul_cast hcop', totient_mul_cast hcop', Nat.cast_mul]
      field_simp
    rw [Finset.sum_congr rfl (fun ν₁ hν₁ =>
      Finset.sum_congr rfl (fun ν₂ hν₂ => hpt ν₁ hν₁ ν₂ hν₂))]
    rw [sum_sum_mul_div]
    rw [P1_eq hs₁, P2_eq hs₂ hodd]
    field_simp
  rw [hRHS]
  -- LHS computation
  rw [← X2Y4_gdens_cubefree_eq_prod hs₁ hs₂ hcop h4]
  change ((d₁ * d₂ ^ 2 : ℕ) : ℚ)
        * ((Xcnt (d₁ * d₂ ^ 2) : ℚ) / (((d₁ * d₂ ^ 2 : ℕ)) : ℚ) ^ 2)
      = (Xcnt d₁ : ℚ) / (d₁ : ℚ) * ((Xcnt (d₂ ^ 2) : ℚ) / (d₂ : ℚ) ^ 2)
  rw [show ((d₁ * d₂ ^ 2 : ℕ) : ℚ) = (d₁ : ℚ) * (d₂ : ℚ) ^ 2 from by push_cast; ring]
  rw [show (Xcnt (d₁ * d₂ ^ 2) : ℚ) = (Xcnt d₁ : ℚ) * (Xcnt (d₂ ^ 2) : ℚ) from by
    rw [Xcnt_mul (hcop.pow_right 2)]; push_cast; ring]
  field_simp

end

end Commons.NumberTheory.FriedlanderIwaniec
