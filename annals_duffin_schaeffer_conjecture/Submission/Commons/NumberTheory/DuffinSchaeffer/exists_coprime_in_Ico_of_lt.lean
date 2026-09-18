import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Star

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.DuffinSchaeffer

private lemma ceil_sub_ceil_le {A B d : ℚ} (hd : 0 < d) :
    (⌈B / d⌉ : ℚ) - ⌈A / d⌉ ≤ (B - A) / d + 1 := by
  have hB : (⌈B / d⌉ : ℚ) ≤ B / d + 1 := by
    exact (Int.ceil_lt_add_one (B / d)).le
  have hA : (A / d : ℚ) ≤ ⌈A / d⌉ := Int.le_ceil (A / d)
  have hB' := mul_le_mul_of_nonneg_right hB (le_of_lt hd)
  have hA' := mul_le_mul_of_nonneg_right hA (le_of_lt hd)
  field_simp [hd.ne'] at hB' hA' ⊢
  nlinarith

private lemma le_ceil_sub_ceil {A B d : ℚ} (hd : 0 < d) :
    (B - A) / d - 1 ≤ (⌈B / d⌉ : ℚ) - ⌈A / d⌉ := by
  have hB : (B / d : ℚ) ≤ ⌈B / d⌉ := Int.le_ceil (B / d)
  have hA : (⌈A / d⌉ : ℚ) ≤ A / d + 1 := by
    exact (Int.ceil_lt_add_one (A / d)).le
  have hB' := mul_le_mul_of_nonneg_right hB (le_of_lt hd)
  have hA' := mul_le_mul_of_nonneg_right hA (le_of_lt hd)
  field_simp [hd.ne'] at hB' hA' ⊢
  nlinarith

private lemma card_multiples_Ico_le (a L d : ℕ) (hd : 0 < d) :
    ((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card ≤ (L : ℚ) / d + 1 := by
  have hcard := Nat.Ico_filter_modEq_card (a := a) (b := a + L) (r := d) hd (v := 0)
  have hcard' : (((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card : ℤ) =
      max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 := by
    simpa [Nat.modEq_zero_iff_dvd] using hcard
  have hcardQ : (((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card : ℚ) =
      (max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 : ℤ) := by
    exact_mod_cast hcard'
  have hdQ : 0 < (d : ℚ) := by exact_mod_cast hd
  have hmonoZ : 0 ≤ (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) := by
    have hle : (↑a : ℚ) / (d : ℚ) ≤ (↑(a + L) : ℚ) / (d : ℚ) := by
      gcongr
      exact_mod_cast Nat.le_add_right a L
    exact sub_nonneg.mpr (Int.ceil_mono hle)
  have hmax : max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 =
      ⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉ := by
    exact max_eq_left hmonoZ
  have hb := ceil_sub_ceil_le (A := (a : ℚ)) (B := ((a + L : ℕ) : ℚ)) (d := (d : ℚ)) hdQ
  have hmainQ : (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ : ℚ) - ⌈(↑a : ℚ) / (d : ℚ)⌉ ≤
      (L : ℚ) / d + 1 := by
    convert hb using 1
    · norm_num [Nat.cast_add]
  calc
    (((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card : ℚ)
        = (max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 : ℤ) := hcardQ
    _ = (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉ : ℤ) := by
      rw [hmax]
    _ ≤ (L : ℚ) / d + 1 := by
      exact_mod_cast hmainQ

private lemma le_card_multiples_Ico (a L d : ℕ) (hd : 0 < d) :
    (L : ℚ) / d - 1 ≤ ((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card := by
  have hcard := Nat.Ico_filter_modEq_card (a := a) (b := a + L) (r := d) hd (v := 0)
  have hcard' : (((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card : ℤ) =
      max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 := by
    simpa [Nat.modEq_zero_iff_dvd] using hcard
  have hcardQ : (((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card : ℚ) =
      (max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 : ℤ) := by
    exact_mod_cast hcard'
  have hdQ : 0 < (d : ℚ) := by exact_mod_cast hd
  have hdiff := le_ceil_sub_ceil (A := (a : ℚ)) (B := ((a + L : ℕ) : ℚ)) (d := (d : ℚ)) hdQ
  have hmainQ : (L : ℚ) / d - 1 ≤
      (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ : ℚ) - ⌈(↑a : ℚ) / (d : ℚ)⌉ := by
    convert hdiff using 1
    · norm_num [Nat.cast_add]
  have hmaxQ : ((⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ : ℚ) - ⌈(↑a : ℚ) / (d : ℚ)⌉) ≤
      ((max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 : ℤ) : ℚ) := by
    exact_mod_cast le_max_left _ _
  calc
    (L : ℚ) / d - 1 ≤ (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ : ℚ) - ⌈(↑a : ℚ) / (d : ℚ)⌉ := hmainQ
    _ ≤ ((max (⌈(↑(a + L) : ℚ) / (d : ℚ)⌉ - ⌈(↑a : ℚ) / (d : ℚ)⌉) 0 : ℤ) : ℚ) := hmaxQ
    _ = (((Finset.Ico a (a + L)).filter (fun m => d ∣ m)).card : ℚ) := hcardQ.symm

private lemma card_fin_dvd_eq_card_Ico_dvd (a L d : ℕ) :
    (Finset.univ.filter (fun i : Fin L => Dvd.dvd d (a + (i : ℕ)))).card =
      ((Finset.Ico a (a + L)).filter (fun m => Dvd.dvd d m)).card := by
  classical
  let s : Finset (Fin L) := Finset.univ.filter (fun i : Fin L => Dvd.dvd d (a + (i : ℕ)))
  let t : Finset ℕ := (Finset.Ico a (a + L)).filter (fun m => Dvd.dvd d m)
  refine Finset.card_bij (s := s) (t := t) (fun i _ => a + (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simp only [s, t, mem_filter, mem_univ, mem_Ico] at hi ⊢
    refine ⟨⟨Nat.le_add_right a i, Nat.add_lt_add_left i.isLt a⟩, hi.2⟩
  · intro i1 hi1 i2 hi2 h
    apply Fin.ext
    exact Nat.add_left_cancel h
  · intro m hm
    have hmI := (mem_filter.1 hm).1
    have hmIco := mem_Ico.1 hmI
    let i : Fin L := ⟨m - a, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · simp only [s, mem_filter, mem_univ]
      rw [Nat.add_sub_of_le hmIco.1]
      exact ⟨trivial, (mem_filter.1 hm).2⟩
    · simpa [i] using Nat.add_sub_of_le hmIco.1

private lemma card_fin_dvd_le (a L d : ℕ) (hd : 0 < d) :
    ((Finset.univ.filter (fun i : Fin L => Dvd.dvd d (a + (i : ℕ)))).card : ℚ) ≤
      (L : ℚ) / d + 1 := by
  rw [card_fin_dvd_eq_card_Ico_dvd]
  exact_mod_cast card_multiples_Ico_le a L d hd

private lemma le_card_fin_dvd (a L d : ℕ) (hd : 0 < d) :
    (L : ℚ) / d - 1 ≤
      ((Finset.univ.filter (fun i : Fin L => Dvd.dvd d (a + (i : ℕ)))).card : ℚ) := by
  rw [card_fin_dvd_eq_card_Ico_dvd]
  exact_mod_cast le_card_multiples_Ico a L d hd

private lemma card_inf_filter_dvd_eq_fin (P : Finset ℕ) (t : Finset ℕ)
    (hPt : t ⊆ P) (hP : ∀ p ∈ P, Nat.Prime p) (a L : ℕ) :
    let S : ℕ → Finset (Fin L) := fun p => Finset.univ.filter (fun i => Dvd.dvd p (a + (i : ℕ)))
    (t.inf S).card =
      (Finset.univ.filter (fun i : Fin L => Dvd.dvd (t.prod (fun p => p)) (a + (i : ℕ)))).card := by
  intro S
  apply congr_arg card
  ext i
  rw [Finset.mem_inf]
  simp only [S, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    apply Finset.prod_primes_dvd
    · intro p hp
      exact Nat.prime_iff.mp (hP p (hPt hp))
    · intro p hp
      exact h p hp
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p => p) hp) h

private lemma prod_one_sub_inv_eq_sum_powerset (P : Finset ℕ) :
    ∏ p ∈ P, (1 - 1 / (p : ℚ)) =
      ∑ t ∈ P.powerset, (-1 : ℚ) ^ #t * (1 / ((t.prod (fun p => p) : ℕ) : ℚ)) := by
  classical
  rw [Finset.prod_sub]
  simp only [prod_const_one]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mul_one]
  rw [Finset.prod_div_distrib]
  rw [prod_const_one]
  rw [← Nat.cast_prod]

private lemma neg_one_pow_mul_sub_one_le_neg_one_pow_mul {n : ℕ} {x y : ℚ}
    (hx : y - 1 ≤ x) (hy : x ≤ y + 1) :
    (-1 : ℚ) ^ n * y - 1 ≤ (-1 : ℚ) ^ n * x := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]
    simpa using hx
  · rw [h.neg_one_pow]
    linarith [hy]

private lemma prod_primes_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    0 < P.prod (fun p => p) := by
  exact Finset.prod_pos (fun p hp => (hP p hp).pos)

private lemma card_not_dvd_Ico_lower_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a L : ℕ) :
    (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) - (2 : ℚ) ^ P.card ≤
      ((P.inf fun p => (Finset.univ.filter (fun i : Fin L => Dvd.dvd p (a + (i : ℕ))))ᶜ).card : ℚ) := by
  classical
  let S : ℕ → Finset (Fin L) := fun p => Finset.univ.filter (fun i => Dvd.dvd p (a + (i : ℕ)))
  let C := P.inf fun p => (S p)ᶜ
  have hCexact_int := Finset.inclusion_exclusion_card_inf_compl P S
  have hCexact : (C.card : ℚ) = ∑ t ∈ P.powerset, (-1 : ℚ) ^ #t * (t.inf S).card := by
    exact_mod_cast hCexact_int
  have hmain_eq : (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) =
      ∑ t ∈ P.powerset, (-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ)) := by
    rw [prod_one_sub_inv_eq_sum_powerset]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hterm : ∀ t ∈ P.powerset,
      (-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ)) - 1 ≤
        (-1 : ℚ) ^ #t * (t.inf S).card := by
    intro t ht
    have htP : t ⊆ P := mem_powerset.1 ht
    have hcard_eq := card_inf_filter_dvd_eq_fin P t htP hP a L
    rw [hcard_eq]
    have hd : 0 < t.prod (fun p => p) := prod_primes_pos t (fun p hp => hP p (htP hp))
    have hle := card_fin_dvd_le a L (t.prod (fun p => p)) hd
    have hge := le_card_fin_dvd a L (t.prod (fun p => p)) hd
    -- hge: L/d -1 ≤ c; hle: c ≤ L/d +1. We want sign*c from sign*(L/d) -1.
    exact neg_one_pow_mul_sub_one_le_neg_one_pow_mul (n := #t) hge hle
  have hsum : ∑ t ∈ P.powerset, ((-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ)) - 1) ≤
      ∑ t ∈ P.powerset, (-1 : ℚ) ^ #t * (t.inf S).card := by
    exact Finset.sum_le_sum hterm
  have hsum_lhs : ∑ t ∈ P.powerset, ((-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ)) - 1) =
      (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) - (2 : ℚ) ^ P.card := by
    calc
      ∑ t ∈ P.powerset, ((-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ)) - 1)
          = (∑ t ∈ P.powerset, (-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ))) -
              ∑ t ∈ P.powerset, 1 := by rw [Finset.sum_sub_distrib]
      _ = (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) - P.powerset.card := by
          rw [← hmain_eq]
          simp
      _ = (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) - (2 : ℚ) ^ P.card := by
          rw [card_powerset]
          norm_num
  calc
    (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) - (2 : ℚ) ^ P.card
        = ∑ t ∈ P.powerset, ((-1 : ℚ) ^ #t * ((L : ℚ) / ((t.prod (fun p => p) : ℕ) : ℚ)) - 1) := hsum_lhs.symm
    _ ≤ ∑ t ∈ P.powerset, (-1 : ℚ) ^ #t * (t.inf S).card := hsum
    _ = (C.card : ℚ) := hCexact.symm



private lemma prod_one_sub_inv_ge_half_pow (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ((1 / 2 : ℚ) ^ P.card) ≤ ∏ p ∈ P, (1 - 1 / (p : ℚ)) := by
  classical
  have hprod_const : ∏ p ∈ P, (1 / 2 : ℚ) = (1 / 2 : ℚ) ^ P.card := by simp
  rw [← hprod_const]
  refine Finset.prod_le_prod₀ ?_ ?_
  · intro p hp
    norm_num
  · intro p hp
    have hpQ : 0 < (p : ℚ) := by exact_mod_cast (hP p hp).pos
    have h_inv : 1 / (p : ℚ) ≤ 1 / 2 := by
      rw [one_div_le_one_div hpQ (by norm_num : (0:ℚ)<2)]
      exact_mod_cast (hP p hp).two_le
    linarith

private lemma lower_bound_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (L : ℕ)
    (hL : 4 ^ P.card < L) :
    0 < (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) - (2 : ℚ) ^ P.card := by
  have hprod := prod_one_sub_inv_ge_half_pow P hP
  have hLQ : (4 : ℚ) ^ P.card < (L : ℚ) := by exact_mod_cast hL
  have hhalf_pos : 0 < (1 / 2 : ℚ) ^ P.card := by positivity
  have hmul_lt : (4 : ℚ) ^ P.card * (1 / 2 : ℚ) ^ P.card <
      (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) := by
    have h1 : (4 : ℚ) ^ P.card * (1 / 2 : ℚ) ^ P.card <
        (L : ℚ) * (1 / 2 : ℚ) ^ P.card := by
      exact mul_lt_mul_of_pos_right hLQ hhalf_pos
    have h2 : (L : ℚ) * (1 / 2 : ℚ) ^ P.card ≤
        (L : ℚ) * ∏ p ∈ P, (1 - 1 / (p : ℚ)) := by
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    exact h1.trans_le h2
  have hpow : (4 : ℚ) ^ P.card * (1 / 2 : ℚ) ^ P.card = (2 : ℚ) ^ P.card := by
    rw [← mul_pow]
    norm_num
  rw [hpow] at hmul_lt
  linarith

theorem exists_coprime_in_Ico_of_lt {n L a : ℕ} (hn : 0 < n)
    (h : 4 ^ n.primeFactors.card < L) :
    ∃ m ∈ Finset.Ico a (a + L), m.gcd n = 1 := by
  classical
  let P : Finset ℕ := n.primeFactors
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  let S : ℕ → Finset (Fin L) := fun p => Finset.univ.filter (fun i => Dvd.dvd p (a + (i : ℕ)))
  let C : Finset (Fin L) := P.inf fun p => (S p)ᶜ
  have hcard_lower := card_not_dvd_Ico_lower_bound P hP a L
  have hpos := lower_bound_pos P hP L h
  have hCposQ : 0 < (C.card : ℚ) := lt_of_lt_of_le hpos hcard_lower
  have hCpos : 0 < C.card := by exact_mod_cast hCposQ
  have hCnonempty : C.Nonempty := Finset.card_pos.mp hCpos
  obtain ⟨i, hi⟩ := hCnonempty
  let m : ℕ := a + (i : ℕ)
  refine ⟨m, ?_, ?_⟩
  · simp only [m, Finset.mem_Ico]
    exact ⟨Nat.le_add_right a i, Nat.add_lt_add_left i.isLt a⟩
  · have hm_not : ∀ k : ℕ, Nat.Prime k → k ∣ m → ¬ k ∣ n := by
      intro k hk hkm hkn
      have hkP : k ∈ P := by
        rw [Nat.mem_primeFactors]
        exact ⟨hk, hkn, ne_of_gt hn⟩
      have hi_mem : i ∈ C := hi
      have hik : i ∈ (S k)ᶜ := by
        exact (Finset.mem_inf.mp hi_mem) k hkP
      have hk_not_dvd : ¬ Dvd.dvd k (a + (i : ℕ)) := by
        simpa [S] using hik
      exact hk_not_dvd hkm
    have hm_coprime : m.Coprime n := Nat.coprime_of_dvd hm_not
    exact Nat.coprime_iff_gcd_eq_one.mp hm_coprime

end Commons.NumberTheory.DuffinSchaeffer