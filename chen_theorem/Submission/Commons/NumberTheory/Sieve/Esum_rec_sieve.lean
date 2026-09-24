import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Commons.NumberTheory.Sieve

open Finset

noncomputable def Esum (y N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc y N).filter (fun p => p.Prime), 1 / ((p : ℝ) - 1)

noncomputable def Esieve (y M : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ (∏ p ∈ S, p).divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) * Esum y (M / d)

lemma divisors_mul_prime_eq (q N : ℕ) (hq : q.Prime) (hqd : ¬ q ∣ N) :
    (q * N).divisors = N.divisors ∪ N.divisors.image (fun d => q * d) := by
  have hN0 : N ≠ 0 := fun h => hqd (h ▸ dvd_zero q)
  have hqN0 : q * N ≠ 0 := Nat.mul_ne_zero hq.ne_zero hN0
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hdvd, _⟩
    by_cases h : q ∣ d
    · obtain ⟨e, rfl⟩ := h
      right
      exact ⟨e, ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp hdvd, hN0⟩, rfl⟩
    · left
      exact ⟨Nat.Coprime.dvd_of_dvd_mul_left ((hq.coprime_iff_not_dvd.mpr h).symm) hdvd, hN0⟩
  · rintro (⟨hdvd, _⟩ | ⟨e, ⟨hed, _⟩, rfl⟩)
    · exact ⟨dvd_mul_of_dvd_right hdvd q, hqN0⟩
    · exact ⟨Nat.mul_dvd_mul_left q hed, hqN0⟩

lemma disjoint_divisors_image_mul_prime (q N : ℕ) (hqd : ¬ q ∣ N) :
    Disjoint N.divisors (N.divisors.image (fun d => q * d)) := by
  rw [Finset.disjoint_left]
  intro d hd1 hd2
  rw [Finset.mem_image] at hd2
  obtain ⟨e, he, rfl⟩ := hd2
  exact hqd (dvd_trans (dvd_mul_right q e) (Nat.mem_divisors.mp hd1).1)

lemma sum_divisors_mul_prime (F : ℕ → ℝ) (q N : ℕ) (hq : q.Prime) (hqd : ¬ q ∣ N) :
    ∑ d ∈ (q * N).divisors, F d
      = ∑ d ∈ N.divisors, F d + ∑ d ∈ N.divisors, F (q * d) := by
  rw [divisors_mul_prime_eq q N hq hqd,
      Finset.sum_union (disjoint_divisors_image_mul_prime q N hqd)]
  congr 1
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel hq.pos hab

lemma moebius_totient_mul_prime (q d : ℕ) (hq : q.Prime) (hqd : ¬ q ∣ d) :
    ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) / (Nat.totient (q * d) : ℝ)
      = -(1 / ((q : ℝ) - 1)) * (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)) := by
  have hcop : q.Coprime d := hq.coprime_iff_not_dvd.mpr hqd
  have hmu : ArithmeticFunction.moebius (q * d) = - ArithmeticFunction.moebius d := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hq]
    ring
  have hphi : Nat.totient (q * d) = (q - 1) * Nat.totient d := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hq]
  have hcastmu : ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) = - ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    rw [hmu]; simp
  have hcastphi : (Nat.totient (q * d) : ℝ) = ((q : ℝ) - 1) * (Nat.totient d : ℝ) := by
    rw [hphi]; push_cast [Nat.cast_sub hq.one_le]; ring
  rw [hcastmu, hcastphi, ← neg_div]
  rw [div_mul_div_comm]
  ring

lemma filter_lt_max'_eq_erase {S : Finset ℕ} (hne : S.Nonempty) :
    S.filter (fun p => p < S.max' hne) = S.erase (S.max' hne) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hp, hlt⟩
    exact ⟨ne_of_lt hlt, hp⟩
  · rintro ⟨hne', hp⟩
    exact ⟨hp, lt_of_le_of_ne (Finset.le_max' S p hp) hne'⟩

lemma filter_lt_eq_filter_erase {S : Finset ℕ} {q q' : ℕ} (h : q' < q) :
    S.filter (fun p => p < q') = (S.erase q).filter (fun p => p < q') := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hp, hlt⟩
    exact ⟨⟨ne_of_lt (lt_trans hlt h), hp⟩, hlt⟩
  · rintro ⟨⟨_, hp⟩, hlt⟩
    exact ⟨hp, hlt⟩

lemma Esieve_erase_max (y M : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    Esieve y M S =
      Esieve y M (S.erase (S.max' hne)) -
        (1 / ((S.max' hne : ℝ) - 1)) * Esieve y (M / S.max' hne) (S.erase (S.max' hne)) := by
  set q := S.max' hne with hq
  have hqmem : q ∈ S := by rw [hq]; exact Finset.max'_mem S hne
  have hqprime : q.Prime := hS q hqmem
  have hS'p : ∀ p ∈ S.erase q, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
  set N := ∏ p ∈ S.erase q, p with hN
  have hqN : ¬ q ∣ N := by
    intro hd
    rw [hN] at hd
    rw [Prime.dvd_finsetProd_iff hqprime.prime (fun p => p)] at hd
    obtain ⟨p, hp, hqp⟩ := hd
    have hpp : p.Prime := hS'p p hp
    have hpq : p = q := by
      rcases (Nat.dvd_prime hpp).mp hqp with h1 | h1
      · exact absurd h1 hqprime.ne_one
      · exact h1.symm
    rw [hpq] at hp
    exact Finset.notMem_erase q S hp
  have hprod : (∏ p ∈ S, p) = q * N := by
    rw [← Finset.insert_erase hqmem, Finset.prod_insert (Finset.notMem_erase q S), hN]
  have hmain : Esieve y M S =
      (∑ d ∈ N.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) * Esum y (M / d))
      + (∑ d ∈ N.divisors, ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) / (Nat.totient (q * d) : ℝ) * Esum y (M / (q * d))) := by
    rw [Esieve, hprod]
    exact sum_divisors_mul_prime
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) * Esum y (M / d)) q N hqprime hqN
  have hfirst : (∑ d ∈ N.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) * Esum y (M / d))
      = Esieve y M (S.erase q) := by
    rw [Esieve, hN]
  have hsecond : (∑ d ∈ N.divisors, ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) / (Nat.totient (q * d) : ℝ) * Esum y (M / (q * d)))
      = -(1 / ((q : ℝ) - 1)) * Esieve y (M / q) (S.erase q) := by
    rw [Esieve, ← hN, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hqd : ¬ q ∣ d := fun hh => hqN (dvd_trans hh (Nat.mem_divisors.mp hd).1)
    rw [moebius_totient_mul_prime q d hqprime hqd, Nat.div_div_eq_div_mul]
    ring
  rw [hmain, hfirst, hsecond]
  ring

theorem Esieve_rec (y M : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Esieve y M S =
      Esum y M - ∑ q ∈ S, (1 / ((q : ℝ) - 1)) * Esieve y (M / q) (S.filter (fun p => p < q)) := by
  classical
  suffices H : ∀ (n : ℕ) (S : Finset ℕ), S.card = n → ∀ M : ℕ, (∀ p ∈ S, p.Prime) →
      Esieve y M S =
        Esum y M - ∑ q ∈ S, (1 / ((q : ℝ) - 1)) * Esieve y (M / q) (S.filter (fun p => p < q)) by
    exact H S.card S rfl M hS
  intro n
  refine Nat.strong_induction_on n ?_
  intro k ih S hScard M hS
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]
    simp [Esieve, Esum]
  · set m := S.max' hne with hm
    have hmmem : m ∈ S := by rw [hm]; exact Finset.max'_mem S hne
    have hmprime : m.Prime := hS m hmmem
    have hSp : ∀ p ∈ S.erase m, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
    have hcard : (S.erase m).card < k := by rw [← hScard]; exact Finset.card_erase_lt_of_mem hmmem
    have hIH := ih (S.erase m).card hcard (S.erase m) rfl M hSp
    have hstep := Esieve_erase_max y M S hS hne
    rw [← hm] at hstep
    rw [hstep, hIH]
    have hfm : S.filter (fun p => p < m) = S.erase m := by
      rw [hm]; exact filter_lt_max'_eq_erase hne
    have hfr : ∀ r ∈ S.erase m,
        S.filter (fun p => p < r) = (S.erase m).filter (fun p => p < r) := by
      intro r hr
      have hrm : r < m := by
        have hle : r ≤ S.max' hne := Finset.le_max' S r (Finset.mem_of_mem_erase hr)
        rw [← hm] at hle
        exact lt_of_le_of_ne hle (Finset.ne_of_mem_erase hr)
      exact filter_lt_eq_filter_erase hrm
    have hsum_eq : (∑ r ∈ S.erase m, (1 / ((r : ℝ) - 1)) * Esieve y (M / r) (S.filter (fun p => p < r)))
        = ∑ r ∈ S.erase m, (1 / ((r : ℝ) - 1)) * Esieve y (M / r) ((S.erase m).filter (fun p => p < r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hfr r hr]
    have hsplit : (∑ r ∈ S, (1 / ((r : ℝ) - 1)) * Esieve y (M / r) (S.filter (fun p => p < r)))
        = (1 / ((m : ℝ) - 1)) * Esieve y (M / m) (S.filter (fun p => p < m))
          + ∑ r ∈ S.erase m, (1 / ((r : ℝ) - 1)) * Esieve y (M / r) (S.filter (fun p => p < r)) :=
      (Finset.add_sum_erase S _ hmmem).symm
    have hSsum : (∑ r ∈ S, (1 / ((r : ℝ) - 1)) * Esieve y (M / r) (S.filter (fun p => p < r)))
        = (∑ r ∈ S.erase m, (1 / ((r : ℝ) - 1)) * Esieve y (M / r) ((S.erase m).filter (fun p => p < r)))
          + (1 / ((m : ℝ) - 1)) * Esieve y (M / m) (S.erase m) := by
      rw [hsplit, hfm, hsum_eq]
      ring
    rw [hSsum]
    ring




theorem Esum_rec_sieve (y M : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ d ∈ (∏ p ∈ S, p).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
        (∑ p ∈ (Finset.Icc y (M / d)).filter (fun p => p.Prime), 1 / ((p : ℝ) - 1)))
    = (∑ p ∈ (Finset.Icc y M).filter (fun p => p.Prime), 1 / ((p : ℝ) - 1))
      - ∑ q ∈ S, (1 / ((q : ℝ) - 1)) *
          (∑ d ∈ (∏ p ∈ S.filter (fun p => p < q), p).divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            (∑ p ∈ (Finset.Icc y ((M / q) / d)).filter (fun p => p.Prime),
              1 / ((p : ℝ) - 1))) := by
  change Esieve y M S = Esum y M - ∑ q ∈ S, (1 / ((q : ℝ) - 1)) * Esieve y (M / q) (S.filter (fun p => p < q))
  exact Esieve_rec y M S hS

end Commons.NumberTheory.Sieve