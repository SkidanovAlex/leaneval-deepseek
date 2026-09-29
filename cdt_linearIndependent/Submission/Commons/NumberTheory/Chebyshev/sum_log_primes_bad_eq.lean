import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_isEquivalent

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Chebyshev

private lemma theta_eq_theta_floor' (x : ℝ) :
    Chebyshev.theta x = Chebyshev.theta ((⌊x⌋₊ : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]

private lemma theta_nat_diff (a b : ℕ) (h : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)
      = ∑ m ∈ (Finset.Icc (a + 1) b).filter Nat.Prime, Real.log (m : ℝ) := by
  have hg : ∀ x : ℕ, Chebyshev.theta (x : ℝ)
      = ∑ p ∈ Finset.range (x + 1), (if p.Prime then Real.log (p : ℝ) else 0) := by
    intro x
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    rw [show (Finset.Icc 0 x : Finset ℕ) = Finset.range (x + 1) from by
      ext y; simp only [Finset.mem_Icc, Finset.mem_range]; omega]
    rw [Finset.sum_filter]
  rw [hg b, hg a,
    ← Finset.sum_Ico_eq_sub (f := fun p => if p.Prime then Real.log (p : ℝ) else 0)
      (m := a + 1) (n := b + 1) (by omega)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr
  · ext y; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  · intro y hy; rfl

private lemma theta_div_diff (A n m N : ℕ) (hm : 0 < m)
    (hle : n / (m + 1) ≤ A / m) (hN : A / m ≤ N) :
    Chebyshev.theta ((A : ℝ) / m) - Chebyshev.theta ((n : ℝ) / (m + 1))
      = ∑ p ∈ Finset.Icc 1 N,
          (if p.Prime ∧ p * m ≤ A ∧ n < p * (m + 1) then Real.log (p : ℝ) else 0) := by
  have hflA : ⌊(A : ℝ) / m⌋₊ = A / m := by rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hfln : ⌊(n : ℝ) / (m + 1)⌋₊ = n / (m + 1) := by
    rw [show (n : ℝ) / (m + 1) = (n : ℝ) / ((m + 1 : ℕ) : ℝ) from by push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  rw [theta_eq_theta_floor' ((A : ℝ) / m), theta_eq_theta_floor' ((n : ℝ) / (m + 1)),
    hflA, hfln]
  rw [theta_nat_diff (n / (m + 1)) (A / m) hle]
  have hset : (Finset.Icc (n / (m + 1) + 1) (A / m)).filter Nat.Prime
      = (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p * m ≤ A ∧ n < p * (m + 1)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨hp.one_le, le_trans h2 hN⟩, hp, (Nat.le_div_iff_mul_le hm).mp h2,
        (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).mp (by omega)⟩
    · rintro ⟨⟨h1, h2⟩, hp, hmul, hlt⟩
      exact ⟨⟨by
        have : n / (m + 1) < p :=
          (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).mpr hlt
        omega, (Nat.le_div_iff_mul_le hm).mpr hmul⟩, hp⟩
  rw [hset, Finset.sum_filter]

private lemma filter_W_eq_singleton (n k p : ℕ)
    (hp : p.Prime) (hpn : p ≤ n)
    (hgood : ¬ ∃ m ∈ Finset.Icc (n - k) n, p ∣ m) :
    (Finset.Icc 1 ((n - 1) / (k + 1) - 1)).filter
        (fun m => p * m ≤ n - k - 1 ∧ n < p * (m + 1)) = {n / p} := by
  have hp2 : 2 ≤ p := hp.two_le
  have hm0pos : 1 ≤ n / p := by
    have : 0 < n / p := Nat.div_pos hpn hp.pos
    omega
  have hlt0 : n < p * (n / p + 1) := Nat.lt_mul_div_succ n hp.pos
  have hmul0 : p * (n / p) ≤ n := Nat.mul_div_le n p
  have hle0 : p * (n / p) ≤ n - k - 1 := by
    have hnotin : ¬ (n - k ≤ p * (n / p)) := by
      intro hge
      exact hgood ⟨p * (n / p), Finset.mem_Icc.mpr ⟨hge, hmul0⟩, ⟨n / p, rfl⟩⟩
    exact Nat.le_sub_one_of_lt (not_le.mp hnotin)
  have hpge : k + 2 ≤ p := by
    have hA : n + 1 ≤ p * (n / p + 1) := by omega
    have hsub : (n + 1) - (n - k - 1) ≤ p * (n / p + 1) - p * (n / p) := by
      refine le_trans (Nat.sub_le_sub_right hA (n - k - 1)) ?_
      exact Nat.sub_le_sub_left hle0 (p * (n / p + 1))
    have hval : p * (n / p + 1) - p * (n / p) = p := by
      rw [show p * (n / p + 1) = p * (n / p) + p from by ring]
      exact Nat.add_sub_cancel_left _ _
    have hk2 : (n + 1) - (n - k - 1) = k + 2 := by omega
    omega
  have hkey : (k + 1) * (n / p) ≤ n - k - 2 := by
    have h1 : (k + 1) * (n / p) + (n / p) ≤ p * (n / p) := by
      rw [show (k + 1) * (n / p) + (n / p) = (k + 2) * (n / p) from by ring]
      exact Nat.mul_le_mul_right (n / p) hpge
    have h3 : (k + 1) * (n / p) ≤ p * (n / p) - 1 := by
      apply Nat.le_sub_one_of_lt
      omega
    have h4 : p * (n / p) - 1 ≤ (n - k - 1) - 1 := Nat.sub_le_sub_right hle0 1
    have h5 : (n - k - 1) - 1 = n - k - 2 := by omega
    calc (k + 1) * (n / p) ≤ p * (n / p) - 1 := h3
      _ ≤ (n - k - 1) - 1 := h4
      _ = n - k - 2 := h5
  have hfin : (k + 1) * (n / p + 1) ≤ n - 1 := by
    have hh : (k + 1) * (n / p + 1) = (k + 1) * (n / p) + (k + 1) := by ring
    omega
  have hfin2 : n / p + 1 ≤ (n - 1) / (k + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < k + 1)]
    rw [Nat.mul_comm (n / p + 1) (k + 1)]
    exact hfin
  have hm0M : n / p ≤ (n - 1) / (k + 1) - 1 := by
    have h := Nat.sub_le_sub_right hfin2 1
    rwa [Nat.add_sub_cancel] at h
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hm1, hm2⟩, hle, hlt⟩
    have h1 : m * p ≤ n := by
      have : p * m ≤ n := le_trans hle (by omega)
      rwa [Nat.mul_comm] at this
    have h2 : n < (m + 1) * p := by rw [Nat.mul_comm]; exact hlt
    exact (Nat.div_eq_of_lt_le h1 h2).symm
  · rintro rfl
    exact ⟨⟨hm0pos, hm0M⟩, hle0, hlt0⟩

private lemma filter_W_eq_empty (n k p : ℕ) (hp : p.Prime)
    (hbad : ∃ m ∈ Finset.Icc (n - k) n, p ∣ m) :
    (Finset.Icc 1 ((n - 1) / (k + 1) - 1)).filter
        (fun m => p * m ≤ n - k - 1 ∧ n < p * (m + 1)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, hm2⟩, hle, hlt⟩ := hm
  obtain ⟨m', hm', hdiv⟩ := hbad
  rw [Finset.mem_Icc] at hm'
  obtain ⟨hm'1, hm'2⟩ := hm'
  obtain ⟨t, rfl⟩ := hdiv
  have hp1 : 1 ≤ p := hp.one_le
  have h1 : m < t := by
    have hA : p * m ≤ n - k - 1 := hle
    have hpos : 0 < n - k := by
      have hm0 : 0 < m := by omega
      have : 0 < n - k - 1 := lt_of_lt_of_le (Nat.mul_pos hp.pos hm0) hA
      omega
    have hlt' : n - k - 1 < n - k := Nat.sub_one_lt (by omega)
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le (lt_of_le_of_lt hA hlt') hm'1)
  have h2 : t ≤ m := by
    have hlt' : p * t < p * (m + 1) := lt_of_le_of_lt hm'2 hlt
    have : t < m + 1 := Nat.lt_of_mul_lt_mul_left hlt'
    omega
  omega

private lemma card_filter_W (n k p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    ((Finset.Icc 1 ((n - 1) / (k + 1) - 1)).filter
        (fun m => p * m ≤ n - k - 1 ∧ n < p * (m + 1))).card
      = if (¬ ∃ m ∈ Finset.Icc (n - k) n, p ∣ m) then 1 else 0 := by
  by_cases hgood : ¬ ∃ m ∈ Finset.Icc (n - k) n, p ∣ m
  · rw [if_pos hgood, filter_W_eq_singleton n k p hp hpn hgood, Finset.card_singleton]
  · rw [if_neg hgood]
    have hbad : ∃ m ∈ Finset.Icc (n - k) n, p ∣ m := by tauto
    rw [filter_W_eq_empty n k p hp hbad, Finset.card_empty]

theorem sum_log_primes_bad_eq (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (∑ p ∈ (Finset.Icc 1 n).filter
        (fun p => p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)), Real.log (p : ℝ))
      = ∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / m)
            - Chebyshev.theta ((n : ℝ) / (m + 1))) := by
  classical
  have hstep : (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / m)
            - Chebyshev.theta ((n : ℝ) / (m + 1))))
      = ∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1), ∑ p ∈ Finset.Icc 1 n,
          (if p.Prime ∧ p * m ≤ n - k - 1 ∧ n < p * (m + 1)
            then Real.log (p : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := by omega
    have ht : (k + 1) * (m + 1) ≤ n := by
      have hdpos : 0 < (n - 1) / (k + 1) := by omega
      have hd : m + 1 ≤ (n - 1) / (k + 1) := by
        have : m < (n - 1) / (k + 1) := (Nat.le_sub_one_iff_lt hdpos).mp hm2
        omega
      have h2 : (k + 1) * ((n - 1) / (k + 1)) ≤ n - 1 := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self (n - 1) (k + 1)
      have h1 : (k + 1) * (m + 1) ≤ (k + 1) * ((n - 1) / (k + 1)) :=
        Nat.mul_le_mul_left _ hd
      omega
    have hreal : (n : ℝ) / (m + 1) ≤ (((n - k - 1 : ℕ) : ℝ)) / m := by
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hmpos)]
      have hn : n * m ≤ (n - k - 1) * (m + 1) := by
        have hAeq : n - k - 1 = n - (k + 1) := by omega
        rw [hAeq, Nat.mul_sub_right_distrib]
        calc n * m = n * (m + 1) - n := by rw [Nat.mul_succ, Nat.add_sub_cancel]
          _ ≤ n * (m + 1) - (k + 1) * (m + 1) := Nat.sub_le_sub_left ht (n * (m + 1))
      exact_mod_cast hn
    have hle : n / (m + 1) ≤ (n - k - 1) / m := by
      rw [← show ⌊(n : ℝ) / (m + 1)⌋₊ = n / (m + 1) from by
            rw [show (n : ℝ) / (m + 1) = (n : ℝ) / ((m + 1 : ℕ) : ℝ) from by push_cast; ring]
            rw [Nat.floor_div_natCast, Nat.floor_natCast],
          ← show ⌊(((n - k - 1 : ℕ) : ℝ)) / m⌋₊ = (n - k - 1) / m from by
            rw [Nat.floor_div_natCast, Nat.floor_natCast]]
      exact Nat.floor_mono hreal
    have hN : (n - k - 1) / m ≤ n := by
      have h := Nat.div_le_self (n - k - 1) m
      omega
    exact theta_div_diff (n - k - 1) n m n hmpos hle hN
  rw [hstep]
  rw [Finset.sum_comm]
  have hinner : ∀ p ∈ Finset.Icc 1 n,
      (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
          (if p.Prime ∧ p * m ≤ n - k - 1 ∧ n < p * (m + 1)
            then Real.log (p : ℝ) else 0))
        = (if p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)
            then Real.log (p : ℝ) else 0) := by
    intro p hp
    have hpn : p ≤ n := (Finset.mem_Icc.mp hp).2
    by_cases hpp : p.Prime
    · have hcard := card_filter_W n k p hpp hpn
      have hkey : (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
            (if p.Prime ∧ p * m ≤ n - k - 1 ∧ n < p * (m + 1)
              then Real.log (p : ℝ) else 0))
          = (((Finset.Icc 1 ((n - 1) / (k + 1) - 1)).filter
              (fun m => p * m ≤ n - k - 1 ∧ n < p * (m + 1))).card : ℝ)
            * Real.log (p : ℝ) := by
        rw [show (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
              (if p.Prime ∧ p * m ≤ n - k - 1 ∧ n < p * (m + 1)
                then Real.log (p : ℝ) else 0))
            = (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
                (if p * m ≤ n - k - 1 ∧ n < p * (m + 1)
                  then Real.log (p : ℝ) else 0)) from by
              apply Finset.sum_congr rfl; intro m hm; simp [hpp]]
        rw [show (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
                (if p * m ≤ n - k - 1 ∧ n < p * (m + 1)
                  then Real.log (p : ℝ) else 0))
            = (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
                (if p * m ≤ n - k - 1 ∧ n < p * (m + 1)
                  then (1 : ℝ) else 0) * Real.log (p : ℝ)) from by
              apply Finset.sum_congr rfl; intro m hm
              by_cases hw : (p * m ≤ n - k - 1 ∧ n < p * (m + 1)) <;> simp [hw]]
        rw [← Finset.sum_mul, Finset.sum_boole]
      rw [hkey, hcard]
      by_cases hgood : ¬ ∃ m ∈ Finset.Icc (n - k) n, p ∣ m
      · simp [hpp, hgood]
      · simp [hpp, hgood]
    · have : (∑ m ∈ Finset.Icc 1 ((n - 1) / (k + 1) - 1),
            (if p.Prime ∧ p * m ≤ n - k - 1 ∧ n < p * (m + 1)
              then Real.log (p : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [if_neg (by intro hc; exact hpp hc.1)]
      rw [this]
      simp [hpp]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_filter]

end Commons.NumberTheory.Chebyshev