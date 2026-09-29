import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq
import Submission.Commons.NumberTheory.Chebyshev.log_lcm_window_sub_theta_sub_bad_lt_le
import Submission.Commons.NumberTheory.Chebyshev.count_window_ge

namespace Commons.NumberTheory.Chebyshev

open Finset
open scoped BigOperators

private lemma theta_range (x : ℕ) :
    Chebyshev.theta (x : ℝ) = ∑ p ∈ Finset.range (x + 1), (if p.Prime then Real.log (p : ℝ) else 0) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  rw [show (Finset.Icc 0 x : Finset ℕ) = Finset.range (x + 1) from by
    ext y; simp only [Finset.mem_Icc, Finset.mem_range]; omega]
  rw [Finset.sum_filter]

private lemma theta_nat_sub (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)
      = ∑ p ∈ (Finset.Icc (a + 1) b).filter Nat.Prime, Real.log (p : ℝ) := by
  rw [theta_range b, theta_range a,
    ← Finset.sum_Ico_eq_sub (f := fun p => if p.Prime then Real.log (p : ℝ) else 0)
      (m := a + 1) (n := b + 1) (by omega)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr
  · ext y; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  · intro y hy; rfl

/-- Band formula for `θ`: if `z ≤ y` then `θ y - θ z` is the sum of `log p` over the
primes `p` with `z < p ≤ ⌊y⌋`. -/
private lemma theta_band_le (y z : ℝ) (hzy : z ≤ y) :
    Chebyshev.theta y - Chebyshev.theta z
      = ∑ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p:ℝ)), Real.log (p:ℝ) := by
  rw [Chebyshev.theta_eq_theta_coe_floor y, Chebyshev.theta_eq_theta_coe_floor z]
  have hle : ⌊z⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hzy
  rw [theta_nat_sub ⌊z⌋₊ ⌊y⌋₊ hle]
  have hset : (Finset.Icc (⌊z⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime
      = (Finset.Icc 1 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p:ℝ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨by omega, h2⟩, hp, by
        calc z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
          _ ≤ (p:ℝ) := by exact_mod_cast h1⟩
    · rintro ⟨⟨h1, h2⟩, hp, hzp⟩
      exact ⟨⟨by
        have hp0 : p ≠ 0 := by omega
        have : ⌊z⌋₊ < p := (Nat.floor_lt' hp0).mpr hzp
        omega, h2⟩, hp⟩
  rw [hset]

/-- There is no prime `p` in the "gap" `((n-k-1)/a, n/(a+1)]` when `a ≤ (n-k-1)/max k l`. -/
private lemma no_prime_gap (n k l a p : ℕ) (hM : 0 < max k l) (hkn : k ≤ n) (ha1 : 1 ≤ a)
    (haM : a ≤ (n - k - 1) / max k l) (_hp : p.Prime)
    (hlt : (n - k - 1) / a < p) (hle : p ≤ n / (a + 1)) : False := by
  have ha : 0 < a := by omega
  have hAM : a * max k l ≤ n - k - 1 := (Nat.le_div_iff_mul_le hM).mp haM
  have hMle : max k l ≤ (n - k - 1) / a :=
    (Nat.le_div_iff_mul_le ha).mpr (by rw [Nat.mul_comm]; exact hAM)
  have hA_lt : n - k - 1 < p * a := (Nat.div_lt_iff_lt_mul ha).mp hlt
  have hlepa : p * (a + 1) ≤ n := (Nat.le_div_iff_mul_le (by omega : 0 < a + 1)).mp hle
  have h1 : n - k ≤ p * a := by omega
  have hpeq : p * (a + 1) = p * a + p := by rw [Nat.mul_succ]
  have hp_le_k : p ≤ k := by omega
  have : p ≤ (n - k - 1) / a := le_trans hp_le_k (le_trans (le_max_left k l) hMle)
  omega

/-- Per-`a` rewriting of the `θ` band: the difference `θ((n-k-1)/a) - θ(max (n/(a+1)) l)`
is the sum of `log p` over the primes `p ≤ n` in the window. -/
private lemma theta_window_eq_filter_sum (n k l a : ℕ) (hM : 0 < max k l) (hkn : k ≤ n)
    (ha1 : 1 ≤ a) (haM : a ≤ (n - k - 1) / max k l) :
    Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
      - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
    = ∑ p ∈ (Finset.Icc 1 n).filter
        (fun p => p.Prime ∧ l < p ∧ p * a ≤ n - k - 1 ∧ n < p * (a + 1)),
        Real.log (p : ℝ) := by
  have ha : 0 < a := by omega
  have hAM : a * max k l ≤ n - k - 1 := (Nat.le_div_iff_mul_le hM).mp haM
  have hlmax : l ≤ max k l := le_max_right _ _
  have hlA : l * a ≤ n - k - 1 := by
    rw [Nat.mul_comm]; exact le_trans (Nat.mul_le_mul_left a hlmax) hAM
  have hAr : (l:ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) / (a:ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast ha : (0:ℝ) < (a:ℝ))]
    exact_mod_cast hlA
  have hflA : ⌊((n - k - 1 : ℕ) : ℝ) / (a:ℝ)⌋₊ = (n - k - 1) / a := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hflx : ⌊(n:ℝ) / ((a:ℝ) + 1)⌋₊ = n / (a + 1) := by
    rw [show (n:ℝ) / ((a:ℝ) + 1) = (n:ℝ) / ((a + 1 : ℕ) : ℝ) by push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  by_cases hxy : (n:ℝ) / ((a:ℝ) + 1) ≤ ((n - k - 1 : ℕ) : ℝ) / (a:ℝ)
  · have hmaxle : max ((n:ℝ) / ((a:ℝ) + 1)) (l:ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) / (a:ℝ) :=
      max_le hxy hAr
    rw [theta_band_le (((n - k - 1 : ℕ) : ℝ) / (a:ℝ))
        (max ((n:ℝ) / ((a:ℝ) + 1)) (l:ℝ)) hmaxle]
    apply Finset.sum_congr _ (fun p _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hpp, hmaxp⟩
      have hxlt : (n:ℝ) / ((a:ℝ) + 1) < (p:ℝ) := lt_of_le_of_lt (le_max_left _ _) hmaxp
      have hlp : l < p := by
        have : (l:ℝ) < (p:ℝ) := lt_of_le_of_lt (le_max_right _ _) hmaxp
        exact_mod_cast this
      have hp0 : p ≠ 0 := by omega
      have hx' : n / (a + 1) < p := by
        rw [← hflx]
        exact (Nat.floor_lt' hp0).mpr hxlt
      have hnlt : n < p * (a + 1) := (Nat.div_lt_iff_lt_mul (by omega : 0 < a + 1)).mp hx'
      have hpa : p * a ≤ n - k - 1 := by
        rw [hflA] at hp2
        exact (Nat.le_div_iff_mul_le ha).mp hp2
      have hpn : p ≤ n := by
        rw [hflA] at hp2
        have hdiv : (n - k - 1) / a ≤ n :=
          le_trans (Nat.div_le_self (n - k - 1) a) (by omega)
        omega
      exact ⟨⟨hp1, hpn⟩, hpp, hlp, hpa, hnlt⟩
    · rintro ⟨⟨hp1, hpn⟩, hpp, hlp, hpa, hnlt⟩
      have hp2 : p ≤ (n - k - 1) / a := (Nat.le_div_iff_mul_le ha).mpr hpa
      have hp0 : p ≠ 0 := by omega
      have hx' : n / (a + 1) < p := (Nat.div_lt_iff_lt_mul (by omega : 0 < a + 1)).mpr hnlt
      have hxlt : (n:ℝ) / ((a:ℝ) + 1) < (p:ℝ) := by
        have h1 : ⌊(n:ℝ) / ((a:ℝ) + 1)⌋₊ < p := by rw [hflx]; exact hx'
        exact (Nat.floor_lt' hp0).mp h1
      have hlpr : (l:ℝ) < (p:ℝ) := by exact_mod_cast hlp
      have hmaxp : max ((n:ℝ) / ((a:ℝ) + 1)) (l:ℝ) < (p:ℝ) := max_lt hxlt hlpr
      rw [hflA]
      exact ⟨⟨hp1, hp2⟩, hpp, hmaxp⟩
  · have hxlt : ((n - k - 1 : ℕ) : ℝ) / (a:ℝ) < (n:ℝ) / ((a:ℝ) + 1) := lt_of_not_ge hxy
    have hmaxeq : max ((n:ℝ) / ((a:ℝ) + 1)) (l:ℝ) = (n:ℝ) / ((a:ℝ) + 1) :=
      max_eq_left (le_trans hAr (le_of_lt hxlt))
    rw [hmaxeq]
    have hA_floor : ((n - k - 1) / a : ℕ) ≤ ⌊(n:ℝ) / ((a:ℝ) + 1)⌋₊ := by
      apply Nat.le_floor
      have h1 : (((n - k - 1) / a : ℕ) : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) / (a:ℝ) := by
        rw [← hflA]; exact Nat.floor_le (by positivity)
      linarith [hxlt]
    have hAle : (n - k - 1) / a ≤ n / (a + 1) := by
      rw [hflx] at hA_floor; exact hA_floor
    have hzerosum :
        (∑ p ∈ (Finset.Icc ((n - k - 1) / a + 1) (n / (a + 1))).filter Nat.Prime,
          Real.log (p:ℝ)) = 0 := by
      have hempty : (Finset.Icc ((n - k - 1) / a + 1) (n / (a + 1))).filter Nat.Prime = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro p hp
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        exact no_prime_gap n k l a p hM hkn ha1 haM hp.2 (by omega) hp.1.2
      rw [hempty, Finset.sum_empty]
    have htheta : Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a:ℝ))
        - Chebyshev.theta ((n:ℝ) / ((a:ℝ) + 1)) = 0 := by
      rw [Chebyshev.theta_eq_theta_coe_floor (((n - k - 1 : ℕ) : ℝ) / (a:ℝ)),
          Chebyshev.theta_eq_theta_coe_floor ((n:ℝ) / ((a:ℝ) + 1)), hflA, hflx]
      have : Chebyshev.theta ((n / (a + 1) : ℕ) : ℝ)
          - Chebyshev.theta (((n - k - 1) / a : ℕ) : ℝ) = 0 := by
        rw [theta_nat_sub ((n - k - 1) / a) (n / (a + 1)) hAle, hzerosum]
      linarith
    rw [htheta]
    have hfilt : (Finset.Icc 1 n).filter
        (fun p => p.Prime ∧ l < p ∧ p * a ≤ n - k - 1 ∧ n < p * (a + 1)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨-, hpp, hlp, hpa, hnlt⟩ := hp
      have hp2 : p ≤ (n - k - 1) / a := (Nat.le_div_iff_mul_le ha).mpr hpa
      have hx' : n / (a + 1) < p := (Nat.div_lt_iff_lt_mul (by omega : 0 < a + 1)).mpr hnlt
      omega
    rw [hfilt, Finset.sum_empty]

open Finset in
open scoped BigOperators in
theorem sum_log_primes_bad_eq_ge (n k l : ℕ) (hM : 0 < max k l) (hkn : k ≤ n) :
    (∑ p ∈ (Finset.Icc 1 n).filter
        (fun p => p.Prime ∧ l < p ∧ ¬ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)),
        Real.log (p : ℝ))
      = ∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))) := by
  classical
  have hR : (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      = ∑ p ∈ Finset.Icc 1 n,
          (if p.Prime ∧ l < p ∧ ¬ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)
            then Real.log (p : ℝ) else 0) := by
    have h1 : (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
        = ∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            ∑ p ∈ (Finset.Icc 1 n).filter
              (fun p => p.Prime ∧ l < p ∧ p * a ≤ n - k - 1 ∧ n < p * (a + 1)),
              Real.log (p : ℝ) :=
      Finset.sum_congr rfl (fun a ha => by
        obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp ha
        exact theta_window_eq_filter_sum n k l a hM hkn ha1 haM)
    rw [h1]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hp1, hpn⟩ := Finset.mem_Icc.mp hp
    by_cases hcond : p.Prime ∧ l < p
    · obtain ⟨hpp, hlp⟩ := hcond
      have hcard := count_window_ge n k l p hM hpp hpn hlp
      have hinner : (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            (if p.Prime ∧ l < p ∧ p * a ≤ n - k - 1 ∧ n < p * (a + 1)
              then Real.log (p : ℝ) else 0))
          = (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
              (if p * a ≤ n - k - 1 ∧ n < p * (a + 1) then (1:ℝ) else 0))
            * Real.log (p : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hw : p * a ≤ n - k - 1 ∧ n < p * (a + 1)
        · rw [if_pos ⟨hpp, hlp, hw.1, hw.2⟩, if_pos hw]; ring
        · rw [if_neg (fun h => hw ⟨h.2.2.1, h.2.2.2⟩), if_neg hw]; ring
      rw [hinner, Finset.sum_boole, hcard]
      by_cases hgood : ¬ ∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m
      · rw [if_pos hgood, if_pos (show p.Prime ∧ l < p ∧ ¬ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m) from ⟨hpp, hlp, hgood⟩)]
        norm_num
      · rw [if_neg hgood,
          if_neg (show ¬ (p.Prime ∧ l < p ∧ ¬ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)) from fun hc => hgood hc.2.2)]
        norm_num
    · have hzero : (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            (if p.Prime ∧ l < p ∧ p * a ≤ n - k - 1 ∧ n < p * (a + 1)
              then Real.log (p : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        rw [if_neg]
        intro hc; exact hcond ⟨hc.1, hc.2.1⟩
      rw [hzero,
        if_neg (show ¬ (p.Prime ∧ l < p ∧ ¬ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)) from
          fun hc => hcond ⟨hc.1, hc.2.1⟩)]
  rw [hR, Finset.sum_filter]

end Commons.NumberTheory.Chebyshev
