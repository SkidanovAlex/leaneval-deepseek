import Mathlib
import Submission.Commons.NumberTheory.Divisors.sum_card_divisors_sq_le
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Work.FITop4.Red5.pow4_omega_le_small_divisor_sum

set_option maxHeartbeats 4000000

open Finset
open scoped BigOperators

namespace Work.FITop4.Red5

attribute [local instance] Classical.propDecidable

noncomputable section

lemma two_pow_card_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n.primeFactors.card) ≤ n := by
  have hdvd : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have hle : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn hdvd
  calc 2 ^ (n.primeFactors.card) = ∏ _p ∈ n.primeFactors, (2:ℕ) := (Finset.prod_const (2:ℕ)).symm
    _ ≤ ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_le_prod₀
        · intro p hp; norm_num
        · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := hle

lemma card_primeFactors_add_one_le (n Y : ℕ) (hn : 1 ≤ n) (hnY : n ≤ Y) :
    ((n.primeFactors.card : ℝ) + 1) ≤ 3 * Real.log ((Y:ℝ) + 2) := by
  set L : ℝ := Real.log ((Y:ℝ) + 2) with hL
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2ge : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnk : (n:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hnY
  have hk2 : (2:ℝ) ^ (n.primeFactors.card) ≤ (Y:ℝ) + 2 := by
    have h1 : (2:ℝ) ^ (n.primeFactors.card) = ((2 ^ (n.primeFactors.card) : ℕ) : ℝ) := by
      push_cast; ring
    rw [h1]
    have h2 : ((2 ^ (n.primeFactors.card) : ℕ) : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast two_pow_card_le n hn
    linarith
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (0:ℝ) ≤ (Y:ℝ) := by positivity
    linarith
  have hklog : (n.primeFactors.card : ℝ) * Real.log 2 ≤ L := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ) ^ (n.primeFactors.card)) hk2
    rwa [Real.log_pow] at h
  rw [hL] at hklog ⊢
  have hk : (n.primeFactors.card : ℝ) ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]; linarith [hklog]
  have hLge : Real.log 2 ≤ L := by
    apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
    have : (0:ℝ) ≤ (Y:ℝ) := by positivity
    linarith
  have hquot : 1 ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]; linarith [hLge]
  calc (n.primeFactors.card : ℝ) + 1 ≤ L / Real.log 2 + 1 := by linarith [hk]
    _ ≤ L / Real.log 2 + L / Real.log 2 := by linarith [hquot]
    _ = 2 * L / Real.log 2 := by ring
    _ ≤ 3 * L := by
        have h23 : (2:ℝ)/Real.log 2 ≤ 3 := by
          rw [div_le_iff₀ hlog2pos]; linarith [hlog2ge]
        calc 2 * L / Real.log 2 = ((2:ℝ)/Real.log 2) * L := by ring
          _ ≤ 3 * L := mul_le_mul_of_nonneg_right h23 (le_of_lt hLpos)

lemma div_count_window (X H d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc (X+1) (X+H)).filter (fun n => d ∣ n)).card ≤ H / d + 1 := by
  have hIoc : Finset.Icc (X+1) (X+H) = Finset.Ioc X (X+H) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIoc]
  have hdisj : Disjoint ((Finset.Ioc 0 X).filter (fun n => d ∣ n))
      ((Finset.Ioc X (X+H)).filter (fun n => d ∣ n)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn1 hn2
    omega
  have hunion : ((Finset.Ioc 0 X).filter (fun n => d ∣ n)) ∪
        ((Finset.Ioc X (X+H)).filter (fun n => d ∣ n))
      = (Finset.Ioc 0 (X+H)).filter (fun n => d ∣ n) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : n ≤ X
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
  have hU := Finset.card_union_of_disjoint hdisj
  rw [hunion, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hU
  have hadd : (X+H)/d = X/d + H/d + (if d ≤ X % d + H % d then 1 else 0) :=
    Nat.add_div (show 0 < d by omega : 0 < d)
  have hle : (X+H)/d ≤ X/d + H/d + 1 := by
    rw [hadd]; split <;> omega
  have hba : X/d ≤ (X+H)/d := Nat.div_le_div_right (Nat.le_add_right X H)
  omega

lemma sum_ite_dvd_mul (s : Finset ℕ) (d : ℕ) (r : ℝ) :
    (∑ n ∈ s, (if d ∣ n then r else 0)) = r * ((s.filter (fun n => d ∣ n)).card : ℝ) := by
  have hcard : ((s.filter (fun n => d ∣ n)).card : ℝ)
      = ∑ n ∈ s, (if d ∣ n then (1:ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : d ∣ n <;> simp [h]

lemma log_le_mul_log (Y k : ℕ) {a : ℝ} (ha1 : 1 ≤ a) (hak : a ≤ ((Y:ℝ)+2)^k) :
    Real.log a ≤ k * Real.log ((Y:ℝ)+2) := by
  have hYpos : (0:ℝ) < (Y:ℝ)+2 := by positivity
  calc Real.log a ≤ Real.log (((Y:ℝ)+2)^k) := Real.log_le_log (by linarith) hak
    _ = k * Real.log ((Y:ℝ)+2) := by rw [Real.log_pow]

theorem window_T3_strip_bound : ∃ C : ℝ, 0 < C ∧ ∀ (X H : ℕ), X ≤ 4 * H * H →
    (∑ n ∈ Finset.Icc (X + 1) (X + H), (4 : ℝ) ^ (n.primeFactors.card))
      ≤ C * (H : ℝ) * (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ (100 : ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 2
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Divisors.sum_card_divisors_sq_le
  refine ⟨max (6 * (16*C1 + 24*C2)) 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro X H hXH
  rcases Nat.eq_zero_or_pos H with hH0 | hHpos
  · subst hH0; simp
  have hH : 1 ≤ H := hHpos
  set L : ℝ := Real.log ((X:ℝ) + (H:ℝ) + 2) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have hx : (3:ℝ) ≤ (X:ℝ)+(H:ℝ)+2 := by
      have h1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
      have h0 : (0:ℝ) ≤ (X:ℝ) := by positivity
      linarith
    have hl3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_three]
    exact le_trans hl3 (Real.log_le_log (by norm_num) hx)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  set s : Finset ℕ := Finset.Icc (X+1) (X+H) with hs
  set Y : ℕ := X + H with hY
  have hLY : Real.log ((Y:ℝ) + 2) = L := by rw [hL, hY]; push_cast; ring_nf
  have hY5 : Y ≤ 5*H*H := by
    rw [hY]
    have hH2 : H ≤ H*H := by
      calc H = H*1 := (mul_one H).symm
        _ ≤ H*H := Nat.mul_le_mul_left H hH
    calc X + H ≤ 4*H*H + H*H := add_le_add hXH hH2
      _ = 5*H*H := by ring
  have hYH : H ≤ Y := by rw [hY]; omega
  -- key log bounds
  have hone3 : (1:ℝ) ≤ ((3*H:ℕ):ℝ) + 2 := by
    have : (0:ℝ) ≤ ((3*H:ℕ):ℝ) := by positivity
    linarith
  have hone6 : (1:ℝ) ≤ 2*((3*H:ℕ):ℝ) + 2 := by
    have : (0:ℝ) ≤ ((3*H:ℕ):ℝ) := by positivity
    linarith
  have hlog3H : Real.log (((3*H:ℕ):ℝ) + 2) ≤ 2*L := by
    have hYR : (H:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hYH
    have hle : ((3*H:ℕ):ℝ) + 2 ≤ ((Y:ℝ)+2)^2 := by
      have hc : ((3*H:ℕ):ℝ) = 3*(H:ℝ) := by push_cast; ring
      rw [hc]
      have h1 : 3*(H:ℝ)+2 ≤ ((H:ℝ)+2)^2 := by nlinarith [hH]
      have h2 : ((H:ℝ)+2)^2 ≤ ((Y:ℝ)+2)^2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
    have h := log_le_mul_log Y 2 hone3 hle
    simpa [hLY] using h
  have hlog6H : Real.log (2*((3*H:ℕ):ℝ) + 2) ≤ 2*L := by
    have hYR : (H:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hYH
    have hle : 2*((3*H:ℕ):ℝ) + 2 ≤ ((Y:ℝ)+2)^2 := by
      have hc : ((3*H:ℕ):ℝ) = 3*(H:ℝ) := by push_cast; ring
      rw [hc]
      have h1 : 2*(3*(H:ℝ))+2 ≤ ((H:ℝ)+2)^2 := by nlinarith [hH, sq_nonneg ((H:ℝ)-1)]
      have h2 : ((H:ℝ)+2)^2 ≤ ((Y:ℝ)+2)^2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
    have h := log_le_mul_log Y 2 hone6 hle
    simpa [hLY] using h
  -- 4^ω(d) ≤ τ(d)^2
  have htau : ∀ d : ℕ, 1 ≤ d → (4:ℝ) ^ (d.primeFactors.card) ≤ ((d.divisors.card : ℝ))^2 := by
    intro d hd
    have h1 : (4:ℝ) ^ (d.primeFactors.card) = ((2:ℝ) ^ (d.primeFactors.card))^2 := by
      rw [show (4:ℝ) = 2*2 by norm_num, mul_pow]; ring
    rw [h1]
    apply pow_le_pow_left₀ (by positivity)
    have h := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
      (d := d) (by omega : 0 < d)
    exact_mod_cast h
  -- the main double-sum bound
  have hcore : (∑ n ∈ s, ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n),
        (4:ℝ) ^ (d.primeFactors.card)) ≤ (16*C1 + 24*C2) * (H:ℝ) * L^4 := by
    set D : Finset ℕ := (Finset.Icc 1 Y).filter (fun d => d*d ≤ Y) with hD
    have hDmem : ∀ d ∈ D, 1 ≤ d ∧ d ≤ Y ∧ d*d ≤ Y := by
      intro d hd; rw [hD] at hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      exact ⟨hd.1.1, hd.1.2, hd.2⟩
    have hDsub3 : D ⊆ Finset.Icc 1 (3*H) := by
      intro d hd
      obtain ⟨hd1, hdY, hdsq⟩ := hDmem d hd
      refine Finset.mem_Icc.mpr ⟨hd1, ?_⟩
      have hlt : d*d < 3*H * (3*H) := by nlinarith [hdsq, hY5, hH]
      exact (Nat.mul_self_lt_mul_self_iff.mp hlt).le
    have hswap : (∑ n ∈ s, ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n),
          (4:ℝ) ^ (d.primeFactors.card))
        ≤ ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * ((s.filter (fun n => d ∣ n)).card : ℝ) := by
      calc (∑ n ∈ s, ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card))
          ≤ ∑ n ∈ s, ∑ d ∈ D, (if d ∣ n then (4:ℝ) ^ (d.primeFactors.card) else 0) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnmem := Finset.mem_Icc.mp (hs ▸ hn)
            have hn1 : 1 ≤ n := by omega
            have hnY : n ≤ Y := by rw [hY]; omega
            have hsub : n.divisors.filter (fun d => d*d ≤ n) ⊆ D.filter (fun d => d ∣ n) := by
              intro d hd
              simp only [Finset.mem_filter] at hd ⊢
              obtain ⟨hdmem, hdsq⟩ := hd
              obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hdmem
              have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdmem
              have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdvd
              rw [hD]
              simp only [Finset.mem_filter, Finset.mem_Icc]
              exact ⟨⟨⟨hd1, by omega⟩, by omega⟩, hdvd⟩
            calc (∑ d ∈ n.divisors.filter (fun d => d*d ≤ n), (4:ℝ) ^ (d.primeFactors.card))
                ≤ ∑ d ∈ D.filter (fun d => d ∣ n), (4:ℝ) ^ (d.primeFactors.card) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
              _ = ∑ d ∈ D, (if d ∣ n then (4:ℝ) ^ (d.primeFactors.card) else 0) := by
                  rw [Finset.sum_filter]
        _ = ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * ((s.filter (fun n => d ∣ n)).card : ℝ) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro d hd
            exact sum_ite_dvd_mul s d ((4:ℝ) ^ (d.primeFactors.card))
    have hcardbound : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * ((s.filter (fun n => d ∣ n)).card : ℝ)
        ≤ ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * (((H/d + 1 : ℕ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : 1 ≤ d := (hDmem d hd).1
      have hcard : ((s.filter (fun n => d ∣ n)).card : ℝ) ≤ (((H/d + 1 : ℕ)) : ℝ) := by
        have h := div_count_window X H d hd1
        exact_mod_cast h
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    have hsplit : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * (((H/d + 1 : ℕ)) : ℝ)
        ≤ (H:ℝ) * (∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ))
            + ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) := by
      have heq : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * (((H/d + 1 : ℕ)) : ℝ)
          = (∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) * ((H/d : ℕ):ℝ))
              + ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      apply add_le_add
      · rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (hDmem d hd).1
        have hle : ((H/d : ℕ) : ℝ) ≤ (H:ℝ)/(d:ℝ) := Nat.cast_div_le
        calc (4:ℝ) ^ (d.primeFactors.card) * (((H/d : ℕ)) : ℝ)
            ≤ (4:ℝ) ^ (d.primeFactors.card) * ((H:ℝ)/(d:ℝ)) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ = (H:ℝ) * ((4:ℝ) ^ (d.primeFactors.card) / (d:ℝ)) := by ring
      · exact le_refl _
    have hsumdiv : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ) ≤ 16*C1*L^4 := by
      have h1 : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ)
          ≤ ∑ d ∈ Finset.Icc 1 (3*H), (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hDsub3 (fun i _ _ => by positivity)
      have h2 : ∑ d ∈ Finset.Icc 1 (3*H), (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ)
          ≤ ∑ d ∈ Finset.Icc 1 (3*H), ((d.divisors.card:ℝ))^2 / (d:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact div_le_div_of_nonneg_right (htau d (Finset.mem_Icc.mp hd).1) (by positivity)
      have h3 : ∑ d ∈ Finset.Icc 1 (3*H), ((d.divisors.card:ℝ))^2 / (d:ℝ)
          ≤ C1 * (Real.log (((3*H:ℕ):ℝ)+2))^4 := hC1 (3*H) (by omega)
      have h4 : (Real.log (((3*H:ℕ):ℝ)+2))^4 ≤ (2*L)^4 :=
        pow_le_pow_left₀ (Real.log_nonneg hone3) hlog3H 4
      have h5 : (2*L)^4 = 16*L^4 := by ring
      calc ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ)
          ≤ C1 * (Real.log (((3*H:ℕ):ℝ)+2))^4 := le_trans h1 (le_trans h2 h3)
        _ ≤ C1 * (2*L)^4 := by apply mul_le_mul_of_nonneg_left h4 hC1pos.le
        _ = 16*C1*L^4 := by rw [h5]; ring
    have hsumn : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) ≤ 24*C2*(H:ℝ)*L^3 := by
      have h1 : ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card)
          ≤ ∑ d ∈ Finset.Icc 1 (3*H), (4:ℝ) ^ (d.primeFactors.card) :=
        Finset.sum_le_sum_of_subset_of_nonneg hDsub3 (fun i _ _ => by positivity)
      have h2 : ∑ d ∈ Finset.Icc 1 (3*H), (4:ℝ) ^ (d.primeFactors.card)
          ≤ ∑ d ∈ Finset.Icc 1 (3*H), ((d.divisors.card:ℝ))^2 := by
        apply Finset.sum_le_sum; intro d hd; exact htau d (Finset.mem_Icc.mp hd).1
      have h3 : ∑ d ∈ Finset.Icc 1 (3*H), ((d.divisors.card:ℝ))^2
          ≤ C2 * ((3*H:ℕ):ℝ) * (Real.log (2*((3*H:ℕ):ℝ)+2))^3 := hC2 (3*H)
      have h4 : (Real.log (2*((3*H:ℕ):ℝ)+2))^3 ≤ (2*L)^3 :=
        pow_le_pow_left₀ (Real.log_nonneg hone6) hlog6H 3
      have h5 : C2 * ((3*H:ℕ):ℝ) * (2*L)^3 = 24*C2*(H:ℝ)*L^3 := by push_cast; ring
      have h6 : C2 * ((3*H:ℕ):ℝ) * (Real.log (2*((3*H:ℕ):ℝ)+2))^3
          ≤ C2 * ((3*H:ℕ):ℝ) * (2*L)^3 := by
        apply mul_le_mul_of_nonneg_left h4
        positivity
      calc ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card)
          ≤ C2 * ((3*H:ℕ):ℝ) * (Real.log (2*((3*H:ℕ):ℝ)+2))^3 := le_trans h1 (le_trans h2 h3)
        _ ≤ C2 * ((3*H:ℕ):ℝ) * (2*L)^3 := h6
        _ = 24*C2*(H:ℝ)*L^3 := h5
    calc (∑ n ∈ s, ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card))
        ≤ (H:ℝ) * (∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) / (d:ℝ))
            + ∑ d ∈ D, (4:ℝ) ^ (d.primeFactors.card) := le_trans hswap (le_trans hcardbound hsplit)
      _ ≤ (H:ℝ) * (16*C1*L^4) + 24*C2*(H:ℝ)*L^3 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hsumdiv (by positivity)
          · exact hsumn
      _ ≤ (16*C1 + 24*C2) * (H:ℝ) * L^4 := by
          have hL34 : L^3 ≤ L^4 := by
            calc L^3 = L^3*1 := by ring
              _ ≤ L^3*L := by apply mul_le_mul_of_nonneg_left hL1 (by positivity)
              _ = L^4 := by ring
          have e : (H:ℝ) * (16*C1*L^4) + 24*C2*(H:ℝ)*L^3
              = 16*C1*(H:ℝ)*L^4 + 24*C2*(H:ℝ)*L^3 := by ring
          rw [e]
          calc 16*C1*(H:ℝ)*L^4 + 24*C2*(H:ℝ)*L^3
              ≤ 16*C1*(H:ℝ)*L^4 + 24*C2*(H:ℝ)*L^4 := by
                exact add_le_add le_rfl (by
                  calc 24*C2*(H:ℝ)*L^3 = (24*C2*(H:ℝ))*L^3 := by ring
                    _ ≤ (24*C2*(H:ℝ))*L^4 := mul_le_mul_of_nonneg_left hL34 (by positivity)
                    _ = 24*C2*(H:ℝ)*L^4 := by ring)
            _ = (16*C1 + 24*C2) * (H:ℝ) * L^4 := by ring
  -- pointwise sum bound
  have hA : (∑ n ∈ s, (4:ℝ) ^ (n.primeFactors.card))
      ≤ ∑ n ∈ s, 2 * ((n.primeFactors.card:ℝ)+1) *
          (∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := by
      have := Finset.mem_Icc.mp (hs ▸ hn); omega
    exact pow4_omega_le_small_divisor_sum n hn1
  have hB : ∑ n ∈ s, 2 * ((n.primeFactors.card:ℝ)+1) *
        (∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card))
      ≤ 6*L * (∑ n ∈ s, ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnmem := Finset.mem_Icc.mp (hs ▸ hn)
    have hn1 : 1 ≤ n := by omega
    have hnY : n ≤ Y := by rw [hY]; omega
    have hw := card_primeFactors_add_one_le n Y hn1 hnY
    rw [hLY] at hw
    have hSn : 0 ≤ ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    calc 2 * ((n.primeFactors.card:ℝ)+1) * (∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card))
        ≤ 2 * (3*L) * (∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card)) := by
          apply mul_le_mul_of_nonneg_right _ hSn
          exact mul_le_mul_of_nonneg_left hw (by norm_num)
      _ = 6*L * (∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card)) := by ring
  -- finish
  have hfinal : (∑ n ∈ s, (4:ℝ) ^ (n.primeFactors.card))
      ≤ max (6 * (16*C1 + 24*C2)) 1 * (H:ℝ) * L^100 := by
    have step : (∑ n ∈ s, (4:ℝ) ^ (n.primeFactors.card))
        ≤ 6*L * ((16*C1 + 24*C2) * (H:ℝ) * L^4) := le_trans hA (le_trans hB (by
          apply mul_le_mul_of_nonneg_left hcore (by positivity)))
    have h6 : 6*L * ((16*C1 + 24*C2) * (H:ℝ) * L^4)
        ≤ max (6 * (16*C1 + 24*C2)) 1 * (H:ℝ) * L^100 := by
      have hcoef : 6 * (16*C1 + 24*C2) ≤ max (6 * (16*C1 + 24*C2)) 1 := le_max_left _ _
      have hL5 : L^5 ≤ L^100 := by
        apply pow_le_pow_right₀ hL1 (by norm_num : 5 ≤ 100)
      have hHnn : (0:ℝ) ≤ (H:ℝ) := by positivity
      have hcoefnn : (0:ℝ) ≤ 6 * (16*C1 + 24*C2) := by positivity
      have hL5nn : (0:ℝ) ≤ L^5 := by positivity
      have e1 : 6*L * ((16*C1 + 24*C2) * (H:ℝ) * L^4) = (6*(16*C1+24*C2)) * (H:ℝ) * L^5 := by ring
      rw [e1]
      calc (6*(16*C1+24*C2)) * (H:ℝ) * L^5
          ≤ max (6 * (16*C1 + 24*C2)) 1 * (H:ℝ) * L^5 := by
            apply mul_le_mul_of_nonneg_right _ hL5nn
            exact mul_le_mul_of_nonneg_right hcoef hHnn
        _ ≤ max (6 * (16*C1 + 24*C2)) 1 * (H:ℝ) * L^100 :=
            mul_le_mul_of_nonneg_left hL5 (by positivity)
    exact le_trans step h6
  exact hfinal

end

end Work.FITop4.Red5
