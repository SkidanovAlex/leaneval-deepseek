import Mathlib
import Submission.Work.FITop4.Red5.window_T3_weight_sum
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex
import Submission.Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. A uniform partial-sum bound for `k^σ`, `σ ∈ [-1/2, 1/4]` -/

lemma sum_rpow_Icc_le' :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (σ : ℝ), 1 ≤ m → -(1 : ℝ) / 2 ≤ σ → σ ≤ 1 / 4 →
      (∑ k ∈ Finset.Icc 1 m, ((k : ℝ)) ^ σ) ≤ C * (m : ℝ) ^ (1 + σ) := by
  refine ⟨5, by norm_num, ?_⟩
  intro m σ hm hσ1 hσ2
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hmnn : (0:ℝ) ≤ (m:ℝ) := le_of_lt hmpos
  rcases lt_or_ge (0:ℝ) σ with hσ | hσ
  · have hstep : (∑ k ∈ Finset.Icc 1 m, ((k:ℝ))^σ) ≤ (Finset.Icc 1 m).card * (m:ℝ)^σ := by
      calc (∑ k ∈ Finset.Icc 1 m, ((k:ℝ))^σ) ≤ ∑ k ∈ Finset.Icc 1 m, (m:ℝ)^σ := by
            apply Finset.sum_le_sum
            intro k hk
            have hk1 : (0:ℝ) < (k:ℝ) := by
              have h1' : (1:ℕ) ≤ k := (Finset.mem_Icc.mp hk).1
              exact_mod_cast (by omega : 0 < k)
            have hkm : (k:ℝ) ≤ (m:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
            exact Real.rpow_le_rpow (le_of_lt hk1) hkm (le_of_lt hσ)
        _ = (Finset.Icc 1 m).card * (m:ℝ)^σ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [Nat.card_Icc 1 m] at hstep
    norm_num at hstep
    have hconv : (m:ℝ) * (m:ℝ)^σ = (m:ℝ)^(1+σ) := by
      rw [Real.rpow_add hmpos 1 σ, Real.rpow_one]
    rw [hconv] at hstep
    have hnn : (0:ℝ) ≤ (m:ℝ)^(1+σ) := Real.rpow_nonneg hmnn _
    linarith
  · have hanti : AntitoneOn (fun x : ℝ => x^σ) (Set.Icc ((1:ℕ):ℝ) ((m:ℕ):ℝ)) := by
      intro x hx y hy hxy
      have hx0 : 0 < x := lt_of_lt_of_le one_pos (by simpa using hx.1)
      exact Real.rpow_le_rpow_of_nonpos hx0 hxy hσ
    have hint := hanti.sum_le_integral_Ico hm
    have hIco : Finset.Ico 2 (m+1) = Finset.Icc 2 m := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    have h2 : (∑ i ∈ Finset.Ico 1 m, (((i+1:ℕ)):ℝ)^σ) = ∑ k ∈ Finset.Icc 2 m, ((k:ℝ))^σ := by
      rw [Finset.sum_Ico_add' (f := fun x : ℕ => ((x:ℝ))^σ) (a := 1) (b := m) (c := 1), hIco]
    have h1 : (∑ k ∈ Finset.Icc 1 m, ((k:ℝ))^σ) = (1:ℝ) + ∑ k ∈ Finset.Icc 2 m, ((k:ℝ))^σ := by
      have hset : Finset.Icc 1 m = insert 1 (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]
      simp [Real.one_rpow]
    rw [h1, ← h2]
    have hσp : 0 < 1 + σ := by linarith
    have hint2 : (∫ x in (1:ℝ)..(m:ℝ), x^σ) ≤ (m:ℝ)^(1+σ)/(1+σ) := by
      rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < σ))]
      rw [show ((1:ℝ))^(σ+1) = 1 by rw [Real.one_rpow], add_comm σ 1]
      rw [sub_div]
      have : (0:ℝ) ≤ 1/(1+σ) := div_nonneg zero_le_one (le_of_lt hσp)
      linarith
    have hb : (m:ℝ)^(1+σ)/(1+σ) ≤ 2 * (m:ℝ)^(1+σ) := by
      rw [div_le_iff₀ hσp]
      nlinarith [hσ1, Real.rpow_nonneg hmnn (1+σ)]
    have hone : (1:ℝ) ≤ (m:ℝ)^(1+σ) := Real.one_le_rpow hmR (by linarith)
    have h0 : (0:ℝ) ≤ (m:ℝ)^(1+σ) := Real.rpow_nonneg hmnn _
    have hA : ∑ i ∈ Finset.Ico 1 m, (((i+1:ℕ)):ℝ)^σ ≤ 2 * (m:ℝ)^(1+σ) := by
      refine le_trans hint ?_
      simpa using le_trans hint2 hb
    linarith [hA, hone, h0]

/-! ## 2. `4^{ω(d)} ≤ τ(d)^2` -/

lemma pow4_omega_le_card_divisors_sq (d : ℕ) (hd : 1 ≤ d) :
    (4:ℝ) ^ (d.primeFactors.card) ≤ ((d.divisors.card : ℕ) : ℝ)^2 := by
  have h1 : (4:ℝ) ^ (d.primeFactors.card) = ((2:ℝ) ^ (d.primeFactors.card))^2 := by
    rw [show (4:ℝ) = 2*2 by norm_num, mul_pow]; ring
  rw [h1]
  apply pow_le_pow_left₀ (by positivity)
  have h := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
    (d := d) (by omega : 0 < d)
  exact_mod_cast h

/-! ## 3. The weighted divisor-sum bound -/

lemma sum_pow4_omega_mul_rpow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ) (σ : ℝ), 1 ≤ X → -(1 : ℝ)/2 ≤ σ → σ ≤ 1/4 →
      (∑ n ∈ Finset.Icc 1 X, (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ)
        ≤ C * (X:ℝ)^(1+σ) * (Real.log ((X:ℝ)+2))^(100:ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := sum_rpow_Icc_le'
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 2
  refine ⟨max (6 * C1 * C2) 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro X σ hX hσ1 hσ2
  set L : ℝ := Real.log ((X:ℝ)+2) with hL
  have hL1 : (1:ℝ) ≤ L := by
    rw [hL]
    have hx : (3:ℝ) ≤ (X:ℝ)+2 := by
      have h1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
      linarith
    have hl3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_three]
    exact le_trans hl3 (Real.log_le_log (by norm_num) hx)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  -- pointwise bound
  have hpt : ∀ n ∈ Finset.Icc 1 X,
      (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ
      ≤ 6 * L * ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    have hpow := pow4_omega_le_small_divisor_sum n hn1
    have hc := card_primeFactors_add_one_le n X hn1 hnX
    have hnσnn : 0 ≤ (n:ℝ)^σ := Real.rpow_nonneg (by positivity) _
    have hAnn : 0 ≤ ∑ d ∈ n.divisors.filter (fun d => d*d ≤ n), (4:ℝ)^(d.primeFactors.card) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hsub : ∑ d ∈ n.divisors.filter (fun d => d*d ≤ n), (4:ℝ)^(d.primeFactors.card)
        ≤ ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)
    have h2L : 2 * ((n.primeFactors.card : ℝ) + 1) ≤ 6 * L := by linarith
    have hBsum : (∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card)) * (n:ℝ)^σ
        = ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ := by
      rw [Finset.sum_mul]
    rw [← hBsum]
    calc (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ
        ≤ (2 * ((n.primeFactors.card : ℝ) + 1)
              * ∑ d ∈ n.divisors.filter (fun d => d*d ≤ n), (4:ℝ)^(d.primeFactors.card))
            * (n:ℝ)^σ := by
          apply mul_le_mul_of_nonneg_right hpow hnσnn
      _ ≤ (6 * L * ∑ d ∈ n.divisors.filter (fun d => d*d ≤ n), (4:ℝ)^(d.primeFactors.card))
            * (n:ℝ)^σ := by
          apply mul_le_mul_of_nonneg_right _ hnσnn
          exact mul_le_mul_of_nonneg_right h2L hAnn
      _ ≤ (6 * L * ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card)) * (n:ℝ)^σ := by
          apply mul_le_mul_of_nonneg_right _ hnσnn
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = 6 * L * ((∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card)) * (n:ℝ)^σ) := by ring
  -- swap
  have hswap : (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
      = ∑ d ∈ Finset.Icc 1 X,
          ∑ n ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
            (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ := by
    have h := Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred (N := X)
      (fun _ : ℕ => True) (fun n d => (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
    simpa only [Finset.filter_true] using h
  -- inner bound
  have hinner : ∀ d ∈ Finset.Icc 1 X,
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
          (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
        ≤ (4:ℝ)^(d.primeFactors.card) * (C1 * (X:ℝ)^(1+σ) / (d:ℝ)) := by
    intro d hd
    obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := hd1
    have hdRpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
    have hm1 : 1 ≤ X / d := Nat.one_le_div_iff hdpos |>.mpr hdX
    have hre := Commons.NumberTheory.Divisors.sum_filter_dvd_reindex (N := X) hdpos
      (fun n => (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
    have hpow : (∑ m ∈ Finset.Icc 1 (X/d), (((d*m : ℕ)):ℝ)^σ)
        = (d:ℝ)^σ * ∑ m ∈ Finset.Icc 1 (X/d), ((m:ℝ))^σ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    have hbnd : (∑ m ∈ Finset.Icc 1 (X/d), ((m:ℝ))^σ) ≤ C1 * (((X/d : ℕ)):ℝ)^(1+σ) :=
      hC1 (X/d) σ hm1 hσ1 hσ2
    have hbnd2 : (((X/d : ℕ)):ℝ)^(1+σ) ≤ ((X:ℝ)/(d:ℝ))^(1+σ) :=
      Real.rpow_le_rpow (by positivity) Nat.cast_div_le (by linarith)
    have hXz : (d:ℝ)^σ * ((X:ℝ)/(d:ℝ))^(1+σ) = (X:ℝ)^(1+σ)/(d:ℝ) := by
      rw [Real.div_rpow (by positivity) (le_of_lt hdRpos)]
      rw [show (d:ℝ)^σ * ((X:ℝ)^(1+σ)/(d:ℝ)^(1+σ))
            = (X:ℝ)^(1+σ) * ((d:ℝ)^σ/(d:ℝ)^(1+σ)) by ring]
      rw [← Real.rpow_sub hdRpos, show σ - (1+σ) = -1 by ring, Real.rpow_neg_one]
      ring
    calc (∑ n ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
          (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
        = (4:ℝ)^(d.primeFactors.card) * (∑ m ∈ Finset.Icc 1 (X/d), (((d*m : ℕ)):ℝ)^σ) := by
          rw [hre, ← Finset.mul_sum]
      _ = (4:ℝ)^(d.primeFactors.card) * ((d:ℝ)^σ * ∑ m ∈ Finset.Icc 1 (X/d), ((m:ℝ))^σ) := by
          rw [hpow]
      _ ≤ (4:ℝ)^(d.primeFactors.card) * ((d:ℝ)^σ * (C1 * (((X/d : ℕ)):ℝ)^(1+σ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ ≤ (4:ℝ)^(d.primeFactors.card) * ((d:ℝ)^σ * (C1 * ((X:ℝ)/(d:ℝ))^(1+σ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hbnd2 hC1pos.le
      _ = (4:ℝ)^(d.primeFactors.card) * (C1 * (X:ℝ)^(1+σ)/(d:ℝ)) := by
          have h2 : (4:ℝ)^(d.primeFactors.card) * ((d:ℝ)^σ * (C1 * ((X:ℝ)/(d:ℝ))^(1+σ)))
              = (4:ℝ)^(d.primeFactors.card) * (C1 * ((d:ℝ)^σ * ((X:ℝ)/(d:ℝ))^(1+σ))) := by ring
          rw [h2, hXz]; ring
  -- core
  have hcore : (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
      ≤ C1 * C2 * (X:ℝ)^(1+σ) * L^4 := by
    rw [hswap]
    have hsum_div : (∑ d ∈ Finset.Icc 1 X, (4:ℝ)^(d.primeFactors.card) / (d:ℝ))
        ≤ C2 * L^4 := by
      have h1 : (∑ d ∈ Finset.Icc 1 X, (4:ℝ)^(d.primeFactors.card) / (d:ℝ))
          ≤ ∑ d ∈ Finset.Icc 1 X, (((d.divisors.card : ℕ)):ℝ)^2 / (d:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact div_le_div_of_nonneg_right (pow4_omega_le_card_divisors_sq d (Finset.mem_Icc.mp hd).1)
          (by positivity)
      have h2 := hC2 X hX
      have h3 : (Real.log ((X:ℝ)+2))^(2^2) = L^4 := by
        rw [hL]; norm_num
      calc (∑ d ∈ Finset.Icc 1 X, (4:ℝ)^(d.primeFactors.card) / (d:ℝ))
          ≤ ∑ d ∈ Finset.Icc 1 X, (((d.divisors.card : ℕ)):ℝ)^2 / (d:ℝ) := h1
        _ ≤ C2 * (Real.log ((X:ℝ)+2))^(2^2) := h2
        _ = C2 * L^4 := by rw [h3]
    calc (∑ d ∈ Finset.Icc 1 X,
            ∑ n ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
              (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ)
        ≤ ∑ d ∈ Finset.Icc 1 X, (4:ℝ)^(d.primeFactors.card) * (C1 * (X:ℝ)^(1+σ) / (d:ℝ)) :=
          Finset.sum_le_sum hinner
      _ = C1 * (X:ℝ)^(1+σ) * ∑ d ∈ Finset.Icc 1 X, (4:ℝ)^(d.primeFactors.card) / (d:ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd; ring
      _ ≤ C1 * (X:ℝ)^(1+σ) * (C2 * L^4) :=
          mul_le_mul_of_nonneg_left hsum_div (by positivity)
      _ = C1 * C2 * (X:ℝ)^(1+σ) * L^4 := by ring
  -- assemble
  have hstepA : (∑ n ∈ Finset.Icc 1 X, (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ)
      ≤ 6 * L * ∑ n ∈ Finset.Icc 1 X,
          ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ := by
    calc (∑ n ∈ Finset.Icc 1 X, (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ)
        ≤ ∑ n ∈ Finset.Icc 1 X,
            6 * L * ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ :=
          Finset.sum_le_sum hpt
      _ = 6 * L * ∑ n ∈ Finset.Icc 1 X,
            ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ := by
          rw [Finset.mul_sum]
  have hne : (X:ℝ)^(1+σ) ≥ 0 := Real.rpow_nonneg (by positivity) _
  have hLnn : (0:ℝ) ≤ L := hL0
  have hfin : 6 * L * (C1 * C2 * (X:ℝ)^(1+σ) * L^4)
      ≤ max (6 * C1 * C2) 1 * (X:ℝ)^(1+σ) * L^100 := by
    have hL5100 : L^5 ≤ L^100 := pow_le_pow_right₀ hL1 (by norm_num)
    have hcoef : 6 * C1 * C2 ≤ max (6 * C1 * C2) 1 := le_max_left _ _
    have hmaxnn : (0:ℝ) ≤ max (6 * C1 * C2) 1 := le_trans zero_le_one (le_max_right _ _)
    have hL5nn : (0:ℝ) ≤ L^5 := pow_nonneg hLnn 5
    have heq : 6 * L * (C1 * C2 * (X:ℝ)^(1+σ) * L^4)
        = (6 * C1 * C2) * (X:ℝ)^(1+σ) * L^5 := by ring
    rw [heq]
    calc (6 * C1 * C2) * (X:ℝ)^(1+σ) * L^5
        ≤ (max (6 * C1 * C2) 1) * (X:ℝ)^(1+σ) * L^5 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hne) hL5nn
      _ ≤ (max (6 * C1 * C2) 1) * (X:ℝ)^(1+σ) * L^100 :=
          mul_le_mul_of_nonneg_left hL5100 (mul_nonneg hmaxnn hne)
  calc (∑ n ∈ Finset.Icc 1 X, (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ)
      ≤ 6 * L * ∑ n ∈ Finset.Icc 1 X,
          ∑ d ∈ n.divisors, (4:ℝ)^(d.primeFactors.card) * (n:ℝ)^σ := hstepA
    _ ≤ 6 * L * (C1 * C2 * (X:ℝ)^(1+σ) * L^4) := by
        apply mul_le_mul_of_nonneg_left hcore; positivity
    _ ≤ max (6 * C1 * C2) 1 * (X:ℝ)^(1+σ) * L^100 := hfin

theorem primAnn_rpow_weight :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (σ : ℝ), 1 ≤ N → -(1 : ℝ) / 2 ≤ σ → σ ≤ 1 / 4 →
      (∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * ((((Work.FIPlan.gnorm z).divisors.card : ℕ)) : ℝ)
            * (Work.FIPlan.gnorm z : ℝ) ^ σ)
        ≤ C * (N : ℝ) ^ (1 + σ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by
  obtain ⟨C3, hC3pos, hC3⟩ := sum_pow4_omega_mul_rpow_le
  refine ⟨16 * C3, by positivity, ?_⟩
  intro N σ hN hσ1 hσ2
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hX : 1 ≤ 2 * N := by omega
  have hmaps : ∀ z ∈ primAnn (2 * N), Work.FIPlan.gnorm z ∈ Finset.Icc 1 (2 * N) := by
    intro z hz
    rw [mem_primAnn_iff] at hz
    exact Finset.mem_Icc.mpr ⟨hz.2.1, hz.2.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun z => |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        * (Work.FIPlan.gnorm z : ℝ) ^ σ)]
  have hstep : ∀ n ∈ Finset.Icc 1 (2 * N),
      (∑ z ∈ (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n),
        |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
          * (Work.FIPlan.gnorm z : ℝ) ^ σ)
        ≤ 4 * ((4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hconst : ∀ z ∈ (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n),
        |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
          * (Work.FIPlan.gnorm z : ℝ) ^ σ
        = |(ArithmeticFunction.moebius n : ℝ)|
          * (((n.divisors.card : ℕ)) : ℝ) * (n:ℝ)^σ := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rw [hz.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard := fiber_card_primAnn_le (N := N) (n := n) hn1 hn2
    have hcardR : (((primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ)
        ≤ 4 * (((n.divisors.card : ℕ)) : ℝ) := by exact_mod_cast hcard
    have hA0 : 0 ≤ |(ArithmeticFunction.moebius n : ℝ)|
        * (((n.divisors.card : ℕ)) : ℝ) * (n:ℝ)^σ := by positivity
    have hmusq := abs_moebius_mul_card_sq_le n
    have hnσnn : 0 ≤ (n:ℝ)^σ := Real.rpow_nonneg (by positivity) _
    calc (((primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ)
          * (|(ArithmeticFunction.moebius n : ℝ)|
              * (((n.divisors.card : ℕ)) : ℝ) * (n:ℝ)^σ)
        ≤ (4 * (((n.divisors.card : ℕ)) : ℝ))
            * (|(ArithmeticFunction.moebius n : ℝ)|
              * (((n.divisors.card : ℕ)) : ℝ) * (n:ℝ)^σ) :=
          mul_le_mul_of_nonneg_right hcardR hA0
      _ = 4 * (|(ArithmeticFunction.moebius n : ℝ)|
              * (((n.divisors.card : ℕ)) : ℝ) * (((n.divisors.card : ℕ)) : ℝ)) * (n:ℝ)^σ := by ring
      _ ≤ 4 * ((4:ℝ)^(n.primeFactors.card)) * (n:ℝ)^σ := by
          apply mul_le_mul_of_nonneg_right _ hnσnn
          apply mul_le_mul_of_nonneg_left hmusq (by norm_num)
      _ = 4 * ((4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ) := by ring
  have h2pow : (2:ℝ)^(1+σ) ≤ 4 := by
    have h1 : (2:ℝ)^(1+σ) = 2 * (2:ℝ)^σ := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
    rw [h1]
    have h2 : (2:ℝ)^σ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : σ ≤ 1)
      simpa [Real.rpow_one] using this
    linarith
  have hcast : (((2*N : ℕ)):ℝ) = 2 * (N:ℝ) := by push_cast; ring
  calc (∑ n ∈ Finset.Icc 1 (2 * N),
          ∑ z ∈ (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n),
            |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * (Work.FIPlan.gnorm z : ℝ) ^ σ)
      ≤ ∑ n ∈ Finset.Icc 1 (2 * N), 4 * ((4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ) :=
        Finset.sum_le_sum hstep
    _ = 4 * ∑ n ∈ Finset.Icc 1 (2 * N), (4:ℝ)^(n.primeFactors.card) * (n:ℝ)^σ := by
        rw [Finset.mul_sum]
    _ ≤ 4 * (C3 * (((2*N : ℕ)):ℝ)^(1+σ) * (Real.log ((((2*N : ℕ)):ℝ)+2))^100) :=
        mul_le_mul_of_nonneg_left (hC3 (2 * N) σ hX hσ1 hσ2) (by norm_num)
    _ = 4 * C3 * ((2:ℝ)^(1+σ) * (N:ℝ)^(1+σ)) * (Real.log (2*(N:ℝ)+2))^100 := by
        rw [hcast, Real.mul_rpow (by norm_num) (by positivity)]
        ring
    _ ≤ 16 * C3 * (N:ℝ)^(1+σ) * (Real.log (2*(N:ℝ)+2))^100 := by
        have hLnn : (0:ℝ) ≤ (Real.log (2*(N:ℝ)+2))^100 := by positivity
        have hNσnn : (0:ℝ) ≤ (N:ℝ)^(1+σ) := Real.rpow_nonneg (by positivity) _
        have hC3nn : (0:ℝ) ≤ C3 := le_of_lt hC3pos
        calc 4 * C3 * ((2:ℝ)^(1+σ) * (N:ℝ)^(1+σ)) * (Real.log (2*(N:ℝ)+2))^100
            ≤ 4 * C3 * (4 * (N:ℝ)^(1+σ)) * (Real.log (2*(N:ℝ)+2))^100 := by
              apply mul_le_mul_of_nonneg_right _ hLnn
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right h2pow hNσnn
          _ = 16 * C3 * (N:ℝ)^(1+σ) * (Real.log (2*(N:ℝ)+2))^100 := by ring

end

end Work.FITop4.Red5
