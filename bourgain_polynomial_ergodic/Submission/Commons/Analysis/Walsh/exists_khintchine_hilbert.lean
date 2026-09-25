import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.Moment.rpow_ave_mono
import Submission.Commons.Analysis.Walsh.rademacher_parseval_inner
import Submission.Commons.Analysis.Walsh.rademacher_hilbert_even_moment

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Walsh

open Finset

universe u

private lemma card_bool_fun (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

private lemma smul_one_neg_one (b : Bool) {H : Type*} [SMul ℂ H] (y : H) :
    (if b then (1 : ℂ) else -1) • y = ((if b then (1 : ℝ) else -1) : ℂ) • y := by
  cases b <;> norm_num

private lemma parseval' (n : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : Fin n → H) :
    (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2:ℕ))
      = 2 ^ n * ∑ i : Fin n, ‖x i‖ ^ (2:ℕ) := by
  rw [← rademacher_parseval_inner n x]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => smul_one_neg_one (e i) (x i))]

private lemma holder_two_third {ι : Type*} (s : Finset ι) (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) :
    (∑ i ∈ s, Y i ^ 2) ≤ (∑ i ∈ s, Y i) ^ ((2:ℝ)/3) * (∑ i ∈ s, Y i ^ 4) ^ ((1:ℝ)/3) := by
  have hpq : Real.HolderConjugate ((3:ℝ)/2) 3 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf : ∀ i ∈ s, 0 ≤ Y i ^ ((2:ℝ)/3) := fun i _ => Real.rpow_nonneg (hY i) _
  have hg : ∀ i ∈ s, 0 ≤ Y i ^ ((4:ℝ)/3) := fun i _ => Real.rpow_nonneg (hY i) _
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun i => Y i ^ ((2:ℝ)/3)) (g := fun i => Y i ^ ((4:ℝ)/3)) hpq hf hg
  have hL : (∑ i ∈ s, Y i ^ ((2:ℝ)/3) * Y i ^ ((4:ℝ)/3)) = ∑ i ∈ s, Y i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.rpow_add_of_nonneg (hY i) (by norm_num) (by norm_num),
      show (2:ℝ)/3 + 4/3 = 2 by norm_num,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hR1 : ∀ i, (Y i ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2) = Y i := by
    intro i
    rw [← Real.rpow_mul (hY i), show (2:ℝ)/3 * (3/2) = 1 by norm_num, Real.rpow_one]
  have hR2 : ∀ i, (Y i ^ ((4:ℝ)/3)) ^ (3:ℝ) = Y i ^ 4 := by
    intro i
    rw [← Real.rpow_mul (hY i), show (4:ℝ)/3 * 3 = 4 by norm_num,
      show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hL] at h
  rw [Finset.sum_congr rfl (fun i _ => hR1 i), Finset.sum_congr rfl (fun i _ => hR2 i)] at h
  rw [show (1:ℝ)/((3:ℝ)/2) = 2/3 by norm_num] at h
  exact h

private lemma lower_of_moments {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) {K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (h2 : ∑ i, Y i ^ 2 = (Fintype.card ι : ℝ) * B)
    (h4 : ∑ i, Y i ^ 4 ≤ (2*K)^2 * B^2 * (Fintype.card ι : ℝ)) :
    (1/(2*K)) * B ^ ((1:ℝ)/2) ≤ (∑ i, Y i) / (Fintype.card ι : ℝ) := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  set A : ℝ := ∑ i, Y i with hA
  set S : ℝ := ∑ i, Y i ^ 2 with hS
  set P4 : ℝ := ∑ i, Y i ^ 4 with hP4
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hι
  have hAnn : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg fun i _ => hY i
  have hSnn : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun i _ => by positivity
  have hP4nn : 0 ≤ P4 := by rw [hP4]; exact Finset.sum_nonneg fun i _ => by positivity
  have hhold : S ≤ A ^ ((2:ℝ)/3) * P4 ^ ((1:ℝ)/3) := by
    have h := holder_two_third (Finset.univ : Finset ι) Y hY
    simpa [hA, hS, hP4] using h
  have hcube : S ^ 3 ≤ A ^ 2 * P4 := by
    have h3 : S ^ (3:ℕ) ≤ (A ^ ((2:ℝ)/3) * P4 ^ ((1:ℝ)/3)) ^ (3:ℕ) :=
      pow_le_pow_left₀ hSnn hhold 3
    refine h3.trans (le_of_eq ?_)
    have e1 : (A ^ ((2:ℝ)/3)) ^ (3:ℕ) = A ^ (2:ℕ) := by
      rw [← Real.rpow_natCast (A ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul hAnn,
        ← Real.rpow_natCast A 2]
      congr 1
      norm_num
    have e2 : (P4 ^ ((1:ℝ)/3)) ^ (3:ℕ) = P4 := by
      rw [← Real.rpow_natCast (P4 ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hP4nn]
      rw [show (1:ℝ)/3 * ((3:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
    rw [mul_pow, e1, e2]
  have hcomb : (N * B) ^ 3 ≤ A ^ 2 * ((2*K) ^ 2 * B ^ 2 * N) := by
    have hc : S ^ 3 ≤ A ^ 2 * ((2*K) ^ 2 * B ^ 2 * N) :=
      hcube.trans (mul_le_mul_of_nonneg_left h4 (pow_nonneg hAnn 2))
    rwa [h2] at hc
  rcases eq_or_lt_of_le hB with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0), mul_zero]
    exact div_nonneg hAnn hNpos.le
  · have hAg : N * Real.sqrt B / (2 * K) ≤ A := by
      have hsq : (N * Real.sqrt B / (2 * K)) ^ 2 ≤ A ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hB]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (2*K)^2)]
        have hfac : 0 < B ^ 2 * N := by positivity
        have hkey : N ^ 2 * B * (B ^ 2 * N) ≤ A ^ 2 * (2 * K) ^ 2 * (B ^ 2 * N) := by
          have hc := hcomb
          rw [mul_pow, mul_pow] at hc
          nlinarith [hc]
        exact le_of_mul_le_mul_right hkey hfac
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hAnn] at this
    have hfinal : Real.sqrt B / (2 * K) ≤ A / N := by
      have h1 : N * Real.sqrt B / (2 * K) / N = Real.sqrt B / (2 * K) := by
        field_simp
      have h2 := (div_le_div_iff_of_pos_right hNpos).mpr hAg
      rwa [h1] at h2
    calc (1 / (2 * K)) * B ^ ((1:ℝ)/2) = Real.sqrt B / (2*K) := by
          rw [Real.sqrt_eq_rpow]; ring
      _ ≤ A / N := hfinal

private lemma lower_lp_of_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι)
    (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) {K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (h2 : ∑ i, Y i ^ 2 = (Fintype.card ι : ℝ) * B)
    (h4 : ∑ i, Y i ^ 4 ≤ (2*K)^2 * B^2 * (Fintype.card ι : ℝ))
    (p : ℝ) (hp : 1 ≤ p) :
    (1/(2*K)) * B ^ ((1:ℝ)/2) ≤ ((∑ i, Y i ^ p) / (Fintype.card ι : ℝ)) ^ (1/p) := by
  have h1 := lower_of_moments hι Y hY hK hB h2 h4
  have hmono := Commons.Analysis.Moment.rpow_ave_mono hι Y hY (q := (1:ℝ)) (p := p)
    (by norm_num) hp
  have hmono' : ((∑ i, Y i) / (Fintype.card ι : ℝ))
      ≤ ((∑ i, Y i ^ p) / (Fintype.card ι : ℝ)) ^ (1/p) := by
    rw [show (1:ℝ)/1 = 1 by norm_num, Real.rpow_one] at hmono
    simpa only [Real.rpow_one] using hmono
  exact h1.trans hmono'

private lemma upper_of_even {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 0 < Fintype.card ι)
    (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) {K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (heven : ∀ m : ℕ, 1 ≤ m →
      (∑ i, Y i ^ (2*m)) / (Fintype.card ι : ℝ) ≤ (K*m)^m * B^m) :
    ∀ p : ℝ, 1 ≤ p → ((∑ i, Y i ^ p) / (Fintype.card ι : ℝ)) ^ (1/p)
      ≤ (Real.sqrt (2*K) + 1) * p ^ ((1:ℝ)/2) * B ^ ((1:ℝ)/2) := by
  intro p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set m : ℕ := ⌈p⌉₊ with hm
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hι
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr hp0)
  have hpm : p ≤ (m:ℝ) := by rw [hm]; exact Nat.le_ceil p
  have hm2p : (m:ℝ) ≤ 2*p := by
    rw [hm]
    have h := Nat.ceil_lt_add_one (le_of_lt hp0)
    linarith
  have hqpos : (0:ℝ) < ((2*m : ℕ) : ℝ) := by positivity
  have hpq : p ≤ ((2*m : ℕ) : ℝ) := by
    have hcast : ((2*m : ℕ) : ℝ) = 2*(m:ℝ) := by push_cast; ring
    rw [hcast]; linarith
  have hmono := Commons.Analysis.Moment.rpow_ave_mono hι Y hY
    (q := p) (p := ((2*m : ℕ) : ℝ)) hp0 hpq
  rw [← hN] at hmono
  have hev := heven m hm1
  have hsum_eq : (∑ i, Y i ^ (((2*m : ℕ)) : ℝ)) = ∑ i, Y i ^ (2*m) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.rpow_natCast]
  have hstep : ((∑ i, Y i ^ (((2*m : ℕ)) : ℝ)) / N) ^ (1/(((2*m : ℕ)) : ℝ))
      ≤ ((K*m)^m * B^m) ^ (1/(((2*m : ℕ)) : ℝ)) := by
    apply Real.rpow_le_rpow
    · exact div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hY i) _) hNpos.le
    · rw [hsum_eq]
      exact hev
    · positivity
  have hmul : (K*m)^m * B^m = (K*m*B)^m := by rw [← mul_pow]
  have hsimp : (((K*m)^m * B^m) ^ (1/(((2*m : ℕ)) : ℝ)))
      = Real.sqrt (K*m) * Real.sqrt B := by
    have hW : (0:ℝ) ≤ K*m*B := by positivity
    rw [hmul]
    calc ((K*m*B)^m) ^ (1/(((2*m : ℕ)) : ℝ))
        = ((K*m*B) ^ ((m:ℕ):ℝ)) ^ (1/(((2*m : ℕ)) : ℝ)) := by
            rw [← Real.rpow_natCast (K*m*B) m]
      _ = (K*m*B) ^ (((m:ℕ):ℝ) * (1/(((2*m : ℕ)) : ℝ))) := by
            rw [← Real.rpow_mul hW]
      _ = (K*m*B) ^ ((1:ℝ)/2) := by
            congr 1
            rw [show (((2*m : ℕ)) : ℝ) = 2*(m:ℝ) by push_cast; ring]
            field_simp
      _ = (K*m) ^ ((1:ℝ)/2) * B ^ ((1:ℝ)/2) := Real.mul_rpow (by positivity) hB
      _ = Real.sqrt (K*m) * Real.sqrt B := by rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (K*m) ≤ Real.sqrt (2*K) * Real.sqrt p := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*K)]
    apply Real.sqrt_le_sqrt
    nlinarith [hm2p]
  have hBnn : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  calc ((∑ i, Y i ^ p) / N) ^ (1/p)
      ≤ ((∑ i, Y i ^ (((2*m : ℕ)) : ℝ)) / N) ^ (1/(((2*m : ℕ)) : ℝ)) := hmono
    _ ≤ ((K*m)^m * B^m) ^ (1/(((2*m : ℕ)) : ℝ)) := hstep
    _ = Real.sqrt (K*m) * Real.sqrt B := hsimp
    _ ≤ (Real.sqrt (2*K) * Real.sqrt p) * Real.sqrt B :=
        mul_le_mul_of_nonneg_right hsqrt hBnn
    _ ≤ (Real.sqrt (2*K) + 1) * p ^ ((1:ℝ)/2) * B ^ ((1:ℝ)/2) := by
        rw [Real.sqrt_eq_rpow p, Real.sqrt_eq_rpow B, Real.sqrt_eq_rpow (2*K)]
        have hp1 : (0:ℝ) ≤ p ^ ((1:ℝ)/2) := Real.rpow_nonneg hp0.le _
        have hB1 : (0:ℝ) ≤ B ^ ((1:ℝ)/2) := Real.rpow_nonneg hB _
        nlinarith [hp1, hB1, Real.sqrt_nonneg (2*K), mul_nonneg hp1 hB1]

private theorem main_of_even
    (hevenAll : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 1 ≤ m → ∀ {H : Type u} [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] (n : ℕ) (x : Fin n → H),
      (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 * m))
        / (2 : ℝ) ^ n ≤ (K * m) ^ m * (∑ i : Fin n, ‖x i‖ ^ 2) ^ m)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (x : Fin n → H),
        c * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ ((∑ e : Fin n → Bool,
                ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ p) / (2 : ℝ) ^ n) ^
              ((1 : ℝ) / p)
          ∧ ((∑ e : Fin n → Bool,
                ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ p) / (2 : ℝ) ^ n) ^
              ((1 : ℝ) / p)
            ≤ C * p ^ ((1 : ℝ) / 2) * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hKpos, hKeven⟩ := hevenAll
  refine ⟨1/(2*K), Real.sqrt (2*K) + 1, by positivity, by positivity, ?_⟩
  intro H _ _ n x
  have hcard : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) = (2:ℝ)^n := by
    rw [card_bool_fun]; push_cast; ring
  have hι : 0 < Fintype.card (Fin n → Bool) := by rw [card_bool_fun]; positivity
  refine ⟨?_, ?_⟩
  · have h2 : (∑ e : Fin n → Bool,
        (‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖) ^ 2)
        = (Fintype.card (Fin n → Bool) : ℝ) * (∑ i : Fin n, ‖x i‖ ^ 2) := by
      rw [hcard]; exact parseval' n x
    have h4 : (∑ e : Fin n → Bool,
        (‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖) ^ 4)
        ≤ (2*K)^2 * (∑ i : Fin n, ‖x i‖ ^ 2)^2 * (Fintype.card (Fin n → Bool) : ℝ) := by
      have h := hKeven 2 (by norm_num) (H := H) n x
      rw [← hcard] at h
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (Fintype.card (Fin n → Bool) : ℝ))] at h
      calc (∑ e : Fin n → Bool, (‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖) ^ 4)
          ≤ (K * 2) ^ 2 * (∑ i : Fin n, ‖x i‖ ^ 2) ^ 2 * (Fintype.card (Fin n → Bool) : ℝ) := h
        _ = (2 * K) ^ 2 * (∑ i : Fin n, ‖x i‖ ^ 2) ^ 2 * (Fintype.card (Fin n → Bool) : ℝ) := by
              ring
    rw [← hcard]
    exact lower_lp_of_moments hι _ (fun e => norm_nonneg _) hKpos (by positivity) h2 h4 p hp
  · have hev : ∀ m : ℕ, 1 ≤ m →
        (∑ e : Fin n → Bool,
            (‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖) ^ (2*m))
          / (Fintype.card (Fin n → Bool) : ℝ)
          ≤ (K*m)^m * (∑ i : Fin n, ‖x i‖ ^ 2)^m := by
      intro m hm
      have h := hKeven m hm (H := H) n x
      rw [← hcard] at h
      exact h
    rw [← hcard]
    exact upper_of_even hι _ (fun e => norm_nonneg _) hKpos (by positivity) hev p hp

/-- **Khintchine's inequality for Hilbert-space-valued Rademacher sums, in both directions.**

For every `p ≥ 1` there are constants `c = c p > 0` and `C = C p > 0` such that for every Hilbert
space `H` (over `ℂ`), every `n` and every `x : Fin n → H`,

`c (∑ᵢ ‖xᵢ‖²)^{1/2} ≤ ( 2^{-n} ∑_{ε} ‖∑ᵢ εᵢ xᵢ‖^p )^{1/p}
    ≤ C p^{1/2} (∑ᵢ ‖xᵢ‖²)^{1/2}`,

where the middle average runs over all `2^n` sign choices `ε ∈ {±1}^n`. -/
theorem exists_khintchine_hilbert (p : ℝ) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (x : Fin n → H),
        c * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ ((∑ e : Fin n → Bool,
                ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ p) / (2 : ℝ) ^ n) ^
              ((1 : ℝ) / p)
          ∧ ((∑ e : Fin n → Bool,
                ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ p) / (2 : ℝ) ^ n) ^
              ((1 : ℝ) / p)
            ≤ C * p ^ ((1 : ℝ) / 2) * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hKpos, hKeven⟩ := rademacher_hilbert_even_moment
  exact main_of_even ⟨K, hKpos, hKeven⟩ p hp

end Commons.Analysis.Walsh