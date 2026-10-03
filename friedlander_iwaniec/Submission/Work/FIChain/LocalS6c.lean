import Mathlib
import Submission.Work.FIChain.LocalS6b
import Submission.Commons.Data.Nat.squarefree_prod_primes
import Submission.Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree
import Submission.Commons.Data.Nat.mul_div_gcd_eq_lcm
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors

namespace Submission.ASP

open Finset

noncomputable section

private lemma dyadic_block_le (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (k Y : ℕ) :
    ∑ p ∈ ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p = k),
        Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ 2 * Real.log 4 * (2 : ℝ) ^ (-(k : ℝ) * ε) := by
  classical
  set S : Finset ℕ := ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p = k) with hS
  have hmem : ∀ p ∈ S, Nat.Prime p ∧ Nat.log 2 p = k ∧ 1 ≤ p ∧ p ≤ Y := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨hp.1.2, hp.2, hp.1.1.1, hp.1.1.2⟩
  have hpoint : ∀ p ∈ S, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ (2 : ℝ) ^ (-(k : ℝ) * (1 + ε)) * Real.log (p : ℝ) := by
    intro p hp
    obtain ⟨hpp, hpk, hp1, hpY⟩ := hmem p hp
    have hp0 : p ≠ 0 := hpp.ne_zero
    have h2k : 2 ^ k ≤ p := by rw [← hpk]; exact Nat.pow_log_le_self 2 hp0
    have hbase : ((2 : ℝ) ^ k) ≤ (p : ℝ) := by exact_mod_cast h2k
    have hposp : 0 < (p : ℝ) := by
      have h2p : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hposb : 0 < ((2 : ℝ) ^ k) := by positivity
    have h1 : ((2 : ℝ) ^ k) ^ (1 + ε) ≤ (p : ℝ) ^ (1 + ε) :=
      Real.rpow_le_rpow (by positivity) hbase (by linarith)
    have h2 : (p : ℝ) ^ (-(1 + ε)) ≤ ((2 : ℝ) ^ k) ^ (-(1 + ε)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hposp _) (Real.rpow_pos_of_pos hposb _)).mpr h1
    have hbase' : ((2 : ℝ) ^ k) ^ (-(1 + ε)) = (2 : ℝ) ^ (-(k : ℝ) * (1 + ε)) := by
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [hbase'] at h2
    exact le_trans (mul_le_mul_of_nonneg_left h2 (Real.log_nonneg (by exact_mod_cast hpp.one_le)))
      (le_of_eq (by ring))
  have hsumlog : ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log 4 * (2 : ℝ) ^ (k + 1) := by
    have hsub : S ⊆ (Finset.Icc 1 (2 ^ (k + 1))).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpp, hpk, hp1, hpY⟩ := hmem p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      have hp0 : p ≠ 0 := hpp.ne_zero
      have hlt : p < 2 ^ (Nat.log 2 p).succ := Nat.lt_pow_succ_log_self (by norm_num) p
      rw [hpk] at hlt
      exact ⟨⟨hp1, le_of_lt hlt⟩, hpp⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => by
        have hp2 : Nat.Prime p := (Finset.mem_filter.mp hp).2
        exact Real.log_nonneg (by exact_mod_cast hp2.one_le : (1:ℝ) ≤ (p:ℝ)))
    refine le_trans hle ?_
    have hset : (Finset.Icc 0 (2 ^ (k+1))).filter Nat.Prime
        = (Finset.Icc 1 (2 ^ (k+1))).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h0, hN⟩, hp⟩; exact ⟨⟨hp.one_le, hN⟩, hp⟩
      · rintro ⟨⟨h1, hN⟩, hp⟩; exact ⟨⟨by omega, hN⟩, hp⟩
    have hth : Chebyshev.theta (((2 ^ (k+1) : ℕ) : ℝ)) =
        ∑ p ∈ (Finset.Icc 1 (2 ^ (k+1))).filter Nat.Prime, Real.log (p : ℝ) := by
      rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, hset]
    rw [← hth]
    have hb := Chebyshev.theta_le_log4_mul_x (show (0:ℝ) ≤ ((2 ^ (k+1) : ℕ) : ℝ) by positivity)
    calc Chebyshev.theta ((2 ^ (k+1) : ℕ) : ℝ) ≤ Real.log 4 * ((2 ^ (k+1) : ℕ) : ℝ) := hb
      _ = Real.log 4 * (2 : ℝ) ^ (k + 1) := by push_cast; ring
  calc ∑ p ∈ S, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ ∑ p ∈ S, (2 : ℝ) ^ (-(k : ℝ) * (1 + ε)) * Real.log (p : ℝ) := Finset.sum_le_sum hpoint
    _ = (2 : ℝ) ^ (-(k : ℝ) * (1 + ε)) * ∑ p ∈ S, Real.log (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (-(k : ℝ) * (1 + ε)) * (Real.log 4 * (2 : ℝ) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left hsumlog (by positivity)
    _ = 2 * Real.log 4 * (2 : ℝ) ^ (-(k : ℝ) * ε) := by
        have hk : (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ k = 1 := by
          rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_add (by norm_num)]
          simp
        rw [show (2:ℝ) ^ (-(k:ℝ)*(1+ε)) = (2:ℝ)^(-(k:ℝ)) * (2:ℝ)^(-(k:ℝ)*ε) by
              rw [← Real.rpow_add (by norm_num)]; congr 1; ring,
            show (2:ℝ) ^ (k+1) = (2:ℝ)^k * 2 by rw [pow_succ]]
        have hstep : (2:ℝ)^(-(k:ℝ)) * (2:ℝ)^(-(k:ℝ)*ε) * (Real.log 4 * ((2:ℝ)^k * 2))
            = ((2:ℝ)^(-(k:ℝ)) * (2:ℝ)^k) * (2 * Real.log 4 * (2:ℝ)^(-(k:ℝ)*ε)) := by ring
        rw [hstep, hk, one_mul]

private lemma partial_sum_le (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (Y K : ℕ) :
    ∑ p ∈ ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p < K),
        Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ 2 * Real.log 4 * ∑ k ∈ Finset.range K, (2 : ℝ) ^ (-(k : ℝ) * ε) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hset : ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p < K + 1)
        = ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p < K)
          ∪ ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p = K) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro p _
      omega
    have hdisj : Disjoint (((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p < K))
        (((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p = K)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      omega
    rw [hset, Finset.sum_union hdisj, Finset.sum_range_succ]
    have hb := dyadic_block_le ε hε0 hε1 K Y
    linarith [ih, hb]

theorem sum_primes_log_mul_rpow_le (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (Y : ℕ) :
    ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ 4 * Real.log 4 / (ε * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  set K := Nat.log 2 Y + 1 with hK
  have hsub : ((Finset.Icc 1 Y).filter Nat.Prime) ⊆
      ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p < K) := by
    intro p hp
    have hpY : p ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    rw [Finset.mem_filter]
    refine ⟨hp, ?_⟩
    have h1 : Nat.log 2 p ≤ Nat.log 2 Y := Nat.log_mono_right hpY
    omega
  have h1 : ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ ∑ p ∈ ((Finset.Icc 1 Y).filter Nat.Prime).filter (fun p => Nat.log 2 p < K),
          Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp2 : Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp2.one_le : (1:ℝ) ≤ (p:ℝ))) (by positivity)
  refine le_trans h1 (le_trans (partial_sum_le ε hε0 hε1 Y K) ?_)
  have hden : ε * Real.log 2 / 2 ≤ 1 - (2 : ℝ) ^ (-ε) := by
    have hexp : 1 + ε * Real.log 2 ≤ Real.exp (ε * Real.log 2) := by
      have := Real.add_one_le_exp (ε * Real.log 2); linarith
    have hrw : (2 : ℝ) ^ (-ε) = (Real.exp (ε * Real.log 2))⁻¹ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
        show Real.log 2 * -ε = -(ε * Real.log 2) by ring, Real.exp_neg]
    rw [hrw]
    have hx1 : ε * Real.log 2 ≤ 1 := by
      have h := mul_le_mul hε1 hlog2le (by positivity : (0:ℝ) ≤ Real.log 2) (by norm_num : (0:ℝ) ≤ 1)
      simpa using h
    have h3 : (Real.exp (ε * Real.log 2))⁻¹ ≤ (1 + ε * Real.log 2)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hexp
    have h5 : (ε * Real.log 2) / 2 ≤ (ε * Real.log 2) * (1 + ε * Real.log 2)⁻¹ := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ ε * Real.log 2)
      rw [inv_le_inv₀ (by norm_num : (0:ℝ) < 2) (by positivity)]
      linarith
    have h6 : (1 + ε * Real.log 2)⁻¹ = 1 - (ε * Real.log 2) * (1 + ε * Real.log 2)⁻¹ := by
      field_simp; ring
    linarith [h3, h5, h6.le, h6.ge]
  have hprod : ∑ k ∈ Finset.range K, (2 : ℝ) ^ (-(k : ℝ) * ε) ≤ 2 / (ε * Real.log 2) := by
    have hne : (2 : ℝ) ^ (-ε) ≠ 1 := by
      intro h
      have := hden
      rw [h] at this; simp at this
      nlinarith [hε0, hlog2]
    have hrw2 : ∑ k ∈ Finset.range K, (2 : ℝ) ^ (-(k : ℝ) * ε)
        = ∑ k ∈ Finset.range K, ((2 : ℝ) ^ (-ε)) ^ k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Real.rpow_natCast ((2:ℝ)^(-ε)) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [hrw2, geom_sum_eq hne]
    rw [show ((2:ℝ)^(-ε))^K - 1 = -(1 - ((2:ℝ)^(-ε))^K) by ring,
      show (2:ℝ)^(-ε) - 1 = -(1 - (2:ℝ)^(-ε)) by ring, neg_div_neg_eq]
    have hposden : (0:ℝ) < 1 - (2:ℝ)^(-ε) := by
      have := hden; nlinarith [hε0, hlog2]
    rw [div_le_iff₀ hposden]
    have hpow : ((2 : ℝ) ^ (-ε)) ^ K = (2 : ℝ) ^ (-(K : ℝ) * ε) := by
      rw [← Real.rpow_natCast ((2:ℝ)^(-ε)) K, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]; ring_nf
    rw [hpow]
    have hle1 : (2 : ℝ) ^ (-(K : ℝ) * ε) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : 0 ≤ (K:ℝ) * ε := by positivity
      linarith
    have hKden : 0 < ε * Real.log 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hKden]
    have hle1' : 1 - (2:ℝ)^(-(K:ℝ)*ε) ≤ 1 := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-(K:ℝ)*ε)
      linarith [hle1]
    have hstep : (1 - (2:ℝ)^(-(K:ℝ)*ε)) * (ε * Real.log 2) ≤ 1 * (ε * Real.log 2) :=
      mul_le_mul_of_nonneg_right hle1' (by positivity)
    have hstep2 : 2 * (ε * Real.log 2 / 2) ≤ 2 * (1 - (2:ℝ)^(-ε)) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)
    linarith [hstep, hstep2]
  have h4 : 2 * Real.log 4 * ∑ k ∈ Finset.range K, (2 : ℝ) ^ (-(k : ℝ) * ε) ≤ 4 * Real.log 4 / (ε * Real.log 2) := by
    have h := mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ) ≤ 2 * Real.log 4)
    calc 2 * Real.log 4 * ∑ k ∈ Finset.range K, (2 : ℝ) ^ (-(k : ℝ) * ε)
        ≤ 2 * Real.log 4 * (2 / (ε * Real.log 2)) := h
      _ = 4 * Real.log 4 / (ε * Real.log 2) := by ring
  linarith [h4]

theorem sum_primes_rpow_tail_le (ε : ℝ) (Δ Y : ℕ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hΔ : 2 ≤ Δ) :
    (∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p : ℝ) ^ (-(1 + ε)))
      ≤ 32 / (ε * Real.log (Δ : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 < Real.log (Δ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Δ))
  have hsub : (Finset.Icc Δ Y).filter Nat.Prime ⊆ (Finset.Icc 1 Y).filter Nat.Prime := by
    intro p hp
    have hp1 : Δ ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hp2 : p ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hp2⟩, hpp⟩
  have hpoint : ∀ p ∈ (Finset.Icc Δ Y).filter Nat.Prime,
      (p : ℝ) ^ (-(1 + ε)) ≤ Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε)) / Real.log (Δ : ℝ) := by
    intro p hp
    have hDp : Δ ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpD : (Δ:ℝ) ≤ (p:ℝ) := by exact_mod_cast hDp
    have hlogp : Real.log (Δ:ℝ) ≤ Real.log (p:ℝ) := Real.log_le_log (by positivity) hpD
    have hnn : 0 ≤ (p:ℝ)^(-(1+ε)) := by positivity
    rw [le_div_iff₀ hlogD]
    nlinarith [mul_le_mul_of_nonneg_right hlogp hnn]
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  rw [← Finset.sum_div]
  have h4 : ∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + ε))
      ≤ 4 * Real.log 4 / (ε * Real.log 2) := by
    refine le_trans ?_ (sum_primes_log_mul_rpow_le ε hε0 hε1 Y)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp1 : (1:ℝ) ≤ (p:ℝ))) (by positivity)
  refine le_trans (div_le_div_of_nonneg_right h4 hlogD.le) ?_
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
  rw [hlog4]
  have heq : 4 * (2 * Real.log 2) / (ε * Real.log 2) / Real.log (Δ:ℝ)
      = 8 / (ε * Real.log (Δ:ℝ)) := by
    field_simp
    ring
  rw [heq]
  have hd : 0 < ε * Real.log (Δ:ℝ) := by positivity
  exact div_le_div_of_nonneg_right (by norm_num : (8:ℝ) ≤ 32) hd.le

/-! ## Part 2: the finite Euler product -/

/-- Multiplicativity of a multiplicative function over a set of distinct primes. -/
lemma mul_of_prod_primes {f : ℕ → ℝ} (hf1 : f 1 = 1)
    (hfmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    f (∏ p ∈ s, p) = ∏ p ∈ s, f p := by
  have hsf : Squarefree (∏ p ∈ s, p) := Commons.Data.Nat.squarefree_prod_primes hs
  rw [Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors f hfmul hf1 hsf,
    Nat.primeFactors_prod hs]

/-- For squarefree `ν` and any `d`, `ν / gcd ν d` is coprime to `d`. -/
lemma coprime_div_gcd_of_squarefree {ν d : ℕ} (hν : Squarefree ν) :
    Nat.Coprime (ν / Nat.gcd ν d) d := by
  set c := ν / Nat.gcd ν d with hcdef
  have hg : Nat.gcd ν d ∣ ν := Nat.gcd_dvd_left ν d
  have hcν : c ∣ ν := Nat.div_dvd_of_dvd hg
  have hνeq : Nat.gcd ν d * c = ν := Nat.mul_div_cancel' hg
  have hc : Nat.gcd c (Nat.gcd ν d) = 1 := by
    have h1 : Nat.gcd c (Nat.gcd ν d) ∣ c := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd c (Nat.gcd ν d) ∣ Nat.gcd ν d := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd c (Nat.gcd ν d) * Nat.gcd c (Nat.gcd ν d) ∣ ν := by
      refine dvd_trans (Nat.mul_dvd_mul h1 h2) ?_
      rw [mul_comm, hνeq]
    exact Nat.isUnit_iff.mp (hν _ h3)
  have h1 : Nat.gcd c d ∣ Nat.gcd c (Nat.gcd ν d) :=
    Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      (Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) hcν) (Nat.gcd_dvd_right _ _))
  rw [hc] at h1
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h1)

/-- The gcd of a squarefree `ν` with a product of distinct primes is the product of the
common primes. -/
lemma gcd_prod_eq {ν : ℕ} (hνsf : Squarefree ν) {S t : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (ht : t ⊆ S) :
    Nat.gcd ν (∏ p ∈ t, p) = ∏ p ∈ t.filter (fun p => p ∣ ν), p := by
  classical
  have hdne : (∏ p ∈ t, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p (ht hp)).ne_zero)
  have hνne : ν ≠ 0 := by
    rintro rfl
    exact absurd (hνsf 0 (by simp)) (by simp)
  have hgcdne : Nat.gcd ν (∏ p ∈ t, p) ≠ 0 := by
    intro h; exact hνne (Nat.gcd_eq_zero_iff.mp h).1
  have hgcdsf : Squarefree (Nat.gcd ν (∏ p ∈ t, p)) :=
    fun x hx => hνsf x (dvd_trans hx (Nat.gcd_dvd_left _ _))
  have hset : t.filter (fun p => p ∣ ν) = (Nat.gcd ν (∏ p ∈ t, p)).primeFactors := by
    ext q
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hqt, hqν⟩
      exact ⟨hS q (ht hqt), Nat.dvd_gcd hqν (Finset.dvd_prod_of_mem (fun p => p) hqt), hgcdne⟩
    · rintro ⟨hqp, hqg, -⟩
      have hqν : q ∣ ν := dvd_trans hqg (Nat.gcd_dvd_left _ _)
      have hqd : q ∣ ∏ p ∈ t, p := dvd_trans hqg (Nat.gcd_dvd_right _ _)
      have : q ∈ (∏ p ∈ t, p).primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, hdne⟩
      rw [Nat.primeFactors_prod (fun p hp => hS p (ht hp))] at this
      exact ⟨this, hqν⟩
  rw [hset, Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree _ hgcdne hgcdsf]

/-- **The finite Euler product of §6**: summing `W d · g(ν/(ν,d))` over the squarefree divisors
of a product of distinct primes factors into the local terms `W p + g p` (for `p ∣ ν`) and
`W p + 1` (for `p ∤ ν`). -/
theorem sum_divisors_lcm_factor {g W : ℕ → ℝ} (hg1 : g 1 = 1)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hW1 : W 1 = 1) (hWmul : ∀ m n : ℕ, Nat.Coprime m n → W (m * n) = W m * W n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (ν : ℕ) (hνsf : Squarefree ν)
    (hνS : ∀ p, Nat.Prime p → p ∣ ν → p ∈ S) :
    ∑ d ∈ (∏ p ∈ S, p).divisors, W d * g (ν / Nat.gcd ν d)
      = ∏ p ∈ S, (W p + if p ∣ ν then g p else 1) := by
  classical
  have hνne : ν ≠ 0 := by
    rintro rfl
    exact absurd (hνsf 0 (by simp)) (by simp)
  set P := ∏ p ∈ S, p with hP
  have hPne : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  rw [Finset.prod_add (fun p => W p) (fun p => if p ∣ ν then g p else 1) S]
  symm
  refine Finset.sum_bij (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Nat.mem_divisors]
    refine ⟨?_, hPne⟩
    have hts : t ⊆ S := Finset.mem_powerset.mp ht
    rw [hP, ← Finset.prod_sdiff hts]
    exact Dvd.intro _ (by rw [mul_comm])
  · intro t₁ h₁ t₂ h₂ heq
    have h1s : t₁ ⊆ S := Finset.mem_powerset.mp h₁
    have h2s : t₂ ⊆ S := Finset.mem_powerset.mp h₂
    have e1 : (∏ p ∈ t₁, p).primeFactors = t₁ := Nat.primeFactors_prod (fun p hp => hS p (h1s hp))
    have e2 : (∏ p ∈ t₂, p).primeFactors = t₂ := Nat.primeFactors_prod (fun p hp => hS p (h2s hp))
    rw [← e1, ← e2, heq]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdiv, -⟩ := hd
    have hdsf : Squarefree d :=
      fun x hx => Commons.Data.Nat.squarefree_prod_primes hS x (dvd_trans hx hdiv)
    have hdne : d ≠ 0 := by
      intro h
      rw [h] at hdiv
      exact hPne (Nat.eq_zero_of_zero_dvd hdiv)
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      have : p ∈ (∏ p ∈ S, p).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp'.1, dvd_trans hp'.2.1 hdiv, hPne⟩
      rwa [Nat.primeFactors_prod hS] at this
    · exact Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree d hdne hdsf
  · intro t ht
    have hts : t ⊆ S := Finset.mem_powerset.mp ht
    have hW : ∏ p ∈ t, W p = W (∏ p ∈ t, p) :=
      (mul_of_prod_primes hW1 hWmul (fun p hp => hS p (hts hp))).symm
    have hgcdeq : Nat.gcd ν (∏ p ∈ t, p) = ∏ p ∈ t.filter (fun p => p ∣ ν), p :=
      gcd_prod_eq hνsf hS hts
    have hSeq : S.filter (fun p => p ∣ ν) = ν.primeFactors := by
      ext q
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hqS, hqν⟩
        exact Nat.mem_primeFactors.mpr ⟨hS q hqS, hqν, hνne⟩
      · intro hq
        have hq' := Nat.mem_primeFactors.mp hq
        exact ⟨hνS q hq'.1 hq'.2.1, hq'.2.1⟩
    have hνeq : ν = ∏ p ∈ S.filter (fun p => p ∣ ν), p := by
      rw [hSeq]
      exact (Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree ν hνne hνsf).symm
    have hdisj : Disjoint (t.filter (fun p => p ∣ ν)) ((S \ t).filter (fun p => p ∣ ν)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp2).1).2 (Finset.mem_filter.mp hp1).1
    have hunion : t.filter (fun p => p ∣ ν) ∪ (S \ t).filter (fun p => p ∣ ν)
        = S.filter (fun p => p ∣ ν) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨hts h1, h2⟩
        · exact ⟨h1, h3⟩
      · rintro ⟨hpS, hpν⟩
        by_cases hp : p ∈ t
        · exact Or.inl ⟨hp, hpν⟩
        · exact Or.inr ⟨⟨hpS, hp⟩, hpν⟩
    have hkey : Nat.gcd ν (∏ p ∈ t, p) * (∏ p ∈ (S \ t).filter (fun p => p ∣ ν), p) = ν := by
      rw [hgcdeq, ← Finset.prod_union hdisj, hunion, ← hνeq]
    have hgne : Nat.gcd ν (∏ p ∈ t, p) ≠ 0 := by
      intro h; exact hνne (Nat.gcd_eq_zero_iff.mp h).1
    have hdiv : ν / Nat.gcd ν (∏ p ∈ t, p) = ∏ p ∈ (S \ t).filter (fun p => p ∣ ν), p :=
      (Nat.eq_div_of_mul_eq_right hgne hkey).symm
    have hfilter : ∏ p ∈ S \ t, (if p ∣ ν then g p else 1)
        = ∏ p ∈ (S \ t).filter (fun p => p ∣ ν), g p := by
      rw [Finset.prod_filter]
    have hgprod : ∏ p ∈ (S \ t).filter (fun p => p ∣ ν), g p
        = g (∏ p ∈ (S \ t).filter (fun p => p ∣ ν), p) :=
      (mul_of_prod_primes hg1 hgmul
        (fun p hp => hS p ((Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1))).symm
    rw [hW, hfilter, hgprod, hdiv]

/-- The `h(ν)` of §6 of the companion paper: `h(ν) = ∏_{p ∣ ν} (1 + p^{-ε})/(1 + g(p)p^{-ε})`. -/
def hSieve (g : ℕ → ℝ) (ε : ℝ) (ν : ℕ) : ℝ :=
  ∏ p ∈ ν.primeFactors, (1 + (p : ℝ) ^ (-ε)) / (1 + (p : ℝ) ^ (-ε) * g p)

lemma hSieve_one (g : ℕ → ℝ) (ε : ℝ) : hSieve g ε 1 = 1 := by
  simp [hSieve]

lemma hSieve_prime (g : ℕ → ℝ) (ε : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    hSieve g ε p = (1 + (p : ℝ) ^ (-ε)) / (1 + (p : ℝ) ^ (-ε) * g p) := by
  rw [hSieve, hp.primeFactors, Finset.prod_singleton]

lemma hSieve_nonneg {g : ℕ → ℝ} (hgnn : ∀ n, 0 ≤ g n) (ε : ℝ) (ν : ℕ) :
    0 ≤ hSieve g ε ν := by
  rw [hSieve]
  apply Finset.prod_nonneg
  intro p hp
  apply div_nonneg _ (by
    have : 0 ≤ (p:ℝ)^(-ε) * g p := mul_nonneg (Real.rpow_nonneg (by positivity) _) (hgnn p)
    linarith)
  have : 0 ≤ (p:ℝ)^(-ε) := Real.rpow_nonneg (by positivity) _
  linarith

/-- The product identity of §6: the local factors recombine as `∏(1+W p)·g(ν)·h(ν)`. -/
lemma prod_W_add_eq {g : ℕ → ℝ} (hg1 : g 1 = 1)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hgnn : ∀ n, 0 ≤ g n) (ε : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) {ν : ℕ} (hνsf : Squarefree ν)
    (hνS : ∀ p, Nat.Prime p → p ∣ ν → p ∈ S) :
    ∏ p ∈ S, ((p : ℝ) ^ (-ε) * g p + if p ∣ ν then g p else 1)
      = (∏ p ∈ S, (1 + (p : ℝ) ^ (-ε) * g p)) * (g ν * hSieve g ε ν) := by
  classical
  have hνne : ν ≠ 0 := by
    rintro rfl
    exact absurd (hνsf 0 (by simp)) (by simp)
  set T := ν.primeFactors with hT
  have hTS : T ⊆ S := fun p hp =>
    hνS p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hgν : g ν = ∏ p ∈ T, g p :=
    Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors g hgmul hg1 hνsf
  have hkey1 : ∀ p ∈ S \ T, ((p : ℝ) ^ (-ε) * g p + (if p ∣ ν then g p else 1))
      = (1 + (p : ℝ) ^ (-ε) * g p) := by
    intro p hp
    have hpnT : p ∉ T := (Finset.mem_sdiff.mp hp).2
    have hnpd : ¬ p ∣ ν := fun h =>
      hpnT (Nat.mem_primeFactors.mpr ⟨hS p (Finset.mem_sdiff.mp hp).1, h, hνne⟩)
    rw [if_neg hnpd]; ring
  have hkey2 : ∀ p ∈ T, ((p : ℝ) ^ (-ε) * g p + (if p ∣ ν then g p else 1))
      = g p * (1 + (p : ℝ) ^ (-ε)) := by
    intro p hp
    have hpd : p ∣ ν := Nat.dvd_of_mem_primeFactors hp
    simp only [hpd, if_true]
    ring
  have hne : ∀ p ∈ T, (1 + (p : ℝ) ^ (-ε) * g p) ≠ 0 := by
    intro p hp
    have h1 : 0 ≤ (p:ℝ)^(-ε) * g p :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (hgnn p)
    linarith
  have hBC : (∏ p ∈ T, (1 + (p : ℝ) ^ (-ε) * g p))
        * (∏ p ∈ T, (1 + (p : ℝ) ^ (-ε)) / (1 + (p : ℝ) ^ (-ε) * g p))
      = ∏ p ∈ T, (1 + (p : ℝ) ^ (-ε)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [mul_div_cancel₀ _ (hne p hp)]
  calc ∏ p ∈ S, ((p : ℝ) ^ (-ε) * g p + if p ∣ ν then g p else 1)
      = (∏ p ∈ S \ T, ((p : ℝ) ^ (-ε) * g p + if p ∣ ν then g p else 1))
        * ∏ p ∈ T, ((p : ℝ) ^ (-ε) * g p + if p ∣ ν then g p else 1) :=
        (Finset.prod_sdiff hTS).symm
    _ = (∏ p ∈ S \ T, (1 + (p : ℝ) ^ (-ε) * g p))
        * (∏ p ∈ T, g p * (1 + (p : ℝ) ^ (-ε))) := by
        rw [Finset.prod_congr rfl hkey1, Finset.prod_congr rfl hkey2]
    _ = (∏ p ∈ S \ T, (1 + (p : ℝ) ^ (-ε) * g p))
        * ((∏ p ∈ T, g p) * ∏ p ∈ T, (1 + (p : ℝ) ^ (-ε))) := by
        rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ S \ T, (1 + (p : ℝ) ^ (-ε) * g p)) * (g ν * ∏ p ∈ T, (1 + (p : ℝ) ^ (-ε))) := by
        rw [hgν]
    _ = (∏ p ∈ S, (1 + (p : ℝ) ^ (-ε) * g p)) * (g ν * hSieve g ε ν) := by
        rw [hSieve, hT, ← Finset.prod_sdiff hTS, ← hBC]
        ring

/-! ## Part 4: (6.5) — the estimate `M(x) ≪ (log Δ)^{-1}` -/

/-- **§6, (6.5)**: for a density `g` with (1.8) (`0 ≤ g(p) < 1`, `g(p) ≪ 1/p`), a Selberg-type
weight `lam` supported on squarefree numbers `≤ Δ` satisfying the sieve positivity and the
upper-bound-sieve axiom, the main term
`M(x) = ∑_{d ≤ δ₂, ♭} ∑_{ν ≤ Δ} λ_ν g([d,ν])`
of (6.3) satisfies `M(x) ≪ (log Δ)^{-1}` (with the Rankin factor `δ₂^ε` kept explicit). -/
theorem M6_le (g lam : ℕ → ℝ) {δ2 Δ Y : ℕ} {ε C_sieve C₁ C₀ : ℝ}
    (hΔ : 3 ≤ Δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεΔ : ε * Real.log (Δ:ℝ) = 1)
    (hY1 : δ2 ≤ Y) (hY2 : Δ ≤ Y)
    (hg1 : g 1 = 1) (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hgnn : ∀ n, 0 ≤ g n)
    (hC₀ : 0 < C₀) (hgpC : ∀ p : ℕ, Nat.Prime p → g p ≤ C₀ / (p:ℝ))
    (hC₁ : 0 < C₁) (hCs : 0 ≤ C_sieve)
    (hprodsub : ∀ Δ' : ℕ, 3 ≤ Δ' → ∏ p ∈ Nat.primesBelow Δ', (1 - g p) ≤ C₁ / Real.log (Δ':ℝ))
    (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0)
    (hpos : ∀ d, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))
    (hsieve : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * (g ν * hSieve g ε ν)
        ≤ C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p)) :
    M6 g lam δ2 Δ
      ≤ (δ2:ℝ)^ε * C_sieve * Real.exp (32 * C₀) * C₁ / Real.log (Δ:ℝ) := by
  classical
  have hlogD : 0 < Real.log (Δ:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Δ))
  have hΔ2 : 2 ≤ Δ := by omega
  set S : Finset ℕ := Nat.primesLE Y with hSdef
  have hS : ∀ p ∈ S, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp hp).2
  set P : ℕ := ∏ p ∈ S, p with hPdef
  have hPne : P ≠ 0 := by
    rw [hPdef]; exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  set W : ℕ → ℝ := fun n => (n:ℝ)^(-ε) * g n with hWdef
  have hW1 : W 1 = 1 := by rw [hWdef]; simp [hg1]
  have hWmul : ∀ m n : ℕ, Nat.Coprime m n → W (m * n) = W m * W n := by
    intro m n hmn
    simp only [hWdef]
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), hgmul m n hmn]
    ring
  have hWnn : ∀ n, 0 ≤ W n := fun n =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (hgnn n)
  have hSnonneg : 0 ≤ ∏ p ∈ S, (1 + W p) :=
    Finset.prod_nonneg (fun p _ => by have := hWnn p; linarith)
  -- ### Step A: open up `M6`
  have hA : M6 g lam δ2 Δ
      = ∑ d ∈ (Finset.Icc 1 δ2).filter Squarefree,
          g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)) := by
    rw [M6]
    apply Finset.sum_congr rfl
    intro d hd
    have hdsf : Squarefree d := (Finset.mem_filter.mp hd).2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν hν
    by_cases hνsf : Squarefree ν
    · have hlcm : Nat.lcm ν d = d * (ν / Nat.gcd ν d) := by
        rw [Nat.lcm_comm, Nat.gcd_comm, Commons.Data.Nat.mul_div_gcd_eq_lcm]
      have hcop : Nat.Coprime d (ν / Nat.gcd ν d) :=
        (coprime_div_gcd_of_squarefree hνsf).symm
      rw [hlcm, hgmul d (ν / Nat.gcd ν d) hcop]
      ring
    · rw [hlam_sq ν hνsf]; ring
  -- ### Step B: Rankin (introduce `(δ₂/d)^ε ≥ 1`)
  have hB : ∀ d ∈ (Finset.Icc 1 δ2).filter Squarefree,
      g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))
        ≤ (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) := by
    intro d hd
    have hd2 : d ≤ δ2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    have hPnn : 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d) := hpos d
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hbase : 1 ≤ (δ2:ℝ) / (d:ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < d))]
      simpa using (show (d:ℝ) ≤ (δ2:ℝ) by exact_mod_cast hd2)
    have hrpow : 1 ≤ ((δ2:ℝ)/(d:ℝ))^ε := Real.one_le_rpow hbase hε0.le
    have hdeq : (δ2:ℝ)^ε * (d:ℝ)^(-ε) = ((δ2:ℝ)/(d:ℝ))^ε := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
      ring
    have hprod : 1 ≤ (δ2:ℝ)^ε * (d:ℝ)^(-ε) := hdeq ▸ hrpow
    have h2 : g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))
        ≤ ((δ2:ℝ)^ε * (d:ℝ)^(-ε))
          * (g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) :=
      le_mul_of_one_le_left (mul_nonneg (hgnn d) hPnn) hprod
    rw [hWdef]
    calc g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))
        ≤ ((δ2:ℝ)^ε * (d:ℝ)^(-ε))
          * (g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) := h2
      _ = (δ2:ℝ)^ε * (((d:ℝ)^(-ε) * g d)
          * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) := by ring
  -- ### Step C: extend the `d`-sum from `d ≤ δ₂` to all squarefree divisors of `P`
  have hsub : (Finset.Icc 1 δ2).filter Squarefree ⊆ P.divisors := by
    intro d hd
    have hdsf : Squarefree d := (Finset.mem_filter.mp hd).2
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hdY : d ≤ Y := le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2 hY1
    have hne : d ≠ 0 := by omega
    rw [Nat.mem_divisors]
    refine ⟨?_, hPne⟩
    rw [hPdef, ← Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree d hne hdsf]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    rw [Nat.mem_primesLE]
    exact ⟨le_trans (Nat.le_of_mem_primeFactors hp) hdY, Nat.prime_of_mem_primeFactors hp⟩
  have hCnn : ∀ d ∈ P.divisors, d ∉ (Finset.Icc 1 δ2).filter Squarefree →
      0 ≤ (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) := by
    intro d _ _
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (mul_nonneg (hWnn d) (hpos d))
  have hC : ∑ d ∈ (Finset.Icc 1 δ2).filter Squarefree,
        (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)))
      ≤ ∑ d ∈ P.divisors,
        (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hCnn
  -- ### Step D: swap the two sums
  have hD : ∑ d ∈ P.divisors,
        (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)))
      = (δ2:ℝ)^ε * ∑ ν ∈ Finset.Icc 1 Δ,
          lam ν * (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d)) := by
    have step1 : ∑ d ∈ P.divisors,
          (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)))
        = (δ2:ℝ)^ε * ∑ d ∈ P.divisors, ∑ ν ∈ Finset.Icc 1 Δ,
            W d * (lam ν * g (ν / Nat.gcd ν d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    have step2 : (∑ d ∈ P.divisors, ∑ ν ∈ Finset.Icc 1 Δ,
            W d * (lam ν * g (ν / Nat.gcd ν d)))
        = ∑ ν ∈ Finset.Icc 1 Δ, ∑ d ∈ P.divisors,
            W d * (lam ν * g (ν / Nat.gcd ν d)) := Finset.sum_comm
    have step3 : ∀ ν ∈ Finset.Icc 1 Δ,
        (∑ d ∈ P.divisors, W d * (lam ν * g (ν / Nat.gcd ν d)))
          = lam ν * (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d)) := by
      intro ν _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    rw [step1, step2, Finset.sum_congr rfl step3, Finset.mul_sum]
  -- ### Step E/F: the finite Euler product and the local factorisation
  have hEF : ∀ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
      (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d))
        = (∏ p ∈ S, (1 + W p)) * (g ν * hSieve g ε ν) := by
    intro ν hν
    have hνsf : Squarefree ν := (Finset.mem_filter.mp hν).2
    have hνle : ν ≤ Δ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).2
    have hνne : ν ≠ 0 := by
      rintro rfl
      exact absurd (hνsf 0 (by simp)) (by simp)
    have hνS : ∀ p, Nat.Prime p → p ∣ ν → p ∈ S := by
      intro p hp hpd
      rw [hSdef, Nat.mem_primesLE]
      exact ⟨le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hνne) hpd) (le_trans hνle hY2), hp⟩
    rw [sum_divisors_lcm_factor hg1 hgmul hW1 hWmul S hS ν hνsf hνS]
    exact prod_W_add_eq hg1 hgmul hgnn ε S hS hνsf hνS
  -- ### Step G: the sieve axiom
  have hG : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        lam ν * (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d))
      ≤ (∏ p ∈ S, (1 + W p)) * (C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p)) := by
    have h1 : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          lam ν * (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d))
        = (∏ p ∈ S, (1 + W p)) * ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            lam ν * (g ν * hSieve g ε ν) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      rw [hEF ν hν]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hsieve hSnonneg
  -- ### Step H: split the product over `S`, and cancel at the primes `p < Δ`
  have hsplit : (∏ p ∈ S, (1 + W p))
      = (∏ p ∈ Nat.primesBelow Δ, (1 + W p))
        * ∏ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (1 + W p) := by
    rw [hSdef,
      ← Finset.prod_union (show Disjoint (Nat.primesBelow Δ) ((Finset.Icc Δ Y).filter Nat.Prime) by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rw [Nat.mem_primesBelow] at hp1
        rw [Finset.mem_filter, Finset.mem_Icc] at hp2
        omega)]
    congr 1
    ext p
    rw [Nat.mem_primesLE, Finset.mem_union, Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpY, hpp⟩
      by_cases hpΔ : p < Δ
      · exact Or.inl ⟨hpΔ, hpp⟩
      · exact Or.inr ⟨⟨by omega, hpY⟩, hpp⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h2, h3⟩
  have hcancel : (∏ p ∈ Nat.primesBelow Δ, (1 + W p))
        * (∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p))
      = ∏ p ∈ Nat.primesBelow Δ, (1 - g p) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
    rw [hSieve_prime g ε hpp, hWdef]
    have hne : (1 + (p:ℝ)^(-ε) * g p) ≠ 0 := by
      have h1 : 0 ≤ (p:ℝ)^(-ε) * g p :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (hgnn p)
      linarith
    field_simp
    ring
  -- ### Step I: the two numerical bounds
  have htail : (∏ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (1 + W p)) ≤ Real.exp (32 * C₀) := by
    refine le_trans (Real.prod_one_add_le_exp_sum _ (fun p => hWnn p)) (Real.exp_le_exp.mpr ?_)
    have h1 : ∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, W p
        ≤ ∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, C₀ * (p:ℝ)^(-(1+ε)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hp0 : (0:ℝ) < (p:ℝ) := by
        have : (2:ℕ) ≤ p := hpp.two_le
        exact_mod_cast (by omega : 0 < p)
      have hgp := hgpC p hpp
      have hpow : (p:ℝ)^(-ε) * (p:ℝ)^(-(1:ℝ)) = (p:ℝ)^(-(1+ε)) := by
        rw [← Real.rpow_add hp0]; ring_nf
      have h1 : (p:ℝ)^(-(1:ℝ)) = (p:ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hp0), Real.rpow_one]
      calc W p = g p * (p:ℝ)^(-ε) := by rw [hWdef]; ring
        _ ≤ (C₀ / (p:ℝ)) * (p:ℝ)^(-ε) := mul_le_mul_of_nonneg_right hgp (by positivity)
        _ = C₀ * ((p:ℝ)^(-(1:ℝ)) * (p:ℝ)^(-ε)) := by rw [h1, div_eq_mul_inv]; ring
        _ = C₀ * ((p:ℝ)^(-ε) * (p:ℝ)^(-(1:ℝ))) := by ring
        _ = C₀ * (p:ℝ)^(-(1+ε)) := by rw [hpow]
    refine le_trans h1 ?_
    rw [← Finset.mul_sum]
    have h2 : ∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p:ℝ)^(-(1+ε)) ≤ 32 := by
      have h3 := sum_primes_rpow_tail_le ε Δ Y hε0 hε1 hΔ2
      rwa [show ε * Real.log (Δ:ℝ) = 1 by exact hεΔ, div_one] at h3
    calc C₀ * (∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p:ℝ)^(-(1+ε)))
        ≤ C₀ * 32 := mul_le_mul_of_nonneg_left h2 hC₀.le
      _ = 32 * C₀ := by ring
  have htailnn : 0 ≤ ∏ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (1 + W p) :=
    Finset.prod_nonneg (fun p _ => by have := hWnn p; linarith)
  have hprodsub' : (∏ p ∈ Nat.primesBelow Δ, (1 - g p)) ≤ C₁ / Real.log (Δ:ℝ) :=
    hprodsub Δ hΔ
  -- ### Assembly
  have hfilter_sum : ∀ T : ℕ → ℝ,
      ∑ ν ∈ Finset.Icc 1 Δ, lam ν * T ν
        = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * T ν := by
    intro T
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ν _
    by_cases h : Squarefree ν
    · rw [if_pos h]
    · rw [if_neg h, hlam_sq ν h, zero_mul]
  have hmain : M6 g lam δ2 Δ
      ≤ (δ2:ℝ)^ε * ((∏ p ∈ S, (1 + W p))
          * (C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p))) := by
    have step1 : ∑ d ∈ (Finset.Icc 1 δ2).filter Squarefree,
          g d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))
        ≤ ∑ d ∈ (Finset.Icc 1 δ2).filter Squarefree,
          (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))) :=
      Finset.sum_le_sum hB
    have step3 : ∑ d ∈ P.divisors,
          (δ2:ℝ)^ε * (W d * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)))
        = (δ2:ℝ)^ε * ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            lam ν * (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d)) := by
      rw [hD, hfilter_sum (fun ν => ∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d))]
    have step4 : (δ2:ℝ)^ε * ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            lam ν * (∑ d ∈ P.divisors, W d * g (ν / Nat.gcd ν d))
        ≤ (δ2:ℝ)^ε * ((∏ p ∈ S, (1 + W p))
            * (C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p))) :=
      mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg (by positivity) _)
    rw [hA]
    exact le_trans step1 (le_trans hC (le_trans step3.le step4))
  refine le_trans hmain ?_
  have hδnn : 0 ≤ (δ2:ℝ)^ε := Real.rpow_nonneg (by positivity) _
  calc (δ2:ℝ)^ε * ((∏ p ∈ S, (1 + W p))
        * (C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p)))
      = (δ2:ℝ)^ε * C_sieve * ((∏ p ∈ Nat.primesBelow Δ, (1 + W p))
          * (∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p)))
          * (∏ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (1 + W p)) := by
        rw [hsplit]; ring
    _ = (δ2:ℝ)^ε * C_sieve * (∏ p ∈ Nat.primesBelow Δ, (1 - g p))
          * (∏ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (1 + W p)) := by
        rw [hcancel]
    _ ≤ (δ2:ℝ)^ε * C_sieve * (C₁ / Real.log (Δ:ℝ)) * Real.exp (32 * C₀) := by
        have hA0 : 0 ≤ (δ2:ℝ)^ε * C_sieve := mul_nonneg hδnn hCs
        have hstep1 : (δ2:ℝ)^ε * C_sieve * (∏ p ∈ Nat.primesBelow Δ, (1 - g p))
            ≤ (δ2:ℝ)^ε * C_sieve * (C₁ / Real.log (Δ:ℝ)) :=
          mul_le_mul_of_nonneg_left hprodsub' hA0
        have hbnn : 0 ≤ (δ2:ℝ)^ε * C_sieve * (C₁ / Real.log (Δ:ℝ)) :=
          mul_nonneg hA0 (div_nonneg hC₁.le hlogD.le)
        exact mul_le_mul hstep1 htail htailnn hbnn
    _ = (δ2:ℝ)^ε * C_sieve * Real.exp (32 * C₀) * C₁ / Real.log (Δ:ℝ) := by ring

/-- **§6, (6.6)**, unconditional modulo the sieve axioms: combining (6.3) (`S1_le_main_rem`),
(6.4) (`L6_le`) and (6.5) (`M6_le`),
`S₁(x;y,z) ≪ A(x)(log δ)(log Δ)^{-1}`. -/
theorem S1_bound_of_sieve (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N : ℕ)
    {sy sz : ℝ} {δ2 Δ M D Y : ℕ} {ε C_sieve C₁ C₀ C₅ : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hrho : ∀ n, 0 ≤ rhoOf lam n) (hsy : 0 < sy)
    (hδ2 : ∀ b c : ℕ, sy < (b : ℝ) → sz < (c : ℝ) → N / (b * c) ≤ δ2)
    (ha_sq : ∀ n, ¬ Squarefree n → a n = 0)
    (happ : Approx a g r (N : ℝ)) (hΔN : Δ ≤ N)
    (hsupp : ∀ ν, ν ∉ Finset.Icc 1 Δ → lam ν = 0)
    (hΔsz : (Δ : ℝ) < sz)
    (hg1 : g 1 = 1)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hgnn : ∀ n, 0 ≤ g n)
    (hΔ3 : 3 ≤ Δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεΔ : ε * Real.log (Δ:ℝ) = 1)
    (hY1 : δ2 ≤ Y) (hY2 : Δ ≤ Y)
    (hC₀ : 0 < C₀) (hgpC : ∀ p : ℕ, Nat.Prime p → g p ≤ C₀ / (p:ℝ))
    (hC₁ : 0 < C₁) (hCs : 0 ≤ C_sieve)
    (hprodsub : ∀ Δ' : ℕ, 3 ≤ Δ' → ∏ p ∈ Nat.primesBelow Δ', (1 - g p) ≤ C₁ / Real.log (Δ':ℝ))
    (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0)
    (hlam1 : ∀ ν, |lam ν| ≤ 1)
    (hpos : ∀ d, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d))
    (hpos' : ∀ d, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d))
    (hMran : ∀ c ∈ cseg N sz sy, c ≤ M) (hDE : Δ * (M * δ2) ≤ D)
    (hC₅ : 0 ≤ C₅) (hL : L6 g N sz sy ≤ C₅)
    (hsieve : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * (g ν * hSieve g ε ν)
        ≤ C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieve g ε p)) :
    |S1 a lam N sy sz|
      ≤ Acount a (N : ℝ) * C₅
          * ((δ2:ℝ)^ε * C_sieve * Real.exp (32 * C₀) * C₁ / Real.log (Δ:ℝ))
        + Real.log ((M : ℝ) * (δ2 : ℝ)) * RemainderSum r D N := by
  have hlogD : 0 < Real.log (Δ:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Δ))
  have hδnn : 0 ≤ (δ2:ℝ)^ε := Real.rpow_nonneg (by positivity) _
  have hexp : 0 < Real.exp (32 * C₀) := Real.exp_pos _
  refine S1_bound a g r lam N ha hrho hsy hδ2 ha_sq happ hΔN hsupp hΔsz hgmul hgnn hpos hlam1
    hlam_sq hMran hDE hC₅ ?_ hL ?_
  · exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hδnn hCs) hexp.le) hC₁.le) hlogD.le
  · exact M6_le g lam hΔ3 hε0 hε1 hεΔ hY1 hY2 hg1 hgmul hgnn hC₀ hgpC hC₁ hCs hprodsub
      hlam_sq hpos' hsieve

end

end Submission.ASP
