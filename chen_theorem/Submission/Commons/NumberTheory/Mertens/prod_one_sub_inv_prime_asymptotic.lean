import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog

open Finset Real Filter
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

open Finset Real Filter
open scoped BigOperators Topology



private def mh (p : ℕ) : ℝ := -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)

private lemma mh_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ mh p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 - 1 / (p : ℝ) by
      have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
      linarith)
    have : 1 - 1 / (p : ℝ) - 1 = -(1 / (p : ℝ)) := by ring
    rwa [this] at h
  unfold mh
  linarith

private lemma mh_le {p : ℕ} (hp : p.Prime) : mh p ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : 0 < (p : ℝ) - 1 := by linarith
  have harg : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
  have hlog : -Real.log (1 - 1 / (p : ℝ)) = Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [harg, Real.log_div (ne_of_gt hpm1) (ne_of_gt hp0),
        Real.log_div (ne_of_gt hp0) (ne_of_gt hpm1)]
    ring
  have hle : Real.log ((p : ℝ) / ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / ((p : ℝ) - 1) by positivity)
    have : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by field_simp; ring
    rwa [this] at h
  unfold mh
  rw [hlog]
  have hkey : 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp; ring
  linarith [hle, hkey]

private def Wn (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, mh p

private lemma primesLE_mono {n m : ℕ} (h : n ≤ m) : n.primesLE ⊆ m.primesLE := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨le_trans hp.1 h, hp.2⟩

private lemma Wn_mono : Monotone Wn := by
  intro n m hnm
  unfold Wn
  exact Finset.sum_le_sum_of_subset_of_nonneg (primesLE_mono hnm)
    (fun p hp _ => mh_nonneg (Nat.mem_primesLE.mp hp).2)

/-- Telescoping: `∑_{k=a}^{b} 1/(k(k-1)) = 1/(a-1) - 1/b` for `2 ≤ a ≤ b`. -/
private lemma sum_Icc_inv_mul_pred (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc a b, 1 / ((k : ℝ) * ((k : ℝ) - 1)))
      = 1 / ((a : ℝ) - 1) - 1 / (b : ℝ) := by
  have h := Finset.sum_Icc_sub (f := fun j : ℕ => 1 / ((j : ℝ) - 1)) (m := a) (n := b) hab
  have key : (∑ k ∈ Finset.Icc a b, 1 / ((k : ℝ) * ((k : ℝ) - 1)))
      = - (∑ i ∈ Finset.Icc a b, (1 / (((i + 1 : ℕ) : ℝ) - 1) - 1 / ((i : ℝ) - 1))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk2 : 2 ≤ k := le_trans ha (Finset.mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    have hkc : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hkm1 : (k : ℝ) - 1 ≠ 0 := by linarith
    rw [hkc]
    have hsimp : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
    rw [hsimp, neg_sub, div_sub_div _ _ hkm1 hk0]
    ring
  rw [key, h]
  have hbR : (((b + 1 : ℕ) : ℝ)) = (b : ℝ) + 1 := by push_cast; ring
  rw [hbR]
  ring_nf

private lemma Wn_diff_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    Wn m - Wn n ≤ 1 / (n : ℝ) := by
  rcases lt_or_eq_of_le hnm with hlt | heq
  · have hsub : n.primesLE ⊆ m.primesLE := primesLE_mono hnm
    have hsdiff : Wn m - Wn n = ∑ p ∈ m.primesLE \ n.primesLE, mh p := by
      have := Finset.sum_sdiff (s₁ := n.primesLE) (s₂ := m.primesLE)
        (f := fun p : ℕ => mh p) hsub
      unfold Wn
      linarith
    rw [hsdiff]
    have hstep1 : (∑ p ∈ m.primesLE \ n.primesLE, mh p)
        ≤ ∑ p ∈ m.primesLE \ n.primesLE, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      exact mh_le (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
    have hsub2 : m.primesLE \ n.primesLE ⊆ Finset.Icc (n + 1) m := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpm, hpn⟩ := hp
      have hp_le : p ≤ m := (Nat.mem_primesLE.mp hpm).1
      have hpprime : p.Prime := (Nat.mem_primesLE.mp hpm).2
      have hpn' : ¬ (p ≤ n) := fun h => hpn (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
      rw [Finset.mem_Icc]
      exact ⟨by omega, hp_le⟩
    have hstep2 : (∑ p ∈ m.primesLE \ n.primesLE, 1 / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤ ∑ k ∈ Finset.Icc (n + 1) m, 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun k hk _ => ?_)
      have hk1 : (1 : ℝ) < (k : ℝ) := by
        have hk2 : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
        exact_mod_cast (by omega : 1 < k)
      have hkR : (0 : ℝ) < (k : ℝ) := by linarith
      have hkden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by
        apply mul_pos hkR; linarith
      exact le_of_lt (one_div_pos.mpr hkden)
    rw [sum_Icc_inv_mul_pred (n + 1) m (by omega) (by omega)] at hstep2
    have hsimp : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) - 1) = 1 / (n : ℝ) := by
      norm_num
    rw [hsimp] at hstep2
    have hmpos : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith [hstep1, hstep2]
  · subst heq
    simp only [sub_self]
    positivity



open Finset Real Filter
open scoped BigOperators Topology



private lemma Wn_one_eq_zero : Wn 1 = 0 := by
  unfold Wn
  apply Finset.sum_eq_zero
  intro p hp
  rw [Nat.mem_primesLE] at hp
  exact absurd hp.2.two_le (by omega)

private def W : ℝ := sSup (Set.range Wn)

private lemma Wn_bddAbove : BddAbove (Set.range Wn) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : Wn 0 = 0 := by
      unfold Wn
      apply Finset.sum_eq_zero
      intro p hp
      rw [Nat.mem_primesLE] at hp
      exact absurd hp.2.two_le (by omega)
    rw [this]; norm_num
  · have h := Wn_diff_le (n := 1) (m := n) (by norm_num) hn
    rw [Wn_one_eq_zero] at h
    linarith

private lemma Wn_le_W (n : ℕ) : Wn n ≤ W := by
  rw [W]
  exact le_csSup Wn_bddAbove ⟨n, rfl⟩

private lemma W_le_Wn_add {n : ℕ} (hn : 1 ≤ n) : W ≤ Wn n + 1 / (n : ℝ) := by
  rw [W]
  refine csSup_le ⟨Wn 0, 0, rfl⟩ ?_
  rintro y ⟨m, rfl⟩
  rcases lt_or_ge m n with hmn | hmn
  · have hm : Wn m ≤ Wn n := Wn_mono (le_of_lt hmn)
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  · have h := Wn_diff_le hn hmn
    linarith

private lemma abs_W_sub_Wn {n : ℕ} (hn : 1 ≤ n) : |W - Wn n| ≤ 1 / (n : ℝ) := by
  have h1 : Wn n ≤ W := Wn_le_W n
  have h2 : W ≤ Wn n + 1 / (n : ℝ) := W_le_Wn_add hn
  have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith





private lemma primeRecips_natCast (n : ℕ) :
    primeRecips (n : ℝ) = ∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ) := by
  unfold primeRecips
  rw [Nat.floor_natCast]

private lemma log_prod_eq (n : ℕ) :
    Real.log (∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))) = -primeRecips (n : ℝ) - Wn n := by
  have hne : ∀ p ∈ n.primesLE, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
    linarith
  rw [Real.log_prod hne, primeRecips_natCast]
  rw [show (∑ p ∈ n.primesLE, Real.log (1 - 1 / (p : ℝ)))
        = ∑ p ∈ n.primesLE, (-(1 / (p : ℝ)) - mh p) from
        Finset.sum_congr rfl (fun p _ => by unfold mh; ring)]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  unfold Wn
  ring





open Filter in
private lemma tendsto_div_log_pow_zero_real (Cp : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => Cp / (Real.log x) ^ A) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => ((Real.log x) ^ A)⁻¹) atTop (nhds 0) :=
    Tendsto.inv_tendsto_atTop ((tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop)
  have h2 := h1.const_mul Cp
  simpa [div_eq_mul_inv] using h2

open Filter in
private lemma tendsto_div_log_pow_zero_nat (Cp : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun n : ℕ => Cp / (Real.log (n : ℝ)) ^ A) atTop (nhds 0) :=
  (tendsto_div_log_pow_zero_real Cp hA).comp tendsto_natCast_atTop_atTop

open Filter in
private lemma eventually_log_pow_le_nat {A : ℝ} (_hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ A ≤ (n : ℝ) := by
  have hlit := isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) A (by norm_num)
  have hbound := hlit.bound (show (0 : ℝ) < 1 by norm_num)
  have hreal : ∀ᶠ x : ℝ in atTop, Real.log x ^ A ≤ x ^ (1 : ℝ) := by
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognn A),
        Real.norm_of_nonneg (Real.rpow_nonneg hx0.le (1 : ℝ)), one_mul] at hx
    simpa using hx
  have hnat : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ A ≤ (n : ℝ) ^ (1 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with n hn
  rwa [Real.rpow_one] at hn

open Filter in
private lemma eventually_inv_add_le_one {Cp A : ℝ} (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n : ℝ) + Cp / (Real.log (n : ℝ)) ^ A ≤ 1 := by
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn)
  have h2 : ∀ᶠ n : ℕ in atTop, Cp / (Real.log (n : ℝ)) ^ A ≤ 1 / 2 := by
    have := (tendsto_order.1 (tendsto_div_log_pow_zero_nat Cp hA)).2 (1 / 2) (by norm_num)
    filter_upwards [this] with n hn
    exact le_of_lt hn
  filter_upwards [h1, h2] with n hn1 hn2
  linarith





open Filter in
private theorem prod_mul_log_nat_powLog {M : ℝ}
    (hM : Tendsto (fun x : ℝ => primeRecips x - Real.log (Real.log x)) atTop (nhds M)) :
    ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 11 ≤ n →
      |(∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))) * Real.log (n : ℝ) - Real.exp (-M - W)| ≤
        K / (Real.log (n : ℝ)) ^ A := by
  intro A hA
  obtain ⟨L, Cp, hCp, hb⟩ := primeRecips_sub_loglog_powLog A hA
  have hL : L = M := by
    apply tendsto_nhds_unique _ hM
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero_norm' _ (tendsto_div_log_pow_zero_real Cp hA)
    filter_upwards [eventually_ge_atTop (11 : ℝ)] with x hx
    have := hb x hx
    simpa [primeRecips] using this
  rw [hL] at hb
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (eventually_log_pow_le_nat hA)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (eventually_inv_add_le_one (Cp := Cp) hA)
  set N : ℕ := max (max N1 N2) 11 with hNdef
  have hN1N : N1 ≤ N := le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 11)
  have hN2N : N2 ≤ N := le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 11)
  have hN11 : 11 ≤ N := le_max_right (max N1 N2) 11
  set C : ℝ := Real.exp (-M - W) with hCdef
  have hCpos : 0 < C := Real.exp_pos _
  refine ⟨max (2 * C * (1 + Cp)) (max ((Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A) 1),
    ?_, ?_⟩
  · have : (1 : ℝ) ≤ max (2 * C * (1 + Cp))
        (max ((Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A) 1) :=
      le_trans (le_max_right _ 1) (le_max_right _ _)
    linarith
  · intro n hn11
    have hn1 : 1 ≤ n := by omega
    have hn11R : (11 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn11
    have hn1R : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1R
    -- product facts
    set P : ℝ := ∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ)) with hPdef
    have hPpos : 0 < P := by
      rw [hPdef]
      refine Finset.prod_pos (fun p hp => ?_)
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
      linarith
    have hPle1 : P ≤ 1 := by
      rw [hPdef]
      refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hle : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
        linarith
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
    have hPnonneg : 0 ≤ P := le_of_lt hPpos
    by_cases hNn : N ≤ n
    · -- good regime
      have hN1n : N1 ≤ n := le_trans hN1N hNn
      have hN2n : N2 ≤ n := le_trans hN2N hNn
      have hlogpow_le : (Real.log (n : ℝ)) ^ A ≤ (n : ℝ) := hN1 n hN1n
      have hsmall : (1 : ℝ) / (n : ℝ) + Cp / (Real.log (n : ℝ)) ^ A ≤ 1 := hN2 n hN2n
      set E : ℝ := primeRecips (n : ℝ) - Real.log (Real.log (n : ℝ)) - M with hEdef
      have hE : |E| ≤ Cp / (Real.log (n : ℝ)) ^ A := by
        have := hb (n : ℝ) hn11R
        rw [hEdef]
        simpa [primeRecips] using this
      set t : ℝ := W - Wn n with htdef
      have ht : |t| ≤ 1 / (n : ℝ) := by rw [htdef]; exact abs_W_sub_Wn hn1
      set u : ℝ := t - E with hudef
      have hu : |u| ≤ 1 / (n : ℝ) + Cp / (Real.log (n : ℝ)) ^ A := by
        rw [hudef]
        calc |t - E| ≤ |t| + |E| := abs_sub _ _
          _ ≤ 1 / (n : ℝ) + Cp / (Real.log (n : ℝ)) ^ A := add_le_add ht hE
      have hu1 : |u| ≤ 1 := le_trans hu hsmall
      have hkey : P * Real.log (n : ℝ) = C * Real.exp u := by
        have h1 : Real.log P = -primeRecips (n : ℝ) - Wn n := by
          rw [hPdef]; exact log_prod_eq n
        have hWn : Wn n = W - t := by rw [htdef]; ring
        have hEeq : primeRecips (n : ℝ) = Real.log (Real.log (n : ℝ)) + M + E := by
          rw [hEdef]; ring
        have hsum : Real.log P + Real.log (Real.log (n : ℝ)) = -M - W + u := by
          rw [h1, hEeq, hWn, hudef]; ring
        calc P * Real.log (n : ℝ)
            = Real.exp (Real.log P) * Real.exp (Real.log (Real.log (n : ℝ))) := by
                rw [Real.exp_log hPpos, Real.exp_log hlogpos]
          _ = Real.exp (Real.log P + Real.log (Real.log (n : ℝ))) := by rw [Real.exp_add]
          _ = Real.exp (-M - W + u) := by rw [hsum]
          _ = Real.exp (-M - W) * Real.exp u := by rw [Real.exp_add]
          _ = C * Real.exp u := by rw [hCdef]
      have hexp : |Real.exp u - 1| ≤ 2 * |u| := Real.abs_exp_sub_one_le hu1
      have hinv : 1 / (n : ℝ) ≤ 1 / (Real.log (n : ℝ)) ^ A := by
        have hpos : 0 < (Real.log (n : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
        exact one_div_le_one_div_of_le hpos hlogpow_le
      have hu' : |u| ≤ (1 + Cp) / (Real.log (n : ℝ)) ^ A := by
        have : (1 : ℝ) / (n : ℝ) + Cp / (Real.log (n : ℝ)) ^ A
            ≤ 1 / (Real.log (n : ℝ)) ^ A + Cp / (Real.log (n : ℝ)) ^ A :=
          add_le_add hinv le_rfl
        have heq : 1 / (Real.log (n : ℝ)) ^ A + Cp / (Real.log (n : ℝ)) ^ A
            = (1 + Cp) / (Real.log (n : ℝ)) ^ A := by ring
        linarith [hu, this, heq.le, heq.ge]
      have hden : 0 < (Real.log (n : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
      have hfinal : |P * Real.log (n : ℝ) - C| ≤ 2 * C * (1 + Cp) / (Real.log (n : ℝ)) ^ A := by
        have hstep : |P * Real.log (n : ℝ) - C| = C * |Real.exp u - 1| := by
          rw [hkey, show C * Real.exp u - C = C * (Real.exp u - 1) by ring,
              abs_mul, abs_of_pos hCpos]
        rw [hstep]
        calc C * |Real.exp u - 1| ≤ C * (2 * |u|) := mul_le_mul_of_nonneg_left hexp hCpos.le
          _ ≤ C * (2 * ((1 + Cp) / (Real.log (n : ℝ)) ^ A)) :=
              mul_le_mul_of_nonneg_left (by linarith [hu']) hCpos.le
          _ = 2 * C * (1 + Cp) / (Real.log (n : ℝ)) ^ A := by ring
      have hKge : 2 * C * (1 + Cp) ≤ max (2 * C * (1 + Cp))
          (max ((Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A) 1) := le_max_left _ _
      calc |P * Real.log (n : ℝ) - C|
          ≤ 2 * C * (1 + Cp) / (Real.log (n : ℝ)) ^ A := hfinal
        _ ≤ max (2 * C * (1 + Cp))
              (max ((Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A) 1)
              / (Real.log (n : ℝ)) ^ A :=
            div_le_div_of_nonneg_right hKge hden.le
    · -- small regime
      have hnN : n < N := not_le.mp hNn
      have hle : n ≤ N := le_of_lt hnN
      have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hlogle : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hle)
      have hlogpow_le : (Real.log (n : ℝ)) ^ A ≤ (Real.log (N : ℝ)) ^ A :=
        Real.rpow_le_rpow hlogpos.le hlogle hA.le
      have hden : 0 < (Real.log (n : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
      have hdenN : 0 < (Real.log (N : ℝ)) ^ A := Real.rpow_pos_of_pos hlogNpos A
      have hc : |P * Real.log (n : ℝ) - C| ≤ Real.log (N : ℝ) + C := by
        have h1 : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := hlogle
        have h2 : |P * Real.log (n : ℝ) - C| ≤ P * Real.log (n : ℝ) + C := by
          have h0 : 0 ≤ P * Real.log (n : ℝ) := mul_nonneg hPnonneg hlogpos.le
          rw [abs_sub_le_iff]
          constructor <;> linarith [h0, hCpos.le]
        have h3 : P * Real.log (n : ℝ) ≤ Real.log (n : ℝ) := by
          nlinarith [hPle1, hlogpos.le]
        linarith
      have hKge : (Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A
          ≤ max (2 * C * (1 + Cp))
              (max ((Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A) 1) :=
        le_trans (le_max_left _ 1) (le_max_right _ _)
      have htarget : Real.log (N : ℝ) + C
          ≤ max (2 * C * (1 + Cp))
              (max ((Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A) 1)
              / (Real.log (n : ℝ)) ^ A := by
        rw [le_div_iff₀ hden]
        calc (Real.log (N : ℝ) + C) * (Real.log (n : ℝ)) ^ A
            ≤ (Real.log (N : ℝ) + C) * (Real.log (N : ℝ)) ^ A :=
              mul_le_mul_of_nonneg_left hlogpow_le (by
                have := hCpos; nlinarith [hlogNpos])
          _ ≤ _ := hKge
      linarith [hc, htarget]




open Filter in
private lemma eventually_log_pow_le_real {A : ℝ} (_hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ A ≤ x := by
  have hlit := isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) A (by norm_num)
  have hbound := hlit.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognn A),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le (1 : ℝ)), one_mul] at hx
  rwa [Real.rpow_one] at hx

theorem prod_one_sub_inv_prime_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → ∃ D : ℝ, 0 < D ∧ ∀ y : ℝ, 2 ≤ y →
      |(∏ p ∈ (⌊y⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log y - C| ≤
        D / (Real.log y) ^ A := by
  obtain ⟨M, hM⟩ := second_mertens_converges
  set C : ℝ := Real.exp (-M - W) with hCdef
  have hCpos : 0 < C := Real.exp_pos _
  refine ⟨C, hCpos, ?_⟩
  intro A hA
  obtain ⟨K, hKpos, hK⟩ := prod_mul_log_nat_powLog hM A hA
  have hK' : ∀ n : ℕ, 11 ≤ n →
      |(∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ))) * Real.log (n : ℝ) - C| ≤
        K / (Real.log (n : ℝ)) ^ A := by
    intro n hn
    rw [hCdef]
    exact hK n hn
  obtain ⟨Y1, hY1⟩ := eventually_atTop.mp (eventually_log_pow_le_real hA)
  set Y : ℝ := max (max Y1 12) 4 with hYdef
  have hY1Y : Y1 ≤ Y := le_trans (le_max_left Y1 12) (le_max_left (max Y1 12) 4)
  have hY12 : 12 ≤ Y := le_trans (le_max_right Y1 12) (le_max_left (max Y1 12) 4)
  set D : ℝ := max (K * 2 ^ A + 2) (max ((Real.log Y + C) * (Real.log Y) ^ A) 1) with hDdef
  refine ⟨D, ?_, ?_⟩
  · rw [hDdef]
    have : (1 : ℝ) ≤ max (K * 2 ^ A + 2) (max ((Real.log Y + C) * (Real.log Y) ^ A) 1) :=
      le_trans (le_max_right _ 1) (le_max_right _ _)
    linarith
  · intro y hy2
    set n : ℕ := ⌊y⌋₊ with hndef
    have hn2 : 2 ≤ n := Nat.le_floor hy2
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hyn : (n : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hyn' : y < (n : ℝ) + 1 := Nat.lt_floor_add_one y
    have hyn1 : y - (n : ℝ) ≤ 1 := by linarith
    have hlogypos : 0 < Real.log y := Real.log_pos (by linarith)
    have hlogypowpos : 0 < (Real.log y) ^ A := Real.rpow_pos_of_pos hlogypos A
    set P : ℝ := ∏ p ∈ n.primesLE, (1 - 1 / (p : ℝ)) with hPdef
    have hPnonneg : 0 ≤ P := by
      rw [hPdef]
      refine Finset.prod_nonneg (fun p hp => ?_)
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hle : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
      linarith
    have hPle1 : P ≤ 1 := by
      rw [hPdef]
      refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hle : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
        linarith
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
    have hlogdiff : |Real.log y - Real.log (n : ℝ)| ≤ 1 / (n : ℝ) := by
      have hypos : 0 < y := by linarith
      have hle : Real.log (n : ℝ) ≤ Real.log y := Real.log_le_log hnpos hyn
      rw [abs_of_nonneg (by linarith)]
      have h1 : Real.log y - Real.log (n : ℝ) = Real.log (y / (n : ℝ)) := by
        rw [Real.log_div hypos.ne' hnpos.ne']
      rw [h1]
      have harg : 0 < y / (n : ℝ) := by positivity
      have h2 := Real.log_le_sub_one_of_pos harg
      have h3 : y / (n : ℝ) - 1 = (y - (n : ℝ)) / (n : ℝ) := by
        rw [sub_div, div_self hnpos.ne']
      rw [h3] at h2
      calc Real.log (y / (n : ℝ)) ≤ (y - (n : ℝ)) / (n : ℝ) := h2
        _ ≤ 1 / (n : ℝ) := div_le_div_of_nonneg_right hyn1 hnpos.le
    by_cases hYy : Y ≤ y
    · -- good regime
      have hn11 : 11 ≤ n := by
        apply Nat.le_floor
        push_cast
        linarith
      have hbase : |P * Real.log (n : ℝ) - C| ≤ K / (Real.log (n : ℝ)) ^ A := by
        rw [hPdef]; exact hK' n hn11
      have hB : |P * (Real.log y - Real.log (n : ℝ))| ≤ 1 / (n : ℝ) := by
        rw [abs_mul, abs_of_nonneg hPnonneg]
        calc P * |Real.log y - Real.log (n : ℝ)| ≤ 1 * (1 / (n : ℝ)) :=
              mul_le_mul hPle1 hlogdiff (abs_nonneg _) (by norm_num)
          _ = 1 / (n : ℝ) := by ring
      have heq : P * Real.log y - C = (P * Real.log (n : ℝ) - C)
          + P * (Real.log y - Real.log (n : ℝ)) := by ring
      have htri : |P * Real.log y - C| ≤ K / (Real.log (n : ℝ)) ^ A + 1 / (n : ℝ) := by
        rw [heq]
        calc |(P * Real.log (n : ℝ) - C) + P * (Real.log y - Real.log (n : ℝ))|
            ≤ |P * Real.log (n : ℝ) - C| + |P * (Real.log y - Real.log (n : ℝ))| :=
              abs_add_le _ _
          _ ≤ K / (Real.log (n : ℝ)) ^ A + 1 / (n : ℝ) := add_le_add hbase hB
      have hlogpow_le_y : (Real.log y) ^ A ≤ y := hY1 y (le_trans hY1Y hYy)
      have hBbound : 1 / (n : ℝ) ≤ 2 / (Real.log y) ^ A := by
        have h1 : 1 / (n : ℝ) ≤ 1 / (y - 1) :=
          one_div_le_one_div_of_le (by linarith : 0 < y - 1) (by linarith)
        have h2 : 1 / (y - 1) ≤ 1 / (y / 2) := by
          apply one_div_le_one_div_of_le (by linarith : 0 < y / 2)
          linarith
        have h3 : (1 : ℝ) / (y / 2) = 2 / y := by ring
        have h4 : 2 / y ≤ 2 / (Real.log y) ^ A := by
          have h5 : 1 / y ≤ 1 / (Real.log y) ^ A :=
            one_div_le_one_div_of_le hlogypowpos hlogpow_le_y
          calc 2 / y = 2 * (1 / y) := by ring
            _ ≤ 2 * (1 / (Real.log y) ^ A) := mul_le_mul_of_nonneg_left h5 (by norm_num)
            _ = 2 / (Real.log y) ^ A := by ring
        exact le_trans h1 (le_trans h2 (le_trans h3.le h4))
      have hlogy2 : Real.log y / 2 ≤ Real.log (n : ℝ) := by
        have hge2 : Real.log 2 ≤ Real.log y - Real.log 2 := by
          have h4y : (4 : ℝ) ≤ y := by linarith [hY12, hYy]
          have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4y
          rw [show Real.log (4 : ℝ) = 2 * Real.log 2 by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num] at h
          linarith
        have hn2R : y / 2 ≤ (n : ℝ) := by linarith
        have hle1 : Real.log (y / 2) ≤ Real.log (n : ℝ) := Real.log_le_log (by linarith) hn2R
        have hsplit : Real.log (y / 2) = Real.log y - Real.log 2 :=
          Real.log_div (by linarith : y ≠ 0) (by norm_num)
        rw [hsplit] at hle1
        linarith
      have hAlog : (Real.log y) ^ A / 2 ^ A ≤ (Real.log (n : ℝ)) ^ A := by
        rw [← Real.div_rpow hlogypos.le (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.rpow_le_rpow (by linarith [hlogypos]) hlogy2 hA.le
      have hAbound : K / (Real.log (n : ℝ)) ^ A ≤ K * 2 ^ A / (Real.log y) ^ A := by
        have hinv : 1 / (Real.log (n : ℝ)) ^ A ≤ 2 ^ A / (Real.log y) ^ A := by
          have h1 : 1 / (Real.log (n : ℝ)) ^ A ≤ 1 / ((Real.log y) ^ A / 2 ^ A) :=
            one_div_le_one_div_of_le (by positivity) hAlog
          have h2 : 1 / ((Real.log y) ^ A / 2 ^ A) = 2 ^ A / (Real.log y) ^ A := by
            rw [one_div_div]
          linarith [h1, h2.le, h2.ge]
        calc K / (Real.log (n : ℝ)) ^ A = K * (1 / (Real.log (n : ℝ)) ^ A) := by ring
          _ ≤ K * (2 ^ A / (Real.log y) ^ A) := mul_le_mul_of_nonneg_left hinv hKpos.le
          _ = K * 2 ^ A / (Real.log y) ^ A := by ring
      have htot : |P * Real.log y - C| ≤ (K * 2 ^ A + 2) / (Real.log y) ^ A := by
        calc |P * Real.log y - C| ≤ K / (Real.log (n : ℝ)) ^ A + 1 / (n : ℝ) := htri
          _ ≤ K * 2 ^ A / (Real.log y) ^ A + 2 / (Real.log y) ^ A := add_le_add hAbound hBbound
          _ = (K * 2 ^ A + 2) / (Real.log y) ^ A := by ring
      have hDge : K * 2 ^ A + 2 ≤ D := by rw [hDdef]; exact le_max_left _ _
      calc |P * Real.log y - C| ≤ (K * 2 ^ A + 2) / (Real.log y) ^ A := htot
        _ ≤ D / (Real.log y) ^ A := div_le_div_of_nonneg_right hDge hlogypowpos.le
    · -- small regime
      have hyY : y ≤ Y := le_of_lt (lt_of_not_ge hYy)
      have hlogYpos : 0 < Real.log Y := Real.log_pos (by linarith [hY12])
      have hlogle : Real.log y ≤ Real.log Y := Real.log_le_log (by linarith) hyY
      have hlogpowle : (Real.log y) ^ A ≤ (Real.log Y) ^ A :=
        Real.rpow_le_rpow hlogypos.le hlogle hA.le
      have hc : |P * Real.log y - C| ≤ Real.log Y + C := by
        have h0 : 0 ≤ P * Real.log y := mul_nonneg hPnonneg hlogypos.le
        have h2 : |P * Real.log y - C| ≤ P * Real.log y + C := by
          rw [abs_sub_le_iff]
          constructor <;> linarith [h0, hCpos.le]
        have h3 : P * Real.log y ≤ Real.log y := by nlinarith [hPle1, hlogypos.le]
        linarith
      have hDge : (Real.log Y + C) * (Real.log Y) ^ A ≤ D := by
        rw [hDdef]; exact le_trans (le_max_left _ 1) (le_max_right _ _)
      have htarget : Real.log Y + C ≤ D / (Real.log y) ^ A := by
        rw [le_div_iff₀ hlogypowpos]
        calc (Real.log Y + C) * (Real.log y) ^ A
            ≤ (Real.log Y + C) * (Real.log Y) ^ A :=
              mul_le_mul_of_nonneg_left hlogpowle (by linarith [hlogYpos])
          _ ≤ D := hDge
      linarith [hc, htarget]

end

end Commons.NumberTheory.Mertens
