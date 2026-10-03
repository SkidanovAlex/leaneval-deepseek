import Mathlib
import Submission.Work.FIChain.TailDefs
import Submission.Work.FIChain.tail_integral_le
import Submission.Work.FIChain.tail_arith_step1
import Submission.Work.FIChain.tail_arith_step2
import Submission.Work.FIChain.tau_cube_swell
import Submission.Work.FIChain.rankin_tau_sq_div_le_strong
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_sq_div_of_cubefree
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.AtilInnerSumLeAd
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The elementary divisor-sum step -/

/-! ## The elementary divisor-sum step -/

/-- `Σ_{N : d ∣ N ∣ K} τ(K/N)² ≤ τ(K/d)³`. -/
lemma sum_tau_sq_divisors_le (x K d : ℕ) :
    (∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
        ((K / N).divisors.card : ℝ) ^ 2)
      ≤ ((K / d).divisors.card : ℝ) ^ 3 := by
  classical
  rcases eq_or_ne K 0 with hK | hK
  · subst hK
    have hzero : (∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ 0),
        ((0 / N).divisors.card : ℝ) ^ 2) = 0 := by
      refine Finset.sum_eq_zero (fun N hN => ?_)
      rw [Finset.mem_filter, Finset.mem_Icc] at hN
      obtain ⟨⟨hN1, _⟩, _⟩ := hN
      have hN0 : N ≠ 0 := by omega
      rw [Nat.zero_div, Nat.divisors_zero]
      norm_num
    rw [hzero]
    positivity
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    have hterm : ∀ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
        ((K / N).divisors.card : ℝ) ≤ ((K / d).divisors.card : ℝ) := by
      intro N hN
      rw [Finset.mem_filter, Finset.mem_Icc] at hN
      obtain ⟨⟨hN1, _⟩, hdN, hNK⟩ := hN
      have hNpos : 0 < N := by omega
      have hdK : d ∣ K := dvd_trans hdN hNK
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN hNpos
      have hkey : K / d = (K / N) * (N / d) := by
        rw [Nat.div_mul_div_comm hNK hdN, mul_comm K N, Nat.mul_div_mul_left K d hNpos]
      have hne : K / d ≠ 0 := (Nat.div_ne_zero_iff).mpr ⟨ne_of_gt hdpos,
        Nat.le_of_dvd hKpos hdK⟩
      exact_mod_cast Submission.ASP.card_divisors_le_of_dvd ⟨N / d, hkey⟩ hne
    have hcard : ((Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K)).card
        ≤ (K / d).divisors.card := by
      refine Finset.card_le_card_of_injOn (fun N => N / d) ?_ ?_
      · intro N hN
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hN
        obtain ⟨⟨hN1, _⟩, hdN, hNK⟩ := hN
        have hNpos : 0 < N := by omega
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN hNpos
        have hdK : d ∣ K := dvd_trans hdN hNK
        change N / d ∈ (K / d).divisors
        rw [Nat.mem_divisors]
        exact ⟨Nat.div_dvd_div hdN hNK, (Nat.div_ne_zero_iff).mpr
          ⟨ne_of_gt hdpos, Nat.le_of_dvd hKpos hdK⟩⟩
      · intro N hN N' hN' heq
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hN hN'
        exact (Nat.div_left_inj hN.2.1 hN'.2.1).mp heq
    calc (∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
            ((K / N).divisors.card : ℝ) ^ 2)
        ≤ ∑ _N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
            (((K / d).divisors.card : ℝ) ^ 2) :=
          Finset.sum_le_sum (fun N hN => pow_le_pow_left₀ (Nat.cast_nonneg _) (hterm N hN) 2)
      _ = (((Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K)).card : ℝ)
            * ((K / d).divisors.card : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((K / d).divisors.card : ℝ) * ((K / d).divisors.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = ((K / d).divisors.card : ℝ) ^ 3 := by ring

/-! ## The eventual numerical facts -/

/-- `Δπ·P ≤ x^{1/4}` eventually. -/
lemma eventually_Dpi_mul_Pcut_le (κ : ℝ) (hκ : (1 : ℝ) ≤ κ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Dpi x κ : ℝ) * (Pzc x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
  have h1 : ∀ᶠ x : ℕ in Filter.atTop,
      (Real.log (Real.log (x : ℝ))) ^ 3 ≤ (Real.log (x : ℝ)) ^ ((1 : ℝ) / 2) := by
    have h := Work.FITop.FI_ev_loglog_rpow_le_nat (b := 3) (ε := (1 : ℝ) / 2) (C := 1)
      one_pos (by norm_num)
    simpa using h
  have h2 : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
    filter_upwards [Work.FITop.FI_ev_log_ge_nat (Real.exp 1)] with x hx
    have h2 : Real.log (Real.exp 1) ≤ Real.log (Real.log (x : ℝ)) :=
      Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h2
  have h3 : ∀ᶠ x : ℕ in Filter.atTop,
      max (16 * Real.log 4) ((8 * (κ + 1)) ^ 2) ≤ Real.log (x : ℝ) :=
    Work.FITop.FI_ev_log_ge_nat _
  have h4 : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ (x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    exact_mod_cast hx
  filter_upwards [h1, h2, h3, h4] with x hll hl1 hl3 hx2
  set L := Real.log (x : ℝ) with hLdef
  set A := Real.log L with hAdef
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := by
    have h := le_trans (le_max_left _ _) hl3
    rw [hLdef]
    linarith
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hL16log : 16 * Real.log 4 ≤ L := le_trans (le_max_left _ _) hl3
  have hLsq : (8 * (κ + 1)) ^ 2 ≤ L := le_trans (le_max_right _ _) hl3
  have hsq : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hLhalf : 8 * (κ + 1) ≤ L ^ ((1 : ℝ) / 2) := by
    calc 8 * (κ + 1) = ((8 * (κ + 1)) ^ 2) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
      _ ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hLsq (by norm_num)
  have h16le : (16 : ℝ) ≤ L ^ ((1 : ℝ) / 2) := by linarith [hLhalf, hκ]
  have hhalf_le : L ^ ((1 : ℝ) / 2) ≤ L / 16 := by
    have hnn : 0 ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hLpos.le _
    nlinarith [mul_le_mul_of_nonneg_left h16le hnn, hsq]
  have hA3 : A ^ 3 ≤ L / 16 := by
    rw [hAdef, hLdef]
    exact le_trans hll hhalf_le
  have hA2 : A ^ 2 ≤ L / 16 := by
    have hA2' : A ^ 2 ≤ A ^ 3 := by
      have h1 := hl1; rw [hAdef, hLdef] at h1
      nlinarith [h1]
    linarith
  have hkA3 : κ * A ^ 3 ≤ L / 8 := by
    have hA3nn : 0 ≤ A ^ 3 := by positivity
    have h1 : κ * A ^ 3 ≤ (κ + 1) * L ^ ((1 : ℝ) / 2) := by
      have hll' := hll
      have hk : (0 : ℝ) ≤ κ := by linarith
      nlinarith [hll', hA3nn, hk, le_of_lt hApos]
    have h2 : (κ + 1) * L ^ ((1 : ℝ) / 2) ≤ L / 8 := by
      have hnn : 0 ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hLpos.le _
      have h3 : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) / 8 = L / 8 := by
        rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_right hLhalf hnn, h3, hnn]
    linarith
  have hlog4 : Real.log 4 ≤ L / 16 := by linarith
  have hsum : Real.log 4 + (κ * A ^ 3 + A ^ 2) ≤ L / 16 + (L / 8 + L / 16) :=
    add_le_add hlog4 (add_le_add hkA3 hA2)
  have hmain : Real.log 4 + (κ * A ^ 3 + A ^ 2) ≤ L / 4 := by
    refine le_trans hsum ?_
    linarith [hLpos]
  have hDpi : (Dpi x κ : ℝ) ≤ 2 * Real.exp (κ * A ^ 3) := by
    rw [Dpi]
    have h := Nat.ceil_lt_add_one (Real.exp_pos (κ * A ^ 3)).le
    have hone : (1 : ℝ) ≤ Real.exp (κ * A ^ 3) := Real.one_le_exp (by positivity)
    linarith
  have hPzc : (Pzc x : ℝ) ≤ 2 * Real.exp (A ^ 2) := by
    rw [Pzc, Work.FITop.Pcut]
    have h := Nat.ceil_lt_add_one (Real.exp_pos (A ^ 2)).le
    have hone : (1 : ℝ) ≤ Real.exp (A ^ 2) := Real.one_le_exp (by positivity)
    linarith
  have h4exp : (4 : ℝ) * Real.exp (κ * A ^ 3 + A ^ 2)
      = Real.exp (Real.log 4 + (κ * A ^ 3 + A ^ 2)) := by
    conv_lhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
  have hrt : (x : ℝ) ^ ((1 : ℝ) / 4) = Real.exp (L / 4) := by
    rw [hLdef, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (x : ℝ))]
    ring_nf
  calc (Dpi x κ : ℝ) * (Pzc x : ℝ)
      ≤ (2 * Real.exp (κ * A ^ 3)) * (2 * Real.exp (A ^ 2)) :=
        mul_le_mul hDpi hPzc (by positivity) (by positivity)
    _ = 4 * Real.exp (κ * A ^ 3 + A ^ 2) := by rw [Real.exp_add]; ring
    _ = Real.exp (Real.log 4 + (κ * A ^ 3 + A ^ 2)) := h4exp
    _ ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr hmain
    _ = (x : ℝ) ^ ((1 : ℝ) / 4) := hrt.symm

/-- `τ(m·n) ≤ τ(m)·τ(n)`: the map `L ↦ (L.gcd m, L / L.gcd m)` injects the divisors of `mn`
into the product of the divisor sets. -/
lemma card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  classical
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun L => (L.gcd m, L / L.gcd m)) ?_ ?_
  · intro L hL
    rw [Finset.mem_coe, Nat.mem_divisors] at hL
    obtain ⟨hLdvd, hLne⟩ := hL
    have hLpos : 0 < L := Nat.pos_of_dvd_of_pos hLdvd (Nat.pos_of_ne_zero hLne)
    have hgpos : 0 < L.gcd m := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left L m) hLpos
    change (L.gcd m, L / L.gcd m) ∈ m.divisors ×ˢ n.divisors
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
    refine ⟨⟨Nat.gcd_dvd_right L m, hm⟩, ?_, hn⟩
    have h1 : L / L.gcd m ∣ (m * n) / L.gcd m :=
      Nat.div_dvd_div (Nat.gcd_dvd_left L m) hLdvd
    have hm' : m = L.gcd m * (m / L.gcd m) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right L m)).symm
    have hmn : m * n = L.gcd m * ((m / L.gcd m) * n) := by
      conv_lhs => rw [hm']
      ring
    have h2 : (m * n) / L.gcd m = (m / L.gcd m) * n := by
      rw [hmn, Nat.mul_div_right _ hgpos]
    rw [h2] at h1
    have hcop : Nat.Coprime (L / L.gcd m) (m / L.gcd m) := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_div_gcd_div_gcd
        (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right m L) hLpos)).symm
    exact hcop.dvd_of_dvd_mul_left h1
  · intro L hL L' hL' heq
    have h1 : L.gcd m = L'.gcd m := congrArg Prod.fst heq
    have h2 : L / L.gcd m = L' / L'.gcd m := congrArg Prod.snd heq
    have h2' : L / L'.gcd m = L' / L'.gcd m := by
      conv_lhs => rw [← h1]
      exact h2
    have key : L = L'.gcd m * (L / L'.gcd m) := by
      rw [← h1]
      exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left L m)).symm
    rw [key, h2', Nat.mul_div_cancel' (Nat.gcd_dvd_left L' m)]

/-- The eventual facts consumed by the tail estimate. -/
lemma tail_facts_eventually (κ : ℝ) (hκ : (2 : ℝ) ^ (30 : ℕ) ≤ κ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Dpi x κ : ℝ) * (Pzc x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) ∧
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) ∧ (1 : ℝ) ≤ Real.log (x : ℝ) ∧
      (2 : ℝ) ≤ (x : ℝ) := by
  have h1 := eventually_Dpi_mul_Pcut_le κ (le_trans (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hκ)
  have h2 : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
    filter_upwards [Work.FITop.FI_ev_log_ge_nat (Real.exp 1)] with x hx
    have h2 : Real.log (Real.exp 1) ≤ Real.log (Real.log (x : ℝ)) :=
      Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h2
  have h3 : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
    Work.FITop.FI_ev_log_ge_nat 1
  have h4 : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ (x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    exact_mod_cast hx
  filter_upwards [h1, h2, h3, h4] with x ha hb hc hd
  exact ⟨ha, hb, hc, hd⟩


/-! ## The main theorem -/

set_option maxHeartbeats 3200000 in
theorem bprime_window_tail_le (B κ : ℝ) (hB : 0 < B) (hκ : (2 : ℝ) ^ (30 : ℕ) ≤ κ) :
    ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      (∫ t in (Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ))..
          (Work.FIChain.sc x B * (Real.exp 1 * Work.FIChain.Yc x B)),
        (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          |∑ b₁ ∈ ((Work.FIChain.ProdP (Work.FIChain.Pzc x)).divisors).filter
              (fun b₁ : ℕ => Work.FIChain.Dpi x κ < b₁),
            (ArithmeticFunction.moebius b₁ : ℝ) *
              Work.FIChain.Xf x (Work.FIChain.Pzc x) (m * b₁) (t / b₁)|) / t)
        ≤ K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
  obtain ⟨C_rank, hC_rank_pos, x_rank, h_rank⟩ := rankin_tau_sq_div_le_strong κ hκ
  obtain ⟨C0, hC0pos, hAd⟩ := Submission.ASP.Ad_le_tau_sq_div_of_cubefree
  obtain ⟨Cs, hCspos, hSum⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 11
  obtain ⟨Xa, hAseqle⟩ := Work.FITop.Aseq_le_const_mul_AcountAtil
  obtain ⟨xt, htx⟩ := Filter.eventually_atTop.mp (tail_facts_eventually κ hκ)
  set G : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hGdef
  have hGpos : 0 < G := by
    rw [hGdef]; have := Submission.ASP.Gprod_FIg_pos; positivity
  refine ⟨max 1 (Real.log 2 * C0 * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs * C_rank * G),
    max x_rank (max xt Xa) + 1, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x hx
  have hx_rank : x_rank ≤ x := by omega
  have hx_t : xt ≤ x := by omega
  have hx_a : Xa ≤ x := by omega
  obtain ⟨hDP_raw, hll1, hL1, hx1R⟩ := htx x hx_t
  have hx1 : 1 ≤ x := by omega
  have hxp : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL1
  have hAseqnn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have hAnn : (0 : ℝ) ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hAseqK : (Submission.Aseq x : ℝ) ≤ G * AcountAtilC x := by
    rw [hGdef]; exact hAseqle x hx_a
  set Pz : ℕ := Pzc x with hPzdef
  set D : ℕ := Dpi x κ with hDdef
  set lo : ℝ := Yc x B / (Deltac x : ℝ) with hlodef
  set hi : ℝ := sc x B * (Real.exp 1 * Yc x B) with hhidef
  have hDP : (D : ℝ) * (Pz : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := hDP_raw
  have hsc1 : (1 : ℝ) ≤ sc x B := by
    rw [sc]; exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hYcpos : 0 < Yc x B := by rw [Yc]; positivity
  have hDelta1 : (1 : ℝ) ≤ (Deltac x : ℝ) := by
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
      Real.one_le_rpow (by linarith : (1 : ℝ) ≤ (x : ℝ)) (by norm_num)
    have h2 : (1 : ℕ) ≤ Deltac x := by
      rw [Deltac, Work.FITop.Delta1, Work.FITop.Lam1]
      exact Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le one_pos h1)
    exact_mod_cast h2
  have hlo_pos : 0 < lo := by rw [hlodef]; exact div_pos hYcpos (by linarith)
  have hlo_hi : lo ≤ hi := by
    rw [hlodef, hhidef]
    have h1 : Yc x B / (Deltac x : ℝ) ≤ Yc x B := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (Deltac x : ℝ))]
      calc Yc x B = Yc x B * 1 := (mul_one _).symm
        _ ≤ Yc x B * (Deltac x : ℝ) := mul_le_mul_of_nonneg_left hDelta1 hYcpos.le
    have h2 : Yc x B ≤ sc x B * (Real.exp 1 * Yc x B) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hse : (1 : ℝ) ≤ sc x B * Real.exp 1 := by nlinarith [hsc1, hexp1]
      calc Yc x B = 1 * Yc x B := (one_mul _).symm
        _ ≤ (sc x B * Real.exp 1) * Yc x B := mul_le_mul_of_nonneg_right hse hYcpos.le
        _ = sc x B * (Real.exp 1 * Yc x B) := by ring
    linarith
  have hPz2 : 2 ≤ Pz := by
    rw [hPzdef, Pzc, Work.FITop.Pcut]
    refine Nat.lt_ceil.mpr ?_
    push_cast
    exact Real.one_lt_exp_iff.mpr (pow_pos (lt_of_lt_of_le one_pos hll1) 2)
  have hD1 : 1 ≤ D := by rw [hDdef, Dpi]; exact Nat.ceil_pos.mpr (Real.exp_pos _)
  -- the delegated steps
  have step1 := tail_integral_le x Pz D lo hi hlo_pos hlo_hi
  have step2 := tail_arith_step1 x Pz D hPz2 hD1
  have step3 := tail_arith_step2 x Pz D
  have step4 : (∑ d ∈ Dsp Pz D, ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
        atilc K * ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ N ∣ K),
          ((K / N).divisors.card : ℝ) ^ 2)
      ≤ ∑ d ∈ Dsp Pz D, ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
        atilc K * ((K / d).divisors.card : ℝ) ^ 3 := by
    refine Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun K _ => ?_))
    exact mul_le_mul_of_nonneg_left (sum_tau_sq_divisors_le x K d)
      (Work.FITop.atilFIa_nonneg K)
  have step5 : (∑ d ∈ Dsp Pz D, ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
        atilc K * ((K / d).divisors.card : ℝ) ^ 3)
      ≤ ∑ d ∈ Dsp Pz D, ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
          (2 * ((e.divisors.card : ℝ))) ^ 9 *
            ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K :=
    Finset.sum_le_sum (fun d _ => tau_cube_swell x d)
  have step6 : ∀ d ∈ Dsp Pz D, ∀ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
      (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K)
        ≤ C0 * (((d * e).divisors.card : ℝ)) ^ 2 * (Submission.Aseq x : ℝ)
          / ((d : ℝ) * (e : ℝ)) := by
    intro d hd e he
    rw [Finset.mem_filter, Finset.mem_Icc] at he
    obtain ⟨⟨he1, hex⟩, hecube⟩ := he
    obtain ⟨hdvd, hDlt, hDle⟩ := mem_Dsp.mp hd
    have hdD : (d : ℝ) ≤ (D : ℝ) * (Pz : ℝ) := by exact_mod_cast hDle
    have hd14 : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := le_trans hdD hDP
    have hd4 : d ^ 4 ≤ x := by
      have h1 : (d : ℝ) ^ 4 ≤ ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hd14 4
      have h2 : ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (x : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxp)]
        norm_num
      have h3 : (d : ℝ) ^ 4 ≤ (x : ℝ) := by rw [← h2]; exact h1
      exact_mod_cast h3
    have hde1 : 1 ≤ d * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hcube : (d * e) ^ 2 ≤ x := by
      have h6 : ((d * e) ^ 2) ^ 3 ≤ x ^ 3 := by
        have heq : ((d * e) ^ 2) ^ 3 = d ^ 4 * (e ^ 3 * d) ^ 2 := by ring
        rw [heq]
        calc d ^ 4 * (e ^ 3 * d) ^ 2 ≤ x * x ^ 2 :=
              Nat.mul_le_mul hd4 (pow_le_pow_left₀ (Nat.zero_le _) hecube 2)
          _ = x ^ 3 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp h6
    by_cases hsf : Squarefree (d * e)
    · have hcb : ∀ p : ℕ, Nat.Prime p → ¬ p ^ 3 ∣ d * e := by
        intro p hp hp3
        have hpp : p * p ∣ p ^ 3 := by
          rw [show p ^ 3 = (p * p) * p by ring]; exact dvd_mul_right _ _
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp) (dvd_trans hpp hp3)
      have h1 : (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K)
          ≤ (Submission.Ad (d * e) x : ℝ) := Work.FITop.AtilInnerSumLeAd (d * e) x
      have h2 : (Submission.Ad (d * e) x : ℝ)
          ≤ C0 * (((d * e).divisors.card : ℝ)) ^ 2 * (Submission.Aseq x : ℝ)
            / ((d : ℝ) * (e : ℝ)) := by
        have := hAd (d * e) x hde1 hcb hcube
        rw [Nat.cast_mul] at this
        calc (Submission.Ad (d * e) x : ℝ)
            ≤ C0 * (((d * e).divisors.card : ℝ)) ^ 2 / (((d : ℝ) * (e : ℝ)))
                * (Submission.Aseq x : ℝ) := by
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
          _ = C0 * (((d * e).divisors.card : ℝ)) ^ 2 * (Submission.Aseq x : ℝ)
                / ((d : ℝ) * (e : ℝ)) := by ring
      linarith
    · have hzero : (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K) = 0 := by
        refine Finset.sum_eq_zero (fun K hK => ?_)
        rw [Finset.mem_filter] at hK
        have hnsf : ¬ Squarefree K := fun hKsf => hsf (Squarefree.squarefree_of_dvd hK.2 hKsf)
        exact Work.FITop.atilFIa_eq_zero_of_not_squarefree hnsf
      rw [hzero]
      positivity
  -- Step 7
  have hS5 : (∑ d ∈ Dsp Pz D, ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
        (2 * ((e.divisors.card : ℝ))) ^ 9 *
          ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K)
      ≤ C0 * (Submission.Aseq x : ℝ) *
        ((∑ d ∈ Dsp Pz D, (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))) *
         (∑ e ∈ Finset.Icc 1 x,
            (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))))) := by
    have h7a : (∑ d ∈ Dsp Pz D, ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
          (2 * ((e.divisors.card : ℝ))) ^ 9 *
            ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K)
        ≤ ∑ d ∈ Dsp Pz D, ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            C0 * (Submission.Aseq x : ℝ) *
              ((2 * ((e.divisors.card : ℝ))) ^ 9 *
                ((((d * e).divisors.card : ℝ)) ^ 2 / ((d : ℝ) * (e : ℝ)))) := by
      refine Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => ?_))
      calc (2 * ((e.divisors.card : ℝ))) ^ 9 *
              (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), atilc K)
          ≤ (2 * ((e.divisors.card : ℝ))) ^ 9 *
              (C0 * (((d * e).divisors.card : ℝ)) ^ 2 * (Submission.Aseq x : ℝ)
                / ((d : ℝ) * (e : ℝ))) :=
            mul_le_mul_of_nonneg_left (step6 d hd e he) (by positivity)
        _ = C0 * (Submission.Aseq x : ℝ) *
              ((2 * ((e.divisors.card : ℝ))) ^ 9 *
                ((((d * e).divisors.card : ℝ)) ^ 2 / ((d : ℝ) * (e : ℝ)))) := by ring
    have hτ : ∀ d e : ℕ, (((d * e).divisors.card : ℝ)) ^ 2
        ≤ (((d.divisors.card : ℝ)) ^ 2) * (((e.divisors.card : ℝ)) ^ 2) := by
      intro d e
      have h := card_divisors_mul_le d e
      have h' : (((d * e).divisors.card : ℝ))
          ≤ ((d.divisors.card : ℝ)) * ((e.divisors.card : ℝ)) := by exact_mod_cast h
      calc (((d * e).divisors.card : ℝ)) ^ 2
          ≤ (((d.divisors.card : ℝ)) * ((e.divisors.card : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h' 2
        _ = (((d.divisors.card : ℝ)) ^ 2) * (((e.divisors.card : ℝ)) ^ 2) := by ring
    refine le_trans h7a ?_
    calc (∑ d ∈ Dsp Pz D, ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            C0 * (Submission.Aseq x : ℝ) *
              ((2 * ((e.divisors.card : ℝ))) ^ 9 *
                ((((d * e).divisors.card : ℝ)) ^ 2 / ((d : ℝ) * (e : ℝ)))))
        ≤ ∑ d ∈ Dsp Pz D, ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            C0 * (Submission.Aseq x : ℝ) *
              ((2 * ((e.divisors.card : ℝ))) ^ 9 *
                ((((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
                  * (((e.divisors.card : ℝ)) ^ 2 / (e : ℝ)))) := by
          refine Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => ?_))
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by positivity)
          calc (((d * e).divisors.card : ℝ)) ^ 2 / ((d : ℝ) * (e : ℝ))
              = (((d * e).divisors.card : ℝ)) ^ 2 * (1 / ((d : ℝ) * (e : ℝ))) := by ring
            _ ≤ ((((d.divisors.card : ℝ)) ^ 2) * (((e.divisors.card : ℝ)) ^ 2))
                  * (1 / ((d : ℝ) * (e : ℝ))) :=
                mul_le_mul_of_nonneg_right (hτ d e) (by positivity)
            _ = (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
                  * (((e.divisors.card : ℝ)) ^ 2 / (e : ℝ)) := by
                rw [div_mul_div_comm, div_eq_mul_inv]
                ring
      _ ≤ ∑ d ∈ Dsp Pz D, ∑ e ∈ Finset.Icc 1 x,
            C0 * (Submission.Aseq x : ℝ) *
              ((2 * ((e.divisors.card : ℝ))) ^ 9 *
                ((((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
                  * (((e.divisors.card : ℝ)) ^ 2 / (e : ℝ)))) := by
          refine Finset.sum_le_sum (fun d hd =>
            Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
          · intro e he; exact (Finset.mem_filter.mp he).1
          · intro e _ _; positivity
      _ = C0 * (Submission.Aseq x : ℝ) *
            ((∑ d ∈ Dsp Pz D, (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))) *
             (∑ e ∈ Finset.Icc 1 x,
                (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))))) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          ring
  -- the two factor bounds
  have hWd : (∑ d ∈ Dsp Pz D, (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ)))
      ≤ C_rank * (Real.log (x : ℝ)) ^ (-(65536 : ℤ)) := by
    have hsubset : Dsp Pz D ⊆ ((ProdP (Pzc x)).divisors).filter (fun d => Dpi x κ < d) := by
      intro d hd
      rw [hPzdef, hDdef] at hd
      rw [Finset.mem_filter]
      exact ⟨Dsp_subset_divisors (Pzc x) (Dpi x κ) hd, (mem_Dsp.mp hd).2.1⟩
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => by positivity))
      (h_rank x hx_rank)
  have hWe : (∑ e ∈ Finset.Icc 1 x,
        (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))))
      ≤ (2 : ℝ) ^ 9 * (Cs * ((2 : ℝ) ^ 2048 * (Real.log (x : ℝ)) ^ (2048 : ℕ))) := by
    have h1 : (∑ e ∈ Finset.Icc 1 x,
          (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))))
        = (2 : ℝ) ^ 9 * (∑ e ∈ Finset.Icc 1 x, ((e.divisors.card : ℝ)) ^ 11 / (e : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      have h2 : ((e.divisors.card : ℝ)) ^ 9 * (((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))
          = ((e.divisors.card : ℝ)) ^ 11 / (e : ℝ) := by
        rw [← mul_div_assoc, ← pow_add]
      rw [mul_pow, mul_assoc, h2]
    rw [h1]
    have h2 := hSum x hx1
    have h3 : (Real.log ((x : ℝ) + 2)) ^ (2 ^ 11)
        ≤ (2 : ℝ) ^ 2048 * (Real.log (x : ℝ)) ^ (2048 : ℕ) := by
      have hx2 : (2 : ℝ) ≤ (x : ℝ) := hx1R
      have h6 : 0 ≤ Real.log ((x : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hlog3 : Real.log ((x : ℝ) + 2) ≤ 2 * Real.log (x : ℝ) := by
        calc Real.log ((x : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
              Real.log_le_log (by linarith) (by linarith)
          _ = Real.log 2 + Real.log (x : ℝ) := Real.log_mul (by norm_num) (by linarith)
          _ ≤ Real.log (x : ℝ) + Real.log (x : ℝ) := by
              have h5 : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx2
              linarith
          _ = 2 * Real.log (x : ℝ) := by ring
      calc (Real.log ((x : ℝ) + 2)) ^ (2 ^ 11)
          = (Real.log ((x : ℝ) + 2)) ^ (2048 : ℕ) := by norm_num
        _ ≤ (2 * Real.log (x : ℝ)) ^ (2048 : ℕ) :=
            pow_le_pow_left₀ h6 hlog3 2048
        _ = (2 : ℝ) ^ 2048 * (Real.log (x : ℝ)) ^ (2048 : ℕ) := mul_pow _ _ _
    calc (2 : ℝ) ^ 9 * (∑ e ∈ Finset.Icc 1 x, ((e.divisors.card : ℝ)) ^ 11 / (e : ℝ))
        ≤ (2 : ℝ) ^ 9 * (Cs * (Real.log ((x : ℝ) + 2)) ^ (2 ^ 11)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (2 : ℝ) ^ 9 * (Cs * ((2 : ℝ) ^ 2048 * (Real.log (x : ℝ)) ^ (2048 : ℕ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hCspos.le) (by positivity)
  -- the exponent comparison
  have hlog512 : (Real.log (x : ℝ)) ^ (2048 : ℕ) * (Real.log (x : ℝ)) ^ (-(65536 : ℤ))
      ≤ (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
    have e1 : (Real.log (x : ℝ)) ^ (2048 : ℕ) = (Real.log (x : ℝ)) ^ ((2048 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    have e2 : (Real.log (x : ℝ)) ^ (-(65536 : ℤ))
        = (Real.log (x : ℝ)) ^ ((((-65536 : ℤ)) : ℝ)) :=
      (Real.rpow_intCast _ (-65536)).symm
    have e3 : (Real.log (x : ℝ)) ^ (-(4 : ℤ)) = (Real.log (x : ℝ)) ^ ((((-4 : ℤ)) : ℝ)) :=
      (Real.rpow_intCast _ (-4)).symm
    rw [e1, e2, e3, ← Real.rpow_add hLpos]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  -- assembly
  have hchain : (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
        ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
          ∑ n ∈ (Finset.Icc 1 x).filter
              (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
            atilc (m * b₁ * n))
      ≤ C0 * (Submission.Aseq x : ℝ) *
        ((∑ d ∈ Dsp Pz D, (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))) *
         (∑ e ∈ Finset.Icc 1 x,
            (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))))) :=
    le_trans step2 (le_trans step3 (le_trans step4 step5)) |>.trans hS5
  calc (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          |∑ b₁ ∈ ((ProdP Pz).divisors).filter
              (fun b₁ : ℕ => Dpi x κ < b₁),
            (ArithmeticFunction.moebius b₁ : ℝ) *
              Xf x Pz (m * b₁) (t / b₁)|) / t)
      = ∫ t in lo..hi,
          (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
            |∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
              (ArithmeticFunction.moebius b₁ : ℝ) *
                Xf x Pz (m * b₁) (t / b₁)|) / t := by rw [hDdef]
    _ ≤ Real.log 2 * (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
          ∑ b₁ ∈ ((ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
            ∑ n ∈ (Finset.Icc 1 x).filter
                (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
              atilc (m * b₁ * n)) := step1
    _ ≤ Real.log 2 * (C0 * (Submission.Aseq x : ℝ) *
          ((∑ d ∈ Dsp Pz D, (((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))) *
           (∑ e ∈ Finset.Icc 1 x,
              (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ)))))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ ≤ Real.log 2 * (C0 * (Submission.Aseq x : ℝ) *
          ((C_rank * (Real.log (x : ℝ)) ^ (-(65536 : ℤ))) *
           ((2 : ℝ) ^ 9 * (Cs * ((2 : ℝ) ^ 2048 * (Real.log (x : ℝ)) ^ (2048 : ℕ)))))) := by
        have hWen : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 x,
            (2 * ((e.divisors.card : ℝ))) ^ 9 * ((((e.divisors.card : ℝ)) ^ 2 / (e : ℝ))) :=
          Finset.sum_nonneg (fun e he => by
            have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
            have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
            positivity)
        have hWdn : (0 : ℝ) ≤ C_rank * (Real.log (x : ℝ)) ^ (-(65536 : ℤ)) :=
          mul_nonneg hC_rank_pos.le (zpow_nonneg hLpos.le _)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul hWd hWe hWen hWdn) (by positivity)) (by positivity)
    _ = (Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs)
          * (Submission.Aseq x : ℝ)
          * ((Real.log (x : ℝ)) ^ (2048 : ℕ) * (Real.log (x : ℝ)) ^ (-(65536 : ℤ))) := by ring
    _ ≤ (Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs)
          * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
        have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h9 : (0 : ℝ) ≤ (2 : ℝ) ^ 9 := by positivity
        have h2048 : (0 : ℝ) ≤ (2 : ℝ) ^ 2048 := by positivity
        have h1 : (0 : ℝ) ≤ Real.log 2 * C0 := mul_nonneg hlog2nn hC0pos.le
        have h2 : (0 : ℝ) ≤ Real.log 2 * C0 * C_rank := mul_nonneg h1 hC_rank_pos.le
        have h3 : (0 : ℝ) ≤ Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 := mul_nonneg h2 h9
        have h4 : (0 : ℝ) ≤ Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 :=
          mul_nonneg h3 h2048
        have hc : (0 : ℝ)
            ≤ Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs :=
          mul_nonneg h4 hCspos.le
        exact mul_le_mul_of_nonneg_left hlog512 (mul_nonneg hc hAseqnn)
    _ ≤ (Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs)
          * (G * AcountAtilC x) * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
        have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h9 : (0 : ℝ) ≤ (2 : ℝ) ^ 9 := by positivity
        have h2048 : (0 : ℝ) ≤ (2 : ℝ) ^ 2048 := by positivity
        have h1 : (0 : ℝ) ≤ Real.log 2 * C0 := mul_nonneg hlog2nn hC0pos.le
        have h2 : (0 : ℝ) ≤ Real.log 2 * C0 * C_rank := mul_nonneg h1 hC_rank_pos.le
        have h3 : (0 : ℝ) ≤ Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 := mul_nonneg h2 h9
        have h4 : (0 : ℝ) ≤ Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 :=
          mul_nonneg h3 h2048
        have hc : (0 : ℝ)
            ≤ Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs :=
          mul_nonneg h4 hCspos.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAseqK hc)
          (zpow_nonneg hLpos.le _)
    _ = ((Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs) * G)
          * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by ring
    _ ≤ max 1 (Real.log 2 * C0 * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs * C_rank * G)
          * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hAnn)
          (zpow_nonneg hLpos.le _)
        have heq : (Real.log 2 * C0 * C_rank * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs) * G
            = Real.log 2 * C0 * (2 : ℝ) ^ 9 * (2 : ℝ) ^ 2048 * Cs * C_rank * G := by ring
        rw [heq]
        exact le_max_right _ _

end

end Work.FIChain
