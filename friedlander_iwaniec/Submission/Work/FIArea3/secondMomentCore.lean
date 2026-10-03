import Mathlib
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith
import Submission.Work.FIArea3.JointCount.joint_sum_le_double
import Submission.Work.FIArea3.logFac_le
import Submission.Work.FIArea3.tauSqLcmReduction
import Submission.Work.FIArea3.lcmTauDivBound
import Submission.Work.FIArea3.lcmTauSqrtBound
import Submission.Work.FIArea2.sum_tau_pow_le

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Helper lemmas -/

/-- `θ ≤ 1`. -/
lemma theta_le_one' (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    exact le_trans h3.le (Real.log_le_log (by norm_num) hx3)
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [Pa.hA, Pa.hA'])

/-- Under the sharp hypothesis `u = θ√N ≥ N^{3/8}` one has `log N ≥ 1`. -/
lemma one_le_log_N' (Pa : Work.FITop.Params)
    (h : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) : 1 ≤ Real.log Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  -- `θ ≥ N^{-1/8}`
  have hθge : Pa.N ^ (-(1 : ℝ) / 8) ≤ Pa.θ := by
    have hs : Real.sqrt Pa.N = Pa.N ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Pa.N
    rw [hs] at h
    have hb : (0 : ℝ) < Pa.N ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hNpos _
    have hm := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hb.le)
    have he : Pa.θ * Pa.N ^ ((1 : ℝ) / 2) * (Pa.N ^ ((1 : ℝ) / 2))⁻¹ = Pa.θ := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one]
    rw [he] at hm
    have h2 : Pa.N ^ ((3 : ℝ) / 8) * (Pa.N ^ ((1 : ℝ) / 2))⁻¹ = Pa.N ^ (-(1 : ℝ) / 8) := by
      rw [← div_eq_mul_inv, ← Real.rpow_sub hNpos]
      congr 1
      norm_num
    rwa [h2] at hm
  have hθ10 : Pa.θ ≤ (1 : ℝ) / 10 := theta_le_tenth Pa
  -- `10 ≤ N^{1/8}`
  have hle : (10 : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 8) := by
    have h10pos : (0 : ℝ) < (1 : ℝ) / 10 := by norm_num
    have hN8pos : (0 : ℝ) < Pa.N ^ (-(1 : ℝ) / 8) := Real.rpow_pos_of_pos hNpos _
    have hle0 := (inv_le_inv₀ h10pos hN8pos).mpr (hθge.trans hθ10)
    have e1 : ((1 : ℝ) / 10)⁻¹ = 10 := by norm_num
    have e2 : (Pa.N ^ (-(1 : ℝ) / 8))⁻¹ = Pa.N ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_neg hNpos.le]
      congr 1
      ring
    rwa [e1, e2] at hle0
  have hN8 : (10 : ℝ) ^ (8 : ℕ) ≤ Pa.N := by
    have hp : (10 : ℝ) ^ (8 : ℕ) ≤ (Pa.N ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hle 8
    have h3 : (Pa.N ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = Pa.N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      rw [show ((1 : ℝ) / 8 * ((8 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]
    linarith [hp, h3.le, h3.ge]
  have hlog : Real.log ((10 : ℝ) ^ (8 : ℕ)) ≤ Real.log Pa.N :=
    Real.log_le_log (by positivity) hN8
  have h1 : (1 : ℝ) ≤ Real.log ((10 : ℝ) ^ (8 : ℕ)) := by
    have hexp : Real.exp 1 ≤ (10 : ℝ) ^ (8 : ℕ) := by
      have h2 : (2.7182818286 : ℝ) ≤ (10 : ℝ) ^ (8 : ℕ) := by norm_num
      linarith [Real.exp_one_lt_d9]
    have hh := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at hh
  linarith

/-- Sub-multiplicativity of `τ` along the `lcm`: `τ(lcm d e) ≤ τ d · τ e`. -/
lemma card_divisors_lcm_le_sm (d e : ℕ) :
    (Nat.lcm d e).divisors.card ≤ d.divisors.card * e.divisors.card := by
  rcases eq_or_ne d 0 with hd | hd
  · subst hd; simp [Nat.divisors_zero]
  rcases eq_or_ne e 0 with he | he
  · subst he; simp [Nat.divisors_zero]
  have hde : d * e ≠ 0 := Nat.mul_ne_zero hd he
  have hdvd : Nat.lcm d e ∣ d * e := Nat.lcm_dvd (Nat.dvd_mul_right d e) (Nat.dvd_mul_left e d)
  have h1 : (Nat.lcm d e).divisors.card ≤ (d * e).divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hde hdvd)
  have h2 : (d * e).divisors.card ≤ d.divisors.card * e.divisors.card := by
    rw [Nat.divisors_mul]; exact Finset.card_mul_le
  exact le_trans h1 h2

/-- The unweighted double `lcm`-divisor sum: `Σ_{d,e ≤ K} τ(d)⁸τ(e)⁸τ(lcm d e) ≤ C K²(log K + 2)^{2^10}`. -/
lemma lcmTauBound_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
      (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((Nat.lcm d e).divisors.card : ℕ) : ℝ))
        ≤ C * (K : ℝ) ^ (2 : ℕ) * (Real.log (K : ℝ) + 2) ^ (1024 : ℕ) := by
  obtain ⟨C9, hC9pos, hC9⟩ := Work.FIArea2.sum_tau_pow_le 9
  refine ⟨C9 ^ 2, by positivity, fun K => ?_⟩
  obtain ⟨Lg, hLg⟩ : ∃ L : ℝ, L = Real.log (K : ℝ) + 2 := ⟨_, rfl⟩
  have hLg0 : (0 : ℝ) ≤ Lg := by
    rw [hLg]
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0; norm_num
    · have hx : (0:ℝ) ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast hKpos)
      linarith
  have hC9' : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)))
      ≤ C9 * (K : ℝ) * Lg ^ (2 ^ 9) := by
    rw [hLg]; exact hC9 K
  have hterm : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (((Nat.lcm d e).divisors.card : ℕ) : ℝ))
      ≤ (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)))
        * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ))) := by
    calc (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((Nat.lcm d e).divisors.card : ℕ) : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
            ((((d.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)) := by
          refine Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun e _ => ?_))
          have hlcm : (((Nat.lcm d e).divisors.card : ℕ) : ℝ)
              ≤ (((d.divisors.card : ℕ) : ℝ)) * (((e.divisors.card : ℕ) : ℝ)) := by
            exact_mod_cast card_divisors_lcm_le_sm d e
          calc ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * (((Nat.lcm d e).divisors.card : ℕ) : ℝ)
              ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * ((((d.divisors.card : ℕ) : ℝ)) * (((e.divisors.card : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left hlcm (by positivity)
            _ = ((((d.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)) := by
                ring
      _ = (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ))) := by
          rw [Finset.sum_mul_sum]
  calc (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (((Nat.lcm d e).divisors.card : ℕ) : ℝ))
      ≤ (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ)))
          * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (9 : ℕ))) := hterm
    _ ≤ (C9 * (K : ℝ) * Lg ^ (2 ^ 9)) * (C9 * (K : ℝ) * Lg ^ (2 ^ 9)) := by
        refine mul_le_mul hC9' hC9' (Finset.sum_nonneg (fun n _ => by positivity)) ?_
        exact mul_nonneg (mul_nonneg hC9pos.le (Nat.cast_nonneg K)) (pow_nonneg hLg0 _)
    _ = C9 ^ 2 * (K : ℝ) ^ (2 : ℕ) * (Real.log (K : ℝ) + 2) ^ (1024 : ℕ) := by
        rw [show (2 : ℕ) ^ 9 = 512 by norm_num, ← hLg]
        ring

/-- The number of points of the polar box with `L ∣ |z|²` is at most
`π u² τ(L)/L + 80 u τ(L)/√L + τ(L)`, `u = θ√N`. -/
lemma card_filter_lcm_le (Pa : Work.FITop.Params) (φ : ℝ) (L : ℕ) (hL : 1 ≤ L) :
    ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => L ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((L.divisors.card : ℝ) / (L : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((L.divisors.card : ℝ) / Real.sqrt (L : ℝ))
        + (L.divisors.card : ℝ) := by
  have h := Work.FIArea3.JointCount.card_filter_le_le_arith Pa φ 0 L 1 hL (le_refl 1)
  have hcard : (Work.FIArea3.JointCount.pairBoxFinset Pa φ 0 L 1).card
      = ((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => L ∣ Work.FIPlan.gnorm z)).card := by
    unfold Work.FIArea3.JointCount.pairBoxFinset
    congr 1
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd _⟩
  rwa [hcard] at h

/-- Splitting a nested double sum of a sum of three products. -/
lemma sum3_nested {ι κ : Type*} (s : Finset ι) (t : Finset κ) (F P Q R : ι → κ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, F i j * (P i j + Q i j + R i j))
      = (∑ i ∈ s, ∑ j ∈ t, F i j * P i j)
        + ((∑ i ∈ s, ∑ j ∈ t, F i j * Q i j) + (∑ i ∈ s, ∑ j ∈ t, F i j * R i j)) := by
  have hinner : ∀ i, (∑ j ∈ t, F i j * (P i j + Q i j + R i j))
      = (∑ j ∈ t, F i j * P i j) + ((∑ j ∈ t, F i j * Q i j) + (∑ j ∈ t, F i j * R i j)) := by
    intro i
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  calc (∑ i ∈ s, ∑ j ∈ t, F i j * (P i j + Q i j + R i j))
      = ∑ i ∈ s, ((∑ j ∈ t, F i j * P i j)
          + ((∑ j ∈ t, F i j * Q i j) + (∑ j ∈ t, F i j * R i j))) :=
        Finset.sum_congr rfl (fun i _ => hinner i)
    _ = (∑ i ∈ s, ∑ j ∈ t, F i j * P i j)
          + ((∑ i ∈ s, ∑ j ∈ t, F i j * Q i j) + (∑ i ∈ s, ∑ j ∈ t, F i j * R i j)) := by
        simp only [Finset.sum_add_distrib]

/-- Factoring a constant out of a nested double sum. -/
lemma sum2_mul_const {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ℝ) (G H : ι → κ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, G i j * (c * H i j)) = c * (∑ i ∈ s, ∑ j ∈ t, G i j * H i j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

namespace Work.FIArea3

set_option maxHeartbeats 1000000

/-- **The second moment of `τ(|z|²)` over the polar box.** With `u = θ√N` and under
`u ≥ N^{3/8}` there is `C > 0` with `Σ_{z ∈ polar box} τ(|z|²)² ≤ C·u²·(log N)^{2^18}`.

Proof route: FI Lemma 2.2 with `k = 4` (`Work.FIArea3.JointCount.tau_le_sum_Icc_aux`) truncates
`τ(|z|²)` at `K₁ = ⌈(2N)^{1/4}⌉`, the block count
`#{z ∈ polar box : m ∣ |z|²} ≤ πu²τ(m)/m + 80uτ(m)/√m + τ(m)` is
`Work.FIArea3.JointCount.card_filter_le_le_arith` (with `e = 1`, `pairBoxFinset Pa φ z₁ m 1`),
and the resulting sums over the `lcm` are controlled by `gcdTauSumLe` and `sum_tau_pow_div_le`;
the errors `80u·K₁^{3/2}`, `K₁²` are `≤ u²·N^{-1/8}` because `θ ≥ N^{-1/8}`.  (The truth is
`≈ u²(log N)^3`, so the exponent `2^18` is generous.) -/
theorem secondMomentCore :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ 2 * (Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
  obtain ⟨CA, hCApos, hCA⟩ := lcmTauDivBound
  obtain ⟨CB, hCBpos, hCB⟩ := lcmTauSqrtBound
  obtain ⟨CC, hCCpos, hCC⟩ := lcmTauBound_aux
  refine ⟨65536 * (Real.pi * CA + 640 * CB + 8 * CC) * (4 : ℝ) ^ ((2 : ℕ) ^ (18 : ℕ)),
    by positivity, ?_⟩
  intro Pa φ h
  have hlogN : 1 ≤ Real.log Pa.N := one_le_log_N' Pa h
  have hlogN0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one hlogN
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  set K : ℕ := Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) with hK
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  have hu1 : (1 : ℝ) ≤ u := by
    rw [hu]; exact le_trans (Real.one_le_rpow Pa.hN1 (by norm_num)) h
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu1
  -- ### the size bounds for `K`
  have hKm : (K : ℝ) * Real.sqrt (K : ℝ) ≤ 8 * u := by
    set a : ℝ := (2 * Pa.N) ^ ((1 : ℝ) / 4) with ha
    have ha1 : (1 : ℝ) ≤ a := Real.one_le_rpow (by linarith) (by norm_num)
    have hapos : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
    have hKle : (K : ℝ) ≤ 2 * a := by
      have h1 : (K : ℝ) < a + 1 := by
        rw [hK, ha]; exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
      linarith
    have hsqrtK : Real.sqrt (K : ℝ) ≤ 2 * a ^ ((1 : ℝ) / 2) := by
      have h2 : Real.sqrt (K : ℝ) ≤ Real.sqrt (2 * a) := Real.sqrt_le_sqrt hKle
      have h3 : Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a := Real.sqrt_mul (by norm_num) a
      have h4 : Real.sqrt a = a ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow a
      have h5 : Real.sqrt 2 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
        exact Real.sqrt_le_sqrt (by norm_num)
      rw [h3, h4] at h2
      nlinarith [h2, h5, Real.sqrt_nonneg a, Real.sqrt_nonneg 2]
    have hprod : (K : ℝ) * Real.sqrt (K : ℝ) ≤ (2 * a) * (2 * a ^ ((1 : ℝ) / 2)) :=
      mul_le_mul hKle hsqrtK (Real.sqrt_nonneg _) (by positivity)
    have ha32 : a * a ^ ((1 : ℝ) / 2) = (2 * Pa.N) ^ ((3 : ℝ) / 8) := by
      have h1 : a * a ^ ((1 : ℝ) / 2) = a ^ ((3 : ℝ) / 2) := by
        nth_rewrite 1 [← Real.rpow_one a]
        rw [← Real.rpow_add hapos]
        congr 1
        norm_num
      have h2 : a ^ ((3 : ℝ) / 2) = (2 * Pa.N) ^ ((3 : ℝ) / 8) := by
        rw [ha, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 2 * Pa.N)]
        congr 1
        norm_num
      exact h1.trans h2
    have hsplit2 : (2 * Pa.N) ^ ((3 : ℝ) / 8)
        = (2 : ℝ) ^ ((3 : ℝ) / 8) * Pa.N ^ ((3 : ℝ) / 8) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h2pow : (2 : ℝ) ^ ((3 : ℝ) / 8) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : ((3:ℝ) / 8) ≤ 1)
      rwa [Real.rpow_one] at h
    have hN38 : Pa.N ^ ((3 : ℝ) / 8) ≤ u := by rw [hu]; exact h
    calc (K : ℝ) * Real.sqrt (K : ℝ) ≤ (2 * a) * (2 * a ^ ((1 : ℝ) / 2)) := hprod
      _ = 4 * (a * a ^ ((1 : ℝ) / 2)) := by ring
      _ = 4 * (2 * Pa.N) ^ ((3 : ℝ) / 8) := by rw [ha32]
      _ = 4 * ((2 : ℝ) ^ ((3 : ℝ) / 8) * Pa.N ^ ((3 : ℝ) / 8)) := by rw [hsplit2]
      _ ≤ 4 * (2 * Pa.N ^ ((3 : ℝ) / 8)) := by
          have h2n0 : (0 : ℝ) ≤ Pa.N ^ ((3 : ℝ) / 8) := Real.rpow_nonneg (by linarith) _
          nlinarith [h2pow, h2n0]
      _ ≤ 8 * u := by linarith [hN38]
  have hKs : (K : ℝ) ^ 2 ≤ 8 * u ^ 2 := by
    have ha1 : (1 : ℝ) ≤ (2 * Pa.N) ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by linarith) (by norm_num)
    have hKle : (K : ℝ) ≤ 2 * (2 * Pa.N) ^ ((1 : ℝ) / 4) := by
      have h1 : (K : ℝ) < (2 * Pa.N) ^ ((1 : ℝ) / 4) + 1 := by
        rw [hK]; exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
      linarith
    have hsq : (K : ℝ) ^ 2 ≤ (2 * (2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg K) hKle 2
    have hval : (2 * (2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ 2 = 4 * Real.sqrt (2 * Pa.N) := by
      have h0 : (0 : ℝ) ≤ 2 * Pa.N := by linarith
      have ha2 : ((2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) = (2 * Pa.N) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
        norm_num
      rw [mul_pow, ha2, ← Real.sqrt_eq_rpow]
      norm_num
    have hsqrt2N : Real.sqrt (2 * Pa.N) = Real.sqrt 2 * Real.sqrt Pa.N :=
      Real.sqrt_mul (by norm_num) Pa.N
    have hu2 : Real.sqrt Pa.N ≤ u ^ 2 := by
      have h' : Pa.N ^ ((3 : ℝ) / 8) ≤ u := by rw [hu]; exact h
      have h1 : Pa.N ^ ((3 : ℝ) / 4) ≤ u ^ 2 := by
        have hh := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Pa.N) _) h' 2
        have hrw : (Pa.N ^ ((3 : ℝ) / 8)) ^ (2 : ℕ) = Pa.N ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ Pa.N)]
          congr 1
          norm_num
        rw [hrw] at hh
        exact hh
      have h2 : Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hspos : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
    calc (K : ℝ) ^ 2 ≤ (2 * (2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ 2 := hsq
      _ = 4 * Real.sqrt (2 * Pa.N) := hval
      _ = 4 * (Real.sqrt 2 * Real.sqrt Pa.N) := by rw [hsqrt2N]
      _ ≤ 4 * (2 * u ^ 2) := by
          have h1 : Real.sqrt 2 * Real.sqrt Pa.N ≤ 2 * Real.sqrt Pa.N :=
            mul_le_mul_of_nonneg_right hsqrt2 hspos
          have h2 : (2 : ℝ) * Real.sqrt Pa.N ≤ 2 * u ^ 2 :=
            mul_le_mul_of_nonneg_left hu2 (by norm_num : (0:ℝ) ≤ 2)
          linarith
      _ = 8 * u ^ 2 := by ring
  -- ### truncation
  have htrunc : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
      (Work.FIPlan.gnorm z : ℝ) ≤ (K : ℝ) ^ (4 : ℕ) := by
    intro z hz
    rw [Work.FIArea3.mem_polarBoxFinset] at hz
    obtain ⟨_, hin⟩ := hz
    have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hin.2.2.1
    have hθ1 : Pa.θ ≤ 1 := theta_le_one' Pa
    have h2N : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by nlinarith [hgn, hθ1, hN1]
    have hpow : (2 * Pa.N : ℝ) = ((2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 2 * Pa.N)]
      rw [show ((1 : ℝ) / 4 * ((4 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]
    rw [hpow] at h2N
    have hceil : (2 * Pa.N) ^ ((1 : ℝ) / 4) ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
    exact le_trans h2N (pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hceil 4)
  have hred := Work.FIArea3.tauSqLcmReduction (Work.FIArea3.polarBoxFinset Pa φ)
    Work.FIPlan.gnorm K htrunc
  -- ### termwise counting
  have hstep : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (((((Work.FIArea3.polarBoxFinset Pa φ).filter
              (fun z => Nat.lcm d e ∣ Work.FIPlan.gnorm z)).card : ℕ)) : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (Real.pi * u ^ 2 * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ))
             + 80 * u * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ))
             + (((Nat.lcm d e).divisors.card : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => ?_))
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hlcm0 : Nat.lcm d e ≠ 0 := by
      intro hh; rcases Nat.lcm_eq_zero_iff.mp hh with h' | h' <;> omega
    have hL1 : 1 ≤ Nat.lcm d e := Nat.pos_of_ne_zero hlcm0
    have hcount := card_filter_lcm_le Pa φ (Nat.lcm d e) hL1
    rw [hu]
    exact mul_le_mul_of_nonneg_left hcount (by positivity)
  -- ### the three divisor sums
  set TA : ℝ := ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
      ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
        * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ)) with hTA
  set TB : ℝ := ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
      ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
        * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ)) with hTB
  set TC : ℝ := ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
      ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
        * (((Nat.lcm d e).divisors.card : ℕ) : ℝ) with hTC
  -- ### the split
  have hsplit : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (Real.pi * u ^ 2 * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ))
             + 80 * u * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ))
             + (((Nat.lcm d e).divisors.card : ℕ) : ℝ)))
      = Real.pi * u ^ 2 * TA + 80 * u * TB + TC := by
    rw [hTA, hTB, hTC]
    rw [sum3_nested]
    rw [sum2_mul_const, sum2_mul_const]
    ring
  -- ### the log atom
  obtain ⟨Lg, hLg⟩ : ∃ L : ℝ, L = Real.log (K : ℝ) + 2 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by
      rw [hK]
      exact le_trans (Real.one_le_rpow (by linarith : (1:ℝ) ≤ 2 * Pa.N) (by norm_num)) (Nat.le_ceil _)
    exact_mod_cast h1
  have hlogK : Lg ≤ 4 * Real.log Pa.N := by
    rw [hLg]
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hK1)
    have hKle : (K : ℝ) ≤ 2 * (2 * Pa.N) ^ ((1 : ℝ) / 4) := by
      have h1 : (K : ℝ) < (2 * Pa.N) ^ ((1 : ℝ) / 4) + 1 := by
        rw [hK]; exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
      have h2 : (1 : ℝ) ≤ (2 * Pa.N) ^ ((1 : ℝ) / 4) :=
        Real.one_le_rpow (by linarith) (by norm_num)
      linarith
    have hbase : (0 : ℝ) < (2 * Pa.N) ^ ((1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hlogKle : Real.log (K : ℝ) ≤ Real.log (2 * (2 * Pa.N) ^ ((1 : ℝ) / 4)) :=
      Real.log_le_log hKpos hKle
    have hm : Real.log (2 * (2 * Pa.N) ^ ((1 : ℝ) / 4))
        = Real.log 2 + (1 / 4) * Real.log (2 * Pa.N) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hbase), Real.log_rpow (by linarith)]
    have hm2 : Real.log (2 * Pa.N) = Real.log 2 + Real.log Pa.N :=
      Real.log_mul (by norm_num) (by linarith)
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
    have hlog20 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith [hlogKle, hm, hm2]
  have hbase1 : (1 : ℝ) ≤ Lg := by
    have : (0 : ℝ) ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
    rw [hLg]; linarith
  have hTAle : TA ≤ CA * Lg ^ (132096 : ℕ) := by
    rw [hTA, hLg]; exact hCA K
  have hTBle : TB ≤ CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ) := by
    rw [hTB, hLg]; exact hCB K
  have hTCle : TC ≤ CC * (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ) := by
    rw [hTC, hLg]; exact hCC K
  have hp : Lg ^ (132096 : ℕ) ≤ Lg ^ ((2 : ℕ) ^ (18 : ℕ)) :=
    pow_le_pow_right₀ hbase1 (by norm_num)
  have hp2 : Lg ^ (1024 : ℕ) ≤ Lg ^ ((2 : ℕ) ^ (18 : ℕ)) :=
    pow_le_pow_right₀ hbase1 (by norm_num)
  -- ### key bounds
  have hA2 : Real.pi * u ^ 2 * TA ≤ Real.pi * u ^ 2 * (CA * Lg ^ (132096 : ℕ)) :=
    mul_le_mul_of_nonneg_left hTAle (by positivity)
  have hB2 : 80 * u * TB
      ≤ 80 * u * (CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ)) :=
    mul_le_mul_of_nonneg_left hTBle (by positivity)
  have hKeyA : Real.pi * u ^ 2 * (CA * Lg ^ (132096 : ℕ))
      ≤ Real.pi * CA * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by
    calc Real.pi * u ^ 2 * (CA * Lg ^ (132096 : ℕ))
        = Real.pi * CA * u ^ 2 * Lg ^ (132096 : ℕ) := by ring
      _ ≤ Real.pi * CA * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
  have hKeyB : 80 * u * (CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ))
      ≤ 80 * (8 * CB) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by
    have hKm' : (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ)
        ≤ 8 * u * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) :=
      mul_le_mul hKm hp2 (pow_nonneg (le_trans zero_le_one hbase1) _) (mul_nonneg (by norm_num) hu0)
    calc 80 * u * (CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ))
        = 80 * CB * (u * ((K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ))) := by ring
      _ ≤ 80 * CB * (u * (8 * u * Lg ^ ((2 : ℕ) ^ (18 : ℕ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKm' hu0) (by positivity)
      _ = 80 * (8 * CB) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by ring
  have hKeyC : CC * (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ)
      ≤ (8 * CC) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by
    have hKs' : (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ)
        ≤ 8 * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) :=
      mul_le_mul hKs hp2 (pow_nonneg (le_trans zero_le_one hbase1) _)
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) (sq_nonneg u))
    calc CC * (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ)
        = CC * ((K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ)) := by ring
      _ ≤ CC * (8 * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ))) :=
          mul_le_mul_of_nonneg_left hKs' hCCpos.le
      _ = (8 * CC) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by ring
  have hfac1 : (0 : ℝ) ≤ 65536 * (Real.pi * CA + 640 * CB + 8 * CC) * u ^ 2 := by
    have hc : (0 : ℝ) < Real.pi * CA + 640 * CB + 8 * CC := by
      have ha : (0 : ℝ) < Real.pi * CA := by positivity
      have hb : (0 : ℝ) < 640 * CB := by linarith [hCBpos]
      have hd : (0 : ℝ) < 8 * CC := by linarith [hCCpos]
      linarith
    positivity
  have hLg0' : (0 : ℝ) ≤ Lg := le_trans zero_le_one hbase1
  have hkey : Lg ^ ((2 : ℕ) ^ (18 : ℕ))
      ≤ (4 : ℝ) ^ ((2 : ℕ) ^ (18 : ℕ)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
    calc Lg ^ ((2 : ℕ) ^ (18 : ℕ)) ≤ (4 * Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
          pow_le_pow_left₀ hLg0' hlogK ((2 : ℕ) ^ (18 : ℕ))
      _ = (4 : ℝ) ^ ((2 : ℕ) ^ (18 : ℕ)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
          mul_pow _ _ _
  -- ### assembly
  calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ 65536 * (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((((Work.FIArea3.polarBoxFinset Pa φ).filter
                (fun z => Nat.lcm d e ∣ Work.FIPlan.gnorm z)).card : ℕ)) : ℝ)) := hred
    _ ≤ 65536 * (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (Real.pi * u ^ 2 * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ))
               + 80 * u * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ))
               + (((Nat.lcm d e).divisors.card : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 65536 * (Real.pi * u ^ 2 * TA + 80 * u * TB + TC) := by rw [hsplit]
    _ ≤ 65536 * (Real.pi * u ^ 2 * (CA * Lg ^ (132096 : ℕ))
          + 80 * u * (CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ))
          + CC * (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ)) := by
        have hsum : Real.pi * u ^ 2 * TA + 80 * u * TB + TC
            ≤ Real.pi * u ^ 2 * (CA * Lg ^ (132096 : ℕ))
              + 80 * u * (CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ))
              + CC * (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ) := by
          linarith [hA2, hB2, hTCle]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 65536 * (Real.pi * CA * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ))
          + 80 * (8 * CB) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ))
          + (8 * CC) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ))) := by
        have hsum : Real.pi * u ^ 2 * (CA * Lg ^ (132096 : ℕ))
              + 80 * u * (CB * (K : ℝ) * Real.sqrt (K : ℝ) * Lg ^ (1024 : ℕ))
              + CC * (K : ℝ) ^ (2 : ℕ) * Lg ^ (1024 : ℕ)
            ≤ Real.pi * CA * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ))
              + 80 * (8 * CB) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ))
              + (8 * CC) * u ^ 2 * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by
          linarith [hKeyA, hKeyB, hKeyC]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 65536 * (Real.pi * CA + 640 * CB + 8 * CC) * u ^ 2
          * Lg ^ ((2 : ℕ) ^ (18 : ℕ)) := by ring
    _ ≤ 65536 * (Real.pi * CA + 640 * CB + 8 * CC) * u ^ 2
          * ((4 : ℝ) ^ ((2 : ℕ) ^ (18 : ℕ)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ))) :=
        mul_le_mul_of_nonneg_left hkey hfac1
    _ = 65536 * (Real.pi * CA + 640 * CB + 8 * CC) * (4 : ℝ) ^ ((2 : ℕ) ^ (18 : ℕ))
          * u ^ 2 * (Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ)) := by ring

end Work.FIArea3

end

end Work.FIArea3

namespace Work.FIArea3

/-- Alias of `Work.FIArea3.Work.FIArea3.secondMomentCore` under the requested name. -/
alias secondMomentCore := _root_.Work.FIArea3.Work.FIArea3.secondMomentCore

end Work.FIArea3
