import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.pairSumContent
import Submission.Work.FIArea3.polarBox_tau_avg
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea3.JointCount.card_filter_le_class

set_option maxHeartbeats 1000000

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable


lemma gContent_sq_dvd_gnorm (z : GaussianInt) : (Work.FIArea3.gContent z)^2 ∣ Work.FIPlan.gnorm z := by
  have hre : (Work.FIArea3.gContent z : ℤ) ∣ z.re := Work.FIArea3.gContent_dvd_re z
  have him : (Work.FIArea3.gContent z : ℤ) ∣ z.im := Work.FIArea3.gContent_dvd_im z
  have h1 : ((Work.FIArea3.gContent z : ℤ))^2 ∣ z.re^2 := pow_dvd_pow_of_dvd hre 2
  have h2 : ((Work.FIArea3.gContent z : ℤ))^2 ∣ z.im^2 := pow_dvd_pow_of_dvd him 2
  have h3 : ((Work.FIArea3.gContent z : ℤ))^2 ∣ z.re^2 + z.im^2 := dvd_add h1 h2
  rw [← Int.ofNat_dvd, Work.FIArea3.JointCount.gnorm_eq_re_im_class]
  push_cast
  exact h3

lemma gnorm_pos_of_mem (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ Work.FIArea3.polarBoxFinset Pa φ) : 0 < Work.FIPlan.gnorm z := by
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hgn : Pa.N < (Work.FIPlan.gnorm z : ℝ) := (Work.FIArea3.mem_polarBoxFinset.mp hz).2.2.1
  have : (0:ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
  exact_mod_cast this

lemma gContent_ne_zero_of_mem (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ Work.FIArea3.polarBoxFinset Pa φ) : Work.FIArea3.gContent z ≠ 0 := by
  intro h
  have h0 : Work.FIPlan.gnorm z = 0 := by
    have hd := Work.FIArea3.gContent_dvd_gnorm z
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  exact Nat.lt_irrefl 0 (h0 ▸ gnorm_pos_of_mem Pa φ hz)

lemma gContent_le_D (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ Work.FIArea3.polarBoxFinset Pa φ) :
    Work.FIArea3.gContent z ≤ Nat.ceil (Real.sqrt (2 * Pa.N)) := by
  have hzi := (Work.FIArea3.mem_polarBoxFinset.mp hz).2
  have hle : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hzi.2.2.1
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea3.theta_le_one_param Pa
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hpos : 0 < Work.FIPlan.gnorm z := gnorm_pos_of_mem Pa φ hz
  have hle2 : ((Work.FIArea3.gContent z : ℕ) : ℝ)^2 ≤ 2 * Pa.N := by
    have h1 : (((Work.FIArea3.gContent z)^2 : ℕ) : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hpos (gContent_sq_dvd_gnorm z)
    have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθ1, hN1]
    push_cast at h1 ⊢
    linarith
  have h3 : ((Work.FIArea3.gContent z : ℕ) : ℝ) ≤ Real.sqrt (2 * Pa.N) := by
    calc ((Work.FIArea3.gContent z : ℕ) : ℝ)
        = Real.sqrt (((Work.FIArea3.gContent z : ℕ) : ℝ)^2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ Real.sqrt (2 * Pa.N) := Real.sqrt_le_sqrt hle2
  have h4 : ((Work.FIArea3.gContent z : ℕ) : ℝ) ≤ (Nat.ceil (Real.sqrt (2*Pa.N)) : ℝ) :=
    le_trans h3 (Nat.le_ceil _)
  exact_mod_cast h4

lemma divisors_gContent_eq (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ Work.FIArea3.polarBoxFinset Pa φ) :
    (Work.FIArea3.gContent z).divisors
      = (Finset.Icc 1 (Nat.ceil (Real.sqrt (2 * Pa.N)))).filter
          (fun d => d ∣ Work.FIArea3.gContent z) := by
  have hD := gContent_le_D Pa φ hz
  have hc0 := gContent_ne_zero_of_mem Pa φ hz
  have hcpos : 0 < Work.FIArea3.gContent z := Nat.pos_of_ne_zero hc0
  ext d
  rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hcpos, (Nat.le_of_dvd hcpos hdvd).trans hD⟩, hdvd⟩
  · rintro ⟨⟨hd1, hd2⟩, hdvd⟩
    exact ⟨hdvd, hc0⟩

/-- Termwise bound used in the content second moment. -/
lemma summand_bound (d : ℕ) (hd : 1 ≤ d) (u : ℝ) (hu : 0 ≤ u) :
    (d.divisors.card : ℝ)^2 * (Real.pi * u^2 * (((d^2).divisors.card : ℝ) / (d:ℝ)^2)
        + 80 * u * (((d^2).divisors.card : ℝ) / (d:ℝ)) + ((d^2).divisors.card : ℝ))
    ≤ Real.pi * u^2 * ((d.divisors.card : ℝ)^4 / (d:ℝ))
      + 80 * u * ((d.divisors.card : ℝ)^4 / (d:ℝ)) + (d.divisors.card : ℝ)^4 := by
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hdle : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hτ2 : (0:ℝ) ≤ (d.divisors.card : ℝ)^2 := by positivity
  have htau : ((d^2).divisors.card : ℝ) ≤ (d.divisors.card : ℝ)^2 := by
    have h : (d^2).divisors.card ≤ d.divisors.card ^ 2 := by
      have hc := Finset.card_mul_le (s := d.divisors) (t := d.divisors)
      rw [← Nat.divisors_mul] at hc
      simpa [pow_two] using hc
    exact_mod_cast h
  have hC : (d.divisors.card : ℝ)^2 * ((d^2).divisors.card : ℝ) ≤ (d.divisors.card : ℝ)^4 := by
    have h := mul_le_mul_of_nonneg_left htau hτ2
    have h2 : (d.divisors.card : ℝ)^2 * (d.divisors.card : ℝ)^2 = (d.divisors.card : ℝ)^4 := by ring
    rw [h2] at h
    exact h
  have hA : (d.divisors.card : ℝ)^2 * (Real.pi * u^2 * (((d^2).divisors.card : ℝ) / (d:ℝ)^2))
      ≤ Real.pi * u^2 * ((d.divisors.card : ℝ)^4 / (d:ℝ)) := by
    have e1 : (d.divisors.card : ℝ)^2 * (Real.pi * u^2 * (((d^2).divisors.card : ℝ) / (d:ℝ)^2))
        = Real.pi * u^2 * (((d.divisors.card : ℝ)^2 * ((d^2).divisors.card : ℝ)) / (d:ℝ)^2) := by
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ((d.divisors.card : ℝ)^2 * ((d^2).divisors.card : ℝ)) / (d:ℝ)^2
        ≤ ((d.divisors.card : ℝ)^4) / (d:ℝ)^2 :=
          div_le_div_of_nonneg_right (by linarith [hC]) (by positivity)
      _ ≤ ((d.divisors.card : ℝ)^4) / (d:ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hdpos hdle
  have hB : (d.divisors.card : ℝ)^2 * (80 * u * (((d^2).divisors.card : ℝ) / (d:ℝ)))
      ≤ 80 * u * ((d.divisors.card : ℝ)^4 / (d:ℝ)) := by
    have e1 : (d.divisors.card : ℝ)^2 * (80 * u * (((d^2).divisors.card : ℝ) / (d:ℝ)))
        = 80 * u * (((d.divisors.card : ℝ)^2 * ((d^2).divisors.card : ℝ)) / (d:ℝ)) := by
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hu)
    exact div_le_div_of_nonneg_right (by linarith [hC]) hdpos.le
  have hsplit : (d.divisors.card : ℝ)^2 * (Real.pi * u^2 * (((d^2).divisors.card : ℝ) / (d:ℝ)^2)
        + 80 * u * (((d^2).divisors.card : ℝ) / (d:ℝ)) + ((d^2).divisors.card : ℝ))
      = (d.divisors.card : ℝ)^2 * (Real.pi * u^2 * (((d^2).divisors.card : ℝ) / (d:ℝ)^2))
        + (d.divisors.card : ℝ)^2 * (80 * u * (((d^2).divisors.card : ℝ) / (d:ℝ)))
        + (d.divisors.card : ℝ)^2 * ((d^2).divisors.card : ℝ) := by ring
  rw [hsplit]
  linarith [hA, hB, hC]

lemma polarBox_content_tau_sq_avg :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIArea3.gContent z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ 2 * (Real.log Pa.N) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FIArea2.sum_tau_pow_le 4
  obtain ⟨C4d, hC4dpos, hC4d⟩ := Work.FIArea2.sum_tau_pow_div_le 4
  have hMpos : (0:ℝ) < max C4d C4 := lt_of_lt_of_le hC4dpos (le_max_left _ _)
  have hM0 : (0:ℝ) ≤ max C4d C4 := hMpos.le
  have hCpos : (0:ℝ) < max C4d C4 * 9 ^ (16:ℕ) * (Real.pi + 84) + 1 := by
    have h2 : (0:ℝ) < 9 ^ (16:ℕ) := by positivity
    have h3 : (0:ℝ) < Real.pi + 84 := by positivity
    have h4 : (0:ℝ) < max C4d C4 * 9 ^ (16:ℕ) * (Real.pi + 84) := mul_pos (mul_pos hMpos h2) h3
    linarith
  refine ⟨max C4d C4 * 9 ^ (16:ℕ) * (Real.pi + 84) + 1, hCpos, ?_⟩
  intro Pa φ hhyp
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  set L : ℝ := Real.log Pa.N with hL
  set D : ℕ := Nat.ceil (Real.sqrt (2 * Pa.N)) with hD
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact Work.FIArea3.one_le_log_N_of_sharp hhyp
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hu_ge : Pa.N ^ ((3:ℝ)/8) ≤ u := by rw [hu]; exact hhyp
  have hu1 : 1 ≤ u := le_trans (Real.one_le_rpow hN1 (by norm_num)) hu_ge
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  have hu' : Pa.θ * Real.sqrt Pa.N = u := hu.symm
  have hsqN : Real.sqrt Pa.N ≤ u^2 := by
    have hpow : ((Pa.N:ℝ) ^ ((3:ℝ)/8))^2 ≤ u^2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) hu_ge 2
    have heq : ((Pa.N:ℝ) ^ ((3:ℝ)/8))^2 = (Pa.N:ℝ) ^ ((3:ℝ)/4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    have h34 : (Pa.N:ℝ) ^ ((1:ℝ)/2) ≤ (Pa.N:ℝ) ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    rw [Real.sqrt_eq_rpow]
    linarith
  have hDle : (D:ℝ) ≤ 4 * Real.sqrt Pa.N := by
    rw [hD]
    have h1 : ((Nat.ceil (Real.sqrt (2*Pa.N))) : ℝ) < Real.sqrt (2*Pa.N) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have h2 : (1:ℝ) ≤ Real.sqrt (2*Pa.N) := by rw [Real.one_le_sqrt]; linarith
    have h3 : Real.sqrt (2*Pa.N) = Real.sqrt 2 * Real.sqrt Pa.N := Real.sqrt_mul (by norm_num) _
    have h4 : Real.sqrt 2 ≤ 2 := by
      have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, h]
    have h5 : Real.sqrt (2*Pa.N) ≤ 2 * Real.sqrt Pa.N := by
      rw [h3]; nlinarith [h4, Real.sqrt_nonneg Pa.N]
    linarith
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by
    rw [hD]
    have h2 : (1:ℝ) ≤ Real.sqrt (2*Pa.N) := by rw [Real.one_le_sqrt]; linarith
    exact le_trans h2 (Nat.le_ceil _)
  have hlogD : Real.log (D:ℝ) + 2 ≤ 9 * L := by
    have hDpos : 0 < (D:ℝ) := lt_of_lt_of_le zero_lt_one hD1
    have hlog : Real.log (D:ℝ) ≤ Real.log (4 * Real.sqrt Pa.N) := Real.log_le_log hDpos hDle
    have hsplit : Real.log (4 * Real.sqrt Pa.N) = Real.log 4 + (1/2) * L := by
      rw [hL, Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hNpos).ne', Real.log_sqrt hNpos.le]
      ring
    have hlog4 : Real.log 4 ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
    rw [hsplit] at hlog
    linarith
  set K : ℝ := (Real.log (D:ℝ) + 2)^(16:ℕ) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK4 : K ≤ 9^(16:ℕ) * L^((2:ℕ)^(18:ℕ)) := by
    have hbase : 0 ≤ Real.log (D:ℝ) + 2 := by
      have h : 0 ≤ Real.log (D:ℝ) := Real.log_nonneg hD1
      linarith
    have hKD : K ≤ (9*L)^(16:ℕ) := by
      rw [hK]
      exact pow_le_pow_left₀ hbase hlogD 16
    calc K ≤ (9*L)^(16:ℕ) := hKD
      _ = 9^(16:ℕ) * L^(16:ℕ) := by rw [mul_pow]
      _ ≤ 9^(16:ℕ) * L^((2:ℕ)^(18:ℕ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_right₀ hL1 (by norm_num)
  have hcount : ∀ d ∈ Finset.Icc 1 D,
      ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ)
      ≤ Real.pi * u^2 * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)^2)
        + 80 * u * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)) + (((d^2).divisors.card : ℕ) : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hsub : (Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)
        ⊆ (Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d^2 ∣ Work.FIPlan.gnorm z) := by
      intro z hz
      obtain ⟨hzB, hzd⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzB, (pow_dvd_pow_of_dvd hzd 2).trans (gContent_sq_dvd_gnorm z)⟩
    have hcard : ((((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ)
        ≤ ((((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => d^2 ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hd2 : 1 ≤ d^2 := by
      calc (1:ℕ) = 1 * 1 := by norm_num
        _ ≤ d * d := Nat.mul_le_mul hd1 hd1
        _ = d^2 := by rw [pow_two]
    have hcd := Work.FIArea3.card_polarBox_filter_dvd_gnorm Pa φ (d^2) hd2
    have hsqd : (((d^2 : ℕ)) : ℝ) = (d:ℝ)^2 := by push_cast; ring
    have hsqrtsq : Real.sqrt (((d^2 : ℕ)) : ℝ) = (d:ℝ) := by
      rw [hsqd, Real.sqrt_sq (Nat.cast_nonneg d)]
    calc ((((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ)
        ≤ ((((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => d^2 ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := hcard
      _ ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((((d^2).divisors.card : ℕ) : ℝ) / (((d^2 : ℕ)) : ℝ))
            + 80 * (Pa.θ * Real.sqrt Pa.N) * ((((d^2).divisors.card : ℕ) : ℝ) / Real.sqrt (((d^2 : ℕ)) : ℝ))
            + (((d^2).divisors.card : ℕ) : ℝ) := hcd
      _ = Real.pi * u^2 * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)^2)
            + 80 * u * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)) + (((d^2).divisors.card : ℕ) : ℝ) := by
          rw [hu', hsqd, Real.sqrt_sq (Nat.cast_nonneg d)]
  have hpoint : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
      (((Work.FIArea3.gContent z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ ∑ d ∈ (Work.FIArea3.gContent z).divisors, ((d.divisors.card : ℝ))^2 := by
    intro z hz
    have hc0 : Work.FIArea3.gContent z ≠ 0 := gContent_ne_zero_of_mem Pa φ hz
    have hmem : Work.FIArea3.gContent z ∈ (Work.FIArea3.gContent z).divisors :=
      Nat.mem_divisors_self _ hc0
    have hle := Finset.single_le_sum (s := (Work.FIArea3.gContent z).divisors)
      (f := fun d => ((d.divisors.card : ℝ))^2) (fun d _ => by positivity) hmem
    simpa using hle
  have hswap : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ, ∑ d ∈ (Work.FIArea3.gContent z).divisors,
        ((d.divisors.card : ℝ))^2)
      = ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ) := by
    have hdiv : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ, (Work.FIArea3.gContent z).divisors
        = (Finset.Icc 1 D).filter (fun d => d ∣ Work.FIArea3.gContent z) := by
      intro z hz
      rw [hD]
      exact divisors_gContent_eq Pa φ hz
    calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ, ∑ d ∈ (Work.FIArea3.gContent z).divisors,
          ((d.divisors.card : ℝ))^2)
        = ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
            ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ Work.FIArea3.gContent z),
              ((d.divisors.card : ℝ))^2 := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [hdiv z hz]
      _ = ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ, ∑ d ∈ Finset.Icc 1 D,
            (if d ∣ Work.FIArea3.gContent z then ((d.divisors.card : ℝ))^2 else 0) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc 1 D, ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
            (if d ∣ Work.FIArea3.gContent z then ((d.divisors.card : ℝ))^2 else 0) := Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc 1 D,
            ∑ z ∈ (Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z),
              ((d.divisors.card : ℝ))^2 := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          rw [Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2
            * ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have h16 : (2:ℕ)^4 = 16 := by norm_num
  have hS1 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ)) ≤ C4d * K := by
    have h := hC4d D
    rw [h16] at h
    rw [hK]
    exact h
  have hS0 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4) ≤ C4 * (D:ℝ) * K := by
    have h := hC4 D
    rw [h16] at h
    rw [hK]
    exact h
  have h1 : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
        (((Work.FIArea3.gContent z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ) := by
    calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIArea3.gContent z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
            ∑ d ∈ (Work.FIArea3.gContent z).divisors, ((d.divisors.card : ℝ))^2 :=
          Finset.sum_le_sum (fun z hz => hpoint z hz)
      _ = _ := hswap
  have h2 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2 *
          (Real.pi * u^2 * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)^2)
            + 80 * u * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)) + (((d^2).divisors.card : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    exact mul_le_mul_of_nonneg_left (hcount d hd) (by positivity)
  have h3 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2 *
          (Real.pi * u^2 * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)^2)
            + 80 * u * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)) + (((d^2).divisors.card : ℕ) : ℝ)))
      ≤ ∑ d ∈ Finset.Icc 1 D, (Real.pi * u^2 * (((d.divisors.card : ℝ))^4 / (d:ℝ))
            + 80 * u * (((d.divisors.card : ℝ))^4 / (d:ℝ)) + ((d.divisors.card : ℝ))^4) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    exact summand_bound d (Finset.mem_Icc.mp hd).1 u hu0
  have h4 : (∑ d ∈ Finset.Icc 1 D, (Real.pi * u^2 * (((d.divisors.card : ℝ))^4 / (d:ℝ))
            + 80 * u * (((d.divisors.card : ℝ))^4 / (d:ℝ)) + ((d.divisors.card : ℝ))^4))
      = Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + 80 * u * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h5 : Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + 80 * u * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4)
      ≤ max C4d C4 * K * (Real.pi * u^2 + 80 * u + (D:ℝ)) := by
    have h6 : Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        ≤ Real.pi * u^2 * (max C4d C4 * K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hS1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0)
    have h7 : 80 * u * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        ≤ 80 * u * (max C4d C4 * K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hS1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0)
    have h8 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4) ≤ max C4d C4 * (D:ℝ) * K := by
      refine hS0.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg D)) hK0
    calc Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + 80 * u * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4)
        ≤ Real.pi * u^2 * (max C4d C4 * K) + 80 * u * (max C4d C4 * K) + max C4d C4 * (D:ℝ) * K := by
          linarith [h6, h7, h8]
      _ = max C4d C4 * K * (Real.pi * u^2 + 80 * u + (D:ℝ)) := by ring
  have huD : Real.pi * u^2 + 80 * u + (D:ℝ) ≤ (Real.pi + 84) * u^2 := by
    have h80 : 80 * u ≤ 80 * u^2 := by nlinarith [hu1]
    have hD4' : (D:ℝ) ≤ 4 * u^2 := by linarith
    nlinarith [h80, hD4']
  have hFinal : max C4d C4 * K * (Real.pi * u^2 + 80 * u + (D:ℝ))
      ≤ max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) * u^2 * L^((2:ℕ)^(18:ℕ)) := by
    have hA : max C4d C4 * K ≤ max C4d C4 * (9^(16:ℕ) * L^((2:ℕ)^(18:ℕ))) :=
      mul_le_mul_of_nonneg_left hK4 hM0
    have hmid : (0:ℝ) ≤ Real.pi * u^2 + 80 * u + (D:ℝ) := by positivity
    have hrhs : (0:ℝ) ≤ max C4d C4 * (9^(16:ℕ) * L^((2:ℕ)^(18:ℕ))) :=
      mul_nonneg hM0 (by positivity)
    calc max C4d C4 * K * (Real.pi * u^2 + 80 * u + (D:ℝ))
        = (max C4d C4 * K) * (Real.pi * u^2 + 80 * u + (D:ℝ)) := rfl
      _ ≤ (max C4d C4 * (9^(16:ℕ) * L^((2:ℕ)^(18:ℕ)))) * ((Real.pi + 84) * u^2) :=
          mul_le_mul hA huD hmid hrhs
      _ = max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) * u^2 * L^((2:ℕ)^(18:ℕ)) := by ring
  have hLast : max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) * u^2 * L^((2:ℕ)^(18:ℕ))
      ≤ (max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) + 1) * u^2 * L^((2:ℕ)^(18:ℕ)) := by
    have h1 : (0:ℝ) ≤ u^2 * L^((2:ℕ)^(18:ℕ)) := by positivity
    have h2 : (max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) + 1) * u^2 * L^((2:ℕ)^(18:ℕ))
        = max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) * u^2 * L^((2:ℕ)^(18:ℕ)) + u^2 * L^((2:ℕ)^(18:ℕ)) := by
      ring
    linarith [h1, h2.le, h2.ge]
  calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
        (((Work.FIArea3.gContent z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIArea3.gContent z)).card : ℕ) : ℝ) := h1
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^2 *
          (Real.pi * u^2 * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)^2)
            + 80 * u * ((((d^2).divisors.card : ℕ) : ℝ) / (d:ℝ)) + (((d^2).divisors.card : ℕ) : ℝ)) := h2
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (Real.pi * u^2 * (((d.divisors.card : ℝ))^4 / (d:ℝ))
            + 80 * u * (((d.divisors.card : ℝ))^4 / (d:ℝ)) + ((d.divisors.card : ℝ))^4) := h3
    _ = Real.pi * u^2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + 80 * u * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4 / (d:ℝ))
        + (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ))^4) := h4
    _ ≤ max C4d C4 * K * (Real.pi * u^2 + 80 * u + (D:ℝ)) := h5
    _ ≤ max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) * u^2 * L^((2:ℕ)^(18:ℕ)) := hFinal
    _ ≤ (max C4d C4 * 9^(16:ℕ) * (Real.pi + 84) + 1) * u^2 * L^((2:ℕ)^(18:ℕ)) := hLast

end

end Work.FIArea3
