import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6V.S16_char_bound_twoV
import Submission.Work.FIArea6c.S16_char_bound_twoP
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea6.S16Assembly
import Submission.Work.FIArea6.DetSum_le_of_chiBound
import Submission.Work.FIArea6.S16_elem_alt
import Submission.Work.FIArea6.S16_beta_mass6
import Submission.Work.FIArea6.S16_exp_arith
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6.S16_sum_chain
import Submission.Work.FIArea6.S16_final_arith
import Submission.Work.FIArea6.S16FcoefSum

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The main half of the §16 display in the clean (τ-vacuous) lane.**

This is the V-lane counterpart of `Work.FIArea6.S16_main_le_twoP`: the pin
`Pa.τ = tauOf Pa.x Asave` is replaced by the τ-vacuity hypothesis `TauVac Pa φ` (and the axis-free
polar box is carried as a hypothesis).  `S16_char_bound_twoV` bounds each character sum `S_χ^k(β)`
of the (16.11) expansion by `C·[exp(-ηc(4d)^{-ε}√logN) + exp(-ηlogN/logPz)]·4d·N·(logN)^6`
(exponent constant `c`, prefactor `C`), `DetSum_le_of_chiBound` turns that into `4d·B₀²` per modulus
and frequency, and the summations over `k` (`Σ_k 1/|k| ≪ log N`), over `d ≤ X`
(`Σ_{d≤X} φ(d)d² ≪ X⁴`) and over the frequencies (`|k| ≤ 2X³`) give `X⁵N²(log(2+N))^13` times the
exponentially small bracket, with `c1 := η·c·4^(-(1/(4·nuU)))/2` (so that
`exp(-ηc(4d)^{-ε}√logN) ≤ exp(-c1(logN)^{1/4})` for all `d ≤ X ≤ (logN)^{nuU}`) and `c2 := η/2`,
while the prefactor `C` is kept separate and propagates into the final constant. -/
theorem S16_main_le_twoV (h : Work.FIArea6V.Area5TwoV) (η : ℝ) (hη0 : 0 < η)
    (hη32 : η < 3 / 32) :
    ∃ C c1 c2 x0 : ℝ, 0 < C ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → Work.FIArea6V.TauVac Pa φ →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      1 ≤ X →
      (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      (X : ℝ) ^ 3 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
      ‖Work.FIArea6.Umain Pa X β‖
        ≤ C * ((Real.exp (-(c1 * (Real.log Pa.N) ^ ((1 : ℝ) / 4)))
              + Real.exp (-(c2 * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * (X : ℝ) ^ (5 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log (2 + Pa.N)) ^ (13 : ℕ)) := by
  have hfcoeffsum := Work.FIArea6.fcoeff_sum_le
  have hdet := Work.FIArea6.norm_DetSum_le
  have hphi1 := Work.FIArea6.totient_sum_le
  obtain ⟨Cm, hCmpos, hmass⟩ := Work.FIArea6.S16_beta_mass6
  obtain ⟨hnuUpos, hnuU1, hexpdom, hrpow⟩ := Work.FIArea6.S16_exp_arith
  obtain ⟨c0, Cp, x5, hc0pos, hCpPos, hx5pos, hchar⟩ := S16_char_bound_twoV h η hη0
  set c1 : ℝ := η * c0 * (4 : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) / 2 with hc1def
  set c2 : ℝ := η / 2 with hc2def
  have hc1pos : 0 < c1 := by rw [hc1def]; positivity
  have hc2pos : 0 < c2 := by rw [hc2def]; positivity
  obtain ⟨t0, ht0pos, hdom⟩ := hexpdom c1 hc1pos
  refine ⟨4096 * Cp ^ (2 : ℕ) + 360 * Cm ^ (2 : ℕ), c1, c2,
    max x5 (Real.exp (4 * max t0 2)), ?_, hc1pos, hc2pos, ?_, ?_⟩
  · nlinarith [sq_nonneg Cp, sq_nonneg Cm, hCpPos, hCmpos]
  · exact lt_max_of_lt_right (Real.exp_pos _)
  intro Pa hx hηeq X φ z0 β hβ hTau hfar hX hXle hXcube
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlogx0 : 0 ≤ Real.log (Pa.x : ℝ) := Real.log_nonneg hx1
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le zero_lt_one hX1
  have hlogPzpos : 0 < Real.log (Pa.Pz : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) Pa.hP2))
  have hlogPznonneg : 0 ≤ Real.log (Pa.Pz : ℝ) := le_of_lt hlogPzpos
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hxe : Real.exp (4 * max t0 2) ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hlogx : 4 * max t0 2 ≤ Real.log (Pa.x : ℝ) := by
    have h1 : Real.log (Real.exp (4 * max t0 2)) ≤ Real.log (Pa.x : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at h1
  have ht_lb : max t0 2 ≤ Real.log Pa.N := by
    have h := Pa.hNlo
    have h1 : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) < Real.log Pa.N :=
      Real.log_lt_log (Real.rpow_pos_of_pos (by linarith) _) h
    rw [Real.log_rpow (by linarith) _] at h1
    have h3 : (1 : ℝ) / 4 * Real.log (Pa.x : ℝ)
        ≤ ((1 : ℝ) / 4 + Pa.η) * Real.log (Pa.x : ℝ) := by
      nlinarith [Pa.hη, hlogx0]
    have h4 : max t0 2 ≤ (1 : ℝ) / 4 * Real.log (Pa.x : ℝ) := by linarith [hlogx]
    linarith [h1, h3, h4]
  have ht2 : (2 : ℝ) ≤ Real.log Pa.N := le_trans (le_max_right t0 2) ht_lb
  have htpos : 0 < Real.log Pa.N := by linarith
  have htt0 : t0 ≤ Real.log Pa.N := le_trans (le_max_left t0 2) ht_lb
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at h
  have hu1 : (1 : ℝ) ≤ Real.log (2 + Pa.N) := by
    have h4 : Real.log 3 ≤ Real.log (2 + Pa.N) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have htu : Real.log Pa.N ≤ Real.log (2 + Pa.N) := Real.log_le_log hNpos (by linarith)
  have hut : Real.log (2 + Pa.N) ≤ Real.log Pa.N + 2 := by
    have h2 : Real.log (2 + Pa.N) = Real.log Pa.N + Real.log (1 + 2 / Pa.N) := by
      rw [← Real.log_mul (ne_of_gt hNpos) (by positivity)]
      congr 1
      field_simp
      ring
    rw [h2]
    have h5 : Real.log (1 + 2 / Pa.N) ≤ 2 / Pa.N := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 / Pa.N by positivity)
      linarith
    have h6 : 2 / Pa.N ≤ 2 := by
      rw [div_le_iff₀ hNpos]; linarith
    linarith
  set t : ℝ := Real.log Pa.N with ht
  set u : ℝ := Real.log (2 + Pa.N) with hu
  set E : ℝ := Real.exp (Real.sqrt t) with hE
  set M : ℝ := ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ with hM
  set A : ℝ := Real.exp (-(c1 * t ^ ((1 : ℝ) / 4)))
    + Real.exp (-(c2 * t / Real.log (Pa.Pz : ℝ))) with hA
  set B0 : ℝ := Cp * A * (4 * (X : ℝ)) * Pa.N * t ^ (6 : ℕ) with hB0
  set KFI : Finset ℤ := Finset.Icc (-(2 * (Work.FIArea6.Kcut X) : ℤ)) (2 * (Work.FIArea6.Kcut X) : ℤ) with hKFI
  set KFS : Finset ℤ := KFI.filter (fun k : ℤ => ¬ |(k : ℝ)| ≤ E) with hKFS
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hAexp : Real.exp (-(c1 * t ^ ((1 : ℝ) / 4))) ≤ A := by
    rw [hA]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  have hA2 : A ≤ 2 := by
    rw [hA]
    have h1 : Real.exp (-(c1 * t ^ ((1 : ℝ) / 4))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h2 : 0 ≤ c1 * t ^ ((1 : ℝ) / 4) :=
        mul_nonneg hc1pos.le (Real.rpow_nonneg (by rw [ht]; linarith) _)
      linarith
    have h2 : Real.exp (-(c2 * t / Real.log (Pa.Pz : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h3 : 0 ≤ c2 * t / Real.log (Pa.Pz : ℝ) :=
        div_nonneg (mul_nonneg hc2pos.le (by rw [ht]; linarith)) hlogPznonneg
      linarith
    linarith
  have hAE : u ^ (5 : ℕ) ≤ A * E := by
    have h1 : u ^ (5 : ℕ) ≤ (t + 2) ^ (5 : ℕ) := by
      apply pow_le_pow_left₀
      · rw [hu]; linarith
      · rw [hu, ht]; exact hut
    have h2 : (t + 2) ^ (5 : ℕ) ≤ Real.exp (Real.sqrt t - c1 * t ^ ((1 : ℝ) / 4)) := by
      have h := hdom t (by rw [ht]; exact htt0)
      simpa only [ht] using h
    have h3 : Real.exp (Real.sqrt t - c1 * t ^ ((1 : ℝ) / 4)) ≤ A * E := by
      calc Real.exp (Real.sqrt t - c1 * t ^ ((1 : ℝ) / 4))
          = Real.exp (Real.sqrt t) * Real.exp (-(c1 * t ^ ((1 : ℝ) / 4))) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (Real.sqrt t) * A := mul_le_mul_of_nonneg_left hAexp (Real.exp_pos _).le
        _ = A * E := by rw [hE]; ring
    linarith [h1, h2, h3]
  have hM0 : 0 ≤ M := by rw [hM]; exact Finset.sum_nonneg (fun z _ => norm_nonneg _)
  have hMle : M ≤ Cm * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * u ^ (9 : ℕ) := by
    rw [hM]
    have h := hmass Pa φ z0 β hβ
    simpa only [hu] using h
  have hbr : Pa.θ * Pa.N + Real.sqrt Pa.N + 1 ≤ 3 * Pa.N := by
    have hs : Real.sqrt Pa.N ≤ Pa.N := by
      rw [Real.sqrt_le_iff]
      exact ⟨hNpos.le, by nlinarith [hN1]⟩
    have hθN : Pa.θ * Pa.N ≤ Pa.N := by
      calc Pa.θ * Pa.N ≤ 1 * Pa.N := mul_le_mul_of_nonneg_right hθ1 hNpos.le
        _ = Pa.N := by ring
    linarith
  have hM9 : M ≤ 3 * Cm * Pa.N * u ^ (9 : ℕ) := by
    have h3 : Cm * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * u ^ (9 : ℕ)
        ≤ 3 * Cm * Pa.N * u ^ (9 : ℕ) := by
      have h4 : Cm * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) ≤ Cm * (3 * Pa.N) :=
        mul_le_mul_of_nonneg_left hbr hCmpos.le
      calc Cm * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * u ^ (9 : ℕ)
          ≤ (Cm * (3 * Pa.N)) * u ^ (9 : ℕ) := mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = 3 * Cm * Pa.N * u ^ (9 : ℕ) := by ring
    linarith [hMle, h3]
  have hM2 : M ^ (2 : ℕ) ≤ 9 * Cm ^ (2 : ℕ) * Pa.N ^ (2 : ℕ) * u ^ (18 : ℕ) := by
    have h2 := pow_le_pow_left₀ hM0 hM9 2
    have h3 : (3 * Cm * Pa.N * u ^ (9 : ℕ)) ^ (2 : ℕ)
        = 9 * Cm ^ (2 : ℕ) * Pa.N ^ (2 : ℕ) * u ^ (18 : ℕ) := by
      rw [show (18 : ℕ) = 9 * 2 by norm_num, pow_mul]
      ring
    rwa [h3] at h2
  have hWkbound : (∑ k ∈ KFI, |Work.FIArea6.fcoeff k|) ≤ 16 * u := by
    have h1 : (1 : ℕ) ≤ 2 * Work.FIArea6.Kcut X := by
      have h2 : 1 ≤ Work.FIArea6.Kcut X := one_le_pow₀ hX
      omega
    have hfs := hfcoeffsum (2 * Work.FIArea6.Kcut X) h1
    have hKFI' : KFI = Finset.Icc (-((2 * Work.FIArea6.Kcut X : ℕ) : ℤ))
        ((2 * Work.FIArea6.Kcut X : ℕ) : ℤ) := by
      rw [hKFI]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hKFI']
    refine le_trans hfs ?_
    have hlog16 : Real.log 16 ≤ 3 := by
      have h2 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
      have h3 := Real.log_two_lt_d9
      linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have h3 := Real.log_two_lt_d9
      linarith
    have hlogK : Real.log (((2 * Work.FIArea6.Kcut X : ℕ) : ℝ)) ≤ Real.log 2 + Real.sqrt t := by
      have h2K : (((2 * Work.FIArea6.Kcut X : ℕ) : ℝ)) = 2 * (X : ℝ) ^ 3 := by
        show (((2 * Work.FIArea6.Kcut X : ℕ) : ℝ)) = 2 * (X : ℝ) ^ 3
        rw [show Work.FIArea6.Kcut X = X ^ 3 from rfl]
        push_cast
        ring
      have hle : 2 * (X : ℝ) ^ 3 ≤ 2 * E := by
        have h := hXcube
        linarith
      have h2E : Real.log (2 * E) = Real.log 2 + Real.sqrt t := by
        rw [Real.log_mul (by norm_num) (by rw [hE]; exact ne_of_gt (Real.exp_pos _)), hE,
          Real.log_exp]
      calc Real.log (((2 * Work.FIArea6.Kcut X : ℕ) : ℝ))
          = Real.log (2 * (X : ℝ) ^ 3) := by rw [h2K]
        _ ≤ Real.log (2 * E) := Real.log_le_log (by positivity) hle
        _ = Real.log 2 + Real.sqrt t := h2E
    have hsq : Real.sqrt t ≤ u := by
      rw [Real.sqrt_le_iff]
      refine ⟨by rw [hu]; linarith, ?_⟩
      have h4 : (2 : ℝ) ≤ u := by linarith [ht2, htu]
      nlinarith [h4]
    have h1u : (1 : ℝ) ≤ u := hu1
    linarith [hlog16, hlog2, hlogK, hsq, h1u]
  have hW2bound : (∑ k ∈ KFS, |Work.FIArea6.fcoeff k|) ≤ 5 * (X : ℝ) ^ 3 / E := by
    have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (Real.sqrt_nonneg t)
    have hterm : ∀ k ∈ KFS, |Work.FIArea6.fcoeff k| ≤ 1 / E := by
      intro k hk
      rw [hKFS] at hk
      have hkE : E < |(k : ℝ)| := lt_of_not_ge (Finset.mem_filter.mp hk).2
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0] at hkE
        simp only [Int.cast_zero, abs_zero] at hkE
        linarith
      have h1 := Work.FIArea6.S16_fcoeff_abs_le k hk0
      have h2 : 1 / |(k : ℝ)| ≤ 1 / E := one_div_le_one_div_of_le (by linarith) hkE.le
      linarith
    have hcard : (KFS.card : ℝ) ≤ 4 * (X : ℝ) ^ 3 + 1 := by
      have h1 : KFS.card ≤ KFI.card := by
        rw [hKFS]
        exact Finset.card_filter_le _ (fun k : ℤ => ¬ |(k : ℝ)| ≤ E)
      have h2 : (KFI.card : ℝ) ≤ 4 * (X : ℝ) ^ 3 + 1 := by
        rw [hKFI, Int.card_Icc]
        have h3 : (2 * (Work.FIArea6.Kcut X) : ℤ) + 1 - (-(2 * (Work.FIArea6.Kcut X) : ℤ))
            = ((4 * Work.FIArea6.Kcut X + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h3, Int.toNat_natCast]
        rw [show Work.FIArea6.Kcut X = X ^ 3 from rfl]
        push_cast
        linarith
      exact le_trans (by exact_mod_cast h1) h2
    calc ∑ k ∈ KFS, |Work.FIArea6.fcoeff k| ≤ ∑ k ∈ KFS, 1 / E := Finset.sum_le_sum hterm
      _ = (KFS.card : ℝ) * (1 / E) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * (X : ℝ) ^ 3 + 1) * (1 / E) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ 5 * (X : ℝ) ^ 3 / E := by
          have hX3 : (1 : ℝ) ≤ (X : ℝ) ^ 3 := one_le_pow₀ hX1
          have h4 : (4 * (X : ℝ) ^ 3 + 1) ≤ 5 * (X : ℝ) ^ 3 := by linarith
          calc (4 * (X : ℝ) ^ 3 + 1) * (1 / E) ≤ 5 * (X : ℝ) ^ 3 * (1 / E) :=
                mul_le_mul_of_nonneg_right h4 (by positivity)
            _ = 5 * (X : ℝ) ^ 3 / E := by ring
  have hcharb : ∀ d ∈ Finset.Icc 1 X, ∀ k ∈ KFI,
      |(k : ℝ)| ≤ E → ‖Work.FIArea6.DetSum Pa d k β‖ ≤ 4 * (d : ℝ) * B0 ^ (2 : ℕ) := by
    intro d hd k hk hkE
    obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
    have hcd := hchar Pa (le_trans (le_max_left x5 _) hx) hηeq X φ z0 d k β hβ hTau hfar hd1 hdX hX
      hXle hkE
    have hdR : (d : ℝ) ≤ (X : ℝ) := by exact_mod_cast hdX
    have hr := hrpow d X t hd1 hdX htpos hXle
    have h4d : ((4 * d : ℕ) : ℝ) = 4 * (d : ℝ) := by push_cast; ring
    have h4dX : ((4 * d : ℕ) : ℝ) ≤ 4 * (X : ℝ) := by rw [h4d]; linarith
    have hηc0pos : 0 < η * c0 := mul_pos hη0 hc0pos
    have hkey : c1 * t ^ ((1 : ℝ) / 4)
        ≤ η * c0 * (((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))) * Real.sqrt t := by
      have h := mul_le_mul_of_nonneg_left hr hηc0pos.le
      rw [hc1def]
      nlinarith [h]
    have he1 : Real.exp (-(η * c0 * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
          * Real.sqrt t)) ≤ Real.exp (-(c1 * t ^ ((1 : ℝ) / 4))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hkey]
    have he2 : Real.exp (-(η * t / Real.log (Pa.Pz : ℝ)))
        ≤ Real.exp (-(c2 * t / Real.log (Pa.Pz : ℝ))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ hlogPznonneg
      exact mul_le_mul_of_nonneg_right (by rw [hc2def]; linarith) (by rw [ht]; linarith)
    have hexps : Real.exp (-(η * c0 * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
          * Real.sqrt t)) + Real.exp (-(η * t / Real.log (Pa.Pz : ℝ))) ≤ A := by
      rw [hA]
      exact add_le_add he1 he2
    have hinner : Cp * (Real.exp (-(η * c0 * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
            * Real.sqrt t)) + Real.exp (-(η * t / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * t ^ (6 : ℕ) ≤ B0 := by
      rw [hB0]
      gcongr
    calc ‖Work.FIArea6.DetSum Pa d k β‖
        ≤ 4 * (d : ℝ) * (Cp * (Real.exp (-(η * c0 * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
                * Real.sqrt t)) + Real.exp (-(η * t / Real.log (Pa.Pz : ℝ))))
              * ((4 * d : ℕ) : ℝ) * Pa.N * t ^ (6 : ℕ)) ^ (2 : ℕ) := hcd
      _ ≤ 4 * (d : ℝ) * B0 ^ (2 : ℕ) := by
          have hnn : (0 : ℝ) ≤ Cp * (Real.exp (-(η * c0 * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
                  * Real.sqrt t)) + Real.exp (-(η * t / Real.log (Pa.Pz : ℝ))))
                * ((4 * d : ℕ) : ℝ) * Pa.N * t ^ (6 : ℕ) := by positivity
          have hmono := pow_le_pow_left₀ hnn hinner 2
          have hdnn : (0 : ℝ) ≤ 4 * (d : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hmono hdnn
  have htrivb : ∀ d ∈ Finset.Icc 1 X, ∀ k ∈ KFI,
      ‖Work.FIArea6.DetSum Pa d k β‖ ≤ 4 * (d : ℝ) * M ^ (2 : ℕ) := by
    intro d hd k hk
    have h := hdet Pa d k β
    simpa only [hM] using h
  have hWk0 : (0 : ℝ) ≤ ∑ k ∈ KFI, |Work.FIArea6.fcoeff k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hW20 : (0 : ℝ) ≤ ∑ k ∈ KFS, |Work.FIArea6.fcoeff k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hsd : (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) ≤ (X : ℝ) ^ (2 : ℕ) := hphi1 X hX
  have hchain := Work.FIArea6.S16_sum_chain Pa X β E B0 M hX hcharb htrivb
  have hstep1 : ‖Work.FIArea6.Umain Pa X β‖
      ≤ 8 * (∑ k ∈ KFI, |Work.FIArea6.fcoeff k|) * (X : ℝ) ^ (2 : ℕ) * B0 ^ (2 : ℕ)
        + 8 * (∑ k ∈ KFS, |Work.FIArea6.fcoeff k|) * M ^ (2 : ℕ) * (X : ℝ) ^ (2 : ℕ) := by
    refine le_trans hchain ?_
    refine add_le_add ?_ ?_
    · have h1 : 8 * (∑ k ∈ KFI, |Work.FIArea6.fcoeff k|)
          * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ))
          ≤ 8 * (∑ k ∈ KFI, |Work.FIArea6.fcoeff k|) * (X : ℝ) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsd (by linarith [hWk0])
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg B0)
    · exact mul_le_mul_of_nonneg_left hsd
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hW20) (sq_nonneg M))
  have hstep2 : 8 * (∑ k ∈ KFI, |Work.FIArea6.fcoeff k|) * (X : ℝ) ^ (2 : ℕ) * B0 ^ (2 : ℕ)
        + 8 * (∑ k ∈ KFS, |Work.FIArea6.fcoeff k|) * M ^ (2 : ℕ) * (X : ℝ) ^ (2 : ℕ)
      ≤ 8 * (16 * u) * (X : ℝ) ^ (2 : ℕ) * (Cp * A * (4 * (X : ℝ)) * Pa.N * t ^ (6 : ℕ)) ^ (2 : ℕ)
        + 8 * (5 * (X : ℝ) ^ 3 / E) * M ^ (2 : ℕ) * (X : ℝ) ^ (2 : ℕ) := by
    rw [hB0]
    refine add_le_add ?_ ?_
    · have h2 : 8 * (∑ k ∈ KFI, |Work.FIArea6.fcoeff k|) * (X : ℝ) ^ (2 : ℕ)
          ≤ 8 * (16 * u) * (X : ℝ) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWkbound (by norm_num : (0 : ℝ) ≤ 8))
          (sq_nonneg (X : ℝ))
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    · have h2 : 8 * (∑ k ∈ KFS, |Work.FIArea6.fcoeff k|) * M ^ (2 : ℕ)
          ≤ 8 * (5 * (X : ℝ) ^ 3 / E) * M ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hW2bound (by norm_num : (0 : ℝ) ≤ 8))
          (sq_nonneg M)
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg (X : ℝ))
  have hstep3 := Work.FIArea6.S16_final_arith Cp Cm c1 t u (X : ℝ) Pa.N A M (16 * u) (5 * (X : ℝ) ^ 3 / E) E
    hA0 hA2 hAexp hAE (by rw [ht]; linarith) (by rw [ht, hu]; exact htu)
    (by rw [hu]; exact hu1) hX1 (Real.exp_pos _) le_rfl le_rfl hM0 hM2
  exact le_trans hstep1 (le_trans hstep2 hstep3)

end

end Work.FIArea6V
