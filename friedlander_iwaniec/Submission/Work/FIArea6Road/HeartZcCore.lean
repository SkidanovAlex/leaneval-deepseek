import Mathlib
import Submission.Work.FIArea6Road.HeartZcAux
import Submission.Work.FIArea6Road.HeartZcDefs
import Submission.Work.FIArea6Road.IntegralSplitIcc
import Submission.Work.FIArea6Road.HeartFarIntegral
import Submission.Work.FIArea6Road.FarTailIntegrable
import Submission.Work.FIArea6Road.sum_tau_sq_window_le
import Submission.Work.FIArea6.S16.HeartIface
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FIArea6Road.HeartAux
import Submission.Work.FIArea6Road.HeartZcFarTail
import Submission.Work.FIArea6Road.HeartZcCzOfWitness
import Submission.Work.FIArea6Road.PolyExpUltimately
import Submission.Work.FIArea6Road.HeartZcCaseAArith
import Submission.Work.FIArea6Road.HeartZcWitnessMine
import Submission.Work.FIArea6Road.HeartZcShiftedLine

set_option maxHeartbeats 8000000

namespace Work.FIArea6Road

open MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `HeartZcCore` — the contour shift with the corrected continuation interface

Write `L = log N`, `θ = Pa.θ`, `T = Work.FIArea6Hecke.heightT Pa`,
`δ = Work.FIArea6Hecke.deltaC Pa d ε c_h`, `σ₀ = 1 - δ`, `σr = 1 + 1/L`,
`R = S16E1 Pa c d ε + S16E2 Pa`, `G s = mellin (fun u => (p u : ℂ)) s * Zc s`.

The contour shift needs the saving `exp (-(η δ L)) ≤ R` (`hzc_Npow_le_R` below); everything else
is the Cauchy shift `[σ₀,σr] × [-T,T]` (`HeartZcShiftedLine`) together with the far tail
(`HeartZcFarTail`).
-/

/-- **The saving.**  For `δ = Work.FIArea6Hecke.deltaC Pa d ε c_h` and `c ≤ c_h 4^ε/16` one has
`exp (-(η δ log N)) ≤ S16E1 Pa c d ε + S16E2 Pa`.

The point is that `η δ L ≥ min (η c (4d)^{-ε}√L) (η L/log Pz)`: writing `δ = min δ₁ δ₂` with
`δ₁ = c_h/(2 d^ε (log T+1))`, `δ₂ = 1/log Pz`, one has `η δ₁ L ≥ η c (4d)^{-ε}√L` because
`√L ≤ log T + 1 ≤ 2√L` and `c 4^{-ε} ≤ c_h/4`. -/
lemma hzc_Npow_le_R (Pa : Work.FITop.Params) (d : ℕ) (ε c_h c : ℝ)
    (hd1 : 1 ≤ d) (hc : c ≤ c_h * (4 : ℝ) ^ ε / 16) (hc_h : 0 < c_h)
    (hlogPz : 6 ≤ Real.log (Pa.Pz : ℝ))
    (hlogT : Real.log (Work.FIArea6Hecke.heightT Pa) + 1 ≤ 2 * Real.sqrt (Real.log Pa.N))
    (hL1 : 1 ≤ Real.log Pa.N) :
    Real.exp (-(Pa.η * Work.FIArea6Hecke.deltaC Pa d ε c_h * Real.log Pa.N))
      ≤ Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa := by
  have hLpos : 0 < Real.log Pa.N := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd1)
  have hT1 : (1 : ℝ) ≤ Work.FIArea6Hecke.heightT Pa := by
    rw [Work.FIArea6Hecke.heightT]
    nlinarith [Real.one_le_exp (Real.sqrt_nonneg (Real.log Pa.N))]
  have hlogT1pos : 0 < Real.log (Work.FIArea6Hecke.heightT Pa) + 1 := by
    have := Real.log_nonneg hT1; linarith
  have hsqrtnn : 0 ≤ Real.sqrt (Real.log Pa.N) := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt (Real.log Pa.N) ≤ Real.log Pa.N := by
    have hsq : Real.sqrt (Real.log Pa.N) ^ 2 = Real.log Pa.N := Real.sq_sqrt hLpos.le
    nlinarith
  set δ₁ : ℝ := c_h / (2 * (d : ℝ) ^ ε * (Real.log (Work.FIArea6Hecke.heightT Pa) + 1))
    with hδ₁
  set δ₂ : ℝ := 1 / Real.log (Pa.Pz : ℝ) with hδ₂
  have hδeq : Work.FIArea6Hecke.deltaC Pa d ε c_h = min δ₁ δ₂ := by
    rw [hδ₁, hδ₂]; rfl
  set A : ℝ := Pa.η * c * ((((4 * d : ℕ)) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N) with hA
  set B : ℝ := Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ) with hB
  -- the key inequality
  have hkey : c * ((((4 * d : ℕ)) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)
      ≤ c_h * Real.log Pa.N
        / (2 * (d : ℝ) ^ ε * (Real.log (Work.FIArea6Hecke.heightT Pa) + 1)) := by
    have h4d : ((((4 * d : ℕ)) : ℝ)) ^ (-ε) = (4 : ℝ) ^ (-ε) * (d : ℝ) ^ (-ε) := by
      rw [show (((4 * d : ℕ)) : ℝ) = 4 * (d : ℝ) by push_cast; ring]
      exact Real.mul_rpow (by norm_num) hdpos.le
    have h4inv : (4 : ℝ) ^ (-ε) * (4 : ℝ) ^ ε = 1 := by
      rw [← Real.rpow_add (show (0 : ℝ) < 4 by norm_num) (-ε) ε, neg_add_cancel]
      exact Real.rpow_zero 4
    have hdinv : (d : ℝ) ^ (-ε) * (d : ℝ) ^ ε = 1 := by
      rw [← Real.rpow_add hdpos (-ε) ε, neg_add_cancel]
      exact Real.rpow_zero (d : ℝ)
    have hc4 : c * (4 : ℝ) ^ (-ε) ≤ c_h / 4 := by
      have h := mul_le_mul_of_nonneg_right hc
        (Real.rpow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (-ε))
      calc c * (4 : ℝ) ^ (-ε) ≤ (c_h * (4 : ℝ) ^ ε / 16) * (4 : ℝ) ^ (-ε) := h
        _ = c_h / 16 * ((4 : ℝ) ^ ε * (4 : ℝ) ^ (-ε)) := by ring
        _ = c_h / 16 := by rw [mul_comm ((4 : ℝ) ^ ε) ((4 : ℝ) ^ (-ε)), h4inv, mul_one]
        _ ≤ c_h / 4 := by linarith
    have hsqrtle' : Real.sqrt (Real.log Pa.N)
        ≤ 2 * Real.log Pa.N / (Real.log (Work.FIArea6Hecke.heightT Pa) + 1) := by
      rw [le_div_iff₀ hlogT1pos]
      have hsq : Real.sqrt (Real.log Pa.N) * Real.sqrt (Real.log Pa.N) = Real.log Pa.N :=
        Real.mul_self_sqrt hLpos.le
      nlinarith [hlogT, hsqrtnn]
    have hdnn : (0 : ℝ) ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg hdpos.le _
    calc c * ((((4 * d : ℕ)) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)
        = (c * (4 : ℝ) ^ (-ε)) * ((d : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)) := by
          rw [h4d]; ring
      _ ≤ (c_h / 4) * ((d : ℝ) ^ (-ε) * (2 * Real.log Pa.N
            / (Real.log (Work.FIArea6Hecke.heightT Pa) + 1))) := by
          apply mul_le_mul hc4 _ (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_left hsqrtle' hdnn
      _ = c_h * Real.log Pa.N
            / (2 * (d : ℝ) ^ ε * (Real.log (Work.FIArea6Hecke.heightT Pa) + 1)) := by
          rw [Real.rpow_neg hdpos.le]
          field_simp
          ring
  have hAle₁ : A ≤ Pa.η * δ₁ * Real.log Pa.N := by
    have h1 : c_h * Real.log Pa.N
        / (2 * (d : ℝ) ^ ε * (Real.log (Work.FIArea6Hecke.heightT Pa) + 1))
        = δ₁ * Real.log Pa.N := by rw [hδ₁]; ring
    rw [h1] at hkey
    rw [hA]
    calc Pa.η * c * ((((4 * d : ℕ)) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)
        = Pa.η * (c * ((((4 * d : ℕ)) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)) := by ring
      _ ≤ Pa.η * (δ₁ * Real.log Pa.N) := mul_le_mul_of_nonneg_left hkey Pa.hη.le
      _ = Pa.η * δ₁ * Real.log Pa.N := by ring
  have hmin : min A B ≤ Pa.η * Work.FIArea6Hecke.deltaC Pa d ε c_h * Real.log Pa.N := by
    rcases le_total δ₁ δ₂ with h | h
    · rw [hδeq, min_eq_left h]
      rcases le_total A B with hAB | hBA
      · exact le_trans (min_le_left _ _) hAle₁
      · exact le_trans (min_le_right _ _) (le_trans hBA hAle₁)
    · rw [hδeq, min_eq_right h]
      refine le_trans (min_le_right _ _) (le_of_eq ?_)
      rw [hB, hδ₂]
      ring
  have hE1 : Work.FIArea6.S16.S16E1 Pa c d ε = Real.exp (-A) := by
    simp only [Work.FIArea6.S16.S16E1, hA]
  have hE2 : Work.FIArea6.S16.S16E2 Pa = Real.exp (-B) := by
    simp only [Work.FIArea6.S16.S16E2, hB]
  calc Real.exp (-(Pa.η * Work.FIArea6Hecke.deltaC Pa d ε c_h * Real.log Pa.N))
      ≤ Real.exp (-(min A B)) := by
        apply Real.exp_le_exp.mpr
        linarith [hmin]
    _ ≤ Real.exp (-A) + Real.exp (-B) := by
        rcases le_total A B with h | h
        · rw [min_eq_left h]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [min_eq_right h]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
    _ = Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa := by rw [hE1, hE2]

/-! ## The heart -/

theorem HeartZcCore (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (c_h : ℝ) (hc_h : 0 < c_h) :
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      ∀ (ν : ℝ) (d : ℕ) (m : ℤ) (chi : GaussianInt → ℂ) (p : ℝ → ℝ),
        Work.FIArea6.S16.HeartHyp Pa ν d m chi p ε →
        (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        (hMellin : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
          Work.FIArea6Hecke.Tsum Pa chi m p
            = (1 / (2 * Real.pi)) * ∫ t : ℝ, (mellin (fun u : ℝ => (p u : ℂ))
                ((σ : ℂ) + (t : ℂ) * Complex.I)
              * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I))) →
        ∀ (C_z : ℝ) (Zc : ℂ → ℂ),
          Work.FIArea6Road.heartZcHyp Pa chi m d ε c_h C_z Zc →
          Work.FIArea6.S16.HeartBound Pa c (C * C_z) d ε m chi p := by

  obtain ⟨K_Far, hKFarpos, hKFar⟩ := HeartZcFarTail
  obtain ⟨K_w, hKwpos, hKw⟩ := ZsfunRightEdgeWitnessMine
  obtain ⟨K_Cz, hKCzpos, hKCz⟩ := HeartZcCzOfWitness K_w hKwpos
  obtain ⟨C_W0, hCW0pos, hCW0⟩ := sum_tau_sq_window_le
  set C_W : ℝ := max C_W0 1 with hCWdef
  have hCWpos : 0 < C_W := lt_of_lt_of_le hCW0pos (le_max_left _ _)
  have hCWge1 : 1 ≤ C_W := le_max_right _ _
  have hCWb : ∀ N M : ℕ, N ≤ M →
      (∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ)) ^ 2)
        ≤ C_W * (((M : ℝ) - (N : ℝ) + 1) * (Real.log ((M : ℝ) + 2)) ^ (3 : ℕ)
            + (M : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M : ℝ) + 2)) ^ (2 : ℕ)) := by
    intro N M hNM
    refine (hCW0 N M hNM).trans ?_
    have h0 : C_W0 ≤ C_W := le_max_left _ _
    have h1 : (0 : ℝ) ≤ (M : ℝ) - (N : ℝ) + 1 := by
      have : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
      linarith
    have h2 : (0 : ℝ) ≤ Real.log ((M : ℝ) + 2) :=
      Real.log_nonneg (by have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; linarith)
    have h3 : (0 : ℝ) ≤ (M : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg M) _
    have ha : C_W0 * ((M : ℝ) - (N : ℝ) + 1) * (Real.log ((M : ℝ) + 2)) ^ (3 : ℕ)
        ≤ C_W * ((M : ℝ) - (N : ℝ) + 1) * (Real.log ((M : ℝ) + 2)) ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h0 h1) (pow_nonneg h2 3)
    have hb : C_W0 * (M : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M : ℝ) + 2)) ^ (2 : ℕ)
        ≤ C_W * (M : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M : ℝ) + 2)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h0 h3) (pow_nonneg h2 2)
    linarith
  -- ### the polynomial-vs-exponential threshold
  set αf : ℝ := 10 ^ 3 * K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6 / 10 ^ 40 with hαfdef
  have hαfpos : 0 < αf := by rw [hαfdef]; positivity
  obtain ⟨Λf, hΛfpos, hΛf⟩ := PolyExpUltimately αf 3 hαfpos
  set Λ : ℝ := max (max Λf 1000) (10 ^ 8) with hΛdef
  have hΛ1000 : 1000 ≤ Λ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hΛ1e8 : 10 ^ 8 ≤ Λ := le_max_right _ _
  have hΛf_le : Λf ≤ Λ := le_trans (le_max_left _ _) (le_max_left _ _)
  -- ### the constants
  set c : ℝ := min (1 / 2) (c_h * (4 : ℝ) ^ ε / 16) with hcdef
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  have hchalf : c ≤ 1 / 2 := min_le_left _ _
  have hc16 : c ≤ c_h * (4 : ℝ) ^ ε / 16 := min_le_right _ _
  set C : ℝ := 10 ^ 100 * (C_W + 1) * (K_Cz + 1) + 10 ^ 40 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCbig : 10 ^ 100 * (C_W + 1) * (K_Cz + 1) ≤ C := by rw [hCdef]; linarith
  have hC40 : 10 ^ 40 ≤ C := by
    have hnn : (0 : ℝ) ≤ 10 ^ 100 * (C_W + 1) * (K_Cz + 1) := by positivity
    rw [hCdef]; linarith
  refine ⟨c, C, Real.exp (4 * Λ), hcpos, hCpos, Real.exp_pos _, ?_⟩
  intro Pa hPa ν d m chi p hh hchibd hMellin C_z Zc hzc
  obtain ⟨hν0, hν1, hd1, hdN, hm, hchi, hpC, hp0, hp1, hpsupp, hpd⟩ := hh
  have hCznn : (0 : ℝ) ≤ C_z := hzc.1.le
  have hpabs : ∀ u : ℝ, |p u| ≤ 1 := fun u => abs_le.mpr ⟨by linarith [hp0 u], hp1 u⟩
  -- ### `log N ≥ Λ`
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlogx4 : 4 * Λ ≤ Real.log (Pa.x : ℝ) := by
    have h1 : Real.exp (4 * Λ) ≤ (Pa.x : ℝ) := hPa
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  set L : ℝ := Real.log Pa.N with hLdef
  have hLge : Λ ≤ L := by
    have h1 : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) < Real.log Pa.N :=
      Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) Pa.hNlo
    rw [Real.log_rpow hxpos] at h1
    have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
      have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
      linarith
    have hlogxnn : 0 ≤ Real.log (Pa.x : ℝ) := Real.log_nonneg hx1
    have h2 : Real.log (Pa.x : ℝ) / 4 ≤ (1 / 4 + Pa.η) * Real.log (Pa.x : ℝ) := by
      nlinarith only [mul_nonneg Pa.hη.le hlogxnn]
    rw [hLdef]
    linarith only [h1, hlogx4, h2]
  have hL1000 : 1000 ≤ L := le_trans hΛ1000 hLge
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hL1e8 : 10 ^ 8 ≤ L := le_trans hΛ1e8 hLge
  have hlogPz6 : 6 ≤ Real.log (Pa.Pz : ℝ) := hzc_logPz_ge_six Pa (by rw [← hLdef]; exact hL1e8)
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hCpos' : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one Pa.hC1
  have hPz1 : (1 : ℝ) < (Pa.Pz : ℝ) := by
    have h2 : (2 : ℕ) ≤ Pa.Pz := Pa.hP2
    exact_mod_cast h2
  have hlogPzpos : 0 < Real.log (Pa.Pz : ℝ) := Real.log_pos hPz1
  -- ### the contour data
  set T : ℝ := Work.FIArea6Hecke.heightT Pa with hTdef
  have hTe : T = 5 * Real.exp (Real.sqrt L) + 10 := by
    rw [hTdef, hLdef]; rfl
  have hT1 : 1 ≤ T := by
    linarith only [hTe, Real.exp_pos (Real.sqrt L)]
  have hT15 : 5 * Real.exp (Real.sqrt L) ≤ T := by
    linarith only [hTe]
  have hmT : |(m : ℝ)| + 3 ≤ T := by
    rw [hTdef]; exact heart_abs_m_le_T Pa m hm
  have hlogTle : Real.log T + 1 ≤ 2 * Real.sqrt L := by
    rw [hTdef, hLdef]
    exact heart_logT_le Pa (by linarith)
  set δ : ℝ := Work.FIArea6Hecke.deltaC Pa d ε c_h with hδdef
  set RR : ℝ := Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa with hRRdef
  have hRRpos : 0 < RR := by
    rw [hRRdef]; exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (Real.exp_pos _).le
  have hRRge : Real.exp (-(Real.sqrt L / 8)) ≤ RR := by
    rw [hRRdef, hLdef]
    exact le_trans (hzc_E1_ge Pa c d ε hcpos hchalf hε.le hd1 (hzc_eta_le_quarter Pa))
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  -- ### the lower bound on `C_z`
  have hCz : 1 / (K_Cz * (d : ℝ) * L ^ (6 : ℕ)) ≤ C_z := by
    obtain ⟨s, hs1, hs2, hs3, hsim, hval⟩ :=
      hKw Pa chi m d hchi hchibd hm (by rw [← hLdef]; linarith)
    exact hKCz Pa chi m d ε c_h C_z Zc hd1 (by linarith [hlogPz6])
      (by rw [← hLdef]; linarith) hm ⟨s, hs1, hs2, hs3, hsim, hval⟩ hzc
  -- ### the goal in the form `‖Tsum‖ ≤ (C*C_z)*(E1+E2)*(4d)*N*(log N)^6`
  rw [Work.FIArea6.S16.HeartBound, Work.FIArea6.S16.S16RH]
  have hfourd : ((4 * d : ℕ) : ℝ) = 4 * (d : ℝ) := by push_cast; ring
  rw [hfourd]
  have hgoal : ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
      ≤ (C * C_z) * (Work.FIArea6.S16.S16E1 Pa c d ε + Work.FIArea6.S16.S16E2 Pa)
        * (4 * (d : ℝ)) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
    have hmain : ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
        ≤ C * C_z * RR * (4 * (d : ℝ)) * Pa.N * L ^ 6 := by
      by_cases hcaseA : Pa.θ ≤ RR / (256 * L ^ 3)
      · -- ## Case A: the trivial window bound
        have hRRle2 : RR ≤ 2 := by
          rw [hRRdef]
          have h1 : Work.FIArea6.S16.S16E1 Pa c d ε ≤ 1 := by
            rw [Work.FIArea6.S16.S16E1, Real.exp_le_one_iff]
            have h2 : 0 ≤ Pa.η * c * ((((4 * d : ℕ)) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N) := by
              have h3 : 0 ≤ ((((4 * d : ℕ)) : ℝ)) ^ (-ε) :=
                Real.rpow_nonneg (by exact_mod_cast Nat.zero_le (4 * d)) _
              exact mul_nonneg (mul_nonneg (mul_nonneg Pa.hη.le hcpos.le) h3)
                (Real.sqrt_nonneg _)
            linarith
          have h2 : Work.FIArea6.S16.S16E2 Pa ≤ 1 := by
            rw [Work.FIArea6.S16.S16E2, Real.exp_le_one_iff]
            exact neg_nonpos.mpr
              (div_nonneg (mul_nonneg Pa.hη.le (Real.log_nonneg hN1)) hlogPzpos.le)
          linarith
        have hθ1 : Pa.θ ≤ 1 := by
          have h1 : RR / (256 * L ^ 3) ≤ 1 := by
            rw [div_le_one (by positivity)]
            have h2 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
            linarith [hRRle2, h2]
          linarith
        have hRL : Real.exp (-(L / 8)) ≤ RR := by
          refine le_trans ?_ hRRge
          apply Real.exp_le_exp.mpr
          have hs : Real.sqrt L ≤ L := by
            rw [Real.sqrt_le_iff]
            exact ⟨hLpos.le, by nlinarith only [mul_le_mul_of_nonneg_left hL1 hLpos.le]⟩
          linarith
        have htriv := Tsum_trivial_bound Pa chi m p hchibd hpabs hpsupp
        set N' : ℕ := ⌊Pa.N⌋₊ + 1 with hN'def
        set M' : ℕ := ⌊(1 + Pa.θ) * Pa.N⌋₊ with hM'def
        have hAArith := HeartZcCaseAArith Pa.N Pa.θ (d : ℝ) K_Cz C_W C_z RR hN1
          (by rw [← hLdef]; linarith) (by exact_mod_cast hd1) hKCzpos hCWpos
          (by rw [← hLdef]; exact hCz) (le_of_lt Pa.hθ0) hcaseA
          (by rw [← hLdef]; exact hRL)
        have hMle : (M' : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
          rw [hM'def]; exact Nat.floor_le (mul_nonneg (by linarith only [Pa.hθ0]) hNpos.le)
        have hNlt : Pa.N < (N' : ℝ) := by
          rw [hN'def]; push_cast; exact Nat.lt_floor_add_one Pa.N
        have hMd : (M' : ℝ) - (N' : ℝ) + 1 ≤ Pa.θ * Pa.N + 1 := by linarith
        have hlogM'nn : 0 ≤ Real.log ((M' : ℝ) + 2) :=
          Real.log_nonneg (by have : (0 : ℝ) ≤ (M' : ℝ) := Nat.cast_nonneg M'; linarith)
        have hlog4N : Real.log ((M' : ℝ) + 2) ≤ Real.log (4 * Pa.N) := by
          apply Real.log_le_log (by positivity)
          nlinarith only [hMle, mul_le_mul_of_nonneg_right hθ1 hNpos.le, hN1]
        have hMpow : (M' : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 * Pa.N) ^ ((3 : ℝ) / 4) := by
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          nlinarith only [hMle, mul_le_mul_of_nonneg_right hθ1 hNpos.le]
        have hstep1 : ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
            ≤ 4 * (C_W * (Pa.θ * Pa.N + 1) * (Real.log (4 * Pa.N)) ^ (3 : ℕ)
              + C_W * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log (4 * Pa.N)) ^ (2 : ℕ)) := by
          by_cases hwin : N' ≤ M'
          · refine htriv.trans ?_
            have h1 : (∑ n ∈ Finset.Icc N' M', ((n.divisors.card : ℝ)) ^ 2)
                ≤ C_W * (((M' : ℝ) - (N' : ℝ) + 1) * (Real.log ((M' : ℝ) + 2)) ^ (3 : ℕ)
                  + (M' : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M' : ℝ) + 2)) ^ (2 : ℕ)) :=
              hCWb N' M' hwin
            have h2 : C_W * (((M' : ℝ) - (N' : ℝ) + 1) * (Real.log ((M' : ℝ) + 2)) ^ (3 : ℕ)
                  + (M' : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M' : ℝ) + 2)) ^ (2 : ℕ))
                ≤ C_W * ((Pa.θ * Pa.N + 1) * (Real.log (4 * Pa.N)) ^ (3 : ℕ)
                  + (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log (4 * Pa.N)) ^ (2 : ℕ)) := by
              apply mul_le_mul_of_nonneg_left _ hCWpos.le
              have hp3 : (Real.log ((M' : ℝ) + 2)) ^ (3 : ℕ) ≤ (Real.log (4 * Pa.N)) ^ (3 : ℕ) :=
                pow_le_pow_left₀ hlogM'nn hlog4N 3
              have hp2 : (Real.log ((M' : ℝ) + 2)) ^ (2 : ℕ) ≤ (Real.log (4 * Pa.N)) ^ (2 : ℕ) :=
                pow_le_pow_left₀ hlogM'nn hlog4N 2
              have hA1 : ((M' : ℝ) - (N' : ℝ) + 1) * (Real.log ((M' : ℝ) + 2)) ^ (3 : ℕ)
                  ≤ (Pa.θ * Pa.N + 1) * (Real.log (4 * Pa.N)) ^ (3 : ℕ) :=
                mul_le_mul hMd hp3 (pow_nonneg hlogM'nn 3)
                  (by nlinarith only [mul_nonneg Pa.hθ0.le hNpos.le])
              have hA2 : (M' : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M' : ℝ) + 2)) ^ (2 : ℕ)
                  ≤ (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log (4 * Pa.N)) ^ (2 : ℕ) :=
                mul_le_mul hMpow hp2 (pow_nonneg hlogM'nn 2) (by positivity)
              linarith
            linarith
          · have hz : (∑ n ∈ Finset.Icc N' M', ((n.divisors.card : ℝ)) ^ 2) = 0 := by
              rw [Finset.Icc_eq_empty hwin, Finset.sum_empty]
            have h0 : ‖Work.FIArea6Hecke.Tsum Pa chi m p‖ ≤ 0 := by
              have h1 := htriv
              rw [hz, mul_zero] at h1
              exact h1
            have h4 : (0 : ℝ) ≤ 4 * (C_W * (Pa.θ * Pa.N + 1) * (Real.log (4 * Pa.N)) ^ (3 : ℕ)
                + C_W * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log (4 * Pa.N)) ^ (2 : ℕ)) := by
              have hl4 : 0 ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith [hN1])
              have h5 : 0 ≤ (Real.log (4 * Pa.N)) ^ (3 : ℕ) := pow_nonneg hl4 3
              have h5' : 0 ≤ (Real.log (4 * Pa.N)) ^ (2 : ℕ) := pow_nonneg hl4 2
              have h6 : 0 ≤ Pa.θ * Pa.N + 1 := by nlinarith only [mul_nonneg Pa.hθ0.le hNpos.le]
              have h7 : 0 ≤ (2 * Pa.N) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
              have h8 : 0 ≤ C_W * (Pa.θ * Pa.N + 1) * (Real.log (4 * Pa.N)) ^ (3 : ℕ) :=
                mul_nonneg (mul_nonneg hCWpos.le h6) h5
              have h9 : 0 ≤ C_W * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log (4 * Pa.N)) ^ (2 : ℕ) :=
                mul_nonneg (mul_nonneg hCWpos.le h7) h5'
              linarith
            linarith
        have hstep2 : 4 * (C_W * (Pa.θ * Pa.N + 1) * (Real.log (4 * Pa.N)) ^ (3 : ℕ)
              + C_W * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log (4 * Pa.N)) ^ (2 : ℕ))
            ≤ C * C_z * RR * (4 * (d : ℝ)) * Pa.N * L ^ 6 := by
          refine hAArith.trans ?_
          rw [← hLdef]
          calc 10 ^ 100 * (C_W + 1) * (K_Cz + 1) * C_z * RR * (4 * (d : ℝ)) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ)
              = (10 ^ 100 * (C_W + 1) * (K_Cz + 1))
                * (C_z * RR * (4 * (d : ℝ)) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) := by ring
            _ ≤ C * (C_z * RR * (4 * (d : ℝ)) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) :=
                mul_le_mul_of_nonneg_right hCbig
                  (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCznn hRRpos.le)
                    (by positivity)) hNpos.le) (pow_nonneg (Real.log_nonneg hN1) 6))
            _ = C * C_z * RR * (4 * (d : ℝ)) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by ring
        exact hstep1.trans hstep2
      · -- ## Case B: the contour shift
        have hθgt : RR / (256 * L ^ 3) < Pa.θ := not_le.mp hcaseA
        set σr : ℝ := 1 + 1 / L with hσrdef
        have hσr1 : 1 < σr := by
          rw [hσrdef]
          have h1 : 0 < 1 / L := by positivity
          linarith
        have hσr2 : σr ≤ 2 := by
          rw [hσrdef]
          have h1 : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
          linarith
        have hMell := hMellin σr hσr1 hσr2
        set G : ℂ → ℂ := fun s => mellin (fun u : ℝ => (p u : ℂ)) s * Zc s with hGdef
        have hZeq : ∀ t : ℝ, Work.FIArea6.TauPieces.Zsfun Pa chi m ((σr : ℂ) + (t : ℂ) * Complex.I)
            = Zc ((σr : ℂ) + (t : ℂ) * Complex.I) := by
          intro t
          have hre : ((σr : ℂ) + (t : ℂ) * Complex.I).re = σr := by simp
          exact (hzc.2.1 _ (by rw [hre]; exact hσr1)).symm
        have hTsum_eq : Work.FIArea6Hecke.Tsum Pa chi m p
            = (1 / (2 * Real.pi)) * ∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I) := by
          rw [hMell]
          congr 1
          refine integral_congr_ae ?_
          filter_upwards with t
          show mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)
              * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σr : ℂ) + (t : ℂ) * Complex.I)
            = G ((σr : ℂ) + (t : ℂ) * Complex.I)
          rw [hZeq t]
        by_cases hInt : Integrable (fun t : ℝ => G ((σr : ℂ) + (t : ℂ) * Complex.I))
        · -- ### integrable case
          have hmt' : |(m : ℝ)| + 3 ≤ Work.FIArea6Hecke.heightT Pa := by rw [← hTdef]; exact hmT
          have hmid := HeartZcShiftedLine Pa chi m d ε c_h C_z Zc p δ hzc hc_h hpC hp0 hp1 hpsupp hpd
            hδdef hmt' (by rw [← hLdef]; linarith)
          have hmid' : ‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
              ≤ Real.pi * (10 ^ 7 * (C_z * (d : ℝ)) * (4 * L) ^ (6 : ℕ)) * (Pa.N ^ (1 - δ) * Pa.C ^ δ)
                + 2 * ((10 ^ 7 * (C_z * (d : ℝ)) * (4 * L) ^ (6 : ℕ)) * (1 / T)
                    * (Pa.N * (δ + Real.exp 1 / L))) := by
            rw [hTdef, hσrdef, hLdef, hGdef]
            exact hmid
          -- ### the far tail
          set Lm : ℝ := L + Real.log (|(m : ℝ)| + 3) + 2 with hLmdef
          have hLmnn : 0 ≤ Lm := by
            rw [hLmdef]
            have h1 : (0 : ℝ) ≤ Real.log (|(m : ℝ)| + 3) :=
              Real.log_nonneg (by have := abs_nonneg (m : ℝ); linarith)
            linarith
          have hd2 : ∀ u : ℝ, |iteratedDeriv 2 p u| ≤ 1048576 / (Pa.θ * Pa.N) ^ 2 := by
            intro u
            have h := hpd 2 le_rfl u
            have hc : Work.FITop4.cMoll 2 = (1048576 : ℝ) := by rw [Work.FITop4.cMoll]; norm_num
            rw [hc, Real.rpow_neg (le_of_lt (mul_pos Pa.hθ0 hNpos)), inv_eq_one_div,
              Real.rpow_natCast, mul_one_div] at h
            exact h
          have hKznn : (0 : ℝ) ≤ 10 ^ 7 * Pa.θ * Pa.N ^ σr * C_z * (d : ℝ) :=
            mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le)
              (Real.rpow_nonneg hNpos.le _)) hzc.1.le) (by positivity)
          have hint : IntegrableOn
              (fun t : ℝ => (1 + (Pa.θ * t) ^ 2)⁻¹ * (Lm + Real.log (1 + |t|)) ^ (6 : ℕ))
              (Set.Ioi T ∪ Set.Iio (-T)) := by
            have h := FarTailIntegrable Pa.θ T Lm Pa.hθ0 hT1 hLmnn
            have h2 : (fun t : ℝ => (1 / Pa.θ) * (Pa.θ * (1 + (Pa.θ * t) ^ 2)⁻¹
                  * (Lm + Real.log (1 + |t|)) ^ (6 : ℕ)))
                = (fun t : ℝ => (1 + (Pa.θ * t) ^ 2)⁻¹ * (Lm + Real.log (1 + |t|)) ^ (6 : ℕ)) := by
              funext t
              rw [← mul_assoc (1 / Pa.θ) (Pa.θ * (1 + (Pa.θ * t) ^ 2)⁻¹)
                ((Lm + Real.log (1 + |t|)) ^ (6 : ℕ))]
              rw [one_div, inv_mul_cancel_left₀ (ne_of_gt Pa.hθ0)]
            rw [← h2]
            exact h.const_mul (1 / Pa.θ)
          have hbd : ∀ t : ℝ, T < |t| → ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖
              ≤ (10 ^ 7 * Pa.θ * Pa.N ^ σr * C_z * (d : ℝ))
                * ((1 + (Pa.θ * t) ^ 2)⁻¹ * (Lm + Real.log (1 + |t|)) ^ (6 : ℕ)) := by
            intro t ht
            have htne : t ≠ 0 := by
              intro h0
              rw [h0, abs_zero] at ht
              linarith [hT1]
            have hmv0 := Work.FIArea6.S16MellinVerticalBound p Pa.N Pa.θ σr hNpos Pa.hθ0
              (heart_theta_le_one Pa) hpC hp0 hp1 hpsupp hd2 (by linarith [hσr1]) hσr2 t htne
            have hmv : ‖mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ 10 ^ 7 * Pa.θ * Pa.N ^ σr * (1 + (Pa.θ * t) ^ 2)⁻¹ := by
              simpa only [show (10 : ℝ) ^ 7 = 10000000 by norm_num] using hmv0
            have hzcb : ‖Zc ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ C_z * (d : ℝ) * (L + Real.log (|(m : ℝ)| + |t| + 3) + 2) ^ (6 : ℕ) := by
              have hre : ((σr : ℂ) + (t : ℂ) * Complex.I).re = σr := by simp
              have him : ((σr : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
              have h1 : 1 < ((σr : ℂ) + (t : ℂ) * Complex.I).re := by rw [hre]; exact hσr1
              have h2 : ((σr : ℂ) + (t : ℂ) * Complex.I).re ≤ 1 + 1 / Real.log Pa.N := by
                rw [hre, hσrdef, hLdef]
              have h3 : ((σr : ℂ) + (t : ℂ) * Complex.I).re ≤ 2 := by rw [hre]; exact hσr2
              have h4 := hzc.2.2.2.2 _ h1 h2 h3
              rw [him, ← hLdef] at h4
              exact h4
            have hlogcmp : Real.log (|(m : ℝ)| + |t| + 3)
                ≤ Real.log (1 + |t|) + Real.log (|(m : ℝ)| + 3) := by
              have h0a := abs_nonneg (m : ℝ)
              have h0b := abs_nonneg t
              have h1 : |(m : ℝ)| + |t| + 3 ≤ (|(m : ℝ)| + 3) * (1 + |t|) := by
                nlinarith only [mul_nonneg h0a h0b, h0a, h0b]
              have h2 : Real.log (|(m : ℝ)| + |t| + 3) ≤ Real.log ((|(m : ℝ)| + 3) * (1 + |t|)) :=
                Real.log_le_log (by positivity) h1
              rw [Real.log_mul (by positivity) (by positivity)] at h2
              linarith
            have hLcmp : L + Real.log (|(m : ℝ)| + |t| + 3) + 2 ≤ Lm + Real.log (1 + |t|) := by
              rw [hLmdef]; linarith
            have hlogargnn : 0 ≤ Real.log (|(m : ℝ)| + |t| + 3) :=
              Real.log_nonneg (by have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t; linarith)
            have hpow : (L + Real.log (|(m : ℝ)| + |t| + 3) + 2) ^ (6 : ℕ)
                ≤ (Lm + Real.log (1 + |t|)) ^ (6 : ℕ) :=
              pow_le_pow_left₀ (by linarith [hLpos.le, hlogargnn]) hLcmp 6
            have hGval : G ((σr : ℂ) + (t : ℂ) * Complex.I)
                = mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)
                  * Zc ((σr : ℂ) + (t : ℂ) * Complex.I) := rfl
            rw [hGval, norm_mul]
            calc ‖mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                  * ‖Zc ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ (10 ^ 7 * Pa.θ * Pa.N ^ σr * (1 + (Pa.θ * t) ^ 2)⁻¹)
                  * (C_z * (d : ℝ) * (L + Real.log (|(m : ℝ)| + |t| + 3) + 2) ^ (6 : ℕ)) :=
                  mul_le_mul hmv hzcb (norm_nonneg _)
                    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le)
                      (Real.rpow_nonneg hNpos.le _)) (inv_nonneg.mpr (by positivity)))
              _ ≤ (10 ^ 7 * Pa.θ * Pa.N ^ σr * (1 + (Pa.θ * t) ^ 2)⁻¹)
                  * (C_z * (d : ℝ) * (Lm + Real.log (1 + |t|)) ^ (6 : ℕ)) := by
                  have hlog1t : 0 ≤ Real.log (1 + |t|) :=
                    Real.log_nonneg (by have h := abs_nonneg t; linarith)
                  apply mul_le_mul_of_nonneg_left
                  · exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hCznn (Nat.cast_nonneg d))
                  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le)
                      (Real.rpow_nonneg hNpos.le _)) (inv_nonneg.mpr (by positivity))
              _ = (10 ^ 7 * Pa.θ * Pa.N ^ σr * C_z * (d : ℝ))
                  * ((1 + (Pa.θ * t) ^ 2)⁻¹ * (Lm + Real.log (1 + |t|)) ^ (6 : ℕ)) := by ring
          have hfar := hKFar (fun t : ℝ => G ((σr : ℂ) + (t : ℂ) * Complex.I)) Pa.θ T Lm
            (10 ^ 7 * Pa.θ * Pa.N ^ σr * C_z * (d : ℝ)) Pa.hθ0 hT1 hLmnn hKznn hint hbd
          -- ### the splitting and the norm estimate
          have hsplit := IntegralSplitIcc (fun t : ℝ => G ((σr : ℂ) + (t : ℂ) * Complex.I)) T hInt
          have hnorm : ‖∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖
              ≤ ‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
                + ((∫ t in Set.Ioi T, ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖)
                  + (∫ t in Set.Iio (-T), ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖)) := by
            rw [hsplit]
            have hb : ‖∫ t in Set.Ioi T, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ ∫ t in Set.Ioi T, ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ :=
              norm_integral_le_integral_norm _
            have hc : ‖∫ t in Set.Iio (-T), G ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ ∫ t in Set.Iio (-T), ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ :=
              norm_integral_le_integral_norm _
            have hab : ‖(∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I))
                  + (∫ t in Set.Ioi T, G ((σr : ℂ) + (t : ℂ) * Complex.I))‖
                ≤ ‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
                  + ‖∫ t in Set.Ioi T, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ := norm_add_le _ _
            calc ‖(∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I))
                    + (∫ t in Set.Ioi T, G ((σr : ℂ) + (t : ℂ) * Complex.I))
                    + (∫ t in Set.Iio (-T), G ((σr : ℂ) + (t : ℂ) * Complex.I))‖
                ≤ ‖(∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I))
                    + (∫ t in Set.Ioi T, G ((σr : ℂ) + (t : ℂ) * Complex.I))‖
                  + ‖∫ t in Set.Iio (-T), G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ := norm_add_le _ _
              _ ≤ (‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
                    + ‖∫ t in Set.Ioi T, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖)
                  + ‖∫ t in Set.Iio (-T), G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ :=
                  add_le_add hab (le_refl _)
              _ ≤ (‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
                    + ∫ t in Set.Ioi T, ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖)
                  + ∫ t in Set.Iio (-T), ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ :=
                  add_le_add (add_le_add (le_refl _) hb) hc
            exact (add_assoc _ _ _).le
          -- ### the three estimates
          set KZ : ℝ := 10 ^ 7 * (C_z * (d : ℝ)) * (4 * L) ^ (6 : ℕ) with hKZdef
          set Kz : ℝ := 10 ^ 7 * Pa.θ * Pa.N ^ σr * C_z * (d : ℝ) with hKzdef
          set Tgt : ℝ := C * C_z * RR * (4 * (d : ℝ)) * Pa.N * L ^ 6 with hTgtdef
          set Wq : ℝ := C_z * (d : ℝ) * Pa.N * L ^ 6 with hWqdef
          have hWqnn : 0 ≤ Wq := by
            rw [hWqdef]
            exact mul_nonneg (mul_nonneg (mul_nonneg hCznn (by exact_mod_cast Nat.zero_le d))
              hNpos.le) (pow_nonneg hLpos.le 6)
          have hTgtpos : 0 < Tgt := by
            rw [hTgtdef]
            exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hCpos hzc.1) hRRpos)
                (by positivity)) hNpos) (pow_pos hLpos 6)
          have hX : (0 : ℝ) ≤ C_z * (d : ℝ) * RR * Pa.N * L ^ 6 :=
            mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCznn (by positivity)) hRRpos.le)
              hNpos.le) (pow_nonneg hLpos.le 6)
          have hP1 : Real.pi * KZ * (Pa.N * RR) ≤ Tgt / 4 := by
            have h1 : Real.pi * 10 ^ 7 * 4 ^ 6 ≤ (1 / 4) * C * 4 := by
              have h2 : (10 : ℝ) ^ 7 * 4 ^ 6 * 16 ≤ C := by linarith only [hC40]
              linarith only [Real.pi_lt_four, h2]
            calc Real.pi * KZ * (Pa.N * RR)
                = (Real.pi * 10 ^ 7 * 4 ^ 6) * (C_z * (d : ℝ) * RR * Pa.N * L ^ 6) := by
                  rw [hKZdef]; ring
              _ ≤ ((1 / 4) * C * 4) * (C_z * (d : ℝ) * RR * Pa.N * L ^ 6) :=
                  mul_le_mul_of_nonneg_right h1 hX
              _ = Tgt / 4 := by rw [hTgtdef]; ring
          have hCN : Pa.N ^ (1 - δ) * Pa.C ^ δ ≤ Pa.N * RR := by
            have hδpos : 0 < δ := by
              rw [hδdef, Work.FIArea6Hecke.deltaC]
              refine lt_min ?_ ?_
              · have hd0 : (0 : ℝ) < (d : ℝ) ^ ε :=
                  Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd1)) _
                have hlT : 0 < Real.log (Work.FIArea6Hecke.heightT Pa) + 1 := by
                  have := Real.log_nonneg
                    (show (1 : ℝ) ≤ Work.FIArea6Hecke.heightT Pa from by rw [← hTdef]; exact hT1)
                  linarith
                positivity
              · positivity
            have hNpow : Real.exp (-(Pa.η * δ * L)) ≤ RR := by
              rw [hδdef, hLdef, hRRdef]
              exact hzc_Npow_le_R Pa d ε c_h c hd1 hc16 hc_h hlogPz6 hlogTle hL1
            have h1 : Pa.N ^ (1 - δ) * Pa.C ^ δ = Pa.N * (Pa.C / Pa.N) ^ δ := by
              rw [Real.rpow_sub hNpos, Real.rpow_one, Real.div_rpow hCpos'.le hNpos.le]
              field_simp
            rw [h1]
            have h2 : (Pa.C / Pa.N) ^ δ ≤ (Pa.N ^ (-Pa.η)) ^ δ := by
              have hle : Pa.C / Pa.N ≤ Pa.N ^ (-Pa.η) := by
                rw [div_le_iff₀ hNpos]
                calc Pa.C ≤ Pa.N ^ (1 - Pa.η) := Pa.hC2
                  _ = Pa.N ^ (-Pa.η) * Pa.N := by
                      rw [Real.rpow_sub hNpos, Real.rpow_one, Real.rpow_neg hNpos.le]
                      field_simp
              exact Real.rpow_le_rpow (by positivity) hle hδpos.le
            have h3 : (Pa.N ^ (-Pa.η)) ^ δ = Pa.N ^ (-Pa.η * δ) := by
              rw [← Real.rpow_mul hNpos.le]
            have h4 : Pa.N ^ (-Pa.η * δ) = Real.exp (-(Pa.η * δ * L)) := by
              rw [Real.rpow_def_of_pos hNpos, hLdef]
              congr 1
              ring
            refine mul_le_mul_of_nonneg_left ?_ hNpos.le
            exact le_trans h2 (le_trans (le_of_eq h3) (le_trans (le_of_eq h4) hNpow))
          have hP2 : 2 * KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L)) ≤ Tgt / 4 := by
            have hδle1 : δ ≤ 1 := by
              have h1 : δ ≤ 1 / Real.log (Pa.Pz : ℝ) := by
                rw [hδdef, Work.FIArea6Hecke.deltaC]; exact min_le_right _ _
              have h2 : (1 : ℝ) ≤ Real.log (Pa.Pz : ℝ) := by linarith
              calc δ ≤ 1 / Real.log (Pa.Pz : ℝ) := h1
                _ ≤ 1 := (div_le_one hlogPzpos).mpr h2
            have heL : Real.exp 1 / L ≤ 3 := by
              have h1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_three; linarith
              rw [div_le_iff₀ hLpos]; linarith only [h1, hL1]
            have hsum : δ + Real.exp 1 / L ≤ 4 := by linarith
            have hA : 2 * KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L))
                ≤ 2 * KZ * (1 / T) * (Pa.N * 4) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (by positivity))
              exact mul_le_mul_of_nonneg_left hsum hNpos.le
            have hRT : (1 : ℝ) ≤ RR * Real.exp (Real.sqrt L) := by
              have h2 : Real.exp (-(Real.sqrt L / 8)) * Real.exp (Real.sqrt L)
                  ≤ RR * Real.exp (Real.sqrt L) :=
                mul_le_mul_of_nonneg_right hRRge (Real.exp_pos _).le
              have h3 : (1 : ℝ) ≤ Real.exp (-(Real.sqrt L / 8)) * Real.exp (Real.sqrt L) := by
                rw [← Real.exp_add]
                apply Real.one_le_exp
                have := Real.sqrt_nonneg L
                linarith
              exact le_trans h3 h2
            have hTbd : 2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / T) ≤ (1 / 4) * C * RR * 4 := by
              have h3 : (1 : ℝ) / T ≤ 1 / (5 * Real.exp (Real.sqrt L)) :=
                one_div_le_one_div_of_le (by positivity) hT15
              have h4 : 2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / T)
                  ≤ 2 * 10 ^ 7 * 4 ^ 6 * 4 / (5 * Real.exp (Real.sqrt L)) := by
                have h4' : 2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / T)
                    ≤ 2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / (5 * Real.exp (Real.sqrt L))) :=
                  mul_le_mul_of_nonneg_left h3 (by norm_num)
                calc 2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / T)
                    ≤ 2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / (5 * Real.exp (Real.sqrt L))) := h4'
                  _ = 2 * 10 ^ 7 * 4 ^ 6 * 4 / (5 * Real.exp (Real.sqrt L)) := by ring
              have h5 : 2 * 10 ^ 7 * 4 ^ 6 * 4 / (5 * Real.exp (Real.sqrt L))
                  ≤ (1 / 4) * C * RR * 4 := by
                rw [div_le_iff₀ (by positivity)]
                have h6 : 20 * C ≤ 20 * C * (RR * Real.exp (Real.sqrt L)) := by
                  have h7 := mul_le_mul_of_nonneg_left hRT (by positivity : (0 : ℝ) ≤ 20 * C)
                  linarith [h7]
                have h8 : (2 : ℝ) * 10 ^ 7 * 4 ^ 6 * 4 * 5 ≤ 20 * C := by linarith only [hC40]
                linarith only [h6, h8]
              linarith [h4, h5]
            calc 2 * KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L))
                ≤ 2 * KZ * (1 / T) * (Pa.N * 4) := hA
              _ = (2 * 10 ^ 7 * 4 ^ 6 * 4 * (1 / T)) * (C_z * (d : ℝ) * Pa.N * L ^ 6) := by
                  rw [hKZdef]; ring
              _ ≤ ((1 / 4) * C * RR * 4) * (C_z * (d : ℝ) * Pa.N * L ^ 6) :=
                  mul_le_mul_of_nonneg_right hTbd (by positivity)
              _ = Tgt / 4 := by rw [hTgtdef]; ring
          have hP3 : K_Far * Kz / (Pa.θ ^ 2 * T) * (Lm + Real.log (2 * T) + 1) ^ (6 : ℕ)
              ≤ Tgt / 4 := by
            have hmL : Real.log (|(m : ℝ)| + 3) ≤ 2 * L := by
              have h1 : |(m : ℝ)| + 3 ≤ 7 * Real.exp (Real.sqrt L) :=
                by linarith only [hm, Real.one_le_exp (Real.sqrt_nonneg L)]
              have h2 : Real.log (|(m : ℝ)| + 3) ≤ Real.log (7 * Real.exp (Real.sqrt L)) :=
                Real.log_le_log (by positivity) h1
              rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h2
              have h3 : Real.log 7 ≤ 2 := by
                rw [Real.log_le_iff_le_exp (by norm_num)]
                have h4 : (2.7 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 :=
                  pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 2
                have h5 : (Real.exp 1) ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
                linarith only [h4, h5.le, h5.ge]
              have h6 : Real.sqrt L ≤ L := by
                rw [Real.sqrt_le_iff]
                exact ⟨hLpos.le, by nlinarith only [mul_le_mul_of_nonneg_left hL1 hLpos.le]⟩
              linarith
            have hlog2T : Real.log (2 * T) ≤ 4 * L := by
              have h1 : 2 * T ≤ 30 * Real.exp (Real.sqrt L) := by
                linarith only [hTe, Real.one_le_exp (Real.sqrt_nonneg L)]
              have h2 : Real.log (2 * T) ≤ Real.log (30 * Real.exp (Real.sqrt L)) :=
                Real.log_le_log (by positivity) h1
              rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h2
              have h3 : Real.log 30 ≤ 4 := by
                rw [Real.log_le_iff_le_exp (by norm_num)]
                have h4 : (2.7 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
                  pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 4
                have h5 : (Real.exp 1) ^ 4 = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
                linarith only [h4, h5.le, h5.ge]
              have h6 : Real.sqrt L ≤ L := by
                rw [Real.sqrt_le_iff]
                exact ⟨hLpos.le, by nlinarith only [mul_le_mul_of_nonneg_left hL1 hLpos.le]⟩
              linarith
            have hL9 : Lm + Real.log (2 * T) + 1 ≤ 9 * L := by
              rw [hLmdef]; linarith
            have hpow : (Lm + Real.log (2 * T) + 1) ^ (6 : ℕ) ≤ (9 * L) ^ (6 : ℕ) :=
              pow_le_pow_left₀ (by
                have := Real.log_nonneg (show (1:ℝ) ≤ 2 * T by linarith only [hT1])
                linarith only [this, hLmnn]) hL9 6
            have hNσ : Pa.N ^ σr = Pa.N * Real.exp 1 := by
              rw [hσrdef, Real.rpow_add hNpos, Real.rpow_one]
              congr 1
              rw [Real.rpow_def_of_pos hNpos, hLdef, mul_one_div, div_self (ne_of_gt hLpos)]
            have hθT : 5 * RR * Real.exp (Real.sqrt L) / (256 * L ^ 3) ≤ Pa.θ * T := by
              have h1 : RR / (256 * L ^ 3) * (5 * Real.exp (Real.sqrt L)) ≤ Pa.θ * T :=
                mul_le_mul hθgt.le hT15 (by positivity) Pa.hθ0.le
              have h2 : RR / (256 * L ^ 3) * (5 * Real.exp (Real.sqrt L))
                  = 5 * RR * Real.exp (Real.sqrt L) / (256 * L ^ 3) := by ring
              linarith [h1, h2.le, h2.ge]
            have hRR2 : Real.exp (3 * Real.sqrt L / 4) ≤ RR ^ 2 * Real.exp (Real.sqrt L) := by
              have h1 : Real.exp (-(Real.sqrt L / 4)) ≤ RR ^ 2 := by
                have h2 : Real.exp (-(Real.sqrt L / 8)) ^ 2 ≤ RR ^ 2 :=
                  pow_le_pow_left₀ (Real.exp_pos _).le hRRge 2
                have h3 : Real.exp (-(Real.sqrt L / 8)) ^ 2 = Real.exp (-(Real.sqrt L / 4)) := by
                  rw [← Real.exp_nat_mul]
                  congr 1
                  ring
                linarith [h2, h3.le, h3.ge]
              have h4 : Real.exp (-(Real.sqrt L / 4)) * Real.exp (Real.sqrt L)
                  = Real.exp (3 * Real.sqrt L / 4) := by
                rw [← Real.exp_add]; congr 1; ring
              calc Real.exp (3 * Real.sqrt L / 4)
                  = Real.exp (-(Real.sqrt L / 4)) * Real.exp (Real.sqrt L) := h4.symm
                _ ≤ RR ^ 2 * Real.exp (Real.sqrt L) :=
                    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
            have hΛf' : αf * L ^ 3 ≤ Real.exp (3 * Real.sqrt L / 4) := (hΛf L (hΛf_le.trans hLge)).2.2.1
            have hαle : K_Far * 10 ^ 7 * 9 ^ 6 * Real.exp 1 * 256 / 5 ≤ αf * 10 ^ 40 := by
              rw [hαfdef]
              nlinarith only [mul_pos hKFarpos (Real.exp_pos 1)]
            have hfin : K_Far * 10 ^ 7 * 9 ^ 6 * Real.exp 1 * 256 / 5 * L ^ 3
                ≤ C * RR ^ 2 * Real.exp (Real.sqrt L) := by
              have h1 : αf * 10 ^ 40 * L ^ 3 ≤ 10 ^ 40 * Real.exp (3 * Real.sqrt L / 4) := by
                have h2 := mul_le_mul_of_nonneg_right hΛf' (by norm_num : (0 : ℝ) ≤ 10 ^ 40)
                linarith [h2]
              have h3 : K_Far * 10 ^ 7 * 9 ^ 6 * Real.exp 1 * 256 / 5 * L ^ 3
                  ≤ αf * 10 ^ 40 * L ^ 3 :=
                mul_le_mul_of_nonneg_right hαle (pow_nonneg hLpos.le 3)
              have h4 : (10 : ℝ) ^ 40 * Real.exp (3 * Real.sqrt L / 4)
                  ≤ 10 ^ 40 * (RR ^ 2 * Real.exp (Real.sqrt L)) :=
                mul_le_mul_of_nonneg_left hRR2 (by norm_num)
              have h5 : (10 : ℝ) ^ 40 * (RR ^ 2 * Real.exp (Real.sqrt L))
                  ≤ C * (RR ^ 2 * Real.exp (Real.sqrt L)) :=
                mul_le_mul_of_nonneg_right hC40 (by positivity)
              linarith [h1, h3, h4, h5]
            have hP3a : K_Far * Kz / (Pa.θ ^ 2 * T) * (Lm + Real.log (2 * T) + 1) ^ (6 : ℕ)
                ≤ K_Far * Kz / (Pa.θ ^ 2 * T) * (9 * L) ^ (6 : ℕ) := by
              apply mul_le_mul_of_nonneg_left hpow
              rw [hKzdef]; positivity
            have hP3b : K_Far * Kz / (Pa.θ ^ 2 * T) * (9 * L) ^ (6 : ℕ)
                ≤ (K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6) * (Wq / (Pa.θ * T)) := by
              rw [hKzdef, hNσ, hWqdef]
              have hθne : Pa.θ ≠ 0 := ne_of_gt Pa.hθ0
              have hTne : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hT1)
              have hLne : L ≠ 0 := ne_of_gt hLpos
              apply le_of_eq
              field_simp
              try ring
            have hθTinv : 1 / (Pa.θ * T) ≤ 256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L)) := by
              have h1 := one_div_le_one_div_of_le
                (by positivity : (0 : ℝ) < 5 * RR * Real.exp (Real.sqrt L) / (256 * L ^ 3)) hθT
              have h2 : 1 / (5 * RR * Real.exp (Real.sqrt L) / (256 * L ^ 3))
                  = 256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L)) := by
                rw [one_div_div]
              linarith [h1, h2.le, h2.ge]
            have hP3c : (K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6) * (Wq / (Pa.θ * T))
                ≤ (K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6)
                  * (Wq * (256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L)))) := by
              refine mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left ((one_div (Pa.θ * T)).symm.trans_le hθTinv) hWqnn) ?_
              exact mul_nonneg (mul_nonneg (mul_nonneg hKFarpos.le (by norm_num))
                (Real.exp_pos 1).le) (by norm_num)
            have hP3d : (K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6)
                  * (Wq * (256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L)))) ≤ C * RR * Wq := by
              have hkey : (K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6)
                    * (256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L))) ≤ C * RR := by
                rw [mul_div_assoc', div_le_iff₀ (by positivity)]
                have hRRsq : RR * RR = RR ^ 2 := by ring
                nlinarith only [hfin, hRRsq]
              calc (K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6)
                    * (Wq * (256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L))))
                  = ((K_Far * 10 ^ 7 * Real.exp 1 * 9 ^ 6)
                    * (256 * L ^ 3 / (5 * RR * Real.exp (Real.sqrt L)))) * Wq := by ring
                _ ≤ (C * RR) * Wq := mul_le_mul_of_nonneg_right hkey hWqnn
            have hfinal3 : C * RR * Wq = Tgt / 4 := by
              rw [hTgtdef, hWqdef]; ring
            exact hP3a.trans (hP3b.trans (hP3c.trans (hP3d.trans (le_of_eq hfinal3))))
          -- ### the assembly
          have hp1' : Real.pi * KZ * (Pa.N ^ (1 - δ) * Pa.C ^ δ) ≤ Real.pi * KZ * (Pa.N * RR) := by
            have h1 : 0 ≤ Real.pi * KZ := by rw [hKZdef]; positivity
            exact mul_le_mul_of_nonneg_left hCN h1
          have hsum3 : ‖∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (3 / 4) * Tgt := by
            calc ‖∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ ‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
                  + ((∫ t in Set.Ioi T, ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖)
                    + (∫ t in Set.Iio (-T), ‖G ((σr : ℂ) + (t : ℂ) * Complex.I)‖)) := hnorm
              _ ≤ (Real.pi * KZ * (Pa.N * RR)
                    + 2 * KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L)))
                    + (K_Far * Kz / (Pa.θ ^ 2 * T) * (Lm + Real.log (2 * T) + 1) ^ (6 : ℕ)) := by
                  have h2 : 2 * KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L))
                      = 2 * ((10 ^ 7 * (C_z * (d : ℝ)) * (4 * L) ^ (6 : ℕ)) * (1 / T)
                          * (Pa.N * (δ + Real.exp 1 / L))) := by rw [hKZdef]; ring
                  linarith [hmid', hp1', hfar, h2.le, h2.ge]
              _ ≤ Tgt / 4 + Tgt / 4 + Tgt / 4 := by linarith [hP1, hP2, hP3]
              _ = (3 / 4) * Tgt := by ring
          calc ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
              = ‖(1 / (2 * Real.pi)) * ∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ := by
                  rw [hTsum_eq]
            _ = (1 / (2 * Real.pi)) * ‖∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I)‖ := by
                rw [norm_mul, show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
                    push_cast; try ring]
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
            _ ≤ (1 / (2 * Real.pi)) * ((3 / 4) * Tgt) :=
                mul_le_mul_of_nonneg_left hsum3 (by positivity)
            _ ≤ Tgt := by
                rw [← mul_assoc]
                have h2 : (1 / (2 * Real.pi)) * (3 / 4) ≤ 1 := by
                  rw [div_mul_eq_mul_div, div_le_one (by positivity)]
                  linarith only [Real.pi_gt_three]
                exact mul_le_of_le_one_left hTgtpos.le h2
            _ = C * C_z * RR * (4 * (d : ℝ)) * Pa.N * L ^ 6 := by rw [hTgtdef]
        · -- ### the degenerate case: the Mellin integral vanishes
          have hzero : (∫ t : ℝ, mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)
                * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σr : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
            have hcongr : (∫ t : ℝ, mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)
                  * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σr : ℂ) + (t : ℂ) * Complex.I))
                = ∫ t : ℝ, G ((σr : ℂ) + (t : ℂ) * Complex.I) := by
              refine integral_congr_ae ?_
              filter_upwards with t
              show mellin (fun u : ℝ => (p u : ℂ)) ((σr : ℂ) + (t : ℂ) * Complex.I)
                  * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σr : ℂ) + (t : ℂ) * Complex.I)
                = G ((σr : ℂ) + (t : ℂ) * Complex.I)
              rw [hZeq t]
            rw [hcongr, integral_undef hInt]
          rw [hMell, hzero, mul_zero, norm_zero]
          have h1 := hzc.1
          have h2 : (0 : ℝ) ≤ C * C_z * RR * (4 * (d : ℝ)) * Pa.N * L ^ 6 :=
            mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCpos.le hCznn)
              hRRpos.le) (by positivity)) hNpos.le) (pow_nonneg hLpos.le 6)
          linarith
    rw [hRRdef, hLdef] at hmain
    exact hmain
  exact hgoal

end

end Work.FIArea6Road
