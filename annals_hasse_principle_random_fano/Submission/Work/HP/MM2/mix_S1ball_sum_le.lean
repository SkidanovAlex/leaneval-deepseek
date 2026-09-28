import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.S1ball_le
import Submission.Work.HP.MM2.mix_arith
import Submission.Work.HP.MM2.ss1_DeltaXY_gcd_ge_one
import Submission.Work.HP.MM2.zetaR_le_two
import Submission.Work.HP.MM2.Sstar1_mix_tail_arith_aux
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.bigW_le_pow

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace Work.HP.MM2
open Work.HP

/-! ## Elementary inputs -/

/-- The volume of the unit ball in `ℝ^R` is positive for `R ≥ 1`. -/
private lemma ballVol_pos_aux (R : ℕ) (hR : 1 ≤ R) : 0 < ballVol R := by
  haveI : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  have hg : 0 < Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    have h1 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : 0 < Real.Gamma ((R : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have h := EuclideanSpace.volume_closedBall (Fin R) (0 : EuclideanSpace ℝ (Fin R)) 1
  simp only [Fintype.card_fin] at h
  have h2 : ballVol R = Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    unfold ballVol
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), one_pow,
      ENNReal.toReal_ofReal (le_of_lt hg)]
    ring
  rw [h2]; exact hg

/-- `1 ≤ λ_{N-1}(Λ_{ν(x)})` for primitive `x`. -/
private lemma one_le_lamX_aux (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (x : Fin (n + 1) → ℤ) (hx : IsPrim x) : 1 ≤ lamX d n x := by
  have hc : IsPrim (veronese d n x) := isPrim_veronese d n (by omega) hx
  have hrk : rk (latOrth (veronese d n x)) = NN d n - 1 :=
    LCD_rk_latOrth (veronese d n x) hc
  have hN : 6 ≤ NN d n := six_le_NN d n hd hdn
  rw [lamX]
  exact LCD_one_le_lam _ (by omega) (by rw [hrk])

/-- `1 ≤ Δ(x,y) · |𝓖(x,y)|`. -/
private lemma one_le_DeltaXY_gcdNatAbs_aux (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d)
    (hn : 1 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hLI : LinearIndependent ℤ ![x, y]) :
    1 ≤ DeltaXY d n x y * (((gcdMinors2 x y).natAbs : ℕ) : ℝ) := by
  have h := ss1_DeltaXY_gcd_ge_one d n hd hn x y hx hy hLI
  have hcast : (((gcdMinors2 x y).natAbs : ℕ) : ℝ) = |(gcdMinors2 x y : ℝ)| := by
    rw [Nat.cast_natAbs]
    norm_num
  have hΔ : 0 ≤ DeltaXY d n x y := by
    rw [DeltaXY, wedgeNorm]
    exact div_nonneg (mul_nonneg (eNorm_toR_nonneg _) (eNorm_toR_nonneg _)) (Real.sqrt_nonneg _)
  calc 1 ≤ DeltaXY d n x y * (gcdMinors2 x y : ℝ) := h
    _ ≤ DeltaXY d n x y * |(gcdMinors2 x y : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hΔ
    _ = DeltaXY d n x y * (((gcdMinors2 x y).natAbs : ℕ) : ℝ) := by rw [hcast]

/-- `x ^ k ≤ y ^ (a * k)` when `x ≤ y ^ a`, `x ≥ 0`, `y ≥ 0`. -/
private lemma pow_le_rpow_mul_aux {x y a : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y ^ a) (hy0 : 0 ≤ y)
    (k : ℕ) : x ^ k ≤ y ^ (a * ((k : ℕ) : ℝ)) := by
  have h1 : x ^ k ≤ (y ^ a) ^ k := pow_le_pow_left₀ hx0 hxy k
  have h2 : (y ^ a) ^ k = y ^ (a * ((k : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (y ^ a) k, ← Real.rpow_mul hy0 a ((k : ℕ) : ℝ)]
  rwa [h2] at h1

/-- `a ≤ K / b / c` from `a * b * c ≤ K` and `b, c > 0`. -/
private lemma le_div_div_of_mul_le_aux {a b c K : ℝ} (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ K) : a ≤ K / b / c := by
  rw [div_div, le_div_iff₀ (mul_pos hb hc)]
  calc a * (b * c) = a * b * c := by ring
    _ ≤ K := h

/-! ## The arithmetic core

All the `log`-power losses are absorbed by the `(N-2)/4 ≥ 1` slack in `A^{N-2}`; the `W` and
`‖ν(x)‖ = E` factors are absorbed by `mix_arith`'s item
`(log A)^4 · W · E ≤ A^{(N-2)/4}`. -/

private lemma arith_core (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (KS C : ℝ) (hKS : 0 < KS)
    (hC : 0 < C) :
    ∀ A B T μ E W G ζ : ℝ,
      1 ≤ A → 1 ≤ Real.log A → 0 < Real.log B → Real.log B ≤ 2 * Real.log A →
      1 ≤ μ → μ ≤ T → T ≤ A ^ ((3 : ℝ) / 4) →
      1 ≤ W → 1 ≤ E → 1 ≤ G → 0 < ζ → ζ ≤ 2 →
      (Real.log A) ^ 4 * W * E ≤ A ^ (((NN d n - 2 : ℕ) : ℝ) / 4) →
      C * (KS * ((T ^ (NN d n - 2) + T ^ (NN d n - n - 1) * μ ^ (n - 1)) /
              E + T ^ (NN d n - n - 2) * (1 + Real.log T))) * (1 + Real.log A)
        ≤ (32 * C * KS / ballVol (NN d n - 2) + 1) *
            (A ^ (NN d n - 2) * ballVol (NN d n - 2) * G /
              (Real.log B * W * E * ζ)) /
          Real.log A := by
  intro A B T μ E W G ζ hA1 hlogA1 hlogBpos hlogB2 hμ1 hμT hTA hW1 hE1 hG1 hζpos hζ2 hPow
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hNn : n + 3 ≤ NN d n := by
    have h := two_mul_add_two_le_NN d n hd hdn
    omega
  have hVpos : 0 < ballVol (NN d n - 2) := ballVol_pos_aux _ (by omega)
  have hT1 : 1 ≤ T := le_trans hμ1 hμT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hlogAnn : 0 ≤ Real.log A := le_of_lt (lt_of_lt_of_le zero_lt_one hlogA1)
  have hlogTnn : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hTA' : T ≤ A := by
    refine le_trans hTA ?_
    have h : A ^ ((3 : ℝ) / 4) ≤ A ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
    rwa [Real.rpow_one] at h
  have hlogT : Real.log T ≤ Real.log A := Real.log_le_log hT0 hTA'
  -- the bracket
  have hbr : (T ^ (NN d n - 2) + T ^ (NN d n - n - 1) * μ ^ (n - 1)) / E
        + T ^ (NN d n - n - 2) * (1 + Real.log T)
      ≤ 2 * T ^ (NN d n - 2) / E + T ^ (NN d n - n - 2) * (1 + Real.log A) := by
    have h1 : T ^ (NN d n - n - 1) * μ ^ (n - 1) ≤ T ^ (NN d n - 2) := by
      have hμ0 : 0 ≤ μ := le_trans zero_le_one hμ1
      have hμT' : μ ^ (n - 1) ≤ T ^ (n - 1) := pow_le_pow_left₀ hμ0 hμT (n - 1)
      have hTnn : 0 ≤ T ^ (NN d n - n - 1) := pow_nonneg hT0.le _
      calc T ^ (NN d n - n - 1) * μ ^ (n - 1)
          ≤ T ^ (NN d n - n - 1) * T ^ (n - 1) := mul_le_mul_of_nonneg_left hμT' hTnn
        _ = T ^ ((NN d n - n - 1) + (n - 1)) := (pow_add T _ _).symm
        _ = T ^ (NN d n - 2) := by
            have h : (NN d n - n - 1) + (n - 1) = NN d n - 2 := by omega
            rw [h]
    have h2 : T ^ (NN d n - n - 2) * (1 + Real.log T) ≤ T ^ (NN d n - n - 2) * (1 + Real.log A) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hT0.le _)
    have h3 : T ^ (NN d n - 2) + T ^ (NN d n - n - 1) * μ ^ (n - 1) ≤ 2 * T ^ (NN d n - 2) := by
      linarith
    exact add_le_add (div_le_div_of_nonneg_right h3 (by linarith)) h2
  -- the expansion identity
  have hexp : C * (KS * (2 * T ^ (NN d n - 2) / E
          + T ^ (NN d n - n - 2) * (1 + Real.log A))) * (1 + Real.log A)
        * (Real.log B * W * E * ζ) * Real.log A
      = 2 * C * KS * T ^ (NN d n - 2) * (1 + Real.log A) * Real.log B * W * ζ * Real.log A
        + C * KS * T ^ (NN d n - n - 2) * (1 + Real.log A) ^ 2 * Real.log B * W * E * ζ
          * Real.log A := by
    field_simp
  -- the power bounds
  have hTA34 : T ^ (NN d n - 2) ≤ (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2) :=
    pow_le_pow_left₀ hT0.le hTA _
  have hTl : T ^ (NN d n - n - 2) ≤ (A ^ ((3 : ℝ) / 4)) ^ (NN d n - n - 2) :=
    pow_le_pow_left₀ hT0.le hTA _
  have hΘ : (Real.log A) ^ 4 * W * E ≤ (A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2) := by
    refine le_trans hPow ?_
    rw [show (((NN d n - 2 : ℕ) : ℝ) / 4) = (1 / 4) * ((NN d n - 2 : ℕ) : ℝ) by ring,
      ← Real.rpow_natCast (A ^ ((1 : ℝ) / 4)) (NN d n - 2), ← Real.rpow_mul hA0.le]
  have hA34ge1 : 1 ≤ A ^ ((3 : ℝ) / 4) := Real.one_le_rpow hA1 (by norm_num)
  have hnm : NN d n - n - 2 ≤ NN d n - 2 := by
    have := two_mul_add_two_le_NN d n hd hdn
    omega
  have hkmono : (A ^ ((3 : ℝ) / 4)) ^ (NN d n - n - 2) ≤ (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2) :=
    pow_le_pow_right₀ hA34ge1 hnm
  have hcomb : (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2) * (A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2)
      = A ^ (NN d n - 2) := by
    rw [← mul_pow, ← Real.rpow_add hA0, show ((3 : ℝ) / 4 + 1 / 4) = 1 by norm_num,
      Real.rpow_one]
  have hreassoc : ∀ c : ℝ, c * (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2)
        * (A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2)
      = c * ((A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2) * (A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2)) := by
    intro c; ring
  -- factor bounds
  have hfac1 : (1 + Real.log A) * Real.log B * ζ * Real.log A ≤ 8 * (Real.log A) ^ 4 * E := by
    have h1 : 1 + Real.log A ≤ 2 * Real.log A := by linarith
    have hstep : (1 + Real.log A) * Real.log B * ζ * Real.log A
        ≤ (2 * Real.log A) * (2 * Real.log A) * 2 * Real.log A := by gcongr
    have h3 : (Real.log A) ^ 3 ≤ (Real.log A) ^ 4 := pow_le_pow_right₀ hlogA1 (by norm_num)
    calc (1 + Real.log A) * Real.log B * ζ * Real.log A
        ≤ (2 * Real.log A) * (2 * Real.log A) * 2 * Real.log A := hstep
      _ = 8 * (Real.log A) ^ 3 := by ring
      _ ≤ 8 * (Real.log A) ^ 4 := by linarith
      _ ≤ 8 * (Real.log A) ^ 4 * E := le_mul_of_one_le_right (by positivity) hE1
  have hfac2 : (1 + Real.log A) ^ 2 * Real.log B * ζ * Real.log A ≤ 16 * (Real.log A) ^ 4 := by
    have h1 : 1 + Real.log A ≤ 2 * Real.log A := by linarith
    have hstep : (1 + Real.log A) ^ 2 * Real.log B * ζ * Real.log A
        ≤ (2 * Real.log A) ^ 2 * (2 * Real.log A) * 2 * Real.log A := by gcongr
    calc (1 + Real.log A) ^ 2 * Real.log B * ζ * Real.log A
        ≤ (2 * Real.log A) ^ 2 * (2 * Real.log A) * 2 * Real.log A := hstep
      _ = 16 * (Real.log A) ^ 4 := by ring
  -- the two dominant pieces
  have hAt : 2 * C * KS * T ^ (NN d n - 2) * (1 + Real.log A) * Real.log B * W * ζ * Real.log A
      ≤ 16 * C * KS * A ^ (NN d n - 2) := by
    have hgrp : 2 * C * KS * T ^ (NN d n - 2) * (1 + Real.log A) * Real.log B * W * ζ
          * Real.log A
        = 2 * C * KS * W * T ^ (NN d n - 2) * ((1 + Real.log A) * Real.log B * ζ * Real.log A) := by
      ring
    rw [hgrp]
    calc 2 * C * KS * W * T ^ (NN d n - 2) * ((1 + Real.log A) * Real.log B * ζ * Real.log A)
        ≤ 2 * C * KS * W * T ^ (NN d n - 2) * (8 * (Real.log A) ^ 4 * E) := by gcongr
      _ = 16 * C * KS * T ^ (NN d n - 2) * ((Real.log A) ^ 4 * W * E) := by ring
      _ ≤ 16 * C * KS * (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2)
            * ((A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2)) := by gcongr
      _ = 16 * C * KS * A ^ (NN d n - 2) := by rw [hreassoc, hcomb]
  have hBt : C * KS * T ^ (NN d n - n - 2) * (1 + Real.log A) ^ 2 * Real.log B * W * E * ζ
        * Real.log A
      ≤ 16 * C * KS * A ^ (NN d n - 2) := by
    have hgrp : C * KS * T ^ (NN d n - n - 2) * (1 + Real.log A) ^ 2 * Real.log B * W * E * ζ
          * Real.log A
        = C * KS * W * E * T ^ (NN d n - n - 2)
            * ((1 + Real.log A) ^ 2 * Real.log B * ζ * Real.log A) := by ring
    rw [hgrp]
    calc C * KS * W * E * T ^ (NN d n - n - 2)
          * ((1 + Real.log A) ^ 2 * Real.log B * ζ * Real.log A)
        ≤ C * KS * W * E * T ^ (NN d n - n - 2) * (16 * (Real.log A) ^ 4) := by gcongr
      _ = 16 * C * KS * T ^ (NN d n - n - 2) * ((Real.log A) ^ 4 * W * E) := by ring
      _ ≤ 16 * C * KS * (A ^ ((3 : ℝ) / 4)) ^ (NN d n - n - 2)
            * ((A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2)) := by gcongr
      _ ≤ 16 * C * KS * (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2)
            * ((A ^ ((1 : ℝ) / 4)) ^ (NN d n - 2)) := by gcongr
      _ = 16 * C * KS * A ^ (NN d n - 2) := by rw [hreassoc, hcomb]
  -- the cross-multiplied bound
  have hcross : C * (KS * (2 * T ^ (NN d n - 2) / E
          + T ^ (NN d n - n - 2) * (1 + Real.log A))) * (1 + Real.log A)
        * (Real.log B * W * E * ζ) * Real.log A
      ≤ (32 * C * KS / ballVol (NN d n - 2) + 1)
          * (A ^ (NN d n - 2) * ballVol (NN d n - 2) * G) := by
    rw [hexp]
    have hsum : 2 * C * KS * T ^ (NN d n - 2) * (1 + Real.log A) * Real.log B * W * ζ
            * Real.log A
          + C * KS * T ^ (NN d n - n - 2) * (1 + Real.log A) ^ 2 * Real.log B * W * E * ζ
            * Real.log A
        ≤ 32 * C * KS * A ^ (NN d n - 2) := by linarith [hAt, hBt]
    refine le_trans hsum ?_
    have hkey : 32 * C * KS ≤ (32 * C * KS / ballVol (NN d n - 2) + 1) * ballVol (NN d n - 2) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hVpos)]
      linarith [hVpos]
    have h0 : 0 ≤ A ^ (NN d n - 2) * G := by positivity
    have h1 : 0 ≤ A ^ (NN d n - 2) := by positivity
    calc 32 * C * KS * A ^ (NN d n - 2)
        ≤ ((32 * C * KS / ballVol (NN d n - 2) + 1) * ballVol (NN d n - 2))
            * A ^ (NN d n - 2) := mul_le_mul_of_nonneg_right hkey h1
      _ ≤ ((32 * C * KS / ballVol (NN d n - 2) + 1) * ballVol (NN d n - 2))
            * (A ^ (NN d n - 2) * G) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h1 hG1) (by positivity)
      _ = (32 * C * KS / ballVol (NN d n - 2) + 1)
            * (A ^ (NN d n - 2) * ballVol (NN d n - 2) * G) := by ring
  -- divide back
  have hden : 0 < Real.log B * W * E * ζ := by positivity
  have hfinal : C * (KS * (2 * T ^ (NN d n - 2) / E
          + T ^ (NN d n - n - 2) * (1 + Real.log A))) * (1 + Real.log A)
        ≤ (32 * C * KS / ballVol (NN d n - 2) + 1)
            * (A ^ (NN d n - 2) * ballVol (NN d n - 2) * G / (Real.log B * W * E * ζ))
          / Real.log A := by
    rw [← mul_div_assoc]
    refine le_div_div_of_mul_le_aux hden (lt_of_lt_of_le zero_lt_one hlogA1) ?_
    exact hcross
  refine le_trans ?_ hfinal
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hbr hKS.le) hC.le) (by linarith)

/-- **`S1ball` sum bound for the degenerate part of `D^mix`.** -/
theorem mix_S1ball_sum_le (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) (C : ℝ) (hC : 0 < C) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
        LinearIndependent ℤ ![x, y] →
        Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * Work.HP.MM2.lamX d n x ≤ A ^ ((3 : ℝ) / 4) →
        C * Work.HP.MM2.S1ball d n x ((Work.HP.bigW (Work.HP.wOf B) : ℝ) * Work.HP.MM2.lamX d n x)
            * (1 + Real.log A)
          ≤ K * (A ^ (Work.HP.NN d n - 2) * Work.HP.ballVol (Work.HP.NN d n - 2)
                * Work.HP.DeltaXY d n x y * (((Work.HP.gcdMinors2 x y).natAbs : ℕ) : ℝ)
                / (Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ)
                    * Work.HP.eNorm (Work.HP.veronese d n x) * Work.HP.MM2.zetaR (Work.HP.NN d n - 2)))
              / Real.log A := by
  classical
  obtain ⟨KS, hKSpos, hS1⟩ := S1ball_le d n hd hdn
  have hn1 : 1 ≤ n := le_trans (by omega : 1 ≤ d) hdn
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hVpos : 0 < ballVol (NN d n - 2) := ballVol_pos_aux _ (by omega)
  have hKpos : 0 < 32 * C * KS / ballVol (NN d n - 2) + 1 := by positivity
  obtain ⟨B₁, hB₁⟩ := mix_arith d n hd hdn h22 1
  refine ⟨32 * C * KS / ballVol (NN d n - 2) + 1, max B₁ 2, hKpos, ?_⟩
  intro A B hB hAB hAB2 x y hx hy hLI hxn hWlam
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hB
  have hB2 : (2 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hBpos : 0 < B := by linarith
  have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
  obtain ⟨hAge1, hlogAge1, -, hWge1, -, -, hPowraw, -, -⟩ := hB₁ B hB1 A hAB hAB2 x hxn
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAge1
  have hlogAnn : 0 ≤ Real.log A := by linarith
  have hlogB2 : Real.log B ≤ 2 * Real.log A := by
    have h1 : Real.log (B ^ ((5 : ℝ) / 6)) ≤ Real.log A :=
      Real.log_le_log (Real.rpow_pos_of_pos hBpos _) hAB
    rw [Real.log_rpow hBpos] at h1
    nlinarith
  have hPow' : (Real.log A) ^ 4 * (bigW (wOf B) : ℝ) * eNorm (veronese d n x)
      ≤ A ^ (((NN d n - 2 : ℕ) : ℝ) / 4) := by
    have h1 : (Real.log A) ^ 4 * (bigW (wOf B) : ℝ) * eNorm (veronese d n x)
        / A ^ (((NN d n - 2 : ℕ) : ℝ) / 4) ≤ 1 := by
      simpa using hPowraw
    rwa [div_le_one (Real.rpow_pos_of_pos hApos _)] at h1
  have hlam1 : 1 ≤ lamX d n x := one_le_lamX_aux d n hd hdn x hx
  have hlam0 : 0 ≤ lamX d n x := by linarith
  have hlamT : lamX d n x ≤ (bigW (wOf B) : ℝ) * lamX d n x := by nlinarith
  have hE1 : 1 ≤ eNorm (veronese d n x) :=
    one_le_eNorm (isPrim_ne_zero (isPrim_veronese d n (by omega) hx))
  have hG1 : 1 ≤ DeltaXY d n x y * (((gcdMinors2 x y).natAbs : ℕ) : ℝ) :=
    one_le_DeltaXY_gcdNatAbs_aux d n hd hn1 x y hx hy hLI
  have hζpos : 0 < zetaR (NN d n - 2) := by
    have h6 := six_le_NN d n hd hdn
    exact MDEstimates.zeta_series_pos _ (by omega)
  have hζ2 : zetaR (NN d n - 2) ≤ 2 := by
    have h6 := six_le_NN d n hd hdn
    exact zetaR_le_two _ (by omega)
  have hT1 : 1 ≤ (bigW (wOf B) : ℝ) * lamX d n x := by nlinarith
  have hcore := arith_core d n hd hdn KS C hKSpos hC A B
    ((bigW (wOf B) : ℝ) * lamX d n x) (lamX d n x) (eNorm (veronese d n x))
    ((bigW (wOf B) : ℝ)) (DeltaXY d n x y * (((gcdMinors2 x y).natAbs : ℕ) : ℝ))
    (zetaR (NN d n - 2)) hAge1 hlogAge1 hlogBpos hlogB2 hlam1 hlamT hWlam hWge1 hE1 hG1 hζpos hζ2 hPow'
  have hS1b := hS1 x hx ((bigW (wOf B) : ℝ) * lamX d n x) (lamX d n x) hT1 hlam1 (le_refl _)
  have hGassoc : (32 * C * KS / ballVol (NN d n - 2) + 1) *
        (A ^ (NN d n - 2) * ballVol (NN d n - 2)
          * (DeltaXY d n x y * (((gcdMinors2 x y).natAbs : ℕ) : ℝ))
          / (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * zetaR (NN d n - 2)))
        / Real.log A
      = (32 * C * KS / ballVol (NN d n - 2) + 1) *
        (A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
          * (((gcdMinors2 x y).natAbs : ℕ) : ℝ)
          / (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * zetaR (NN d n - 2)))
        / Real.log A := by ring
  rw [hGassoc] at hcore
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS1b hC.le)
    (by linarith)) hcore

end Work.HP.MM2
