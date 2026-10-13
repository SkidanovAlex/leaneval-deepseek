import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.monoCount_bounds
import Submission.Work.WilkiesH.Interp.V2master.Basic
import Submission.Work.WilkiesH.Interp.V2master.arith_final
import Submission.Work.WilkiesH.Interp.V2master.dV_le_rho
import Submission.Work.WilkiesH.Interp.V2master.log_dV_le

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.WilkiesH.Interp.V2master

open Work.WilkiesH.Interp

-- Master numerical inequality for the `v2` parameters.  Writing `b = bV μ g H`,
-- `d = dV μ g (bV μ g H)`, `N1 = N1V μ g H` and `K = KK μ = 2μ+4 = 1/ρ`, the goal is
--   `(1/4) · b · log K > CM μ · (g+1) · ((d+1)(log(d+1)+1) + log N1 + 1) + (μ+2) · d · g² · log H`.
-- Useful ingredients: `CM μ = 10(μ+2)² + 100`; `bV μ g H = EE μ · (g+1)^A · Lg^B` with
-- `A = B = 100(μ+1)^3`, `Lg = lgNat H = ⌈log H⌉ + 1` and `EE μ = (μ+2)^(40(μ+1)^2)`;
-- `log N1 ≤ (μ+1) log (d+1)` (`Work.WilkiesH.Interp.monoCount_bounds`); and the hypothesis `hd`
-- bounds `d` in terms of `(g+1)^(1/(μ+1)) (b+2)^(μ/(μ+1))`, whence `log (d+1) ≤ c₂ (g+1) Lg`
-- for an explicit constant `c₂` depending on `μ` only.  The exponents `A = B = 100(μ+1)^3` give
-- `(g+1)^(A/(μ+1)) ≥ (g+1)^3` and `Lg^(B/(μ+1)) ≥ Lg`, which covers all growing terms, while
-- `EE μ` covers the constants (`EE μ = (μ+2)^(40(μ+1)^2)`; note `EE μ ≥ 2^40`).

/-- Elementary facts about the `v2` parameters. -/
lemma mr_facts (μ g H : ℕ) (Q Lg ρ x y n : ℝ)
    (hQ : Q = (g : ℝ) + 1) (hLg : Lg = ((lgNat H : ℕ) : ℝ))
    (hρ : ρ = ((rhoN μ g H : ℕ) : ℝ)) (hx : x = ((bV μ g H : ℕ) : ℝ))
    (hy : y = ((dV μ g (bV μ g H) : ℕ) : ℝ)) (hn : n = ((N1V μ g H : ℕ) : ℝ))
    (hn_le : n ≤ (y+1)^(μ+1)) :
    (1 ≤ Q) ∧ (1 ≤ Lg) ∧ (1 ≤ ρ) ∧ (1 ≤ x) ∧ (1 ≤ y) ∧ (0 < n) ∧
    (ρ = ((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2)) ∧
    (Real.log n ≤ ((μ:ℝ)+1) * Real.log (y+1)) ∧
    (Real.log (H:ℝ) ≤ Lg) := by
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hQ]; linarith
  · rw [hLg]; exact_mod_cast lgNat_pos H
  · rw [hρ]; exact_mod_cast one_le_rhoN μ g H
  · rw [hx]; exact_mod_cast one_le_bV μ g H
  · rw [hy]; exact_mod_cast one_le_dV μ g (bV μ g H)
  · rw [hn]; exact_mod_cast one_le_N1V μ g H
  · rw [hρ, hQ, hLg, rhoN]; push_cast; ring
  · have h2 := Real.log_le_log (by rw [hn]; exact_mod_cast one_le_N1V μ g H) hn_le
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith [h2]
  · rw [hLg]; exact log_le_lgNat H

/-- `W ≤ S`, the logarithmic comparison in the master inequality. -/
lemma mr_WS (μ g H : ℕ) (Q Lg ρ : ℝ)
    (hQ : Q = (g:ℝ)+1) (hLg : Lg = ((lgNat H:ℕ):ℝ)) (hρ : ρ = ((rhoN μ g H:ℕ):ℝ))
    (hQ1 : 1 ≤ Q) (hLg1 : 1 ≤ Lg) (hρ1 : 1 ≤ ρ) :
    17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ
      ≤ 17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
        + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg := by
  have hμ0 : (0:ℝ) ≤ (μ:ℝ) := Nat.cast_nonneg μ
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hLgp : 0 < Lg := lt_of_lt_of_le zero_lt_one hLg1
  have hμ2p : (0:ℝ) < (μ:ℝ)+2 := by linarith
  have hAne : ((μ:ℝ)+2) ≠ 0 := ne_of_gt hμ2p
  have hρa : ρ = ((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2) := by
    rw [hρ, hQ, hLg, rhoN]; push_cast; ring
  have hlogρ : Real.log ρ = 40*((μ:ℝ)+1)*Real.log ((μ:ℝ)+2)
      + 100*((μ:ℝ)+1)^2*Real.log Q + 100*((μ:ℝ)+1)^2*Real.log Lg := by
    rw [hρa,
      Real.log_mul (mul_ne_zero (pow_ne_zero _ hAne) (pow_ne_zero _ (ne_of_gt hQp)))
        (pow_ne_zero _ (ne_of_gt hLgp)),
      Real.log_mul (pow_ne_zero _ hAne) (pow_ne_zero _ (ne_of_gt hQp)),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hlogρ]
  have hP2 : Real.log ((μ:ℝ)+2) ≤ 2*((μ:ℝ)+1) := by
    have h1 : Real.log ((μ:ℝ)+2) ≤ (μ:ℝ)+2-1 := Real.log_le_sub_one_of_pos hμ2p
    linarith
  have hQ2 : Real.log Q ≤ Q := by
    have h1 : Real.log Q ≤ Q - 1 := Real.log_le_sub_one_of_pos hQp
    linarith
  have hLg2 : Real.log Lg ≤ Lg := by
    have h1 : Real.log Lg ≤ Lg - 1 := Real.log_le_sub_one_of_pos hLgp
    linarith
  have hA : 40*((μ:ℝ)+1)*Real.log ((μ:ℝ)+2) ≤ 40*((μ:ℝ)+1)*(2*((μ:ℝ)+1)) :=
    mul_le_mul_of_nonneg_left hP2 (by linarith)
  have hB : 100*((μ:ℝ)+1)^2*Real.log Q ≤ 100*((μ:ℝ)+1)^2*Q :=
    mul_le_mul_of_nonneg_left hQ2 (by nlinarith [sq_nonneg ((μ:ℝ)+1)])
  have hCl : 100*((μ:ℝ)+1)^2*Real.log Lg ≤ 100*((μ:ℝ)+1)^2*Lg :=
    mul_le_mul_of_nonneg_left hLg2 (by nlinarith [sq_nonneg ((μ:ℝ)+1)])
  have hA2 : (μ:ℝ) * (40*((μ:ℝ)+1)*Real.log ((μ:ℝ)+2)) ≤ 80*((μ:ℝ)+1)^2*(μ:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hA hμ0
    have h2 : (μ:ℝ) * (40*((μ:ℝ)+1)*(2*((μ:ℝ)+1))) = 80*((μ:ℝ)+1)^2*(μ:ℝ) := by ring
    rw [h2] at h1; exact h1
  have hB2 : (μ:ℝ) * (100*((μ:ℝ)+1)^2*Real.log Q) ≤ 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q := by
    have h1 := mul_le_mul_of_nonneg_left hB hμ0
    have h2 : (μ:ℝ) * (100*((μ:ℝ)+1)^2*Q) = 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q := by ring
    rw [h2] at h1; exact h1
  have hC2 : (μ:ℝ) * (100*((μ:ℝ)+1)^2*Real.log Lg) ≤ 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg := by
    have h1 := mul_le_mul_of_nonneg_left hCl hμ0
    have h2 : (μ:ℝ) * (100*((μ:ℝ)+1)^2*Lg) = 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg := by ring
    rw [h2] at h1; exact h1
  linarith [hA2, hB2, hC2]

/-- The bracket bound. -/
lemma mr_bracket (μ g : ℕ) (Q ρ x y n : ℝ)
    (hQ : Q = (g:ℝ)+1) (hQ1 : 1 ≤ Q) (hx1 : 1 ≤ x) (hρ1 : 1 ≤ ρ) (hy1 : 1 ≤ y)
    (hyb : y + 1 ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
    (hlogy : Real.log (y+1) ≤ 16 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
    (hn_log : Real.log n ≤ ((μ:ℝ)+1) * Real.log (y+1)) :
    (y+1)*(Real.log (y+1)+1) + Real.log n + 1
      ≤ ((μ:ℝ)+3) * ((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)) := by
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  have hμ0 : (0:ℝ) ≤ (μ:ℝ) := Nat.cast_nonneg μ
  have hxρ0 : (0:ℝ) ≤ x/ρ := div_nonneg (by linarith) (by linarith)
  have hW : (0:ℝ) ≤ 17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ := by
    have h1 : (0:ℝ) ≤ Real.log Q := Real.log_nonneg hQ1
    have h2 : (0:ℝ) ≤ Real.log ρ := Real.log_nonneg (by linarith)
    have h4 : (0:ℝ) ≤ (μ:ℝ) * Real.log ρ := mul_nonneg hμ0 h2
    nlinarith [h1, h4, sq_nonneg ((μ:ℝ)+1)]
  have hC0 : (0:ℝ) ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ) := by
    have h1 : (0:ℝ) ≤ 25 := by norm_num
    have h2 : (0:ℝ) ≤ (((μ+1).factorial : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ 8*(g:ℝ)+9 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hxρ0
  have hyl : (1:ℝ) ≤ y + 1 := by linarith
  have hA0 : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
  have hA1 : 1 ≤ (y+1) * (Real.log (y+1) + 1) := by
    have h := mul_le_mul hyl (by linarith : (1:ℝ) ≤ Real.log (y+1)+1) (by norm_num) (by linarith)
    simpa using h
  have hA2 : Real.log (y+1) ≤ (y+1) * (Real.log (y+1)+1) := by
    have h2 : Real.log (y+1) + 1 ≤ (y+1)*(Real.log (y+1)+1) := by
      have h := mul_le_mul hyl (le_refl (Real.log (y+1)+1)) (by linarith [hA0]) (by linarith)
      simpa using h
    linarith
  have hlogyW : Real.log (y+1) + 1
      ≤ 17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ := by linarith [hlogy]
  have hAW : (y+1)*(Real.log (y+1)+1)
      ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
        * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ) := by
    have h1 : (y+1)*(Real.log (y+1)+1)
        ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * (Real.log (y+1)+1) :=
      mul_le_mul_of_nonneg_right hyb (by linarith [hA0])
    have h2 : (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * (Real.log (y+1)+1)
        ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ) :=
      mul_le_mul_of_nonneg_left hlogyW hC0
    linarith [h1, h2]
  have h1 : (y+1)*(Real.log (y+1)+1) + Real.log n + 1
      ≤ (y+1)*(Real.log (y+1)+1) + ((μ:ℝ)+1)*(Real.log (y+1)) + 1 := by linarith
  have h2 : (y+1)*(Real.log (y+1)+1) + ((μ:ℝ)+1)*(Real.log (y+1)) + 1
      ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
        + ((μ:ℝ)+1)*((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ))
        + ((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)) := by
    have ha : ((μ:ℝ)+1)*(Real.log (y+1))
        ≤ ((μ:ℝ)+1)*((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hA2, hAW]) (by linarith)
    have hb : (1:ℝ) ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
        * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ) := by linarith [hA1, hAW]
    linarith [ha, hb]
  have h3 : ((μ:ℝ)+3) * ((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ))
      = (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
        + ((μ:ℝ)+1)*((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ))
        + ((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)) := by ring
  linarith [h1, h2, h3.ge]

/-- The sum bound. -/
lemma mr_sum (μ g H : ℕ) (Q Lg ρ x y n S : ℝ)
    (hS : S = 17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
          + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg)
    (hQ : Q = (g:ℝ)+1) (hQ1 : 1 ≤ Q) (hLg1 : 1 ≤ Lg) (hx1 : 1 ≤ x) (hρ1 : 1 ≤ ρ)
    (hy1 : 1 ≤ y)
    (hyb : y + 1 ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
    (hlogy : Real.log (y+1) ≤ 16 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
    (hn_log : Real.log n ≤ ((μ:ℝ)+1) * Real.log (y+1))
    (hlogH : Real.log (H:ℝ) ≤ Lg)
    (hWS : 17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ ≤ S) :
    CM μ * Q * ((y+1)*(Real.log (y+1)+1) + Real.log n + 1)
      + ((μ:ℝ)+2)*y*(g:ℝ)^2*Real.log (H:ℝ)
      ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)
        * (CM μ * Q * ((μ:ℝ)+3) * S + ((μ:ℝ)+2)*Q^2*Lg) := by
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hρ0 : (0:ℝ) ≤ ρ := by linarith
  have hxρ0 : (0:ℝ) ≤ x/ρ := div_nonneg hx0 hρ0
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hQ0 : (0:ℝ) ≤ Q := by linarith
  have hLg0 : (0:ℝ) ≤ Lg := by linarith
  have hmu0 : (0:ℝ) ≤ (μ:ℝ) := Nat.cast_nonneg μ
  have hCM0 : (0:ℝ) ≤ CM μ := by rw [CM]; nlinarith [sq_nonneg ((μ:ℝ)+2)]
  have hCMQ0 : (0:ℝ) ≤ CM μ * Q := mul_nonneg hCM0 hQ0
  have hmu2 : (0:ℝ) ≤ (μ:ℝ)+2 := by linarith
  have hmu3 : (0:ℝ) ≤ (μ:ℝ)+3 := by linarith
  have hF0 : (0:ℝ) ≤ (((μ+1).factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3n : (0:ℝ) ≤ 8*(g:ℝ)+9 := by linarith
  have hC0 : (0:ℝ) ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF0) h3n) hxρ0
  have hbracket := mr_bracket μ g Q ρ x y n hQ hQ1 hx1 hρ1 hy1 hyb hlogy hn_log
  have hstep1 : CM μ * Q * ((y+1)*(Real.log (y+1)+1) + Real.log n + 1)
      ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
        * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)) := by
    calc CM μ * Q * ((y+1)*(Real.log (y+1)+1) + Real.log n + 1)
        ≤ CM μ * Q * (((μ:ℝ)+3)
            * ((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
              * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ))) :=
          mul_le_mul_of_nonneg_left hbracket hCMQ0
      _ = (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
        * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)) := by ring
  have hg2le : (g:ℝ)^2 ≤ Q^2 := by
    have h1 : (g:ℝ) ≤ Q := by rw [hQ]; linarith
    nlinarith [h1, hg0, sq_nonneg ((g:ℝ)), sq_nonneg Q]
  have hstep2 : ((μ:ℝ)+2)*y*(g:ℝ)^2*Real.log (H:ℝ)
      ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * (((μ:ℝ)+2)*Q^2*Lg) := by
    have ha : ((μ:ℝ)+2)*y*(g:ℝ)^2*Real.log (H:ℝ) ≤ ((μ:ℝ)+2)*y*(g:ℝ)^2*Lg :=
      mul_le_mul_of_nonneg_left hlogH (mul_nonneg (mul_nonneg hmu2 hy0) (sq_nonneg _))
    have hyl' : y ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ) := by linarith
    have hgm : (0:ℝ) ≤ (g:ℝ)^2 * Lg := mul_nonneg (sq_nonneg _) hLg0
    have h1 : y * ((g:ℝ)^2 * Lg)
        ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * ((g:ℝ)^2 * Lg) :=
      mul_le_mul_of_nonneg_right hyl' hgm
    have hgl : ((μ:ℝ)+2)*((g:ℝ)^2 * Lg) ≤ ((μ:ℝ)+2)*(Q^2*Lg) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg2le hLg0) hmu2
    calc ((μ:ℝ)+2)*y*(g:ℝ)^2*Real.log (H:ℝ)
        ≤ ((μ:ℝ)+2)*y*(g:ℝ)^2*Lg := ha
      _ = ((μ:ℝ)+2) * (y * ((g:ℝ)^2 * Lg)) := by ring
      _ ≤ ((μ:ℝ)+2) * ((25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
            * ((g:ℝ)^2 * Lg)) := mul_le_mul_of_nonneg_left h1 hmu2
      _ = (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
            * (((μ:ℝ)+2)*((g:ℝ)^2*Lg)) := by ring
      _ ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * (((μ:ℝ)+2)*(Q^2*Lg)) :=
          mul_le_mul_of_nonneg_left hgl hC0
      _ = (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * (((μ:ℝ)+2)*Q^2*Lg) := by ring
  have hfinal : CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
      ≤ CM μ * Q * ((μ:ℝ)+3) * S :=
    mul_le_mul_of_nonneg_left hWS (mul_nonneg hCMQ0 hmu3)
  calc CM μ * Q * ((y+1)*(Real.log (y+1)+1) + Real.log n + 1)
        + ((μ:ℝ)+2)*y*(g:ℝ)^2*Real.log (H:ℝ)
      ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ))
        + (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)) * (((μ:ℝ)+2)*Q^2*Lg) :=
          add_le_add hstep1 hstep2
    _ = (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
            + ((μ:ℝ)+2)*Q^2*Lg) := by ring
    _ ≤ (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
          * (CM μ * Q * ((μ:ℝ)+3) * S + ((μ:ℝ)+2)*Q^2*Lg) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact add_le_add hfinal (le_refl _)

/-- The final numerical step, reducing to `arith_final`. -/
lemma mr_fin (μ g : ℕ) (Q Lg ρ x : ℝ) (hQ : Q = (g:ℝ)+1) (hQ1 : 1 ≤ Q) (hLg1 : 1 ≤ Lg)
    (hρ1 : 1 ≤ ρ) (hx1 : 1 ≤ x)
    (hρa : ρ = ((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2)) :
    25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)
      * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
           + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg)
        + ((μ:ℝ)+2)*Q^2*Lg) ≤ (1/4)*x := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hρ0 : (0:ℝ) ≤ ρ := by linarith
  have hxρ0 : (0:ℝ) ≤ x/ρ := div_nonneg hx0 hρ0
  have harith := arith_final μ Q Lg hQ1 hLg1
  have hF18 : 8*(g:ℝ)+9 = 8*Q+1 := by rw [hQ]; ring
  have hCMeq : CM μ = 10*((μ:ℝ)+2)^2+100 := by rw [CM]
  have harith' : 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9)
      * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
           + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg)
        + ((μ:ℝ)+2)*Q^2*Lg) ≤ (1/4)*ρ := by
    rw [hCMeq, hF18, hρa]
    exact harith
  have h1 : 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ)
      * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
           + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg)
        + ((μ:ℝ)+2)*Q^2*Lg)
      = (x/ρ) * (25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9)
          * (CM μ * Q * ((μ:ℝ)+3) * (17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
               + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg)
            + ((μ:ℝ)+2)*Q^2*Lg)) := by ring
  rw [h1]
  have h2 := mul_le_mul_of_nonneg_left harith' hxρ0
  have h3 : (x/ρ) * ((1/4)*ρ) = (1/4)*x := by
    field_simp
  linarith [h2, h3.le]

lemma master_reduce (μ g H : ℕ) (hH : 1 ≤ H)
    (Q Lg ρ x y n : ℝ)
    (hQ : Q = (g : ℝ) + 1) (hLg : Lg = ((lgNat H : ℕ) : ℝ))
    (hρ : ρ = ((rhoN μ g H : ℕ) : ℝ)) (hx : x = ((bV μ g H : ℕ) : ℝ))
    (hy : y = ((dV μ g (bV μ g H) : ℕ) : ℝ)) (hn : n = ((N1V μ g H : ℕ) : ℝ))
    (hyb : y + 1 ≤ 25 * (((μ+1).factorial : ℕ) : ℝ) * (8*(g:ℝ)+9) * (x/ρ))
    (hlogy : Real.log (y+1) ≤ 16 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ)
    (hn_le : n ≤ (y+1)^(μ+1)) :
    CM μ * Q * ((y+1)*(Real.log (y+1)+1) + Real.log n + 1)
      + ((μ:ℝ)+2)*y*(g:ℝ)^2*Real.log (H:ℝ) ≤ (1/4)*x := by
  obtain ⟨hQ1, hLg1, hρ1, hx1, hy1, hn1, hρa, hn_log, hlogH⟩ :=
    mr_facts μ g H Q Lg ρ x y n hQ hLg hρ hx hy hn hn_le
  set S : ℝ := 17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
      + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg with hS
  have hWS : 17 + ((μ:ℝ)+1)^2 + Real.log Q + (μ:ℝ)*Real.log ρ ≤ S := by
    rw [hS]; exact mr_WS μ g H Q Lg ρ hQ hLg hρ hQ1 hLg1 hρ1
  have hsum := mr_sum μ g H Q Lg ρ x y n S hS hQ hQ1 hLg1 hx1 hρ1 hy1 hyb hlogy hn_log hlogH hWS
  have hfin := mr_fin μ g Q Lg ρ x hQ hQ1 hLg1 hρ1 hx1 hρa
  exact le_trans hsum hfin

theorem master_ineq (μ g H : ℕ) (hH : 1 ≤ H)
    (hd : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))) :
    (1 / 4) * ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) * Real.log ((Work.WilkiesH.Interp.KK μ : ℕ) : ℝ) >
      Work.WilkiesH.Interp.CM μ * ((g : ℝ) + 1) *
          ((((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 1) *
              (Real.log (((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 1) + 1) +
            Real.log ((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) + 1) +
        (((μ : ℝ) + 2) * ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) *
          (g : ℝ) ^ 2 * Real.log (H : ℝ)) := by
  have hyb0 := dV_le_rho μ g H hd
  have hlog0 := log_dV_le μ g H hyb0
  have hn_le0 : ((N1V μ g H : ℕ) : ℝ)
      ≤ ((((dV μ g (bV μ g H) : ℕ) : ℝ)) + 1)^(μ+1) := by
    have h1 : Work.WilkiesH.monoCount (μ+1) (dV μ g (bV μ g H))
        ≤ (dV μ g (bV μ g H) + 1)^(μ+1) :=
      (monoCount_bounds (μ+1) (dV μ g (bV μ g H)) 0).1
    have h2 : ((N1V μ g H : ℕ) : ℝ) ≤ (((dV μ g (bV μ g H) + 1)^(μ+1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h2
    exact h2
  have hmain := master_reduce μ g H hH ((g:ℝ)+1) (((lgNat H : ℕ)) : ℝ)
      (((rhoN μ g H : ℕ)) : ℝ) (((bV μ g H : ℕ)) : ℝ)
      (((dV μ g (bV μ g H) : ℕ)) : ℝ) (((N1V μ g H : ℕ)) : ℝ)
      rfl rfl rfl rfl rfl rfl hyb0 hlog0 hn_le0
  have hk1 : (1:ℝ) < Real.log ((KK μ : ℕ) : ℝ) := log_KK_gt_one μ
  have hbx0 : (0:ℝ) < (1/4)*((bV μ g H : ℕ) : ℝ) := by
    have h2 : (0:ℝ) < ((bV μ g H : ℕ) : ℝ) := by
      have h := one_le_bV μ g H
      exact_mod_cast (show 0 < bV μ g H by omega)
    linarith
  have hlt : (1/4)*((bV μ g H : ℕ) : ℝ) * 1
      < (1/4)*((bV μ g H : ℕ) : ℝ) * Real.log ((KK μ : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_left hk1 hbx0
  simp only [mul_one] at hlt
  linarith [hmain, hlt]

end Work.WilkiesH.Interp.V2master
