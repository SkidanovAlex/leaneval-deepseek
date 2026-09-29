import Mathlib
import Submission.Work.C17.lead_defs
import Submission.Work.C17.lead_api
import Submission.Work.C17.exp2_defs
import Submission.Work.C17.exp2_mul
import Submission.Work.C17.exp2_inv
import Submission.Work.C17.exp2_dRat

/-!
# Local expansion data at `x = 0` for the anti-invariant functions `Z2, Z3, Y2, Y3`

This file proves `Work.C17.local_dw`: the leading terms at `x = 0` of the four rational
functions

`Z₂ = u₂ − σu₂`,  `Z₃ = u₃ − σu₃`,  `Y₂ = w₂ − σw₂`,  `Y₃ = w₃ − σw₃`

(see `Submission.Work.C17.lead_defs` for `u₂, u₃, w₂, w₃, Z₂, Z₃, Y₂, Y₃` and `sigmaQ`).

The starting data are the two-term expansions of `rhoQ, dRat rhoQ, P₀Q, P₁Q, P₂Q` and of the
quotient `P₁Q/P₂Q` (`Work.C17.local_base`), together with the formulas describing the action of
the deck involution `σ : x ↦ x/(x−1)` on two-term expansions
(`Lead2At f e l m → Lead2At (σf) e ((-1)^e l) ((-1)^e (e·l − m))`).

The engine is `Exp2` (a two-term expansion without a non-vanishing leading coefficient), closed
under `+`, `−`, `neg`, scalar multiplication, multiplication (`exp2_mul`), inversion
(`exp2_inv`) and differentiation (`exp2_dRat`); the anti-invariant combinations are formed with
`LeadAt.sub_of_eq` (leading terms at the same order with opposite signs add up) and
`leadAt_sub_of_lead2At` (equal order, equal leading coefficient: the difference drops one order).
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

theorem dw_exp2_congr {f f' : RatFunc ℚ} {e e' : ℤ} {l l' m m' : ℚ}
    (h : Exp2 f e l m) (hf : f = f') (he : e = e') (hl : l = l') (hm : m = m') :
    Exp2 f' e' l' m' := by
  rw [hf, he, hl, hm] at h; exact h

theorem dw_lead2At_congr {f f' : RatFunc ℚ} {e e' : ℤ} {l l' m m' : ℚ}
    (h : Lead2At f e l m) (hf : f = f') (he : e = e') (hl : l = l') (hm : m = m') :
    Lead2At f' e' l' m' := by
  rw [hf, he, hl, hm] at h; exact h

theorem dw_leadAt_congr {f f' : RatFunc ℚ} {e e' : ℤ} {l l' : ℚ}
    (h : LeadAt f e l) (hf : f = f') (he : e = e') (hl : l = l') :
    LeadAt f' e' l' := by
  rw [hf, he, hl] at h; exact h

private lemma dw_hpow_m3 : (-1 : ℚ) ^ ((-3 : ℤ)) = -1 := by
  rw [zpow_neg]; norm_num

private lemma dw_hpow_m2 : (-1 : ℚ) ^ ((-2 : ℤ)) = 1 := by
  rw [zpow_neg]; norm_num

private lemma dw_hpow_m4 : (-1 : ℚ) ^ ((-4 : ℤ)) = 1 := by
  rw [zpow_neg]; norm_num

private lemma dw_hpow_m5 : (-1 : ℚ) ^ ((-5 : ℤ)) = -1 := by
  rw [zpow_neg]; norm_num

theorem local_dw (a b : ℚ) (hA : AdmQ a b)
    (hρ : Lead2At rhoQ (-1) (-1/2) (3/4))
    (hρ' : Lead2At (Submission.CDT.dRat rhoQ) (-2) (1/2) 0)
    (hP0 : Lead2At (P0Q a b) 0 (a * b) (1 - 3 * a ^ 2 - 3 * b ^ 2))
    (hP1 : Lead2At (P1Q a b) 0 (-1) (8 * a * b))
    (hP2 : Lead2At (P2Q a b) 1 (-1) (4 * a * b))
    (hP1dP2 : Lead2At (P1Q a b / P2Q a b) (-1) 1 (-4 * a * b))
    (hσ1 : ∀ (f : RatFunc ℚ) (e : ℤ) (l : ℚ), LeadAt f e l → LeadAt (sigmaQ f) e ((-1 : ℚ) ^ e * l))
    (hσ2 : ∀ (f : RatFunc ℚ) (e : ℤ) (l m : ℚ), Lead2At f e l m →
      Lead2At (sigmaQ f) e ((-1 : ℚ) ^ e * l) ((-1 : ℚ) ^ e * ((e : ℚ) * l - m))) :
    LeadAt (Z2 a b) (-3) (a * b / 2) ∧ LeadAt (Z3 a b) (-5) (5 * a * b / 4) ∧
    LeadAt (Y2 a b) (-1) (1 / 2 - 4 * a * b) ∧ LeadAt (Y3 a b) (-3) (5 / 4 - 19 * a * b / 2) := by
  have ha3 : (3 : ℚ) ≤ a := hA.1
  have hab : a < b := hA.2.1
  have ha0 : (0 : ℚ) < a := by linarith
  have hb0 : (0 : ℚ) < b := by linarith
  have hp0 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha0) (ne_of_gt hb0)
  suffices hbig : (5 / 38 : ℚ) < a * b by
    have hpos : (0 : ℚ) < a * b := by linarith
    -- base
    have hρe : Exp2 rhoQ (-1) (-1/2) (3/4) := hρ.to_exp2
    have hρ'e : Exp2 (Submission.CDT.dRat rhoQ) (-2) (1/2) 0 := hρ'.to_exp2
    have hP0e : Exp2 (P0Q a b) 0 (a * b) (1 - 3 * a ^ 2 - 3 * b ^ 2) := hP0.to_exp2
    have hP1e : Exp2 (P1Q a b) 0 (-1) (8 * a * b) := hP1.to_exp2
    have hP2e : Exp2 (P2Q a b) 1 (-1) (4 * a * b) := hP2.to_exp2
    -- C^{-1}
    have hCinv : Exp2 (P2Q a b)⁻¹ (-1) (-1) (-4 * a * b) :=
      dw_exp2_congr (exp2_inv hP2e (by norm_num : (-1 : ℚ) ≠ 0)) rfl
        (by ring) (by norm_num) (by ring)
    -- rhoQ * P0Q
    have hρA : Exp2 (rhoQ * P0Q a b) (-1) (-(a * b) / 2)
        (3 * (a * b) / 4 - (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2) :=
      dw_exp2_congr (exp2_mul hρe hP0e) rfl (by ring) (by ring) (by ring)
    -- (rhoQ*P0Q) * C^{-1}
    have hρAC : Exp2 ((rhoQ * P0Q a b) * (P2Q a b)⁻¹) (-2) ((a * b) / 2)
        (2 * (a * b) ^ 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 - 3 * (a * b) / 4) :=
      dw_exp2_congr (exp2_mul hρA hCinv) rfl (by ring) (by ring) (by ring)
    -- rhoQ * ((rhoQ*P0Q)*C^{-1})
    have hρS : Exp2 (rhoQ * ((rhoQ * P0Q a b) * (P2Q a b)⁻¹)) (-3) (-(a * b) / 4)
        (3 * (a * b) / 4 - (a * b) ^ 2 - (1 - 3 * a ^ 2 - 3 * b ^ 2) / 4) :=
      dw_exp2_congr (exp2_mul hρe hρAC) rfl (by ring) (by ring) (by ring)
    -- u2 = -(rhoQ * (...))
    have hu2 : Exp2 (u2 a b) (-3) ((a * b) / 4)
        ((a * b) ^ 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 4 - 3 * (a * b) / 4) :=
      dw_exp2_congr (Exp2.neg hρS) (by rw [u2, div_eq_mul_inv]) (by ring) (by ring) (by ring)
    -- rhoQ * P1Q
    have hρB : Exp2 (rhoQ * P1Q a b) (-1) (1/2) (-4 * (a * b) - 3/4) :=
      dw_exp2_congr (exp2_mul hρe hP1e) rfl (by ring) (by ring) (by ring)
    -- (rhoQ*P1Q)*C^{-1}
    have hρBC : Exp2 ((rhoQ * P1Q a b) * (P2Q a b)⁻¹) (-2) (-1/2) (2 * (a * b) + 3/4) :=
      dw_exp2_congr (exp2_mul hρB hCinv) rfl (by ring) (by ring) (by ring)
    -- w2 = dRat rhoQ - ...
    have hw2 : Exp2 (w2 a b) (-2) 1 (-2 * (a * b) - 3/4) :=
      dw_exp2_congr (Exp2.sub hρ'e hρBC) (by rw [w2, div_eq_mul_inv]) (by ring) (by ring) (by ring)
    -- v2 = rhoQ * w2
    have hv2 : Exp2 (v2 a b) (-3) (-1/2) (a * b + 9/8) :=
      dw_exp2_congr (exp2_mul hρe hw2) rfl (by ring) (by ring) (by ring)
    -- dRat u2
    have hdU2 : Exp2 (Submission.CDT.dRat (u2 a b)) (-4) (-3 * (a * b) / 4)
        (-2 * (a * b) ^ 2 - (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 + 3 * (a * b) / 2) :=
      dw_exp2_congr (exp2_dRat hu2) rfl (by ring) (by ring) (by ring)
    -- v2 * P0Q
    have hv2A : Exp2 (v2 a b * P0Q a b) (-3) (-(a * b) / 2)
        ((a * b) ^ 2 + 9 * (a * b) / 8 - (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2) :=
      dw_exp2_congr (exp2_mul hv2 hP0e) rfl (by ring) (by ring) (by ring)
    -- (v2*P0Q)*C^{-1}
    have hv2AC : Exp2 ((v2 a b * P0Q a b) * (P2Q a b)⁻¹) (-4) ((a * b) / 2)
        ((a * b) ^ 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 - 9 * (a * b) / 8) :=
      dw_exp2_congr (exp2_mul hv2A hCinv) rfl (by ring) (by ring) (by ring)
    -- T4 = dRat u2 - (v2*P0Q)*C^{-1}
    have hT4 : Exp2 (Submission.CDT.dRat (u2 a b) - (v2 a b * P0Q a b) * (P2Q a b)⁻¹)
        (-4) (-5 * (a * b) / 4)
        (-3 * (a * b) ^ 2 - (1 - 3 * a ^ 2 - 3 * b ^ 2) + 21 * (a * b) / 8) :=
      dw_exp2_congr (Exp2.sub hdU2 hv2AC) rfl (by ring) (by ring) (by ring)
    -- u3 = rhoQ * T4
    have hu3 : Exp2 (u3 a b) (-5) (5 * (a * b) / 8)
        (3 * (a * b) ^ 2 / 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 - 9 * (a * b) / 4) :=
      dw_exp2_congr (exp2_mul hρe hT4) (by rw [u3, div_eq_mul_inv]) (by ring) (by ring) (by ring)
    -- dRat v2
    have hdV2 : Exp2 (Submission.CDT.dRat (v2 a b)) (-4) (3/2) (-2 * (a * b) - 9/4) :=
      dw_exp2_congr (exp2_dRat hv2) rfl (by ring) (by ring) (by ring)
    -- v2 * P1Q
    have hv2B : Exp2 (v2 a b * P1Q a b) (-3) (1/2) (-5 * (a * b) - 9/8) :=
      dw_exp2_congr (exp2_mul hv2 hP1e) rfl (by ring) (by ring) (by ring)
    -- (v2*P1Q)*C^{-1}
    have hv2BC : Exp2 ((v2 a b * P1Q a b) * (P2Q a b)⁻¹) (-4) (-1/2) (3 * (a * b) + 9/8) :=
      dw_exp2_congr (exp2_mul hv2B hCinv) rfl (by ring) (by ring) (by ring)
    -- T3
    have hT3 : Exp2 (Submission.CDT.dRat (v2 a b) - (v2 a b * P1Q a b) * (P2Q a b)⁻¹)
        (-4) 2 (-5 * (a * b) - 27/8) :=
      dw_exp2_congr (Exp2.sub hdV2 hv2BC) rfl (by ring) (by ring) (by ring)
    -- shift u2
    have hshift : Exp2 (u2 a b) (-4) 0 ((a * b) / 4) :=
      dw_exp2_congr (Exp2.shift hu2) rfl (by ring) (by ring) (by ring)
    -- w3
    have hw3 : Exp2 (w3 a b) (-4) 2 (-19 * (a * b) / 4 - 27/8) :=
      dw_exp2_congr (Exp2.add hshift hT3) (by rw [w3]; ring) (by ring) (by ring) (by ring)
    -- lead2 facts
    have hp4 : (a * b) / 4 ≠ 0 := by
      exact div_ne_zero hp0 (by norm_num)
    have hp58 : 5 * (a * b) / 8 ≠ 0 := by
      exact div_ne_zero (mul_ne_zero (by norm_num) hp0) (by norm_num)
    have Lu2 : Lead2At (u2 a b) (-3) ((a * b) / 4)
        ((a * b) ^ 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 4 - 3 * (a * b) / 4) :=
      hu2.to_Lead2At hp4
    have Lw2 : Lead2At (w2 a b) (-2) 1 (-2 * (a * b) - 3/4) := hw2.to_Lead2At one_ne_zero
    have Lu3 : Lead2At (u3 a b) (-5) (5 * (a * b) / 8)
        (3 * (a * b) ^ 2 / 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 - 9 * (a * b) / 4) :=
      hu3.to_Lead2At hp58
    have Lw3 : Lead2At (w3 a b) (-4) 2 (-19 * (a * b) / 4 - 27/8) :=
      hw3.to_Lead2At (by norm_num)
    -- sigma images
    have hσu2 : Lead2At (sigmaQ (u2 a b)) (-3) (-(a * b) / 4)
        ((a * b) ^ 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 4) :=
      dw_lead2At_congr (hσ2 (u2 a b) (-3) ((a * b) / 4)
        ((a * b) ^ 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 4 - 3 * (a * b) / 4) Lu2)
        rfl (by ring) (by rw [dw_hpow_m3]; ring)
        (by rw [dw_hpow_m3]; ring)
    have hσw2 : Lead2At (sigmaQ (w2 a b)) (-2) 1 (2 * (a * b) - 5/4) :=
      dw_lead2At_congr (hσ2 (w2 a b) (-2) 1 (-2 * (a * b) - 3/4) Lw2)
        rfl (by ring) (by rw [dw_hpow_m2]; ring)
        (by rw [dw_hpow_m2]; ring)
    have hσu3 : Lead2At (sigmaQ (u3 a b)) (-5) (-(5 * (a * b) / 8))
        (3 * (a * b) ^ 2 / 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 + 7 * (a * b) / 8) :=
      dw_lead2At_congr (hσ2 (u3 a b) (-5) (5 * (a * b) / 8)
        (3 * (a * b) ^ 2 / 2 + (1 - 3 * a ^ 2 - 3 * b ^ 2) / 2 - 9 * (a * b) / 4) Lu3)
        rfl (by ring) (by rw [dw_hpow_m5]; ring)
        (by rw [dw_hpow_m5]; ring)
    have hσw3 : Lead2At (sigmaQ (w3 a b)) (-4) 2 (19 * (a * b) / 4 - 37/8) :=
      dw_lead2At_congr (hσ2 (w3 a b) (-4) 2 (-19 * (a * b) / 4 - 27/8) Lw3)
        rfl (by ring) (by rw [dw_hpow_m4]; ring)
        (by rw [dw_hpow_m4]; ring)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hne : (a * b) / 4 - (-(a * b) / 4) ≠ 0 := by
        intro hh; apply hp0
        have h2 : (a * b) / 2 = 0 := by linarith
        linarith
      exact dw_leadAt_congr (LeadAt.sub_of_eq Lu2.to_LeadAt hσu2.to_LeadAt hne)
        (by rw [Z2]) rfl (by ring)
    · have hne : 5 * (a * b) / 8 - (-(5 * (a * b) / 8)) ≠ 0 := by
        intro hh
        have h2 : 5 * (a * b) / 4 = 0 := by linarith
        exact hp58 (by linarith)
      exact dw_leadAt_congr (LeadAt.sub_of_eq Lu3.to_LeadAt hσu3.to_LeadAt hne)
        (by rw [Z3]) rfl (by ring)
    · have hne : (-2 * (a * b) - 3/4 : ℚ) ≠ (2 * (a * b) - 5/4) := by
        intro hh
        have h2 : (a * b) = 1/8 := by linarith
        linarith [hbig]
      exact dw_leadAt_congr (leadAt_sub_of_lead2At Lw2 hσw2 hne)
        (by rw [Y2]) (by ring) (by ring)
    · have hne : (-19 * (a * b) / 4 - 27/8 : ℚ) ≠ (19 * (a * b) / 4 - 37/8) := by
        intro hh
        have h2 : (a * b) = 5/38 := by linarith
        linarith [hbig]
      exact dw_leadAt_congr (leadAt_sub_of_lead2At Lw3 hσw3 hne)
        (by rw [Y3]) (by ring) (by ring)
  -- hbig
  have hb3 : (3 : ℚ) < b := lt_of_le_of_lt ha3 hab
  nlinarith [ha3, hb3]


end

end Work.C17
