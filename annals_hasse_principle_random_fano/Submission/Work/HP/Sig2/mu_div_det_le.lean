import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.Sig2.d3_lt_of_caseI
import Submission.Work.HP.MDEstimates.muXY_le

/-!
# `μ^R / det Γ ≪ W^{2(R-d)} 𝔡₃^{-R}` in Case I

In Case I (`¬(𝔡₂³ ≤ 𝔡₃‖x‖‖y‖)`) the maximum in `muXY` is the first argument, so
`μ = 3n²𝔡₂/𝔡₃`; combined with the lower bound `det Γ ≥ C 𝔡₂‖x‖^{d-1}‖y‖^{d-1}` and
`‖x‖,‖y‖ ≤ W` this gives

`μ^R / det Γ ≤ (3n²)^R W^{2(R-d)} 𝔡₃^{-R} / C`.

This is the isolated algebraic step of `per_pair_sum_bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.Sig2

open Work.HP

theorem mu_div_det_le (d n : ℕ) (hd : 2 ≤ d)
    (Cdet : ℝ) (hCdet : 0 < Cdet) (R : ℕ) (hRd : d ≤ R)
    (x y : Fin (n + 1) → ℤ) (W : ℝ) (hW0 : 0 ≤ W)
    (hd2pos : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd3pos : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd2le : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x * eNorm y)
    (hxW : eNorm x ≤ W) (hyW : eNorm y ≤ W)
    (hdet : Cdet * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)
        ≤ detL (Gam d n x y))
    (hcase : ¬ (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) *
        dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2
        ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) * (eNorm x * eNorm y))) :
    (muXY n x y) ^ R / detL (Gam d n x y)
      ≤ (3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) *
          (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)) / Cdet := by
  set d2 := dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) with hd2def
  set d3 := dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) with hd3def
  set X := eNorm x with hXdef
  set Y := eNorm y with hYdef
  have hXnn : 0 ≤ X := eNorm_nonneg x
  have hYnn : 0 ≤ Y := eNorm_nonneg y
  have hXYpos : 0 < X * Y := lt_of_lt_of_le hd2pos hd2le
  have hXYW : X * Y ≤ W ^ 2 := by nlinarith [hxW, hyW, hXnn, hYnn, hW0]
  have hR1 : 1 ≤ R := le_trans (by omega) hRd
  -- Case I: the first argument of the `max` is the larger one
  have hlt : X * Y / d2 ^ 2 < d2 / d3 := by
    rw [div_lt_div_iff₀ (by positivity) hd3pos]
    have h := not_le.mp hcase
    nlinarith [h]
  have hμeq : muXY n x y = 3 * (n : ℝ) ^ 2 * (d2 / d3) := by
    rw [muXY]
    rw [show dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) = d2 from hd2def.symm,
      show dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) = d3 from hd3def.symm,
      show eNorm x = X from hXdef.symm, show eNorm y = Y from hYdef.symm]
    rw [max_eq_left (le_of_lt hlt)]
  have hXYpow : X ^ (d - 1) * Y ^ (d - 1) = (X * Y) ^ (d - 1) :=
    (mul_pow X Y (d - 1)).symm
  have hdet' : Cdet * d2 * (X * Y) ^ (d - 1) ≤ detL (Gam d n x y) := by
    have h2 : Cdet * d2 * X ^ (d - 1) * Y ^ (d - 1)
        = Cdet * d2 * (X * Y) ^ (d - 1) := by rw [← hXYpow]; ring
    linarith [hdet, h2.le]
  have hdetpos : 0 < detL (Gam d n x y) := lt_of_lt_of_le (by positivity) hdet'
  have hkey : Cdet * d3 ^ R * ((muXY n x y) ^ R / detL (Gam d n x y))
      ≤ (3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) := by
    have hnum : (muXY n x y) ^ R = (3 * (n : ℝ) ^ 2) ^ R * (d2 ^ R / d3 ^ R) := by
      rw [hμeq, mul_pow, div_pow]
    have h1 : Cdet * d3 ^ R * ((muXY n x y) ^ R / detL (Gam d n x y))
        = (3 * (n : ℝ) ^ 2) ^ R * d2 ^ R * (Cdet / detL (Gam d n x y)) := by
      rw [hnum]
      field_simp
    have hden : (0:ℝ) < d2 * (X * Y) ^ (d - 1) := mul_pos hd2pos (pow_pos hXYpos _)
    have h2 : Cdet / detL (Gam d n x y) ≤ 1 / (d2 * (X * Y) ^ (d - 1)) := by
      rw [div_le_div_iff₀ hdetpos hden]
      have h := hdet'
      ring_nf at h ⊢
      linarith [h]
    have hd2pow : d2 ^ R = d2 * d2 ^ (R - 1) := by
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0) with ⟨k, rfl⟩
      simp [pow_succ, Nat.add_sub_cancel, mul_comm]
    have h3 : d2 ^ R / (d2 * (X * Y) ^ (d - 1)) = d2 ^ (R - 1) / (X * Y) ^ (d - 1) := by
      rw [hd2pow, mul_div_mul_left _ _ (ne_of_gt hd2pos)]
    have h4 : d2 ^ (R - 1) ≤ (X * Y) ^ (R - 1) := pow_le_pow_left₀ hd2pos.le hd2le _
    have h5 : (X * Y) ^ (R - 1) / (X * Y) ^ (d - 1) = (X * Y) ^ (R - d) := by
      rw [show R - 1 = (R - d) + (d - 1) by omega, pow_add,
        mul_div_cancel_right₀ _ (ne_of_gt (pow_pos hXYpos _))]
    have h6 : (X * Y) ^ (R - d) ≤ W ^ (2 * (R - d)) := by
      have h7 : (X * Y) ^ (R - d) ≤ (W ^ 2) ^ (R - d) :=
        pow_le_pow_left₀ hXYpos.le hXYW _
      rwa [← pow_mul] at h7
    calc Cdet * d3 ^ R * ((muXY n x y) ^ R / detL (Gam d n x y))
        = (3 * (n : ℝ) ^ 2) ^ R * d2 ^ R * (Cdet / detL (Gam d n x y)) := h1
      _ ≤ (3 * (n : ℝ) ^ 2) ^ R * d2 ^ R * (1 / (d2 * (X * Y) ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (3 * (n : ℝ) ^ 2) ^ R * (d2 ^ R / (d2 * (X * Y) ^ (d - 1))) := by ring
      _ = (3 * (n : ℝ) ^ 2) ^ R * (d2 ^ (R - 1) / (X * Y) ^ (d - 1)) := by rw [h3]
      _ ≤ (3 * (n : ℝ) ^ 2) ^ R * ((X * Y) ^ (R - 1) / (X * Y) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 (by positivity))
            (by positivity)
      _ = (3 * (n : ℝ) ^ 2) ^ R * (X * Y) ^ (R - d) := by rw [h5]
      _ ≤ (3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
  have hfinal : (muXY n x y) ^ R / detL (Gam d n x y) * Cdet * d3 ^ R
      ≤ (3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) := by
    have h := hkey
    rw [show Cdet * d3 ^ R * ((muXY n x y) ^ R / detL (Gam d n x y))
        = (muXY n x y) ^ R / detL (Gam d n x y) * Cdet * d3 ^ R from by ring] at h
    exact h
  have hd3Rpos : (0:ℝ) < d3 ^ R := pow_pos hd3pos _
  rw [Real.rpow_neg hd3pos.le, Real.rpow_natCast]
  rw [le_div_iff₀ hCdet]
  rw [← div_eq_mul_inv]
  rw [le_div_iff₀ hd3Rpos]
  exact hfinal

end Work.HP.Sig2
