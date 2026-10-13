import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.AuxOmegaStar
import Submission.Work.ConstructionInstance.A0_rpow_sub_le
import Submission.Work.ConstructionInstance.A0_inv_sq_sub_le
import Submission.Work.ConstructionInstance.A0_Pall_diff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance


/-- `|s₁ ^ (3β) - s₂ ^ (3β)| ≤ 3^β S^(2β) d^β` for `0 ≤ s₁,s₂ ≤ S` and `|s₁ - s₂| ≤ d`.

This is the elementary Hölder estimate for `t ↦ t^{3β}`: `t^{3β} = (t³)^β`, the cube is
`3S²`-Lipschitz on `[0,S]`, and `t ↦ t^β` is `β`-Hölder on `[0,∞)` (`A0_rpow_sub_le`). -/
private lemma rho_pow_diff_le {β s₁ s₂ S d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (h1 : 0 ≤ s₁) (h2 : 0 ≤ s₂) (hS1 : s₁ ≤ S) (hS2 : s₂ ≤ S) (hd : |s₁ - s₂| ≤ d) :
    |s₁ ^ (3 * β) - s₂ ^ (3 * β)| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have hS0 : 0 ≤ S := le_trans h1 hS1
  have hpow : s₁ ^ (3 * β) = (s₁ ^ 3) ^ β := by
    rw [← Real.rpow_natCast s₁ 3]
    exact Real.rpow_mul h1 3 β
  have hpow' : s₂ ^ (3 * β) = (s₂ ^ 3) ^ β := by
    rw [← Real.rpow_natCast s₂ 3]
    exact Real.rpow_mul h2 3 β
  have hcub : |s₁ ^ 3 - s₂ ^ 3| ≤ 3 * S ^ 2 * d := by
    have hfac : s₁ ^ 3 - s₂ ^ 3 = (s₁ - s₂) * (s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2) := by ring
    rw [hfac, abs_mul]
    have hkey : s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2 ≤ 3 * S ^ 2 := by nlinarith [hS1, hS2, h1, h2]
    have hkey0 : (0:ℝ) ≤ s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2 := by positivity
    calc |s₁ - s₂| * |s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2|
        = |s₁ - s₂| * (s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2) := by rw [abs_of_nonneg hkey0]
      _ ≤ d * (3 * S ^ 2) := mul_le_mul hd hkey hkey0 hd0
      _ = 3 * S ^ 2 * d := by ring
  calc |s₁ ^ (3 * β) - s₂ ^ (3 * β)|
      = |(s₁ ^ 3) ^ β - (s₂ ^ 3) ^ β| := by rw [hpow, hpow']
    _ ≤ |s₁ ^ 3 - s₂ ^ 3| ^ β := A0_rpow_sub_le hβ hβ1 (by positivity) (by positivity)
    _ ≤ (3 * S ^ 2 * d) ^ β := Real.rpow_le_rpow (abs_nonneg _) hcub hβ.le
    _ = 3 ^ β * S ^ (2 * β) * d ^ β := by
        have h1' : (3 * S ^ 2 * d : ℝ) = 3 * (S ^ 2 * d) := by ring
        rw [h1', Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ S ^ 2 * d),
          Real.mul_rpow (by positivity : (0:ℝ) ≤ S ^ 2) hd0,
          ← Real.rpow_natCast S 2, ← Real.rpow_mul hS0]
        ring

/-! ### the case `4 d < S` -/


lemma A0_holder_caseB {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x y : R3}
    (hd : 4 * ‖x - y‖ < max (Work.Cyl.rho x) (Work.Cyl.rho y)) :
    |A0 β x - A0 β y| ≤ 3170304 * ‖x - y‖ ^ β := by
  set d : ℝ := ‖x - y‖ with hddef
  set S : ℝ := max (Work.Cyl.rho x) (Work.Cyl.rho y) with hSdef
  set rx : ℝ := Work.Cyl.rho x with hrxdef
  set ry : ℝ := Work.Cyl.rho y with hrydef
  have hd0 : 0 ≤ d := by rw [hddef]; exact norm_nonneg _
  have hSd : 4 * d < S := by simpa [← hddef, ← hSdef] using hd
  have hSpos : 0 < S := by linarith
  have hrx0 : 0 ≤ rx := by rw [hrxdef]; exact Work.Cyl.rho_nonneg x
  have hry0 : 0 ≤ ry := by rw [hrydef]; exact Work.Cyl.rho_nonneg y
  have hrxS : rx ≤ S := by rw [hrxdef, hSdef]; exact le_max_left _ _
  have hryS : ry ≤ S := by rw [hrydef, hSdef]; exact le_max_right _ _
  have hdiff : |rx - ry| ≤ d := by
    have h1 : |rx - ry| = |‖x‖ - ‖y‖| := by
      rw [hrxdef, hrydef, Work.Cyl.rho_eq_norm, Work.Cyl.rho_eq_norm]
    rw [h1, hddef]; exact abs_norm_sub_norm_le x y
  have hS4 : S / 4 ≤ min rx ry := by
    have h1 : S - min rx ry = |ry - rx| := by rw [hSdef]; exact max_sub_min_eq_abs rx ry
    have h2 : |ry - rx| = |rx - ry| := abs_sub_comm _ _
    have h3 : min rx ry = S - |rx - ry| := by linarith
    have h4 : |rx - ry| ≤ S / 4 := by linarith
    linarith
  have hsm0 : 0 < min rx ry := lt_of_lt_of_le (by positivity) hS4
  have hAx : A0 β x = 2 * Pall x ^ β / (1 + rx ^ (3 * β)) ^ 2 := by
    rw [hrxdef]; exact A0_eq_Pall β x
  have hAy : A0 β y = 2 * Pall y ^ β / (1 + ry ^ (3 * β)) ^ 2 := by
    rw [hrydef]; exact A0_eq_Pall β y
  have hUx1 : 1 ≤ 1 + rx ^ (3 * β) := by
    have := Real.rpow_nonneg hrx0 (3 * β); linarith
  have hUy1 : 1 ≤ 1 + ry ^ (3 * β) := by
    have := Real.rpow_nonneg hry0 (3 * β); linarith
  have hPx0 : 0 ≤ Pall x := Pall_nonneg x
  have hPy0 : 0 ≤ Pall y := Pall_nonneg y
  have hPxβ : 0 ≤ Pall x ^ β := Real.rpow_nonneg hPx0 β
  have hPyβ : 0 ≤ Pall y ^ β := Real.rpow_nonneg hPy0 β
  have hdβ0 : 0 ≤ d ^ β := Real.rpow_nonneg hd0 β
  have h3β0 : (0:ℝ) ≤ 3 ^ β := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) β
  have h9β0 : (0:ℝ) ≤ (4 : ℝ) ^ (9 * β) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) (9 * β)
  have h6β0 : (0:ℝ) ≤ (4 : ℝ) ^ (6 * β) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) (6 * β)
  have hdecomp : A0 β x - A0 β y
      = 2 * Pall x ^ β * (1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2)
        + 2 * (Pall x ^ β - Pall y ^ β) / (1 + ry ^ (3 * β)) ^ 2 := by
    rw [hAx, hAy]
    field_simp
    ring
  have htri : |A0 β x - A0 β y|
      ≤ 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
        + 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 := by
    rw [hdecomp]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    have h1 : |2 * Pall x ^ β * (1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2)|
        = 2 * Pall x ^ β
          * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hPxβ]
    have h2 : |2 * (Pall x ^ β - Pall y ^ β) / (1 + ry ^ (3 * β)) ^ 2|
        = 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_pos (by positivity : (0:ℝ) < (1 + ry ^ (3 * β)) ^ 2)]
    rw [h1, h2]
  have hPxS : Pall x ^ β ≤ S ^ (3 * β) := by
    have h1 : Pall x ≤ S ^ 3 := by
      refine le_trans (Pall_le_rho_cube x) ?_
      rw [← hrxdef]
      exact pow_le_pow_left₀ hrx0 hrxS 3
    calc Pall x ^ β ≤ (S ^ 3) ^ β := Real.rpow_le_rpow hPx0 h1 hβ.le
      _ = S ^ (3 * β) := by
          rw [← Real.rpow_natCast S 3]
          exact (Real.rpow_mul hSpos.le 3 β).symm
  have hPP : |Pall x ^ β - Pall y ^ β| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
    have hPd : |Pall x - Pall y| ≤ 3 * S ^ 2 * d := by
      have h := A0_Pall_diff x y
      rw [hSdef, hddef]
      exact h
    calc |Pall x ^ β - Pall y ^ β| ≤ |Pall x - Pall y| ^ β := A0_rpow_sub_le hβ hβ1 hPx0 hPy0
      _ ≤ (3 * S ^ 2 * d) ^ β := Real.rpow_le_rpow (abs_nonneg _) hPd hβ.le
      _ = 3 ^ β * S ^ (2 * β) * d ^ β := by
          have h1 : (3 * S ^ 2 * d : ℝ) = 3 * (S ^ 2 * d) := by ring
          rw [h1, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3)
                (by positivity : (0:ℝ) ≤ S ^ 2 * d),
            Real.mul_rpow (by positivity : (0:ℝ) ≤ S ^ 2) hd0,
            ← Real.rpow_natCast S 2, ← Real.rpow_mul hSpos.le]
          ring
  have hUU : |(1 + rx ^ (3 * β)) - (1 + ry ^ (3 * β))| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
    have h := rho_pow_diff_le hβ hβ1 hrx0 hry0 hrxS hryS hdiff
    have he : (1 + rx ^ (3 * β)) - (1 + ry ^ (3 * β)) = rx ^ (3 * β) - ry ^ (3 * β) := by ring
    rwa [he]
  have hminU : min (1 + rx ^ (3 * β)) (1 + ry ^ (3 * β)) = 1 + min rx ry ^ (3 * β) := by
    rcases le_total rx ry with h | h
    · have h2 : 1 + rx ^ (3 * β) ≤ 1 + ry ^ (3 * β) := by
        have h0 : rx ^ (3 * β) ≤ ry ^ (3 * β) :=
          Real.rpow_le_rpow hrx0 h (by linarith : (0:ℝ) ≤ 3 * β)
        linarith
      rw [min_eq_left h2, min_eq_left h]
    · have h2 : 1 + ry ^ (3 * β) ≤ 1 + rx ^ (3 * β) := by
        have h0 : ry ^ (3 * β) ≤ rx ^ (3 * β) :=
          Real.rpow_le_rpow hry0 h (by linarith : (0:ℝ) ≤ 3 * β)
        linarith
      rw [min_eq_right h2, min_eq_right h]
  have hinv : |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
      ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + min rx ry ^ (3 * β)) ^ 3 := by
    have h := A0_inv_sq_sub_le hUx1 hUy1
    rw [hminU] at h
    refine h.trans ?_
    have hM0 : (0:ℝ) < (1 + min rx ry ^ (3 * β)) ^ 3 := by positivity
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hUU (by norm_num : (0:ℝ) ≤ 2)) hM0.le
  have hterm1 : 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
      ≤ 3145728 * d ^ β := by
    have hstep : 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
        ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
            * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := by
      have h1 : 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              / (1 + min rx ry ^ (3 * β)) ^ 3) := by
        refine mul_le_mul (by linarith) hinv (abs_nonneg _) (by positivity)
      calc 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              / (1 + min rx ry ^ (3 * β)) ^ 3) := h1
        _ = 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := by
            simp only [div_eq_mul_inv, one_mul]
    rcases le_total S 1 with hS1 | hS1
    · have hS3 : S ^ (3 * β) ≤ 1 := Real.rpow_le_one hSpos.le hS1 (by linarith)
      have hS2 : S ^ (2 * β) ≤ 1 := Real.rpow_le_one hSpos.le hS1 (by linarith)
      have hS3β0 : (0:ℝ) ≤ S ^ (3 * β) := Real.rpow_nonneg hSpos.le _
      have hS2β0 : (0:ℝ) ≤ S ^ (2 * β) := Real.rpow_nonneg hSpos.le _
      have hM3 : 1 / (1 + min rx ry ^ (3 * β)) ^ 3 ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (1 + min rx ry ^ (3 * β)) ^ 3)]
        have h0 : (0:ℝ) ≤ min rx ry ^ (3 * β) := Real.rpow_nonneg hsm0.le _
        calc (1:ℝ) = 1 ^ 3 := by ring
          _ ≤ (1 + min rx ry ^ (3 * β)) ^ 3 :=
              pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith) 3
      have hM30 : (0:ℝ) ≤ 1 / (1 + min rx ry ^ (3 * β)) ^ 3 := by positivity
      have hprod : S ^ (3 * β) * S ^ (2 * β) * (1 / (1 + min rx ry ^ (3 * β)) ^ 3) ≤ 1 := by
        calc S ^ (3 * β) * S ^ (2 * β) * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul ?_ hM3 hM30 (by norm_num)
              exact mul_le_mul hS3 hS2 hS2β0 (by norm_num)
          _ = 1 := by norm_num
      have hkey : 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
          * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) ≤ 4 * 3 ^ β * d ^ β := by
        calc 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3))
            = (S ^ (3 * β) * S ^ (2 * β) * (1 / (1 + min rx ry ^ (3 * β)) ^ 3))
                * (4 * 3 ^ β * d ^ β) := by ring
          _ ≤ 1 * (4 * 3 ^ β * d ^ β) := mul_le_mul_of_nonneg_right hprod (by positivity)
          _ = 4 * 3 ^ β * d ^ β := by ring
      calc 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := hstep
        _ ≤ 4 * 3 ^ β * d ^ β := hkey
        _ ≤ 3145728 * d ^ β := by
            have h3β : (3:ℝ) ^ β ≤ 3 := by
              have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
              rwa [Real.rpow_one] at h
            have hcoef : (4:ℝ) * 3 ^ β ≤ 4 * 3 := by linarith
            calc 4 * 3 ^ β * d ^ β ≤ 4 * 3 * d ^ β := mul_le_mul_of_nonneg_right hcoef hdβ0
              _ ≤ 3145728 * d ^ β := mul_le_mul_of_nonneg_right (by norm_num) hdβ0
    · have hM3 : 1 / (1 + min rx ry ^ (3 * β)) ^ 3 ≤ 4 ^ (9 * β) / S ^ (9 * β) := by
        have h1 : (S / 4) ^ (9 * β) ≤ (min rx ry) ^ (9 * β) :=
          Real.rpow_le_rpow (by positivity) hS4 (by linarith)
        have h5 : (min rx ry) ^ (9 * β) ≤ (1 + min rx ry ^ (3 * β)) ^ 3 := by
          have h6 : min rx ry ^ (3 * β) ≤ 1 + min rx ry ^ (3 * β) := by
            have h0 : (0:ℝ) ≤ min rx ry ^ (3 * β) := Real.rpow_nonneg hsm0.le _
            linarith
          calc (min rx ry) ^ (9 * β) = ((min rx ry) ^ (3 * β)) ^ 3 := by
                rw [← Real.rpow_natCast ((min rx ry) ^ (3 * β)) 3, ← Real.rpow_mul hsm0.le]
                congr 1
                ring
            _ ≤ (1 + min rx ry ^ (3 * β)) ^ 3 :=
                pow_le_pow_left₀ (Real.rpow_nonneg hsm0.le _) h6 3
        have h6 : (S / 4) ^ (9 * β) ≤ (1 + min rx ry ^ (3 * β)) ^ 3 := le_trans h1 h5
        have h7 : 0 < (S / 4) ^ (9 * β) := Real.rpow_pos_of_pos (by positivity) _
        have h8 := one_div_le_one_div_of_le h7 h6
        have h9 : 1 / ((S / 4) ^ (9 * β)) = 4 ^ (9 * β) / S ^ (9 * β) := by
          rw [Real.div_rpow hSpos.le (by norm_num : (0:ℝ) ≤ 4) (9 * β)]
          field_simp
        rw [← h9]
        exact h8
      have hkey0 : S ^ (3 * β) * S ^ (2 * β) * ((4:ℝ) ^ (9 * β) / S ^ (9 * β)) ≤ 4 ^ (9 * β) := by
        have h5 : S ^ (3 * β) * S ^ (2 * β) = S ^ (5 * β) := by
          rw [← Real.rpow_add hSpos]
          congr 1
          ring
        rw [h5]
        have hr : S ^ (5 * β) / S ^ (9 * β) ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hSpos _)]
          exact Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
        calc S ^ (5 * β) * (4 ^ (9 * β) / S ^ (9 * β))
            = 4 ^ (9 * β) * (S ^ (5 * β) / S ^ (9 * β)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]; ring
          _ ≤ 4 ^ (9 * β) * 1 := mul_le_mul_of_nonneg_left hr h9β0
          _ = 4 ^ (9 * β) := mul_one _
      have hkey : 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
          * (4 ^ (9 * β) / S ^ (9 * β))) ≤ 4 * 3 ^ β * 4 ^ (9 * β) * d ^ β := by
        have h4 : (0:ℝ) ≤ 4 * 3 ^ β * d ^ β := by positivity
        have h := mul_le_mul_of_nonneg_right hkey0 h4
        calc 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (4 ^ (9 * β) / S ^ (9 * β)))
            = (S ^ (3 * β) * S ^ (2 * β) * (4 ^ (9 * β) / S ^ (9 * β)))
                * (4 * 3 ^ β * d ^ β) := by ring
          _ ≤ 4 ^ (9 * β) * (4 * 3 ^ β * d ^ β) := h
          _ = 4 * 3 ^ β * 4 ^ (9 * β) * d ^ β := by ring
      calc 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := hstep
        _ ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (4 ^ (9 * β) / S ^ (9 * β))) := by
            have h0 : (0:ℝ) ≤ 2 * S ^ (3 * β) := by positivity
            have h1 : (0:ℝ) ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM3 h1) h0
        _ ≤ 4 * 3 ^ β * 4 ^ (9 * β) * d ^ β := hkey
        _ ≤ 3145728 * d ^ β := by
            have h3β : (3:ℝ) ^ β ≤ 3 := by
              have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
              rwa [Real.rpow_one] at h
            have h49 : (4:ℝ) ^ (9 * β) ≤ 262144 := by
              calc (4:ℝ) ^ (9 * β) ≤ (4:ℝ) ^ (9:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith)
                _ = 262144 := by norm_num
            have hcoef : (4:ℝ) * 3 ^ β * 4 ^ (9 * β) ≤ 3145728 := by
              have h1 : (4:ℝ) * 3 ^ β ≤ 4 * 3 := by linarith
              have h2 : (4:ℝ) * 3 ^ β * 4 ^ (9 * β) ≤ 4 * 3 * 262144 :=
                mul_le_mul h1 h49 h9β0 (by norm_num : (0:ℝ) ≤ 4 * 3)
              linarith
            exact mul_le_mul_of_nonneg_right hcoef hdβ0
  have hterm2 : 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 ≤ 24576 * d ^ β := by
    have hstep : 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2
        ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + ry ^ (3 * β)) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPP (by norm_num : (0:ℝ) ≤ 2))
        (by positivity)
    rcases le_total S 1 with hS1 | hS1
    · have hS2 : S ^ (2 * β) ≤ 1 := Real.rpow_le_one hSpos.le hS1 (by linarith)
      have hS2β0 : (0:ℝ) ≤ S ^ (2 * β) := Real.rpow_nonneg hSpos.le _
      have hden : 1 / (1 + ry ^ (3 * β)) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (1 + ry ^ (3 * β)) ^ 2)]
        have h0 : (0:ℝ) ≤ ry ^ (3 * β) := Real.rpow_nonneg hry0 _
        calc (1:ℝ) = 1 ^ 2 := by ring
          _ ≤ (1 + ry ^ (3 * β)) ^ 2 :=
              pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith) 2
      have hden0 : (0:ℝ) ≤ 1 / (1 + ry ^ (3 * β)) ^ 2 := by positivity
      have hprod : S ^ (2 * β) * (1 / (1 + ry ^ (3 * β)) ^ 2) ≤ 1 := by
        calc S ^ (2 * β) * (1 / (1 + ry ^ (3 * β)) ^ 2) ≤ 1 * 1 :=
              mul_le_mul hS2 hden hden0 (by norm_num)
          _ = 1 := by norm_num
      have hkey : 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2)
          ≤ 6 * d ^ β := by
        calc 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2)
            = (S ^ (2 * β) * (1 / (1 + ry ^ (3 * β)) ^ 2)) * (2 * 3 ^ β * d ^ β) := by ring
          _ ≤ 1 * (2 * 3 ^ β * d ^ β) := mul_le_mul_of_nonneg_right hprod (by positivity)
          _ = 2 * 3 ^ β * d ^ β := by ring
          _ ≤ 6 * d ^ β := by
              have h3β : (3:ℝ) ^ β ≤ 3 := by
                have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
                rwa [Real.rpow_one] at h
              have hcoef : (2:ℝ) * 3 ^ β ≤ 2 * 3 := by linarith
              calc 2 * 3 ^ β * d ^ β ≤ 2 * 3 * d ^ β := mul_le_mul_of_nonneg_right hcoef hdβ0
                _ = 6 * d ^ β := by ring
      calc 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2
          ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + ry ^ (3 * β)) ^ 2 := hstep
        _ = 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2) := by
            simp only [div_eq_mul_inv, one_mul]
        _ ≤ 6 * d ^ β := hkey
        _ ≤ 24576 * d ^ β := mul_le_mul_of_nonneg_right (by norm_num) hdβ0
    · have hden : 1 / (1 + ry ^ (3 * β)) ^ 2 ≤ 4 ^ (6 * β) / S ^ (6 * β) := by
        have h1 : (S / 4) ^ (6 * β) ≤ ry ^ (6 * β) :=
          Real.rpow_le_rpow (by positivity) (le_trans hS4 (min_le_right rx ry)) (by linarith)
        have h6 : ry ^ (6 * β) ≤ (1 + ry ^ (3 * β)) ^ 2 := by
          have h7 : ry ^ (3 * β) ≤ 1 + ry ^ (3 * β) := by
            have h0 : (0:ℝ) ≤ ry ^ (3 * β) := Real.rpow_nonneg hry0 _
            linarith
          calc ry ^ (6 * β) = (ry ^ (3 * β)) ^ 2 := by
                rw [← Real.rpow_natCast (ry ^ (3 * β)) 2, ← Real.rpow_mul hry0]
                congr 1
                ring
            _ ≤ (1 + ry ^ (3 * β)) ^ 2 :=
                pow_le_pow_left₀ (Real.rpow_nonneg hry0 _) h7 2
        have h7 : (S / 4) ^ (6 * β) ≤ (1 + ry ^ (3 * β)) ^ 2 := le_trans h1 h6
        have h8 : 0 < (S / 4) ^ (6 * β) := Real.rpow_pos_of_pos (by positivity) _
        have h9 := one_div_le_one_div_of_le h8 h7
        have h10 : 1 / ((S / 4) ^ (6 * β)) = 4 ^ (6 * β) / S ^ (6 * β) := by
          rw [Real.div_rpow hSpos.le (by norm_num : (0:ℝ) ≤ 4) (6 * β)]
          field_simp
        rw [← h10]
        exact h9
      have hkey0 : S ^ (2 * β) * ((4:ℝ) ^ (6 * β) / S ^ (6 * β)) ≤ 4 ^ (6 * β) := by
        have hr : S ^ (2 * β) / S ^ (6 * β) ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hSpos _)]
          exact Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
        calc S ^ (2 * β) * (4 ^ (6 * β) / S ^ (6 * β))
            = 4 ^ (6 * β) * (S ^ (2 * β) / S ^ (6 * β)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]; ring
          _ ≤ 4 ^ (6 * β) * 1 := mul_le_mul_of_nonneg_left hr h6β0
          _ = 4 ^ (6 * β) := mul_one _
      have hkey : 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (4 ^ (6 * β) / S ^ (6 * β))
          ≤ 2 * 3 ^ β * 4 ^ (6 * β) * d ^ β := by
        have h4 : (0:ℝ) ≤ 2 * 3 ^ β * d ^ β := by positivity
        have h := mul_le_mul_of_nonneg_right hkey0 h4
        calc 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (4 ^ (6 * β) / S ^ (6 * β))
            = (S ^ (2 * β) * ((4:ℝ) ^ (6 * β) / S ^ (6 * β))) * (2 * 3 ^ β * d ^ β) := by ring
          _ ≤ 4 ^ (6 * β) * (2 * 3 ^ β * d ^ β) := h
          _ = 2 * 3 ^ β * 4 ^ (6 * β) * d ^ β := by ring
      have h3β : (3:ℝ) ^ β ≤ 3 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
        rwa [Real.rpow_one] at h
      have h46 : (4:ℝ) ^ (6 * β) ≤ 4096 := by
        calc (4:ℝ) ^ (6 * β) ≤ (4:ℝ) ^ (6:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith)
          _ = 4096 := by norm_num
      calc 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2
          ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + ry ^ (3 * β)) ^ 2 := hstep
        _ = 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2) := by
            simp only [div_eq_mul_inv, one_mul]
        _ ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (4 ^ (6 * β) / S ^ (6 * β)) := by
            have h0 : (0:ℝ) ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) := by positivity
            exact mul_le_mul_of_nonneg_left hden h0
        _ ≤ 2 * 3 ^ β * 4 ^ (6 * β) * d ^ β := hkey
        _ ≤ 24576 * d ^ β := by
            have hcoef : (2:ℝ) * 3 ^ β * 4 ^ (6 * β) ≤ 24576 := by
              have h1 : (2:ℝ) * 3 ^ β ≤ 2 * 3 := by linarith
              have h2 : (2:ℝ) * 3 ^ β * 4 ^ (6 * β) ≤ 2 * 3 * 4096 :=
                mul_le_mul h1 h46 h6β0 (by norm_num : (0:ℝ) ≤ 2 * 3)
              linarith
            exact mul_le_mul_of_nonneg_right hcoef hdβ0
  calc |A0 β x - A0 β y|
      ≤ 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
        + 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 := htri
    _ ≤ 3145728 * d ^ β + 24576 * d ^ β := add_le_add hterm1 hterm2
    _ = 3170304 * d ^ β := by ring
    _ = 3170304 * ‖x - y‖ ^ β := by rw [hddef]

theorem A0_holder {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : NNReal, ∀ x y : Work.ConstructionInstance.R3,
      |Work.ConstructionInstance.A0 β x - Work.ConstructionInstance.A0 β y|
        ≤ (C : ℝ) * ‖x - y‖ ^ β := by
  refine ⟨3200000, ?_⟩
  intro x y
  show |A0 β x - A0 β y| ≤ (3200000 : ℝ) * ‖x - y‖ ^ β
  have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hdβ0 : (0:ℝ) ≤ ‖x - y‖ ^ β := Real.rpow_nonneg hd0 β
  by_cases hdbig : 1 ≤ ‖x - y‖
  · have h1 : |A0 β x - A0 β y| ≤ 1 := by
      have hx := A0_le_half β hβ x
      have hy := A0_le_half β hβ y
      have hx0 := A0_nonneg β x
      have hy0 := A0_nonneg β y
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have h2 : (1:ℝ) ≤ ‖x - y‖ ^ β := Real.one_le_rpow hdbig hβ.le
    have h3 : (1:ℝ) * ‖x - y‖ ^ β ≤ 3200000 * ‖x - y‖ ^ β :=
      mul_le_mul_of_nonneg_right (by norm_num) hdβ0
    linarith
  · push_neg at hdbig
    by_cases hA : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 4 * ‖x - y‖
    · have hx2 : |x 2| ≤ 4 * ‖x - y‖ := by
        refine le_trans (Work.Cyl.abs_axial_le_rho x) ?_
        exact le_trans (le_max_left _ _) hA
      have hy2 : |y 2| ≤ 4 * ‖x - y‖ := by
        refine le_trans (Work.Cyl.abs_axial_le_rho y) ?_
        exact le_trans (le_max_right _ _) hA
      have hbx : |x 2| ^ β ≤ 4 ^ β * ‖x - y‖ ^ β := by
        have hpow4 : (4 * ‖x - y‖) ^ β = 4 ^ β * ‖x - y‖ ^ β :=
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hd0
        rw [← hpow4]
        exact Real.rpow_le_rpow (abs_nonneg _) hx2 hβ.le
      have hby : |y 2| ^ β ≤ 4 ^ β * ‖x - y‖ ^ β := by
        have hpow4 : (4 * ‖x - y‖) ^ β = 4 ^ β * ‖x - y‖ ^ β :=
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hd0
        rw [← hpow4]
        exact Real.rpow_le_rpow (abs_nonneg _) hy2 hβ.le
      have hxax := A0_le_ax β hβ x
      have hyax := A0_le_ax β hβ y
      have hx0 := A0_nonneg β x
      have hy0 := A0_nonneg β y
      have h4β : (4:ℝ) ^ β ≤ 4 := by
        calc (4:ℝ) ^ β ≤ 4 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hβ1
          _ = 4 := Real.rpow_one 4
      have hfinal : 4 * 4 ^ β * ‖x - y‖ ^ β ≤ 3200000 * ‖x - y‖ ^ β := by
        have h1 : 4 * 4 ^ β * ‖x - y‖ ^ β ≤ 4 * 4 * ‖x - y‖ ^ β :=
          mul_le_mul_of_nonneg_right (by linarith [h4β]) hdβ0
        have h2 : (4:ℝ) * 4 * ‖x - y‖ ^ β ≤ 3200000 * ‖x - y‖ ^ β :=
          mul_le_mul_of_nonneg_right (by norm_num) hdβ0
        linarith
      calc |A0 β x - A0 β y| ≤ A0 β x + A0 β y := by
            rw [abs_sub_le_iff]; exact ⟨by linarith, by linarith⟩
        _ ≤ 2 * |x 2| ^ β + 2 * |y 2| ^ β := by linarith
        _ ≤ 2 * (4 ^ β * ‖x - y‖ ^ β) + 2 * (4 ^ β * ‖x - y‖ ^ β) := by linarith
        _ = 4 * 4 ^ β * ‖x - y‖ ^ β := by ring
        _ ≤ 3200000 * ‖x - y‖ ^ β := hfinal
    · push_neg at hA
      have hcaseB := A0_holder_caseB hβ hβ1 hA
      calc |A0 β x - A0 β y| ≤ 3170304 * ‖x - y‖ ^ β := hcaseB
        _ ≤ 3200000 * ‖x - y‖ ^ β := mul_le_mul_of_nonneg_right (by norm_num) hdβ0

end Work.ConstructionInstance
