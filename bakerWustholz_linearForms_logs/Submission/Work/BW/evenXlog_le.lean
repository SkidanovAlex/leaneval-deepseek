import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 1000000

/-- The `log(X·(T'+1))` term of the ℐ-condition of the even step is dominated by `S·D`.

`X = evX r J S = 2·evSP`, `T' = evTp r J T`, `S = pS r d h`, `D = pD r d σ`, `T = pT r d σ`, `ξ = pxi r`. Hypothesis `hnd : ∃j, 2^J ≤ pDj r d σ j` is used through `u := ξ^{-rJ} ≤ D/r`.

Route. `u ≥ 1`, `X ≤ 4uS`, `T'+1 ≤ 6.3ξ^rD/u + 1`, so `X(T'+1) ≤ 25.2ξ^rSD + 4uS ≤ (25.2 + 2)SD = 27.2·S·D`. Also `S ≥ 608` (`num_T`) and `D ≥ 1` (`pD_ge_one`), so `SD ≥ 108.8`.
Then `log(X(T'+1)) ≤ 2√(X(T'+1)) ≤ 2√(27.2·SD)` where `log y ≤ 2√y` follows from `Real.log_le_sub_one_of_pos` applied to `√y`. Finally `2√(27.2·SD) ≤ SD` because `SD ≥ 4·27.2 = 108.8`. -/
theorem evenXlog_le {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) {σ : Fin r → ℝ}
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : J + 1 ≤ pI r d)
    (hnd : ∃ j, (2 : ℝ) ^ J ≤ (pDj r d σ j : ℝ)) :
    Real.log ((evX r J (pS r d h : ℝ) : ℝ) * (((evTp r J (pT r d σ : ℝ)) + 1 : ℕ) : ℝ))
      ≤ (pS r d h : ℝ) * pD r d σ := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hxi_pos : 0 < pxi r := by
    rw [pxi]
    have h : (0.536 : ℝ) / r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hxi_le1 : pxi r ≤ 1 := by
    rw [pxi]
    have h : (0 : ℝ) ≤ (0.536 : ℝ) / r := by positivity
    linarith
  have hxi_ne : pxi r ≠ 0 := ne_of_gt hxi_pos
  have hS608 : (608 : ℝ) ≤ (pS r d h : ℝ) := (num_T hr hd hh σ hσ).2.2.2
  have hD1 : (1 : ℝ) ≤ pD r d σ := pD_ge_one hr hd σ hσ
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hDnn : (0 : ℝ) ≤ pD r d σ := le_of_lt hDpos
  have hSnn : (0 : ℝ) ≤ (pS r d h : ℝ) := by linarith
  have hUpos : (0 : ℝ) < pxi r ^ (-(((r*J : ℕ)) : ℤ)) := zpow_pos hxi_pos _
  have hUnn : (0 : ℝ) ≤ pxi r ^ (-(((r*J : ℕ)) : ℤ)) := le_of_lt hUpos
  have hUne : pxi r ^ (-(((r*J : ℕ)) : ℤ)) ≠ 0 := ne_of_gt hUpos
  have hUeq : pxi r ^ (-(((r*J : ℕ)) : ℤ)) = (pxi r ^ (-(r:ℤ)))^J := by
    have h : (((r*J : ℕ)) : ℤ) = (r : ℤ) * (J : ℤ) := by push_cast; ring
    have h2 : -(((r*J : ℕ)) : ℤ) = (-(r : ℤ)) * (J : ℤ) := by rw [h]; ring
    rw [h2, zpow_mul, zpow_natCast]
  have hUge1 : 1 ≤ pxi r ^ (-(((r*J : ℕ)) : ℤ)) := by
    rw [hUeq]
    have hxr1 : pxi r ^ r ≤ 1 := pow_le_one₀ (le_of_lt hxi_pos) hxi_le1
    have hxrpos : 0 < pxi r ^ r := pow_pos hxi_pos r
    have hinv : 1 ≤ (pxi r ^ (-(r:ℤ))) := by
      rw [zpow_neg, zpow_natCast]
      exact (one_le_inv₀ hxrpos).mpr hxr1
    exact one_le_pow₀ hinv
  have hUle2J : pxi r ^ (-(((r*J : ℕ)) : ℤ)) ≤ (2 : ℝ)^J := by
    rw [hUeq]
    have hb : pxi r ^ (-(r:ℤ)) ≤ 2 := by have := (num_xi hr).1; linarith
    have hb0 : 0 ≤ pxi r ^ (-(r:ℤ)) := le_of_lt (zpow_pos hxi_pos _)
    exact pow_le_pow_left₀ hb0 hb J
  obtain ⟨j, hj⟩ := hnd
  have hUle : pxi r ^ (-(((r*J : ℕ)) : ℤ)) ≤ pD r d σ / r := by
    have h1 := pDj_le_r hr hd σ hσ j
    have h2 : (2 : ℝ)^J ≤ pD r d σ / r := le_trans hj h1
    linarith [hUle2J, h2]
  have hXle : (evX r J (pS r d h : ℝ) : ℝ) ≤ 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) := by
    have hq : (0 : ℝ) ≤ 2 * (pxi r ^ (-(((r*J : ℕ)) : ℤ)) * (pS r d h : ℝ)) :=
      mul_nonneg (by norm_num) (mul_nonneg hUnn hSnn)
    have hfloor := Nat.floor_le hq
    have hevSP : (evSP r J (pS r d h : ℝ) : ℝ)
        ≤ 2 * (pxi r ^ (-(((r*J : ℕ)) : ℤ)) * (pS r d h : ℝ)) := hfloor
    have hevX : (evX r J (pS r d h : ℝ) : ℝ) = 2 * (evSP r J (pS r d h : ℝ) : ℝ) := by
      simp only [evX]; push_cast; ring
    rw [hevX]; nlinarith [hevSP]
  have hTpu : (evTp r J (pT r d σ : ℝ) : ℝ) * pxi r ^ (-(((r*J : ℕ)) : ℤ))
      ≤ 6.3 * pD r d σ * pxi r ^ r := by
    have hq : (0 : ℝ) ≤ (1 - pxi r) * pxi r ^ r * (pxi r ^ (r*J) * (pT r d σ : ℝ)) := by
      have h1 : (0 : ℝ) ≤ 1 - pxi r := by linarith
      have h2 : (0 : ℝ) < pxi r ^ r := pow_pos hxi_pos r
      have h3 : (0 : ℝ) < pxi r ^ (r*J) := pow_pos hxi_pos (r*J)
      positivity
    have hfloor := Nat.floor_le hq
    have hpoweq : pxi r ^ (r*J) * pxi r ^ (-(((r*J : ℕ)) : ℤ)) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hxi_ne]
      simp
    have h1 : (evTp r J (pT r d σ : ℝ) : ℝ) * pxi r ^ (-(((r*J : ℕ)) : ℤ))
        ≤ (1 - pxi r) * pxi r ^ r * (pxi r ^ (r*J) * (pT r d σ : ℝ))
            * pxi r ^ (-(((r*J : ℕ)) : ℤ)) :=
      mul_le_mul_of_nonneg_right hfloor hUnn
    have h2 : (1 - pxi r) * pxi r ^ r * (pxi r ^ (r*J) * (pT r d σ : ℝ))
            * pxi r ^ (-(((r*J : ℕ)) : ℤ))
        = (1 - pxi r) * (pT r d σ : ℝ) * pxi r ^ r := by
      calc (1 - pxi r) * pxi r ^ r * (pxi r ^ (r*J) * (pT r d σ : ℝ))
                * pxi r ^ (-(((r*J : ℕ)) : ℤ))
          = (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ)
              * (pxi r ^ (r*J) * pxi r ^ (-(((r*J : ℕ)) : ℤ))) := by ring
        _ = (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ) * 1 := by rw [hpoweq]
        _ = (1 - pxi r) * (pT r d σ : ℝ) * pxi r ^ r := by ring
    have hTle : (1 - pxi r) * (pT r d σ : ℝ) ≤ 6.3 * pD r d σ := (num_T hr hd hh σ hσ).2.1
    have hxirnn : (0 : ℝ) ≤ pxi r ^ r := pow_nonneg (le_of_lt hxi_pos) r
    have h3 : (1 - pxi r) * (pT r d σ : ℝ) * pxi r ^ r ≤ 6.3 * pD r d σ * pxi r ^ r :=
      mul_le_mul_of_nonneg_right hTle hxirnn
    rw [h2] at h1
    linarith [h1, h3]
  -- ============ assembly ============
  have hTp_le : (evTp r J (pT r d σ : ℝ) : ℝ)
      ≤ 6.3 * pD r d σ * pxi r ^ r / pxi r ^ (-(((r*J : ℕ)) : ℤ)) := by
    rw [le_div_iff₀ hUpos]; exact hTpu
  have hTp1 : (evTp r J (pT r d σ : ℝ) : ℝ) + 1
      ≤ 6.3 * pD r d σ * pxi r ^ r / pxi r ^ (-(((r*J : ℕ)) : ℤ)) + 1 := by linarith
  have hPle1 : (evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1)
      ≤ 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) *
          (6.3 * pD r d σ * pxi r ^ r / pxi r ^ (-(((r*J : ℕ)) : ℤ)) + 1) := by
    apply mul_le_mul hXle hTp1
    · positivity
    · exact mul_nonneg (mul_nonneg (by norm_num) hUnn) hSnn
  have hexpand : 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) *
        (6.3 * pD r d σ * pxi r ^ r / pxi r ^ (-(((r*J : ℕ)) : ℤ)) + 1)
      = 25.2 * pxi r ^ r * (pS r d h : ℝ) * pD r d σ
        + 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) := by
    have hUinv : pxi r ^ (-(((r*J : ℕ)) : ℤ)) * (pxi r ^ (-(((r*J : ℕ)) : ℤ)))⁻¹ = 1 :=
      mul_inv_cancel₀ hUne
    calc 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) *
            (6.3 * pD r d σ * pxi r ^ r / pxi r ^ (-(((r*J : ℕ)) : ℤ)) + 1)
        = 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) *
              (6.3 * pD r d σ * pxi r ^ r * (pxi r ^ (-(((r*J : ℕ)) : ℤ)))⁻¹)
            + 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) := by
          rw [div_eq_mul_inv, mul_add, mul_one]
      _ = 25.2 * pxi r ^ r * (pS r d h : ℝ) * pD r d σ
            + 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) := by
          have hc : 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ)
                * (6.3 * pD r d σ * pxi r ^ r * (pxi r ^ (-(((r*J : ℕ)) : ℤ)))⁻¹)
              = 25.2 * pxi r ^ r * (pS r d h : ℝ) * pD r d σ := by
            calc 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ)
                    * (6.3 * pD r d σ * pxi r ^ r * (pxi r ^ (-(((r*J : ℕ)) : ℤ)))⁻¹)
                = 4 * (pS r d h : ℝ) * (6.3 * pD r d σ * pxi r ^ r)
                    * (pxi r ^ (-(((r*J : ℕ)) : ℤ)) * (pxi r ^ (-(((r*J : ℕ)) : ℤ)))⁻¹) := by ring
              _ = 4 * (pS r d h : ℝ) * (6.3 * pD r d σ * pxi r ^ r) * 1 := by rw [hUinv]
              _ = 25.2 * pxi r ^ r * (pS r d h : ℝ) * pD r d σ := by ring
          linarith [hc]
  have h25 : 25.2 * pxi r ^ r * (pS r d h : ℝ) * pD r d σ
      ≤ 25.2 * (pS r d h : ℝ) * pD r d σ := by
    have hxr1 : pxi r ^ r ≤ 1 := pow_le_one₀ (le_of_lt hxi_pos) hxi_le1
    have hnn : (0 : ℝ) ≤ 25.2 * (pS r d h : ℝ) * pD r d σ :=
      mul_nonneg (mul_nonneg (by norm_num) hSnn) hDnn
    have := mul_le_mul_of_nonneg_left hxr1 hnn
    nlinarith [this]
  have hUlehalf : pxi r ^ (-(((r*J : ℕ)) : ℤ)) ≤ pD r d σ / 2 := by
    have h := div_le_div_of_nonneg_left hDnn (by norm_num : (0 : ℝ) < 2) hr2
    linarith [hUle, h]
  have h4US : 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ)
      ≤ 2 * (pS r d h : ℝ) * pD r d σ := by
    have h4S : (0 : ℝ) ≤ 4 * (pS r d h : ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_left hUlehalf h4S
    nlinarith [h]
  have hPle : (evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1)
      ≤ 27.2 * (pS r d h : ℝ) * pD r d σ := by
    calc (evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1)
        ≤ _ := hPle1
      _ = 25.2 * pxi r ^ r * (pS r d h : ℝ) * pD r d σ
          + 4 * (pxi r ^ (-(((r*J : ℕ)) : ℤ))) * (pS r d h : ℝ) := hexpand
      _ ≤ 27.2 * (pS r d h : ℝ) * pD r d σ := by linarith [h25, h4US]
  have hXge2 : 2 ≤ (evX r J (pS r d h : ℝ) : ℝ) := by
    have h2US : (1 : ℝ) ≤ 2 * (pxi r ^ (-(((r*J : ℕ)) : ℤ)) * (pS r d h : ℝ)) := by
      have h := mul_le_mul hUge1 hS608 (by norm_num : (0 : ℝ) ≤ 608) hUnn
      nlinarith [h]
    have hge1 : 1 ≤ evSP r J (pS r d h : ℝ) := by
      apply Nat.le_floor
      simpa using h2US
    have hevX : (evX r J (pS r d h : ℝ) : ℝ) = 2 * (evSP r J (pS r d h : ℝ) : ℝ) := by
      simp only [evX]; push_cast; ring
    have hge1' : (1 : ℝ) ≤ (evSP r J (pS r d h : ℝ) : ℝ) := by exact_mod_cast hge1
    rw [hevX]; linarith
  have hPpos : 0 < (evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1) := by
    apply mul_pos
    · linarith [hXge2]
    · have hTpnn : (0 : ℝ) ≤ (evTp r J (pT r d σ : ℝ) : ℝ) := Nat.cast_nonneg _; linarith
  have hlog_le : Real.log ((evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1))
      ≤ 2 * Real.sqrt ((evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1)) := by
    have hPnn : 0 ≤ (evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1) :=
      le_of_lt hPpos
    have hspos : 0 < Real.sqrt ((evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1)) :=
      Real.sqrt_pos.mpr hPpos
    have h1 := Real.log_le_sub_one_of_pos hspos
    have h2 := Real.log_sqrt hPnn
    have h3 := Real.sqrt_nonneg ((evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1))
    linarith [h1, h2, h3]
  have hsqrt_le : 2 * Real.sqrt ((evX r J (pS r d h : ℝ) : ℝ) * ((evTp r J (pT r d σ : ℝ) : ℝ) + 1))
      ≤ 2 * Real.sqrt (27.2 * (pS r d h : ℝ) * pD r d σ) := by
    have h := Real.sqrt_le_sqrt hPle
    linarith [h]
  have hfinal : 2 * Real.sqrt (27.2 * (pS r d h : ℝ) * pD r d σ)
      ≤ (pS r d h : ℝ) * pD r d σ := by
    have hz : (108.8 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ := by nlinarith [hS608, hD1]
    have hz0 : (0 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ := by linarith
    have hkey : 27.2 * (pS r d h : ℝ) * pD r d σ
        ≤ ((pS r d h : ℝ) * pD r d σ / 2)^2 := by
      nlinarith [hz, hz0, mul_nonneg (by linarith : (0 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ - 108.8) hz0]
    have h := (Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ / 2)).mpr hkey
    linarith [h]
  have hcast : (((evTp r J (pT r d σ : ℝ)) + 1 : ℕ) : ℝ)
      = (evTp r J (pT r d σ : ℝ) : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  linarith [hlog_le, hsqrt_le, hfinal]

end Work.BW
