import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi
import Submission.Work.BW.pxi_ratio_eight_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `evX r J S = 2·evSP r J S = 2·⌊2ξ^{-rJ}S⌋ ≤ 4ξ^{-rJ}S` for `S ≥ 0` (only `⌊x⌋ ≤ x`). -/
private lemma evX_le_four_mul_aux {r J : ℕ} (hr : 2 ≤ r) {S : ℝ} (hS : 0 ≤ S) :
    (evX r J S : ℝ) ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) := by
  have hxipos : 0 < pxi r := pxi_pos hr
  have hpowpos : 0 < pxi r ^ (-((r * J : ℕ) : ℤ)) := zpow_pos hxipos _
  have hnn : (0 : ℝ) ≤ 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) :=
    mul_nonneg (by norm_num) (mul_nonneg hpowpos.le hS)
  have hfloor : ((evSP r J S : ℕ) : ℝ) ≤ 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) := by
    have h := Nat.floor_le hnn
    simpa only [evSP] using h
  calc (evX r J S : ℝ) = 2 * ((evSP r J S : ℕ) : ℝ) := by rw [evX]; push_cast; ring
    _ ≤ 2 * (2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)) := by linarith
    _ = 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) := by ring

/-- Numeric bound on the (21)-exponent `evV` of the even step at descent level `J`, in units of `S·D`.

`evV r d h σ J = d·h·(ξ^r·(ξ^{rJ}·T)) + (1.133 − 9·2^r)·S·D + 1.01·((X + 4ξ^{-rJ}S)/2^{J+1})·D + (0.044(J+1)/log(2rd))·S·D`, with `X = evX = 2·evSP ≤ 4ξ^{-rJ}S`, `S = pS r d h`, `D = pD r d σ`, `T = pT r d σ`, `ξ = pxi r`.

Route: `d·h·ξ^rξ^{rJ}T ≤ 0.735 S D` (`num_T` and `ξ^{r(J+1)} ≤ 1`); `X + 4ξ^{-rJ}S ≤ 8ξ^{-rJ}S`, so the third term is `≤ 1.01·4·(2ξ^r)^{-J}·S·D ≤ 4.04 S D` (`num_xi`: `1.07 ≤ 2ξ^r`); the last is `≤ 2.2 S D` as in `evenU_le`. Total `0.735 + 1.133 + 4.04 + 2.2 = 8.108 ≤ 8.11`. -/
theorem evenV_le {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) {σ : Fin r → ℝ}
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : J + 1 ≤ pI r d) :
    evV r d h σ J ≤ (8.11 - 9 * (2:ℝ)^r) * (pS r d h : ℝ) * pD r d σ := by
  have hS0 : (0 : ℝ) ≤ (pS r d h : ℝ) := by positivity
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD0 : (0 : ℝ) ≤ pD r d σ := le_of_lt hDpos
  have hSD : (0 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ := mul_nonneg hS0 hD0
  -- ## Term 1: `d·h·ξ^r·ξ^{rJ}·T ≤ 0.735·S·D`
  obtain ⟨_, _, hdhT, _⟩ := num_T hr hd hh σ hσ
  have hξ0 : (0 : ℝ) ≤ pxi r := le_of_lt (pxi_pos hr)
  have hξ1 : pxi r ≤ 1 := pxi_le_one r
  have hξr : pxi r ^ r ≤ 1 := pow_le_one₀ hξ0 hξ1
  have hξrJ : pxi r ^ (r * J) ≤ 1 := pow_le_one₀ hξ0 hξ1
  have hT0 : (0 : ℝ) ≤ (pT r d σ : ℝ) := by positivity
  have hprod : pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)) ≤ (pT r d σ : ℝ) := by
    have h1 : pxi r ^ (r * J) * (pT r d σ : ℝ) ≤ 1 * (pT r d σ : ℝ) :=
      mul_le_mul_of_nonneg_right hξrJ hT0
    have h2 : pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ))
        ≤ pxi r ^ r * (1 * (pT r d σ : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hξ0 r)
    have h3 : pxi r ^ r * (1 * (pT r d σ : ℝ)) ≤ 1 * (1 * (pT r d σ : ℝ)) :=
      mul_le_mul_of_nonneg_right hξr (by positivity)
    linarith [h2, h3]
  have hkey1 : (d : ℝ) * (h : ℝ) * (pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
      ≤ 0.735 * (pS r d h : ℝ) * pD r d σ := by
    have hdh : (0 : ℝ) ≤ (d : ℝ) * (h : ℝ) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hprod hdh
    linarith [hstep, hdhT]
  -- ## Term 3: `1.01·((X + 4ξ^{-rJ}S)/2^{J+1})·D ≤ 4.04·S·D`
  have hX4 : (evX r J (pS r d h : ℝ) : ℝ)
      ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) :=
    evX_le_four_mul_aux hr hS0
  have h8u : 8 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) / 2 ^ (J + 1)
      ≤ 4 * (pS r d h : ℝ) := by
    have hratio := pxi_ratio_eight_le hr J
    have hmul := mul_le_mul_of_nonneg_right hratio hS0
    calc 8 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) / 2 ^ (J + 1)
        = (8 * pxi r ^ (-((r * J : ℕ) : ℤ)) / 2 ^ (J + 1)) * (pS r d h : ℝ) := by ring
      _ ≤ 4 * (pS r d h : ℝ) := hmul
  have hA : ((evX r J (pS r d h : ℝ) : ℝ)
        + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)
      ≤ 4 * (pS r d h : ℝ) := by
    have h8 : (evX r J (pS r d h : ℝ) : ℝ)
          + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))
        ≤ 8 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) := by linarith [hX4]
    have hp : (0 : ℝ) < 2 ^ (J + 1) := by positivity
    calc ((evX r J (pS r d h : ℝ) : ℝ)
            + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)
        ≤ 8 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) / 2 ^ (J + 1) :=
          div_le_div_of_nonneg_right h8 hp.le
      _ ≤ 4 * (pS r d h : ℝ) := h8u
  have hkey3 : 1.01 * (((evX r J (pS r d h : ℝ) : ℝ)
            + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)) * pD r d σ
      ≤ 4.04 * (pS r d h : ℝ) * pD r d σ := by
    have h1 : 1.01 * (((evX r J (pS r d h : ℝ) : ℝ)
            + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1))
        ≤ 4.04 * (pS r d h : ℝ) := by
      have hmulA := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 1.01)
      nlinarith [hmulA]
    have hmul := mul_le_mul_of_nonneg_right h1 hD0
    calc 1.01 * (((evX r J (pS r d h : ℝ) : ℝ)
              + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)) * pD r d σ
        = (1.01 * (((evX r J (pS r d h : ℝ) : ℝ)
              + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1))) * pD r d σ :=
          by ring
      _ ≤ (4.04 * (pS r d h : ℝ)) * pD r d σ := hmul
      _ = 4.04 * (pS r d h : ℝ) * pD r d σ := by ring
  -- ## Term 4: `0.044(J+1)/log(2rd)·S·D ≤ 2.2·S·D`
  have hLpos : (0 : ℝ) < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hJle : ((J + 1 : ℕ) : ℝ) ≤ (pI r d : ℝ) := by exact_mod_cast hJ
  have hpIle : (pI r d : ℝ) ≤ 50 * Real.log (2 * r * d) := by
    have h0 : (0 : ℝ) ≤ 50 * Real.log (2 * r * d) := by
      linarith [log_2rd_ge hr hd]
    simpa only [pI] using Nat.floor_le h0
  have hcoef : 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) ≤ 2.2 := by
    rw [div_le_iff₀ hLpos]
    nlinarith [hJle, hpIle]
  have hkey4 : 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ
      ≤ 2.2 * (pS r d h : ℝ) * pD r d σ := by
    calc 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ
        = (0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d)) * ((pS r d h : ℝ) * pD r d σ) :=
          by ring
      _ ≤ 2.2 * ((pS r d h : ℝ) * pD r d σ) := mul_le_mul_of_nonneg_right hcoef hSD
      _ = 2.2 * (pS r d h : ℝ) * pD r d σ := by ring
  -- ## Assembly
  have hsum : 0.735 * ((pS r d h : ℝ) * pD r d σ)
      + (1.133 - 9 * (2 : ℝ) ^ r) * ((pS r d h : ℝ) * pD r d σ)
      + 4.04 * ((pS r d h : ℝ) * pD r d σ)
      + 2.2 * ((pS r d h : ℝ) * pD r d σ)
      ≤ (8.11 - 9 * (2 : ℝ) ^ r) * ((pS r d h : ℝ) * pD r d σ) := by
    nlinarith [hSD]
  unfold evV
  linarith [hkey1, hkey3, hkey4, hsum]

end Work.BW
