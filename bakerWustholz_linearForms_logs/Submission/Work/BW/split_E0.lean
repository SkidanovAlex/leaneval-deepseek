import Mathlib
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # `Work.BW.split_E0`

The first exclusion condition (E0) of `multiplicity_prop` / `split_conditions`, for the
half split of the BW §21 budgets.

With `𝒟_j = calD r d h σ j`, `𝒮 = calS r d h`, `𝒯 = calT r d σ` and
`Sq m = halfSplit r 𝒮 m`, `Tq m = halfSplit r 𝒯 m`, condition (E0) reads

  `(r+1) · 𝒟_j < Tq 0 + 1`  for every `j ≥ 1`,

i.e. `(r+1) · 2^{-I} D_j < ⌊𝒯/2⌋ + 1`. It is what excludes point collisions in the
`G_a × ker χ` case (BW §21, condition (5) at `m = 0`).

The whole content is a numerical comparison. Writing `D = pD r d σ` and `I = pI r d`,
the chain is

  `(r+1) 𝒟_j = (r+1) D_j / 2^I ≤ (r+1) D / (r 2^I) ≤ 2 D / 2^I ≤ 𝒯 / 2 < ⌊𝒯/2⌋ + 1`,

where the middle inequality `4 D ≤ 2^I 𝒯` follows from
`pT ≥ 11 r D` (the definitional floor bound) and `2^I ξ^{rI} = (2 ξ^r)^I ≥ 1`, the last
being the numerical fact `ξ^r ≥ 1/2` for `r ≥ 2` (`ξ = 1 - 0.536/r`). -/

namespace Work.BW

/-- `ξ^r ≥ 1/2` for `r ≥ 2`, where `ξ = pxi r = 1 - 0.536/r`.

Equivalently `2 ξ^r ≥ 1` (see `one_le_two_mul_pxi_pow`). The minimum of `2 ξ^r` over
`r ≥ 2` is attained at `r = 2` (`2 · 0.732² = 1.0716`). -/
theorem pxi_pow_ge_half {r : ℕ} (hr : 2 ≤ r) : (1 / 2 : ℝ) ≤ pxi r ^ r := by
  rcases Nat.eq_or_lt_of_le hr with h | h
  · subst h; norm_num [pxi]
  · have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    have hden : (0 : ℝ) < (r : ℝ) - 0.536 := by linarith
    -- `-log ξ ≤ 0.536/(r - 0.536)`
    have hlog : -Real.log (pxi r) ≤ (0.536 : ℝ) / ((r : ℝ) - 0.536) := by
      have hInv : (1 - (0.536 : ℝ) / (r : ℝ))⁻¹ = (r : ℝ) / ((r : ℝ) - 0.536) := by
        field_simp
      rw [show pxi r = 1 - (0.536 : ℝ) / (r : ℝ) from rfl, ← Real.log_inv, hInv]
      have h1 : Real.log ((r : ℝ) / ((r : ℝ) - 0.536)) ≤
          (r : ℝ) / ((r : ℝ) - 0.536) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hrpos hden)
      have h2 : (r : ℝ) / ((r : ℝ) - 0.536) - 1 = (0.536 : ℝ) / ((r : ℝ) - 0.536) := by
        rw [div_sub_one hden.ne']; ring_nf
      linarith
    -- `r · (-log ξ) ≤ 0.536 r/(r - 0.536) ≤ 0.66`
    have hbound : (r : ℝ) * (-Real.log (pxi r)) ≤ 0.66 := by
      have hstep : (r : ℝ) * ((0.536 : ℝ) / ((r : ℝ) - 0.536)) ≤ 0.66 := by
        rw [← mul_div_assoc, div_le_iff₀ hden]
        nlinarith
      linarith [mul_le_mul_of_nonneg_left hlog hrpos.le]
    have hconv : (r : ℝ) * (-Real.log (pxi r)) = -((r : ℝ) * Real.log (pxi r)) := by ring
    rw [hconv] at hbound
    have hlog2 : (0.66 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hmain : -Real.log 2 ≤ (r : ℝ) * Real.log (pxi r) := by linarith
    have heq : pxi r ^ r = Real.exp ((r : ℝ) * Real.log (pxi r)) := by
      rw [← Real.rpow_natCast (pxi r) r, Real.rpow_def_of_pos (pxi_pos hr)]
      congr 1
      ring
    rw [heq]
    have h1 : Real.exp (-Real.log 2) ≤ Real.exp ((r : ℝ) * Real.log (pxi r)) :=
      Real.exp_le_exp.mpr hmain
    have h2 : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rwa [h2] at h1

/-- `1 ≤ 2 ξ^r`, the form in which the growth of `(2 ξ^r)^I` is used. -/
theorem one_le_two_mul_pxi_pow {r : ℕ} (hr : 2 ≤ r) : (1 : ℝ) ≤ 2 * pxi r ^ r := by
  have h := pxi_pow_ge_half hr
  linarith

/-- **Condition (E0) of the half split**: `(r+1) 𝒟_j < Tq 0 + 1` for every `j ≥ 1`.
This is the exclusion of point collisions in the `G_a × ker χ` case of BW §21. -/
theorem split_E0 {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d : ℝ) ≤ σ j) :
    ∀ j : Fin r, ((r : ℝ) + 1) * calD r d h σ j.succ < (halfSplit r (calT r d σ) 0 : ℝ) + 1 := by
  intro j
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hpxi : (0.7 : ℝ) ≤ pxi r := pxi_ge hr
  have h2I : (0 : ℝ) < (2 : ℝ) ^ pI r d := by positivity
  -- `(2 ξ^r)^I ≥ 1`
  have hxi : (1 : ℝ) ≤ (2 : ℝ) ^ pI r d * pxi r ^ (r * pI r d) := by
    have hbase : (1 : ℝ) ≤ 2 * pxi r ^ r := one_le_two_mul_pxi_pow hr
    have : (2 : ℝ) ^ pI r d * pxi r ^ (r * pI r d) = (2 * pxi r ^ r) ^ pI r d := by
      rw [mul_pow, ← pow_mul]
    rw [this]
    exact one_le_pow₀ hbase
  -- `4 D ≤ 2^I 𝒯`
  have hkey : 4 * pD r d σ ≤ (2 : ℝ) ^ pI r d * calT r d σ := by
    have hT : 11 * (r : ℝ) * pD r d σ ≤ (pT r d σ : ℝ) := pT_ge hr hd σ hσ
    have hXnn : (0 : ℝ) ≤ (2 : ℝ) ^ pI r d * pxi r ^ (r * pI r d) := by positivity
    have hPnonneg : (0 : ℝ) ≤ (pT r d σ : ℝ) := Nat.cast_nonneg _
    have hQP : (0 : ℝ) ≤ 11 * (r : ℝ) * pD r d σ := by positivity
    have hmul1 : (1 : ℝ) * (11 * (r : ℝ) * pD r d σ) ≤
        ((2 : ℝ) ^ pI r d * pxi r ^ (r * pI r d)) * (pT r d σ : ℝ) :=
      mul_le_mul hxi hT hQP hXnn
    have hpxinn : (0 : ℝ) ≤ pxi r := by linarith
    have hmul2 : pxi r * ((1 : ℝ) * (11 * (r : ℝ) * pD r d σ)) ≤
        pxi r * (((2 : ℝ) ^ pI r d * pxi r ^ (r * pI r d)) * (pT r d σ : ℝ)) :=
      mul_le_mul_of_nonneg_left hmul1 hpxinn
    have h4 : 4 * pD r d σ ≤ pxi r * ((1 : ℝ) * (11 * (r : ℝ) * pD r d σ)) := by
      have h1 : (2 : ℝ) * 0.7 ≤ (r : ℝ) * pxi r :=
        mul_le_mul hr2 hpxi (by norm_num) (by norm_num)
      have h11 : (4 : ℝ) ≤ 11 * ((r : ℝ) * pxi r) := by nlinarith [h1]
      have h2 := mul_le_mul_of_nonneg_right h11 hDpos.le
      nlinarith [h2]
    have hring : pxi r * (((2 : ℝ) ^ pI r d * pxi r ^ (r * pI r d)) * (pT r d σ : ℝ))
        = (2 : ℝ) ^ pI r d * calT r d σ := by
      rw [calT]; ring
    linarith [h4, hmul2, hring]
  -- `(r+1) 𝒟_j ≤ 2 D / 2^I`
  have hL : ((r : ℝ) + 1) * calD r d h σ j.succ ≤ 2 * pD r d σ / (2 : ℝ) ^ pI r d := by
    have hDj := pDj_le_r hr hd σ hσ j
    have hnum : ((r : ℝ) + 1) * (pDj r d σ j : ℝ) ≤ 2 * pD r d σ := by
      have h1 : ((r : ℝ) + 1) * (pDj r d σ j : ℝ) ≤ ((r : ℝ) + 1) * (pD r d σ / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hDj (by positivity)
      have h2 : ((r : ℝ) + 1) * (pD r d σ / (r : ℝ)) = ((r : ℝ) + 1) / (r : ℝ) * pD r d σ := by
        field_simp
      have h3 : ((r : ℝ) + 1) / (r : ℝ) ≤ 2 := by rw [div_le_iff₀ hrpos]; linarith
      have h4 : ((r : ℝ) + 1) / (r : ℝ) * pD r d σ ≤ 2 * pD r d σ :=
        mul_le_mul_of_nonneg_right h3 hDpos.le
      linarith
    rw [calD_succ]
    have : ((r : ℝ) + 1) * ((pDj r d σ j : ℝ) / (2 : ℝ) ^ pI r d)
        = (((r : ℝ) + 1) * (pDj r d σ j : ℝ)) / (2 : ℝ) ^ pI r d := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hnum h2I.le
  -- `2 D / 2^I ≤ 𝒯/2`
  have hcalT : 2 * pD r d σ / (2 : ℝ) ^ pI r d ≤ calT r d σ / 2 := by
    rw [div_le_div_iff₀ h2I (by norm_num : (0 : ℝ) < 2)]
    linarith [hkey]
  have hfloor : calT r d σ / 2 < (⌊calT r d σ / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [halfSplit_zero]
  linarith [hL, hcalT, hfloor]

end Work.BW
