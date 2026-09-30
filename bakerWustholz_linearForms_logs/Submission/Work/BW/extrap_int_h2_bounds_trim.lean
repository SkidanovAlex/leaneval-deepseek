import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `ξ = 1 - 0.536/r` is positive for `r ≥ 2`. -/
private lemma pxi_pos_trim {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  rw [pxi, sub_pos, div_lt_one hr0]
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  linarith

/-- `ξ = 1 - 0.536/r ≤ 1`. -/
private lemma pxi_le_one_trim (r : ℕ) : pxi r ≤ 1 := by
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  rw [pxi]
  have : 0 ≤ (0.536:ℝ) / r := div_nonneg (by norm_num) hr0
  linarith

/-- `D ≥ 608` under `r ≥ 2`, `d ≥ 1`, `σ_j ≥ 1/d`:
`D ≥ 2 r^r 32^{r+1} d log(2rd) ≥ 2·4·32768·1·(4/3) ≥ 608`. -/
private lemma pD_ge_608 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : (608:ℝ) ≤ pD r d σ := by
  have hlow := pD_low hr hd σ hσ
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    have h1 : (2:ℝ)^(2:ℕ) ≤ (r:ℝ)^(2:ℕ) := pow_le_pow_left₀ (by norm_num) hr2 2
    have h2 : (r:ℝ)^(2:ℕ) ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) hr
    calc (4:ℝ) = (2:ℝ)^(2:ℕ) := by norm_num
      _ ≤ (r:ℝ)^(2:ℕ) := h1
      _ ≤ (r:ℝ)^r := h2
  have h32 : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 32 by norm_num) (show 3 ≤ r + 1 by omega)
    norm_num at h
    exact h
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hlog : (4/3:ℝ) ≤ Real.log (2*r*d) := log_2rd_ge hr hd
  have h608 : (608:ℝ) ≤ 2 * (4:ℝ) * 32768 * 1 * (4/3) := by norm_num
  have hmono : 2 * (4:ℝ) * 32768 * 1 * (4/3)
      ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2*r*d) := by
    gcongr
  linarith [hlow, hmono, h608]

/-- Trimmed floor/parameter bundle for `extrap_int_h2`: the facts that `Work.BW.extrap_int_h2`
actually consumes (the sibling `BW/extrap_int_h2_bounds` states the same facts *plus* two
`Real.log` estimates that `extrap_int_h2` does not use; this trimmed node is the one the caller
imports). Routes:
`608 ≤ Sp`: `Sp = ⌊2^j ξ^{-rJ} S⌋₊`, `2^j ≥ 1`, `ξ^{-rJ} ≥ 1`, `608 ≤ pS` (`num_T`) and `Nat.le_floor`.
`Sp ≤ 2^j ξ^{-rJ} S`: `Nat.floor_le` (argument nonnegative). `Sp ≤ 2^j (qD) S`: `hq3` gives
`ξ^{-rJ} ≤ q·pD`; multiply.
`|s| ≤ 2Sp+1`: `hss` gives `|s| ≤ 2·(2^jξ^{-rJ}S) = 2A < 2Sp + 2` (`Nat.lt_floor_add_one`), and
both sides are integers, so `≤ 2Sp+1` (`Int.cast_lt`).
`max 1 (|s|/Sp) ≤ 2.003`: `|s|/Sp ≤ (2Sp+1)/Sp = 2 + 1/Sp ≤ 2 + 1/608`.
`Tp ≤ (1-ξ)ξ^jξ^{rJ}(pT)`: `Nat.floor_le`. `Tp+1 ≤ 7D`: `(1-ξ)T ≤ 6.3D` (`num_T`) and `D ≥ 1`.
`608 ≤ D`, `0 < D`: `num_D_lower` with `r ≥ 2`, `d ≥ 1`, `log 4 > 1`. `608 ≤ S`, `0 < S`:
`num_T`. `2^j q ≤ 2^(r-2)`: `q ≤ ((2ξ^r)^{-1})^J/r ≤ 1/r ≤ 1` (using `1.07 ≤ 2ξ^r`, `num_xi`) and
`2^j ≤ 2^(r-2)` from `hj`. `608 ≤ S·D`, `0 < S·D`: from the above. -/
theorem extrap_int_h2_bounds_trim {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (h : ℕ) (hh : 19 ≤ h)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (j : ℕ) (hj : j + 2 ≤ r) (Sp : ℕ)
    (hSp : (Sp : ℝ) = ⌊2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)⌋₊)
    (Tp : ℕ)
    (hTp : (Tp : ℝ) = ⌊(1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ)⌋₊)
    (s : ℤ) (hss : ((|s| : ℤ) : ℝ) ≤ 2 ^ (j + 1) * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))
    (q : ℝ) (hq1 : q ≤ ((2 * pxi r ^ r)⁻¹) ^ J / r)
    (hq3 : pxi r ^ (-((r * J : ℕ) : ℤ)) / pD r d σ ≤ q) :
    (608 : ℝ) ≤ (Sp : ℝ) ∧
    (Sp : ℝ) ≤ 2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) ∧
    (Sp : ℝ) ≤ 2 ^ j * (q * pD r d σ) * (pS r d h : ℝ) ∧
    ((|s| : ℤ) : ℝ) ≤ 2 * (Sp : ℝ) + 1 ∧
    max 1 (((|s| : ℤ) : ℝ) / (Sp : ℝ)) ≤ 2.003 ∧
    (Tp : ℝ) ≤ (1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ) ∧
    (Tp : ℝ) + 1 ≤ 7 * pD r d σ ∧
    (0 : ℝ) ≤ (pT r d σ : ℝ) ∧
    0 < pD r d σ ∧ (608 : ℝ) ≤ pD r d σ ∧
    0 < (pS r d h : ℝ) ∧ (608 : ℝ) ≤ (pS r d h : ℝ) ∧
    (2 : ℝ) ^ j * q ≤ (2 : ℝ) ^ (r - 2) ∧
    0 < (pS r d h : ℝ) * pD r d σ ∧ (608 : ℝ) ≤ (pS r d h : ℝ) * pD r d σ := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hxi_pos : 0 < pxi r := pxi_pos_trim hr
  have hxi_nonneg : 0 ≤ pxi r := le_of_lt hxi_pos
  have hxi_le_one : pxi r ≤ 1 := pxi_le_one_trim r
  -- §`S` and `T` facts from `num_T`
  obtain ⟨_, hT_up, _, hS_ge⟩ := num_T hr hd hh σ hσ
  have hS_pos : 0 < (pS r d h : ℝ) := by linarith [hS_ge]
  -- §`D` facts
  have hD_pos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD_ge_one : (1:ℝ) ≤ pD r d σ := pD_ge_one hr hd σ hσ
  have hD_ge : (608:ℝ) ≤ pD r d σ := pD_ge_608 hr hd σ hσ
  -- the factor `E = ξ^{-rJ}`
  set E : ℝ := pxi r ^ (-((r * J : ℕ) : ℤ)) with hEdef
  have hE_pos : 0 < E := by rw [hEdef]; exact zpow_pos hxi_pos _
  have hE_ge_one : (1:ℝ) ≤ E := by
    rw [hEdef]
    have hz : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (r * J))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hz, one_le_inv₀ (pow_pos hxi_pos (r * J))]
    exact pow_le_one₀ hxi_nonneg hxi_le_one
  -- the argument `A = 2^j ξ^{-rJ} S` of the floor defining `Sp`
  have hA_nonneg : (0:ℝ) ≤ (2:ℝ)^j * E * (pS r d h : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt hE_pos)) (le_of_lt hS_pos)
  have hA_ge : (608:ℝ) ≤ (2:ℝ)^j * E * (pS r d h : ℝ) := by
    have h2j1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num)
    calc (608:ℝ) = 1 * 1 * 608 := by ring
      _ ≤ (2:ℝ)^j * E * (pS r d h : ℝ) :=
          mul_le_mul (mul_le_mul h2j1 hE_ge_one (by norm_num) (by positivity))
            hS_ge (by norm_num) (mul_nonneg (by positivity) (le_of_lt hE_pos))
  -- §conjunct 1: `608 ≤ Sp`
  have hSp_ge608 : (608:ℝ) ≤ (Sp:ℝ) := by
    rw [hSp]
    exact_mod_cast (Nat.le_floor hA_ge)
  -- §conjunct 2
  have hSp_le_A : (Sp:ℝ) ≤ (2:ℝ)^j * E * (pS r d h : ℝ) := by
    rw [hSp]; exact Nat.floor_le hA_nonneg
  -- §conjunct 3
  have hE_le_qD : E ≤ q * pD r d σ := (div_le_iff₀ hD_pos).mp hq3
  have hSp_le_qDS : (Sp:ℝ) ≤ (2:ℝ)^j * (q * pD r d σ) * (pS r d h : ℝ) := by
    calc (Sp:ℝ) ≤ (2:ℝ)^j * E * (pS r d h : ℝ) := hSp_le_A
      _ ≤ (2:ℝ)^j * (q * pD r d σ) * (pS r d h : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hE_le_qD (by positivity : (0:ℝ) ≤ (2:ℝ)^j))
            (by linarith [hS_ge] : (0:ℝ) ≤ (pS r d h : ℝ))
  -- §conjunct 4: `|s| ≤ 2Sp + 1`
  have hss2 : ((|s|:ℤ):ℝ) ≤ 2 * ((2:ℝ)^j * E * (pS r d h : ℝ)) := by
    calc ((|s|:ℤ):ℝ) ≤ (2:ℝ)^(j+1) * E * (pS r d h : ℝ) := hss
      _ = 2 * ((2:ℝ)^j * E * (pS r d h : ℝ)) := by rw [pow_succ]; ring
  have hA_lt : (2:ℝ)^j * E * (pS r d h : ℝ) < (Sp:ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((2:ℝ)^j * E * (pS r d h : ℝ))
    rw [← hSp] at h
    exact h
  have h2A_lt : ((|s|:ℤ):ℝ) < 2 * (Sp:ℝ) + 2 := by linarith [hss2, hA_lt]
  have hs_le : ((|s|:ℤ):ℝ) ≤ 2 * (Sp:ℝ) + 1 := by
    have hcast : (((2*Sp+2:ℕ):ℤ):ℝ) = 2 * (Sp:ℝ) + 2 := by push_cast; ring
    have hc : ((|s|:ℤ):ℝ) < (((2*Sp+2:ℕ):ℤ):ℝ) := by rw [hcast]; exact h2A_lt
    have hn_lt : (|s|:ℤ) < ((2*Sp+2:ℕ):ℤ) := (Int.cast_lt).mp hc
    have hn_le : (|s|:ℤ) ≤ ((2*Sp+1:ℕ):ℤ) := by
      have he : ((2*Sp+2:ℕ):ℤ) = ((2*Sp+1:ℕ):ℤ) + 1 := by push_cast; ring
      omega
    calc ((|s|:ℤ):ℝ) ≤ (((2*Sp+1:ℕ):ℤ):ℝ) := by exact_mod_cast hn_le
      _ = 2 * (Sp:ℝ) + 1 := by push_cast; ring
  -- §conjunct 5: `max 1 (|s|/Sp) ≤ 2.003`
  have hSp_pos : (0:ℝ) < (Sp:ℝ) := by linarith [hSp_ge608]
  have hratio : ((|s|:ℤ):ℝ) / (Sp:ℝ) ≤ 2.003 := by
    rw [div_le_iff₀ hSp_pos]
    nlinarith [hs_le, hSp_ge608]
  have hmax : max 1 (((|s|:ℤ):ℝ) / (Sp:ℝ)) ≤ 2.003 := by
    rw [max_le_iff]; exact ⟨by norm_num, hratio⟩
  -- §conjunct 6: `Tp ≤ (1-ξ) ξ^j ξ^{rJ} T`
  have hTp_le : (Tp:ℝ) ≤ (1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ) := by
    rw [hTp]
    apply Nat.floor_le
    have h1m : 0 ≤ 1 - pxi r := by linarith [hxi_le_one]
    have hjnn : 0 ≤ pxi r ^ j := pow_nonneg hxi_nonneg j
    have hJnn : 0 ≤ pxi r ^ (r*J) := pow_nonneg hxi_nonneg (r*J)
    have hTnn : 0 ≤ (pT r d σ : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1m hjnn) hJnn) hTnn
  -- §conjunct 7: `Tp + 1 ≤ 7 D`
  have hTp_le_63 : (Tp:ℝ) ≤ 6.3 * pD r d σ := by
    have hprod : pxi r ^ j * pxi r ^ (r*J) ≤ 1 := by
      rw [← pow_add]; exact pow_le_one₀ hxi_nonneg hxi_le_one
    have h1m : 0 ≤ 1 - pxi r := by linarith [hxi_le_one]
    have hTnn : 0 ≤ (pT r d σ : ℝ) := Nat.cast_nonneg _
    have hle : (1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ)
        ≤ (1 - pxi r) * (pT r d σ : ℝ) := by
      have hX : (1 - pxi r) * (pxi r ^ j * pxi r ^ (r*J)) ≤ (1 - pxi r) * 1 :=
        mul_le_mul_of_nonneg_left hprod h1m
      calc (1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ)
          = ((1 - pxi r) * (pxi r ^ j * pxi r ^ (r*J))) * (pT r d σ : ℝ) := by ring
        _ ≤ ((1 - pxi r) * 1) * (pT r d σ : ℝ) := mul_le_mul_of_nonneg_right hX hTnn
        _ = (1 - pxi r) * (pT r d σ : ℝ) := by ring
    linarith [hTp_le, hle, hT_up]
  have hTp_add : (Tp:ℝ) + 1 ≤ 7 * pD r d σ := by
    nlinarith [hTp_le_63, hD_ge]
  -- §conjunct 11: `2^j q ≤ 2^{r-2}`
  have hb1 : (1:ℝ) ≤ 2 * pxi r ^ r := by linarith [(num_xi hr).2.2.2.2]
  have hq_pos : 0 < q := by
    have hEdiv : 0 < E / pD r d σ := div_pos hE_pos hD_pos
    linarith [hEdiv, hq3]
  have hq_le_one : q ≤ 1 := by
    have hbpos : (0:ℝ) < 2 * pxi r ^ r := by linarith [hb1]
    have hinv : ((2 * pxi r ^ r)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hb1
    have hpow : ((2 * pxi r ^ r)⁻¹) ^ J ≤ 1 :=
      pow_le_one₀ (le_of_lt (inv_pos.mpr hbpos)) hinv
    have hr1 : (1:ℝ) ≤ (r:ℝ) := by linarith [hr2]
    have hstep : ((2 * pxi r ^ r)⁻¹) ^ J / (r:ℝ) ≤ 1 := by
      rw [div_le_one hr0]; linarith [hpow, hr1]
    linarith [hq1, hstep]
  have h2j_le : (2:ℝ)^j ≤ (2:ℝ)^(r-2) :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : j ≤ r - 2)
  have hconj11 : (2:ℝ)^j * q ≤ (2:ℝ)^(r-2) := by
    have h2nn : (0:ℝ) ≤ (2:ℝ)^(r-2) := by positivity
    calc (2:ℝ)^j * q ≤ (2:ℝ)^(r-2) * q := mul_le_mul_of_nonneg_right h2j_le (le_of_lt hq_pos)
      _ ≤ (2:ℝ)^(r-2) * 1 := mul_le_mul_of_nonneg_left hq_le_one h2nn
      _ = (2:ℝ)^(r-2) := by ring
  -- §conjunct 12
  have hSD_ge : (608:ℝ) ≤ (pS r d h : ℝ) * pD r d σ := by
    calc (608:ℝ) = 608 * 1 := by ring
      _ ≤ (pS r d h : ℝ) * pD r d σ :=
          mul_le_mul hS_ge hD_ge_one (by norm_num) (by linarith [hS_ge])
  have hSD_pos : 0 < (pS r d h : ℝ) * pD r d σ := mul_pos hS_pos hD_pos
  exact ⟨hSp_ge608, hSp_le_A, hSp_le_qDS, hs_le, hmax, hTp_le, hTp_add,
    Nat.cast_nonneg _, hD_pos, hD_ge, hS_pos, hS_ge, hconj11, hSD_pos, hSD_ge⟩

end Work.BW
