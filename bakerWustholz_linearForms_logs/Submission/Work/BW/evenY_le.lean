import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi
import Submission.Work.BW.evY_term2_bound
import Submission.Work.BW.evY_term4_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 1000000

/-- `D ≥ 262144 ≥ 2·4·32³`: from `pD_low` and `r ≥ 2`, `d ≥ 1`, `log(2rd) ≥ 4/3 ≥ 1`. -/
private lemma pD_ge_262144 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) : (262144 : ℝ) ≤ pD r d σ := by
  have hDlow := pD_low hr hd σ hσ
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hrr : (4 : ℝ) ≤ (r : ℝ) ^ r := by
    have h1 : (2 : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hr2 2
    have h2 : (r : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (r : ℝ) ^ (2 : ℕ) := h1
      _ ≤ (r : ℝ) ^ r := h2
  have h32 : (32768 : ℝ) ≤ (32 : ℝ) ^ (r + 1) := by
    have h1 : (32 : ℝ) ^ (3 : ℕ) ≤ (32 : ℝ) ^ (r + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (32 : ℝ) ^ (3 : ℕ) = 32768 := by norm_num
    linarith [h1, h3]
  have hA : (262144 : ℝ) ≤ 2 * (r : ℝ) ^ r * (32 : ℝ) ^ (r + 1) := by
    have h1 : (8 : ℝ) ≤ 2 * (r : ℝ) ^ r := by linarith
    have hX : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r := by linarith
    have h := mul_le_mul h1 h32 (by norm_num : (0 : ℝ) ≤ 32768) hX
    norm_num at h
    exact h
  have hlog : (1 : ℝ) ≤ (d : ℝ) * Real.log (2 * r * d) := by
    have hL : (1 : ℝ) ≤ Real.log (2 * r * d) := by have := log_2rd_ge hr hd; linarith
    have := mul_le_mul hd1 hL (by norm_num : (0 : ℝ) ≤ 1) hd0.le
    simpa using this
  have hprod : (262144 : ℝ)
      ≤ (2 * (r : ℝ) ^ r * (32 : ℝ) ^ (r + 1)) * ((d : ℝ) * Real.log (2 * r * d)) := by
    have hX : (0 : ℝ) ≤ 2 * (r : ℝ) ^ r * (32 : ℝ) ^ (r + 1) := by linarith
    have hY : (0 : ℝ) ≤ (d : ℝ) * Real.log (2 * r * d) := by linarith
    calc (262144 : ℝ) = 262144 * 1 := by ring
      _ ≤ (2 * (r : ℝ) ^ r * (32 : ℝ) ^ (r + 1)) * ((d : ℝ) * Real.log (2 * r * d)) :=
          mul_le_mul hA hlog (by norm_num) hX
  have heq : 2 * (r : ℝ) ^ r * (32 : ℝ) ^ (r + 1) * (d : ℝ) * Real.log (2 * r * d)
      = (2 * (r : ℝ) ^ r * (32 : ℝ) ^ (r + 1)) * ((d : ℝ) * Real.log (2 * r * d)) := by ring
  linarith [hDlow, hprod, heq]

/-- Numeric bound on the (25)-term `evY` of the even step at descent level `J`, in units of `S·D`.

`evY r d h σ J = (T'+1)·(X + 2·log X + 3)` with `T' = evTp r J T = ⌊(1−ξ)ξ^rξ^{rJ}T⌋`, `X = evX = 2·evSP`, `evSP = ⌊2ξ^{-rJ}S⌋`, `S = pS r d h`, `D = pD r d σ`, `T = pT r d σ`, `ξ = pxi r`. Hypothesis `hnd : ∃j, 2^J ≤ pDj r d σ j` (non-degeneracy) is used through `pDj ≤ D/r`, i.e. `2^J ≤ D/r`, which with `1.07 ≤ 2ξ^r` (`num_xi`) gives `u := ξ^{-rJ} ≤ D/r`.

Route. `T' ≤ A := (1−ξ)ξ^rξ^{rJ}T ≤ 6.3ξ^r·D/u` (`num_T`), `X ≤ 4uS`.
* `(T'+1)X ≤ (6.3ξ^rD/u + 1)·4uS = 25.2ξ^r·S·D + 4uS` and `4uS ≤ (4/r)SD ≤ 2SD`.
* `(T'+1)(2log X + 3) ≤ (6.3ξ^rD/u + 1)(2log(4uS) + 3)`. Divide by `SD`: `6.3ξ^r(2log(4uS)+3)/(uS) + (2log(4uS)+3)/(SD)`. For `u ≥ 1`, `(2log(4uS)+3)/u ≤ 2log(4S)+3` (using `log u ≤ u−1`); and `u ≤ D` handles the second. Now `S ≥ 608` (`num_T`) makes `6.3(2log(4S)+3)/S ≤ 6.3(2log(2432)+3)/608 = 0.1927`, and `(2log(4S)+3)/(SD) + 2/S ≤ 0.004`. So the total is `≤ (25.2·ξ^r + 2.197)·S·D ≤ (25.2·ξ^r + 2.2)·S·D`.

Note `hnd` is genuinely needed (without it `4uS` is not bounded by `SD`). -/
theorem evenY_le {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) {σ : Fin r → ℝ}
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : J + 1 ≤ pI r d)
    (hnd : ∃ j, (2 : ℝ) ^ J ≤ (pDj r d σ j : ℝ)) :
    evY r d h σ J ≤ (25.2 * pxi r ^ r + 2.2) * (pS r d h : ℝ) * pD r d σ := by
  -- basic facts about `ξ = pxi r`
  have hxipos : 0 < pxi r := by
    rw [pxi]
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < r := by linarith
    have : (0.536 : ℝ) / r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hxile1 : pxi r ≤ 1 := by
    rw [pxi]
    have : (0 : ℝ) ≤ 0.536 / (r : ℝ) := by positivity
    linarith
  have hxipow : pxi r ^ r ≤ 0.732 := by
    have h1 := (num_xi hr).2.2.1
    calc pxi r ^ r ≤ pxi r ^ (r - 1) :=
          pow_le_pow_of_le_one (le_of_lt hxipos) hxile1 (Nat.sub_le r 1)
      _ ≤ 0.732 := h1
  have hnum := num_T hr hd hh σ hσ
  have hT2 : (1 - pxi r) * (pT r d σ : ℝ) ≤ 6.3 * pD r d σ := hnum.2.1
  have hS608 : (608 : ℝ) ≤ (pS r d h : ℝ) := hnum.2.2.2
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hD262 : (262144 : ℝ) ≤ pD r d σ := pD_ge_262144 hr hd σ hσ
  -- unfold `evY` and abbreviate
  simp only [evY]
  set xi : ℝ := pxi r ^ r with hxi_def
  set u : ℝ := pxi r ^ (-((r * J : ℕ) : ℤ)) with hu_def
  set S : ℝ := (pS r d h : ℝ) with hS_def
  set D : ℝ := pD r d σ with hD_def
  have hu_def' : u = pxi r ^ (-((r * J : ℕ) : ℤ)) := hu_def
  have hS_def' : S = (pS r d h : ℝ) := hS_def
  have hD_def' : D = pD r d σ := hD_def
  -- `ξ^r` facts
  have hxipos' : 0 < xi := by rw [hxi_def]; positivity
  have hxinn : 0 ≤ xi := le_of_lt hxipos'
  have hxipow' : xi ≤ 0.732 := by rw [hxi_def]; exact hxipow
  -- `D`, `S` nonnegativity
  have hDnn : 0 ≤ D := by rw [hD_def]; exact le_of_lt hDpos
  have hDpp : 0 < D := by rw [hD_def]; exact hDpos
  have hSnn : 0 ≤ S := by rw [hS_def]; linarith
  have hS608' : (608 : ℝ) ≤ S := by rw [hS_def]; exact hS608
  have hD262' : (262144 : ℝ) ≤ D := by rw [hD_def]; exact hD262
  -- `u` facts
  have hu_pos : 0 < u := by
    rw [hu_def', zpow_neg]
    exact inv_pos.mpr (pow_pos hxipos _)
  have hu1 : 1 ≤ u := by
    rw [hu_def']
    have hu_eq : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (r * J))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hu_eq]
    exact (one_le_inv₀ (pow_pos hxipos _)).mpr (pow_le_one₀ (le_of_lt hxipos) hxile1)
  have hu2 : u ≤ D / 2 := by
    have hu_le_2J : u ≤ (2 : ℝ) ^ J := by
      rw [hu_def']
      have hu_eq : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (r * J))⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      rw [hu_eq]
      have hpowpos : 0 < pxi r ^ (r * J) := pow_pos hxipos _
      have hxi07 : 1.07 ≤ 2 * pxi r ^ r := (num_xi hr).2.2.2.2
      have h1 : 1 ≤ (2 * pxi r ^ r) ^ J := one_le_pow₀ (by linarith)
      have h2 : (2 * pxi r ^ r) ^ J = 2 ^ J * (pxi r ^ r) ^ J := by rw [mul_pow]
      have h3 : pxi r ^ (r * J) = (pxi r ^ r) ^ J := by rw [pow_mul]
      have h4 : 1 ≤ 2 ^ J * pxi r ^ (r * J) := by rw [h3, ← h2]; exact h1
      rw [inv_le_iff_one_le_mul₀ hpowpos]
      exact h4
    obtain ⟨j, hj⟩ := hnd
    have hDjr := pDj_le_r hr hd σ hσ j
    have hDJ : (2 : ℝ) ^ J ≤ D / r := by rw [hD_def]; exact le_trans hj hDjr
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hle : D / r ≤ D / 2 := div_le_div_of_nonneg_left hDnn (by norm_num) hr2
    linarith [hu_le_2J, hDJ, hle]
  -- `T' + 1` bound
  have hTp1 : ((evTp r J (pT r d σ : ℝ) + 1 : ℕ) : ℝ) ≤ 6.3 * xi * D / u + 1 := by
    have hu_eq : u = (pxi r ^ (r * J))⁻¹ := by
      rw [hu_def', zpow_neg, zpow_natCast]
    have hxiJu : pxi r ^ (r * J) * u = 1 := by
      rw [hu_eq, mul_inv_cancel₀ (ne_of_gt (pow_pos hxipos _))]
    have h1mxi : 0 < 1 - pxi r := by
      rw [pxi]
      have hr0 : (0 : ℝ) < r := by linarith [show (2 : ℝ) ≤ r from by exact_mod_cast hr]
      have : (0 : ℝ) < 0.536 / r := by positivity
      linarith
    have hA : 0 ≤ (1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)) := by
      have : 0 < pxi r ^ (r * J) := pow_pos hxipos _
      positivity
    have hfloor := Nat.floor_le hA
    have hkey : (1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ))
        ≤ 6.3 * xi * D / u := by
      rw [le_div_iff₀ hu_pos]
      have hXeq : (1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)) * u
          = (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ) := by
        calc (1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)) * u
            = (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ) * (pxi r ^ (r * J) * u) := by ring
          _ = (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ) * 1 := by rw [hxiJu]
          _ = (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ) := by ring
      rw [hXeq, hxi_def, hD_def]
      have hstep : (1 - pxi r) * pxi r ^ r * (pT r d σ : ℝ) ≤ 6.3 * pxi r ^ r * pD r d σ := by
        have hxirnn : (0 : ℝ) ≤ pxi r ^ r := by positivity
        have := mul_le_mul_of_nonneg_left hT2 hxirnn
        nlinarith [this]
      exact hstep
    have hTp_le : ((evTp r J (pT r d σ : ℝ) : ℕ) : ℝ)
        ≤ (1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)) := hfloor
    rw [Nat.cast_add, Nat.cast_one]
    linarith [hTp_le, hkey]
  -- `X` bound
  have hXb : ((evX r J S : ℕ) : ℝ) + 2 * Real.log ((evX r J S : ℕ) : ℝ) + 3
      ≤ 4 * u * S + (2 * Real.log (4 * u * S) + 3) := by
    have harg : (0 : ℝ) ≤ 2 * (u * S) := by positivity
    have hfloor : ((evSP r J S : ℕ) : ℝ) ≤ 2 * (u * S) := by
      rw [evSP, ← hu_def']
      exact Nat.floor_le harg
    have hXeq : ((evX r J S : ℕ) : ℝ) = 2 * ((evSP r J S : ℕ) : ℝ) := by
      simp only [evX]; push_cast; ring
    have hXle : ((evX r J S : ℕ) : ℝ) ≤ 4 * u * S := by rw [hXeq]; linarith [hfloor]
    have hge : 1216 ≤ evSP r J S := by
      rw [evSP, ← hu_def']
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu_pos
      have hmul : (1 : ℝ) * 608 ≤ u * S := mul_le_mul hu1 hS608' (by norm_num) hu0
      have hgoal : (1216 : ℝ) ≤ 2 * (u * S) := by nlinarith [hmul]
      exact Nat.le_floor hgoal
    have hXge : 1 ≤ ((evX r J S : ℕ) : ℝ) := by
      rw [hXeq]
      have hgeR : (1216 : ℝ) ≤ (evSP r J S : ℝ) := by exact_mod_cast hge
      linarith [hgeR]
    have hlog : Real.log ((evX r J S : ℕ) : ℝ) ≤ Real.log (4 * u * S) :=
      Real.log_le_log (by linarith [hXge]) hXle
    linarith [hXle, hlog]
  have hXge1 : 1 ≤ ((evX r J S : ℕ) : ℝ) := by
    have hXeq : ((evX r J S : ℕ) : ℝ) = 2 * ((evSP r J S : ℕ) : ℝ) := by
      simp only [evX]; push_cast; ring
    rw [hXeq]
    have hge : 1216 ≤ evSP r J S := by
      rw [evSP, ← hu_def']
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu_pos
      have hmul : (1 : ℝ) * 608 ≤ u * S := mul_le_mul hu1 hS608' (by norm_num) hu0
      have hgoal : (1216 : ℝ) ≤ 2 * (u * S) := by nlinarith [hmul]
      exact Nat.le_floor hgoal
    have hgeR : (1216 : ℝ) ≤ (evSP r J S : ℝ) := by exact_mod_cast hge
    linarith [hgeR]
  -- the two numeric helpers
  have h2b : 6.3 * xi * D * (2 * Real.log (4 * u * S) + 3) / u ≤ 0.15 * S * D :=
    evY_term2_bound hS608' hDnn hu1 hxipos' hxipow'
  have h4b : 2 * Real.log (4 * u * S) + 3 ≤ 0.04 * S * D :=
    evY_term4_bound hS608' hD262' hu1 (by linarith [hu2])
  -- assembly
  have hCnn : 0 ≤ ((evX r J S : ℕ) : ℝ) + 2 * Real.log ((evX r J S : ℕ) : ℝ) + 3 := by
    have := Real.log_nonneg hXge1
    linarith
  have hB1nn : 0 ≤ 6.3 * xi * D / u + 1 := by
    have : 0 ≤ 6.3 * xi * D / u := by positivity
    linarith
  have hstep1 : ((evTp r J (pT r d σ : ℝ) + 1 : ℕ) : ℝ)
        * (((evX r J S : ℕ) : ℝ) + 2 * Real.log ((evX r J S : ℕ) : ℝ) + 3)
      ≤ (6.3 * xi * D / u + 1) * (4 * u * S + (2 * Real.log (4 * u * S) + 3)) :=
    mul_le_mul hTp1 hXb hCnn hB1nn
  have h4uS : 4 * u * S ≤ 2 * S * D := by nlinarith [hu2, hSnn]
  have hexp : (6.3 * xi * D / u + 1) * (4 * u * S + (2 * Real.log (4 * u * S) + 3))
      = 25.2 * xi * S * D + 6.3 * xi * D * (2 * Real.log (4 * u * S) + 3) / u
        + 4 * u * S + (2 * Real.log (4 * u * S) + 3) := by
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    field_simp
    ring
  calc ((evTp r J (pT r d σ : ℝ) + 1 : ℕ) : ℝ)
        * (((evX r J S : ℕ) : ℝ) + 2 * Real.log ((evX r J S : ℕ) : ℝ) + 3)
      ≤ (6.3 * xi * D / u + 1) * (4 * u * S + (2 * Real.log (4 * u * S) + 3)) := hstep1
    _ = 25.2 * xi * S * D + 6.3 * xi * D * (2 * Real.log (4 * u * S) + 3) / u
          + 4 * u * S + (2 * Real.log (4 * u * S) + 3) := hexp
    _ ≤ 25.2 * xi * S * D + 0.15 * S * D + 2 * S * D + 0.04 * S * D := by
          linarith [h2b, h4uS, h4b]
    _ ≤ (25.2 * xi + 2.2) * S * D := by
          have hSD : 0 ≤ S * D := mul_nonneg hSnn hDnn
          nlinarith [hSD]

end Work.BW
