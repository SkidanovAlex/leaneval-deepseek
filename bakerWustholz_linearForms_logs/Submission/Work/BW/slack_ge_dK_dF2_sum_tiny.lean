import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.ph_ge_nineteen
import Submission.Work.BW.sysRow_height_bound
import Submission.Work.BW.sigma_sum_le
import Submission.Work.BW.slack_ge_dK_dF2_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- **Numeric core of the §13 slack estimate, sharpened constant.**  For `r ≥ 2`, `d ≥ 1`,
`h ≥ 19` and any `σ : Fin r → ℝ` with `∏σ ≥ 0`,

`4·r·d^{r+2}·∏σ ≤ 0.001·pS r d h·pD r d σ`.

Unfolding `pS r d h = 16 r d h` and `pD r d σ = 2 r^r (32d)^{r+1} log(2rd)·∏σ`, both sides carry
a common factor `d^{r+2}·∏σ ≥ 0`, and the assertion reduces to
`4r ≤ 0.032·h·r^{r+1}·32^{r+1}·log(2rd)`.  This follows from `h ≥ 19`, `r^{r+1} ≥ r^3`,
`32^{r+1} ≥ 32^3` and `log(2rd) ≥ 1` (as `2rd ≥ 4 > e`): the right-hand side is at least
`0.032·19·32768·r^3 = 19922.944 r^3`, against the left-hand side `4r` — a margin of a factor
`≈ 5·10^3` in `r^2`. -/
lemma slack_core_tiny {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h)
    (σ : Fin r → ℝ) (hP : 0 ≤ ∏ j, σ j) :
    4 * (r:ℝ) * (d:ℝ)^(r+2) * (∏ j, σ j) ≤
      0.001 * ((pS r d h : ℝ) * pD r d σ) := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hhR : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlog : (1:ℝ) ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_three]
  have hbase : 4 * (r:ℝ) ≤
      0.032 * (h:ℝ) * (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * Real.log (2 * (r:ℝ) * (d:ℝ)) := by
    have hB : (r:ℝ)^3 ≤ (r:ℝ)^(r+1) := pow_le_pow_right₀ (by linarith) (by omega)
    have hC : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
      have h32 : (32:ℝ)^3 = 32768 := by norm_num
      rw [← h32]
      exact pow_le_pow_right₀ (show (1:ℝ) ≤ 32 by norm_num) (show 3 ≤ r + 1 by omega)
    have hA : (0.608:ℝ) ≤ 0.032 * (h:ℝ) := by linarith
    have h1 : 4 * (r:ℝ) ≤ 0.608 * (r:ℝ)^3 * 32768 * 1 := by
      have hr2 : (4:ℝ) ≤ (r:ℝ)^2 := by nlinarith
      have hr0 : (0:ℝ) ≤ (r:ℝ) := by linarith
      nlinarith [hr2, hr0]
    have h2 : 0.608 * (r:ℝ)^3 * 32768 * 1
        ≤ (0.032 * (h:ℝ)) * (r:ℝ)^(r+1) * (32:ℝ)^(r+1)
          * Real.log (2 * (r:ℝ) * (d:ℝ)) := by
      have h3 : (0:ℝ) ≤ 0.032 * (h:ℝ) := by positivity
      have h4 : (0:ℝ) ≤ 0.032 * (h:ℝ) * (r:ℝ)^(r+1) := by positivity
      exact mul_le_mul (mul_le_mul (mul_le_mul hA hB (by positivity) h3) hC (by norm_num) h4)
        hlog (by norm_num) (by positivity)
    linarith [h1, h2]
  have hkey : (0.032 * (h:ℝ) * (r:ℝ)^(r+1) * (32:ℝ)^(r+1)
          * Real.log (2 * (r:ℝ) * (d:ℝ))) * (d:ℝ)^(r+2) * (∏ j, σ j)
        = 0.001 * ((pS r d h : ℝ) * pD r d σ) := by
    have h1 : (r:ℝ)^(r+1) = (r:ℝ)^r * (r:ℝ) := pow_succ _ _
    have h2 : (d:ℝ)^(r+2) = (d:ℝ) * (d:ℝ)^(r+1) := by
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ']
    have h3 : (32 * (d:ℝ))^(r+1) = (32:ℝ)^(r+1) * (d:ℝ)^(r+1) := mul_pow _ _ _
    rw [pS, pD]
    push_cast
    rw [h3, h2, h1]
    ring
  calc 4 * (r:ℝ) * (d:ℝ)^(r+2) * (∏ j, σ j)
      ≤ (0.032 * (h:ℝ) * (r:ℝ)^(r+1) * (32:ℝ)^(r+1)
          * Real.log (2 * (r:ℝ) * (d:ℝ))) * (d:ℝ)^(r+2) * (∏ j, σ j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbase (pow_nonneg (by positivity) _)) hP
    _ = 0.001 * ((pS r d h : ℝ) * pD r d σ) := hkey

/-- **Slack estimate (sum form), sharpened constant.**  Under the Baker–Wüstholz standing hypotheses
and the §11 basic hypothesis, the §13 "slack" term `0.001·pS·pD` dominates
`4·[K:ℚ]·[F:ℚ]²·∑σⱼ`, where `F = auxField α'`.

The proof is the same as for `slack_ge_dK_dF2_sum`, with the numeric core `slack_core` replaced by
the sharper `slack_core_tiny` (the constant `0.1` becomes `0.001`, and the numerical margin
`≈ 5·10^3` against the factor `r^2` is more than enough). -/
theorem slack_ge_dK_dF2_sum_tiny {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (hr : 2 ≤ r) :
    4 * (Module.finrank ℚ K : ℝ) * (Module.finrank ℚ ↥(auxField α') : ℝ) ^ 2 * (Finset.univ.sum fun j => σ j)
      ≤ 0.001 * ((pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ) := by
  have hr1 : 1 ≤ r := by omega
  have hd1 : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hfd : Module.finrank ℚ ↥(auxField α') ≤ Module.finrank ℚ K := finrank_auxField_le α'
  have h19 : 19 ≤ ph (hL b (Module.finrank ℚ K)) v := ph_ge_nineteen φ α b k c v hst
  have hσpos : ∀ j, 0 < σ j := fun j => hBH.2.2.2.2.1 j
  have hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j := fun j =>
    le_trans (one_div_finrank_le_hmod (α' j) (lamP φ α v L j)) (hBH.2.2.2.2.2.1 j)
  have hSle := sigma_sum_le (K := K) σ hσ
  have hSnn : (0:ℝ) ≤ ∑ j, σ j := Finset.sum_nonneg fun j _ => le_of_lt (hσpos j)
  have hPnn : (0:ℝ) ≤ ∏ j, σ j := Finset.prod_nonneg fun j _ => le_of_lt (hσpos j)
  have hfdR : (Module.finrank ℚ ↥(auxField α') : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast hfd
  have hf2 : ((Module.finrank ℚ ↥(auxField α') : ℝ))^2 ≤ ((Module.finrank ℚ K : ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) hfdR 2
  have hpw : (Module.finrank ℚ K : ℝ)^(r+2)
      = (Module.finrank ℚ K : ℝ) * (Module.finrank ℚ K : ℝ)^(r-1)
        * (Module.finrank ℚ K : ℝ)^2 := by
    rw [show r + 2 = (1 + (r - 1)) + 2 by omega, pow_add, pow_add, pow_one]
  calc 4 * (Module.finrank ℚ K : ℝ) * (Module.finrank ℚ ↥(auxField α') : ℝ) ^ 2 * (∑ j, σ j)
      ≤ 4 * (Module.finrank ℚ K : ℝ) * (Module.finrank ℚ K : ℝ)^2 * (∑ j, σ j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 (by positivity)) hSnn
    _ ≤ 4 * (Module.finrank ℚ K : ℝ) * (Module.finrank ℚ K : ℝ)^2
          * ((r : ℝ) * (Module.finrank ℚ K : ℝ)^(r-1) * ∏ j, σ j) :=
        mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = 4 * (r : ℝ) * (Module.finrank ℚ K : ℝ)^(r+2) * ∏ j, σ j := by
        rw [hpw]; ring
    _ ≤ 0.001 * ((pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ)
          * pD r (Module.finrank ℚ K) σ) := slack_core_tiny hr hd1 h19 σ hPnn

end Work.BW
