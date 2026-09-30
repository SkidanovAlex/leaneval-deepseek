import Mathlib
import Submission.Work.BMF.vke_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-! ## Helper arithmetic for `Work.BMF.vke_delta`

Pure real-arithmetic lemmas used in the exponent comparison `vke_delta`. -/

/-- Numeric core of the bound on `s = (k-1) r`: if `K ≤ 4λ+4`, `log K ≤ B`, `1 ≤ λ`, `1 ≤ B`,
`0 ≤ B`, `0 ≤ K`, then `K (4 K log K + 2) ≤ 272 λ² B`. -/
lemma vkeS_arith {lam K logK B : ℝ} (hlam : 1 ≤ lam) (hK0 : 0 ≤ K)
    (hKle : K ≤ 4 * lam + 4) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B) (hlog : logK ≤ B) :
    K * (4 * K * logK + 2) ≤ 272 * lam ^ 2 * B := by
  have hK2 : K ^ 2 ≤ (4 * lam + 4) ^ 2 := by
    have := mul_self_le_mul_self hK0 hKle
    nlinarith [this]
  have hl2 : (lam + 1) ^ 2 ≤ 4 * lam ^ 2 := by nlinarith [hlam]
  have hK2' : K ^ 2 ≤ 64 * lam ^ 2 := by nlinarith [hK2, hl2]
  have hmul : K ^ 2 * logK ≤ K ^ 2 * B := mul_le_mul_of_nonneg_left hlog (by positivity)
  have h1 : 4 * K ^ 2 * logK ≤ 4 * K ^ 2 * B := by linarith [hmul]
  have h2 : 4 * K ^ 2 * B ≤ 256 * lam ^ 2 * B := by
    have h44 : 4 * K ^ 2 ≤ 256 * lam ^ 2 := by nlinarith [hK2']
    exact mul_le_mul_of_nonneg_right h44 hB0
  have hK16 : 2 * K ≤ 16 * lam := by nlinarith [hKle, hlam]
  have hb : (1 : ℝ) ≤ lam * B := by
    have := mul_le_mul hlam hB1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ lam)
    simpa using this
  have hb2 : lam ≤ lam ^ 2 * B := by nlinarith [hb, hlam]
  have h3 : 2 * K ≤ 16 * lam ^ 2 * B := by nlinarith [hK16, hb2]
  have heq : K * (4 * K * logK + 2) = 4 * K ^ 2 * logK + 2 * K := by ring
  rw [heq]
  linarith [h1, h2, h3]

/-- The reduction exponent product satisfies `s = (k-1) r ≤ 272 λ² (log 4 + log(λ+2))`. -/
lemma vke_deltaS_bound {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) :
    ((vkS N t : ℕ) : ℝ) ≤ 272 * (vkLam N t) ^ 2 * (Real.log 4 + Real.log (vkLam N t + 2)) := by
  have hlam1 : 1 ≤ vkLam N t := vkLam_ge_one hN hNt
  have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
  obtain ⟨_, hKge⟩ := vkK_bounds hN hNt
  have hK0 : (0 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by positivity
  have hKpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by
    have : (0 : ℕ) < vkK N t := by omega
    exact_mod_cast this
  have hrle : ((vkR N t : ℕ) : ℝ)
      ≤ 4 * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) + 2 := vkR_le hN hNt
  have hrpos : (0 : ℝ) < ((vkR N t : ℕ) : ℝ) := by
    have : (0 : ℕ) < vkR N t := by rw [vkR]; omega
    exact_mod_cast this
  have hlogk : Real.log ((vkK N t : ℕ) : ℝ)
      ≤ Real.log 4 + Real.log (vkLam N t + 2) := by
    have h1 : Real.log ((vkK N t : ℕ) : ℝ) ≤ Real.log (4 * vkLam N t + 4) :=
      Real.log_le_log hKpos hKge
    have h2 : Real.log (4 * vkLam N t + 4) = Real.log 4 + Real.log (vkLam N t + 1) := by
      rw [show 4 * vkLam N t + 4 = 4 * (vkLam N t + 1) by ring,
        Real.log_mul (by norm_num) (by linarith : (vkLam N t + 1) ≠ 0)]
    have h3 : Real.log (vkLam N t + 1) ≤ Real.log (vkLam N t + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hB1 : (1 : ℝ) ≤ Real.log 4 + Real.log (vkLam N t + 2) := by
    have h3 : Real.log 3 ≤ Real.log (vkLam N t + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith [Real.log_three_gt_d9, h3, h4]
  have hB0 : (0 : ℝ) ≤ Real.log 4 + Real.log (vkLam N t + 2) := by linarith [hB1]
  have hs_eq : ((vkS N t : ℕ) : ℝ)
      = (((vkK N t - 1 : ℕ)) : ℝ) * ((vkR N t : ℕ) : ℝ) := by
    rw [vkS]; push_cast; ring
  have hk1 : (((vkK N t - 1 : ℕ)) : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ vkK N t)]; push_cast; linarith
  have hstep : ((vkS N t : ℕ) : ℝ) ≤ ((vkK N t : ℕ) : ℝ)
      * (4 * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) + 2) := by
    rw [hs_eq]
    calc (((vkK N t - 1 : ℕ)) : ℝ) * ((vkR N t : ℕ) : ℝ)
        ≤ ((vkK N t : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hk1 (le_of_lt hrpos)
      _ ≤ ((vkK N t : ℕ) : ℝ)
            * (4 * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hrle hK0
  exact le_trans hstep (vkeS_arith hlam1 hK0 hKge hB0 hB1 hlogk)

/-- Numeric comparison `36 c s ≤ λ² log(λ+2)` for `s ≤ 272 λ² (log 4 + log(λ+2))`. -/
lemma vke_delta_num1 {lam s c : ℝ} (hlam : 1 ≤ lam) (hc : 0 < c) (hc1 : c ≤ 1/100000)
    (hs : s ≤ 272 * lam ^ 2 * (Real.log 4 + Real.log (lam + 2))) :
    36 * c * s ≤ lam ^ 2 * Real.log (lam + 2) := by
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4_le : Real.log 4 ≤ 2 := by
    rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
  have hL : (1 : ℝ) ≤ Real.log (lam + 2) := by
    have h3 : Real.log 3 ≤ Real.log (lam + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_three_gt_d9, h3]
  have h1 : 36 * c * s ≤ 36 * c * (272 * lam ^ 2 * (Real.log 4 + Real.log (lam + 2))) := by
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 36 * c)
    linarith [this]
  have h2 : 36 * c * (272 * lam ^ 2 * (Real.log 4 + Real.log (lam + 2)))
      ≤ lam ^ 2 * Real.log (lam + 2) := by
    have hlam2pos : 0 < lam ^ 2 := by nlinarith [hlam]
    have hcore : 9792 * c * (Real.log 4 + Real.log (lam + 2)) ≤ Real.log (lam + 2) := by
      have hBnn : 0 ≤ Real.log 4 + Real.log (lam + 2) := by linarith
      have hcB : 9792 * c * (Real.log 4 + Real.log (lam + 2))
          ≤ 9792 * (1/100000) * (Real.log 4 + Real.log (lam + 2)) := by
        have hcc : 9792 * c ≤ 9792 * (1/100000) := by linarith [hc1]
        nlinarith [mul_le_mul_of_nonneg_right hcc hBnn]
      have hstep2 : 9792 * (1/100000) * (Real.log 4 + Real.log (lam + 2))
          ≤ Real.log (lam + 2) := by nlinarith [hlog4_le, hL]
      linarith [hcB, hstep2]
    have hgoal : 36 * c * (272 * lam ^ 2 * (Real.log 4 + Real.log (lam + 2)))
        = lam ^ 2 * (9792 * c * (Real.log 4 + Real.log (lam + 2))) := by ring
    rw [hgoal]
    exact mul_le_mul_of_nonneg_left hcore hlam2pos.le
  linarith [h1, h2]

/-- Numeric comparison `c / (λ² log(λ+2)) ≤ λ/(2k)` for `0 < k ≤ 4λ+4`. -/
lemma vke_delta_num2 {lam k c : ℝ} (hlam : 1 ≤ lam) (hc : 0 < c) (hc1 : c ≤ 1/100000)
    (hk : k ≤ 4 * lam + 4) (hkpos : 0 < k) :
    c / (lam ^ 2 * Real.log (lam + 2)) ≤ lam / (2 * k) := by
  have hL : (1 : ℝ) ≤ Real.log (lam + 2) := by
    have h3 : Real.log 3 ≤ Real.log (lam + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_three_gt_d9, h3]
  have hlam2pos : 0 < lam ^ 2 := by nlinarith [hlam]
  have hDpos : 0 < lam ^ 2 * Real.log (lam + 2) := mul_pos hlam2pos (by linarith)
  have hD1 : (1 : ℝ) ≤ lam ^ 2 * Real.log (lam + 2) := by nlinarith [hlam, hL]
  have hLHS : c / (lam ^ 2 * Real.log (lam + 2)) ≤ 1/100000 := by
    have hcD : c / (lam ^ 2 * Real.log (lam + 2)) ≤ c := by
      rw [div_le_iff₀ hDpos]
      nlinarith [hD1, le_of_lt hc]
    linarith [hcD, hc1]
  have hRHS : (1 : ℝ) / 16 ≤ lam / (2 * k) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
    nlinarith [hk, hlam]
  linarith [hLHS, hRHS]

/-- **The exponent comparison.**  For `2 ≤ N ≤ t`, the saving produced by the reduction dominates
twice the saving required by the target, the required saving is at most `(λ/k)/2`, and `λ ≤ k`:
`2 δ_req ≤ δ_avail`, `δ_req ≤ λ/(2k)`, `0 ≤ δ_req`, `λ ≤ k`.

Route.  Only `λ ≥ 1` is used.  `Work.BMF.vkDeltaA_ge` gives `δ_avail ≥ 1/(18 s)` with `s = (k-1)r`;
`δ_req = c/(λ² log(λ+2))` so it suffices that `λ² log(λ+2) ≥ 36 c s`.  With `4λ+2 ≤ k ≤ 4λ+4`
(from `k = 2⌈2λ⌉+2`) and `r ≤ 4k log k + 2`, one has `s ≤ 272 λ² (log 4 + log(λ+2))`; the hypothesis
`c ≤ 1/100000` makes `log(λ+2) ≥ 8568 c (log 4 + log(λ+2))` for every `λ ≥ 1` (since
`log(λ+2) ≥ log 3`).  The same bounds give `δ_req ≤ λ/(2k)`, and `λ ≤ k` is `λ ≤ 4λ+2`. -/
theorem vke_delta (c N t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1/100000) (hN : 2 ≤ N) (hNt : N ≤ t) :
    2 * vkDelta c N t ≤ vkDeltaA N t ∧
      vkDelta c N t ≤ vkLam N t / (2 * ((vkK N t : ℕ) : ℝ)) ∧
      0 ≤ vkDelta c N t ∧ vkLam N t ≤ ((vkK N t : ℕ) : ℝ) := by
  have hlam1 : 1 ≤ vkLam N t := vkLam_ge_one hN hNt
  have hlampos : 0 < vkLam N t := vkLam_pos hN hNt
  obtain ⟨_, hKge⟩ := vkK_bounds hN hNt
  have hKpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by
    have : (0 : ℕ) < vkK N t := by have := vkK_ge_six hN hNt; omega
    exact_mod_cast this
  have hLpos : 0 < Real.log (vkLam N t + 2) := Real.log_pos (by linarith)
  have hEQ : vkDelta c N t = c / (vkLam N t ^ 2 * Real.log (vkLam N t + 2)) := by
    rw [vkDelta]
    have hratio : Real.log N / Real.log t = 1 / vkLam N t := by
      rw [vkLam, one_div, inv_div]
    rw [hratio, div_pow, one_pow]
    have h1 : vkLam N t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hlampos)
    have h2 : Real.log (vkLam N t + 2) ≠ 0 := ne_of_gt hLpos
    field_simp
  -- (4) λ ≤ k
  have h4 : vkLam N t ≤ ((vkK N t : ℕ) : ℝ) := by
    obtain ⟨hKle, _⟩ := vkK_bounds hN hNt
    linarith
  -- (3) 0 ≤ δ_req
  have h3 : 0 ≤ vkDelta c N t := by
    rw [hEQ]
    exact div_nonneg (le_of_lt hc) (le_of_lt (mul_pos (pow_pos hlampos 2) hLpos))
  -- (2) δ_req ≤ λ/(2k)
  have h2 : vkDelta c N t ≤ vkLam N t / (2 * ((vkK N t : ℕ) : ℝ)) :=
    le_trans (le_of_eq hEQ) (vke_delta_num2 hlam1 hc hc1 hKge hKpos)
  -- (1) 2 δ_req ≤ δ_avail
  have hs1 : (1 : ℝ) ≤ ((vkS N t : ℕ) : ℝ) := by
    have hk1 : 1 ≤ vkK N t - 1 := by have := vkK_ge_six hN hNt; omega
    have hr1 : 1 ≤ vkR N t := by rw [vkR]; omega
    have hmul : 1 ≤ vkS N t := by
      rw [vkS]
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ (vkK N t - 1) * vkR N t := Nat.mul_le_mul hk1 hr1
    exact_mod_cast hmul
  have hs0 : (0 : ℝ) < ((vkS N t : ℕ) : ℝ) := lt_of_lt_of_le one_pos hs1
  have hnum1 : 36 * c * ((vkS N t : ℕ) : ℝ) ≤ (vkLam N t) ^ 2 * Real.log (vkLam N t + 2) :=
    vke_delta_num1 hlam1 hc hc1 (vke_deltaS_bound hN hNt)
  have hA : 1 / (18 * ((vkS N t : ℕ) : ℝ)) ≤ vkDeltaA N t := vkDeltaA_ge hN hNt
  have h2c : 2 * (c / (vkLam N t ^ 2 * Real.log (vkLam N t + 2)))
      ≤ 1 / (18 * ((vkS N t : ℕ) : ℝ)) := by
    rw [← mul_div_assoc]
    refine div_le_div_of_mul_le (by positivity) (by linarith [hs0]) ?_
    nlinarith [hnum1]
  have h1 : 2 * vkDelta c N t ≤ vkDeltaA N t := by
    rw [hEQ]
    exact le_trans h2c hA
  exact ⟨h1, h2, h3, h4⟩

end Work.BMF
