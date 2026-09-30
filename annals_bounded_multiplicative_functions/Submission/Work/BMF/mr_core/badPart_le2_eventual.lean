import Mathlib
import Submission.Work.BMF.mr_core_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

open Filter
open Work.BMF.mrCore

/-- For `c > 0`, `(log Y)^{-c} → 0` as `Y → ∞`. -/
lemma tendsto_log_rpow_neg_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun Y : ℝ => (Real.log Y) ^ (-c)) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hc).comp Real.tendsto_log_atTop

/-- For `c > 0`, `(log Y)^c → ∞` as `Y → ∞`. -/
lemma tendsto_log_rpow_pos_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun Y : ℝ => (Real.log Y) ^ c) Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop

/-- A function tending to `0` is eventually dominated by any positive constant. -/
lemma eventually_le_of_tendsto_zero {f : ℝ → ℝ} (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    {c : ℝ} (hc : 0 < c) : ∀ᶠ Y in Filter.atTop, f Y ≤ c := by
  filter_upwards [(tendsto_order.1 hf).2 c hc] with Y hY
  exact le_of_lt hY

/-- For `r < 1` and `s > 0`, `exp (a (log Y)^r - s log Y) → 0` as `Y → ∞`. -/
lemma tendsto_exp_rpow_log_sub (a s r : ℝ) (hr : r < 1) (hs : 0 < s) :
    Filter.Tendsto (fun Y : ℝ => Real.exp (a * (Real.log Y) ^ r - s * Real.log Y))
      Filter.atTop (nhds 0) := by
  have hc : 0 < 1 - r := by linarith
  have hbase : Filter.Tendsto (fun Y : ℝ => (Real.log Y) ^ (r - 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hc).comp Real.tendsto_log_atTop
    simpa only [Function.comp_def, neg_sub] using h
  have h1 : Filter.Tendsto (fun Y : ℝ => a * (Real.log Y) ^ (r - 1) - s)
      Filter.atTop (nhds (-s)) := by
    have h := (hbase.const_mul a).sub (tendsto_const_nhds (x := s))
    simpa using h
  have h2 : Filter.Tendsto (fun Y : ℝ => Real.log Y * (a * (Real.log Y) ^ (r - 1) - s))
      Filter.atTop Filter.atBot :=
    Filter.Tendsto.atTop_mul_neg (by linarith : -s < 0) Real.tendsto_log_atTop h1
  have heq : (fun Y : ℝ => Real.log Y * (a * (Real.log Y) ^ (r - 1) - s)) =ᶠ[Filter.atTop]
      (fun Y : ℝ => a * (Real.log Y) ^ r - s * Real.log Y) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with Y hY
    have hx : 0 < Real.log Y := Real.log_pos hY
    rw [show r = 1 + (r - 1) by ring, Real.rpow_add hx, Real.rpow_one]
    ring_nf
  have h3 : Filter.Tendsto (fun Y : ℝ => a * (Real.log Y) ^ r - s * Real.log Y)
      Filter.atTop Filter.atBot := h2.congr' heq
  exact Real.tendsto_exp_atBot.comp h3

theorem badPart_le2_eventual (ε C₀ θ K W Cbs Cm B : ℝ)
    (hε : 0 < ε) (hC₀ : 0 < C₀) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hK : 4 ≤ K) (hW : 4 ≤ W) (hCbs : 0 < Cbs) (hCm : 0 < Cm) :
    ∀ᶠ Y in Filter.atTop,
      (16 : ℝ) ≤ Y ∧ (2 : ℝ) ≤ Work.BMF.mrCore.Pc Y ∧
      Real.exp (Work.BMF.mrCore.logQc B Y) ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4 ∧
      (Work.BMF.mrCore.Qc B Y) ^ 2 ≤ Y ∧
      1 / Work.BMF.mrCore.Pc Y ≤ ε / (96 * Cbs * (3 + 4 * C₀ / ε)) ∧
      max 1 (Real.log (4 * C₀ / ε)) ≤ Real.log Y ∧
      2 * Cbs * Cm * (K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2 *
          (Real.log Y) ^ (-(198 - 47 / 24 : ℝ))
        + 2 * K * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (-(198 - 47 / 48 : ℝ))) ≤ ε / 32 ∧
      2 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3 * (1 + B ^ 2) ^ 2 *
          Real.exp (-(B ^ 2 / 4)) * (Real.log Y) ^ (-(47 / 48 : ℝ)) ≤ ε / 64 ∧
      8 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3 * (Real.log Y) ^ (-(47 / 48 : ℝ)) / W
        ≤ ε / 64 := by
  have h1 : ∀ᶠ Y in Filter.atTop, (16 : ℝ) ≤ Y := Filter.eventually_ge_atTop 16
  have hPc_inf : Filter.Tendsto Work.BMF.mrCore.Pc Filter.atTop Filter.atTop := by
    have hg : Filter.Tendsto (fun Y : ℝ => (Real.log Y) ^ (47/48:ℝ)) Filter.atTop Filter.atTop :=
      tendsto_log_rpow_pos_atTop (47/48) (by norm_num)
    have h := Real.tendsto_exp_atTop.comp hg
    rw [show Work.BMF.mrCore.Pc = (fun Y : ℝ => Real.exp ((Real.log Y)^(47/48:ℝ))) by
          funext Y; simp [Work.BMF.mrCore.Pc, Work.BMF.mrCore.logPc]]
    exact h
  have h2 : ∀ᶠ Y in Filter.atTop, (2 : ℝ) ≤ Work.BMF.mrCore.Pc Y :=
    hPc_inf.eventually_ge_atTop 2
  have h3e : ∀ᶠ Y in Filter.atTop,
      Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)
        - (1 / 2) * Real.log Y) ≤ 1 / 16 ^ 4 :=
    eventually_le_of_tendsto_zero
      (tendsto_exp_rpow_log_sub (Work.BMF.mrCore.Ac B) (1/2) (47/48)
        (by norm_num) (by norm_num)) (by norm_num)
  have h3 : ∀ᶠ Y in Filter.atTop,
      Real.exp (Work.BMF.mrCore.logQc B Y) ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4 := by
    filter_upwards [h3e, Filter.eventually_gt_atTop (0 : ℝ)] with Y hle hY
    rw [show Work.BMF.mrCore.logQc B Y = Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ) by
      simp [Work.BMF.mrCore.logQc, Work.BMF.mrCore.logPc]]
    have hkey : Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ))
        = Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ) - (1/2) * Real.log Y)
          * Real.exp ((1/2) * Real.log Y) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : Real.exp ((1 / 2) * Real.log Y) = Y ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hY]; congr 1; ring
    rw [hkey, hexp]
    calc Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ) - (1/2) * Real.log Y)
            * Y ^ (1 / 2 : ℝ)
        ≤ (1 / 16 ^ 4) * Y ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt (Real.rpow_pos_of_pos hY _))
      _ = Y ^ (1 / 2 : ℝ) / 16 ^ 4 := by ring
  have h4e : ∀ᶠ Y in Filter.atTop,
      Real.exp (2 * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)
        - 1 * Real.log Y) ≤ 1 :=
    eventually_le_of_tendsto_zero
      (tendsto_exp_rpow_log_sub (2 * Work.BMF.mrCore.Ac B) 1 (47/48)
        (by norm_num) (by norm_num)) (by norm_num)
  have h4 : ∀ᶠ Y in Filter.atTop, (Work.BMF.mrCore.Qc B Y) ^ 2 ≤ Y := by
    filter_upwards [h4e, Filter.eventually_gt_atTop (0 : ℝ)] with Y hle hY
    have hQc : Work.BMF.mrCore.Qc B Y
        = Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by
      simp [Work.BMF.mrCore.Qc, Work.BMF.mrCore.logQc, Work.BMF.mrCore.logPc]
    have hsq : (Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ))) ^ 2
        = Real.exp (2 * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hle' : 2 * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)
        - 1 * Real.log Y ≤ 0 := by
      rw [← Real.exp_le_exp, Real.exp_zero]; exact hle
    rw [hQc, hsq]
    calc Real.exp (2 * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ))
        ≤ Real.exp (Real.log Y) := by rw [Real.exp_le_exp]; linarith
      _ = Y := Real.exp_log hY
  have hPc_inv : Filter.Tendsto (fun Y : ℝ => 1 / Work.BMF.mrCore.Pc Y) Filter.atTop (nhds 0) := by
    have h := hPc_inf.inv_tendsto_atTop
    have heq : Work.BMF.mrCore.Pc⁻¹ = (fun Y : ℝ => 1 / Work.BMF.mrCore.Pc Y) := by
      funext Y; simp [one_div]
    rwa [heq] at h
  have h5R : 0 < ε / (96 * Cbs * (3 + 4 * C₀ / ε)) := by positivity
  have h5 : ∀ᶠ Y in Filter.atTop,
      1 / Work.BMF.mrCore.Pc Y ≤ ε / (96 * Cbs * (3 + 4 * C₀ / ε)) :=
    eventually_le_of_tendsto_zero hPc_inv h5R
  have h6 : ∀ᶠ Y in Filter.atTop, max 1 (Real.log (4 * C₀ / ε)) ≤ Real.log Y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have h7 : ∀ᶠ Y in Filter.atTop,
      2 * Cbs * Cm * (K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2 *
          (Real.log Y) ^ (-(198 - 47 / 24 : ℝ))
        + 2 * K * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (-(198 - 47 / 48 : ℝ))) ≤ ε / 32 := by
    have hc1 : 0 < (198 - 47 / 24 : ℝ) := by norm_num
    have hc2 : 0 < (198 - 47 / 48 : ℝ) := by norm_num
    have hlim : Filter.Tendsto (fun Y : ℝ => 2 * Cbs * Cm *
        (K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2 * (Real.log Y) ^ (-(198 - 47 / 24 : ℝ))
          + 2 * K * Work.BMF.mrCore.Ac B * (Real.log Y) ^ (-(198 - 47 / 48 : ℝ))))
        Filter.atTop (nhds 0) := by
      have t1 := (tendsto_log_rpow_neg_tendsto_zero (198 - 47/24) hc1).const_mul
        (K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 2)
      have t2 := (tendsto_log_rpow_neg_tendsto_zero (198 - 47/48) hc2).const_mul
        (2 * K * Work.BMF.mrCore.Ac B)
      have h := (t1.add t2).const_mul (2 * Cbs * Cm)
      simpa using h
    exact eventually_le_of_tendsto_zero hlim (by linarith)
  have h8 : ∀ᶠ Y in Filter.atTop,
      2 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3 * (1 + B ^ 2) ^ 2 *
          Real.exp (-(B ^ 2 / 4)) * (Real.log Y) ^ (-(47 / 48 : ℝ)) ≤ ε / 64 := by
    have hc : 0 < (47 / 48 : ℝ) := by norm_num
    have hlim : Filter.Tendsto (fun Y : ℝ => 2 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3
        * (1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) * (Real.log Y) ^ (-(47 / 48 : ℝ)))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_log_rpow_neg_tendsto_zero (47/48) hc).const_mul
        (2 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3 * (1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)))
      simpa using h
    exact eventually_le_of_tendsto_zero hlim (by linarith)
  have h9 : ∀ᶠ Y in Filter.atTop,
      8 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3 * (Real.log Y) ^ (-(47 / 48 : ℝ)) / W
        ≤ ε / 64 := by
    have hc : 0 < (47 / 48 : ℝ) := by norm_num
    have hlim : Filter.Tendsto (fun Y : ℝ => 8 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3
        * (Real.log Y) ^ (-(47 / 48 : ℝ)) / W) Filter.atTop (nhds 0) := by
      have h := ((tendsto_log_rpow_neg_tendsto_zero (47/48) hc).const_mul
        (8 * Cbs * Cm * K * (Work.BMF.mrCore.Ac B) ^ 3)).div_const W
      simpa using h
    exact eventually_le_of_tendsto_zero hlim (by linarith)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9] with Y h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Work.BMF.mr_core
