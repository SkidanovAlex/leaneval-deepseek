import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Green.eventually_not_mem_mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Critical

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-!
# `Φ c / c → 1` for the product-formula parameter Böttcher coordinate

`Work.Bottcher.Phi c = φ_c(c)` is the value at the critical value `c` of the
Böttcher coordinate given by the product formula
`φ_c(z) = z · exp (Σ_n 4^{-(n+1)} log (p_c^n z / (p_c^n z)^4))`, `p_c = T_c ∘ T_c`,
with the junk value `0` on the mandelbar `M*`.

Since the mandelbar is compact (`Work.Escape.isCompact_mandelbar`), the junk value
is irrelevant for the cocompact filter: eventually `c ∉ M*`, and then
`Phi c = φ_c c = c · exp (bottcherSeries c c)`.  So it suffices to show

`bottcherSeries c c = Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] c)) → 0`

as `c → ∞`.  This is completely elementary.  Writing `D = ‖c‖` and using
`‖c‖ ≤ ‖(pMap c)^[n] c‖` for every `n` (proved below from the simple growth
`‖w‖ ≤ ‖pMap c w‖` valid as soon as `‖c‖ ≤ ‖w‖` and `‖c‖ ≥ 5`), each factor
`normFactor c w = 1 + (2 c̄ w² + c̄² + c)/w⁴` is within `1/2` of `1`, and

`‖log (normFactor c w)‖ ≤ (3/2)(2/‖w‖ + 1/‖w‖² + 1/‖w‖³)`

with a right-hand side bounded by `2/D + 1/D² + 1/D³ → 0`.  Summing with the
weights `4^{-(n+1)}` (whose total mass is `1/3`) gives
`‖bottcherSeries c c‖ ≤ 2/‖c‖ + 1/‖c‖² + 1/‖c‖³ → 0`.  Continuity of `exp`
finishes the proof.
-/

/-! ## Elementary estimates for the normalised factor -/

/-- Numerator estimate for `normFactor c w - 1`. -/
private lemma normFactor_pert_le (c w : ℂ) :
    ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by
  have h1 := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2) c
  have h2 := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2) ((starRingEnd ℂ c) ^ 2)
  have hrw : ‖2 * (starRingEnd ℂ c) * w ^ 2‖ + ‖(starRingEnd ℂ c) ^ 2‖
      = 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 := by
    simp only [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_ofNat]
  linarith

/-- **Refined asymptotic of the Böttcher factor.**  If `‖c‖ ≤ ‖w‖` then
`normFactor c w = 1 + O(1/‖w‖)`, with the explicit constant
`2/‖w‖ + 1/‖w‖² + 1/‖w‖³`. -/
private lemma normFactor_sub_one_bound (c w : ℂ) (h : ‖c‖ ≤ ‖w‖) (hw : 1 ≤ ‖w‖) :
    ‖Work.Bottcher.normFactor c w - 1‖ ≤ 2 / ‖w‖ + 1 / ‖w‖ ^ 2 + 1 / ‖w‖ ^ 3 := by
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
  have hwne : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwpos; exact lt_irrefl _ hwpos
  have hrew : Work.Bottcher.normFactor c w - 1
      = (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c) / w ^ 4 := by
    simp only [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply]
    field_simp
    ring
  rw [hrew, norm_div, norm_pow]
  refine le_trans (div_le_div_of_nonneg_right (normFactor_pert_le c w) (by positivity)) ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖ ^ 4)]
  have hkey : (2 / ‖w‖ + 1 / ‖w‖ ^ 2 + 1 / ‖w‖ ^ 3) * ‖w‖ ^ 4
      = 2 * ‖w‖ ^ 3 + ‖w‖ ^ 2 + ‖w‖ := by
    have hw0 : (‖w‖ : ℝ) ≠ 0 := ne_of_gt hwpos
    field_simp
  rw [hkey]
  have h1 : 2 * ‖c‖ * ‖w‖ ^ 2 ≤ 2 * ‖w‖ ^ 3 := by
    have hsq : ‖c‖ * ‖w‖ ^ 2 ≤ ‖w‖ * ‖w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  have h2 : ‖c‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [h, norm_nonneg c]
  linarith

/-- Logarithmic form of the previous estimate, using
`‖log (1+u)‖ ≤ (3/2)‖u‖` for `‖u‖ ≤ 1/2`. -/
private lemma log_normFactor_bound (c w : ℂ) (h : ‖c‖ ≤ ‖w‖) (hw : 1 ≤ ‖w‖)
    (hB : 2 / ‖w‖ + 1 / ‖w‖ ^ 2 + 1 / ‖w‖ ^ 3 ≤ 1 / 2) :
    ‖Complex.log (Work.Bottcher.normFactor c w)‖
      ≤ (3 / 2) * (2 / ‖w‖ + 1 / ‖w‖ ^ 2 + 1 / ‖w‖ ^ 3) := by
  have h1 := normFactor_sub_one_bound c w h hw
  have hlog := Complex.norm_log_one_add_half_le_self (z := Work.Bottcher.normFactor c w - 1)
    (le_trans h1 hB)
  have hsum : (1 : ℂ) + (Work.Bottcher.normFactor c w - 1) = Work.Bottcher.normFactor c w := by
    ring
  rw [hsum] at hlog
  exact le_trans hlog (mul_le_mul_of_nonneg_left h1 (by norm_num))

/-- The bound function `t ↦ 2/t + 1/t² + 1/t³` is antitone on `(0,∞)`. -/
private lemma bound_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    2 / t + 1 / t ^ 2 + 1 / t ^ 3 ≤ 2 / s + 1 / s ^ 2 + 1 / s ^ 3 := by
  have h1 : 2 / t ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs hst
  have h2 : 1 / t ^ 2 ≤ 1 / s ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hs.le hst 2)
  have h3 : 1 / t ^ 3 ≤ 1 / s ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hs.le hst 3)
  linarith

/-! ## Growth of the `p_c`-orbit of the critical value -/

/-- The holomorphic quartic `p_c` grows once `‖c‖ ≤ ‖w‖` and `‖c‖ ≥ 5`:
`‖w‖ ≤ ‖p_c w‖`. -/
private lemma norm_le_norm_pMap_of_le (c w : ℂ) (hc : 5 ≤ ‖c‖) (h : ‖c‖ ≤ ‖w‖) :
    ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖ := by
  have hexp : Work.Bottcher.pMap c w
      = w ^ 4 + (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c) := by
    simp only [Work.Bottcher.pMap_apply]; ring
  have hnum := normFactor_pert_le c w
  have htri : ‖w ^ 4‖ - ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ ‖w ^ 4 + (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c)‖ := by
    have h' := norm_sub_norm_le (w ^ 4)
      (-(2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c))
    rw [sub_neg_eq_add, norm_neg] at h'
    exact h'
  rw [norm_pow] at htri
  rw [hexp]
  have hmain : ‖w‖ ≤ ‖w‖ ^ 4 - (2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) := by
    have hA : ‖w‖ ^ 4 - 2 * ‖c‖ * ‖w‖ ^ 2 ≥ ‖w‖ ^ 3 * (‖w‖ - 2) := by
      nlinarith [h, sq_nonneg ‖w‖]
    have hB : ‖w‖ ^ 3 * (‖w‖ - 2) ≥ ‖w‖ + ‖c‖ ^ 2 + ‖c‖ := by
      have ht : 5 ≤ ‖w‖ := le_trans hc h
      nlinarith [h, hc, ht, sq_nonneg ‖w‖, sq_nonneg ‖c‖,
        mul_nonneg (sub_nonneg.mpr ht) (pow_nonneg (norm_nonneg w) 3),
        mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg ‖w‖),
        mul_nonneg (sub_nonneg.mpr h) (sq_nonneg ‖w‖)]
    linarith
  linarith

/-- Along the `p_c`-orbit of the critical value, the norms never drop below `‖c‖`
(as soon as `‖c‖ ≥ 5`). -/
private lemma norm_iterate_pMap_self_ge (c : ℂ) (hc : 5 ≤ ‖c‖) (n : ℕ) :
    ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[n] c‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (norm_le_norm_pMap_of_le c _ hc ih)

/-! ## Summability helpers -/

private lemma summable_quarterPow_succ : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
  have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [pow_succ] using h0.mul_right (1 / 4 : ℝ)

private lemma tsum_quarterPow_succ : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1)) = 1 / 3 := by
  have h0 : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ n) ((1 : ℝ) - 1 / 4)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have h1 : HasSum (fun n : ℕ => (1 / 4 : ℝ) * (1 / 4) ^ n)
      ((1 / 4 : ℝ) * ((1 : ℝ) - 1 / 4)⁻¹) := h0.mul_left (1 / 4 : ℝ)
  have h2 : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1)) = (1 / 4 : ℝ) * ((1 : ℝ) - 1 / 4)⁻¹ := by
    rw [← h1.tsum_eq]
    exact tsum_congr (fun n => by rw [pow_succ'])
  rw [h2]; norm_num

/-! ## The bound on the Böttcher series of the critical value -/

/-- **The Böttcher series of the critical value is `O(1/‖c‖)`.**  For `‖c‖ ≥ 5`,
`‖bottcherSeries c c‖ ≤ 2/‖c‖ + 1/‖c‖² + 1/‖c‖³`. -/
theorem norm_bottcherSeries_self_le (c : ℂ) (hc : 5 ≤ ‖c‖) :
    ‖Work.Bottcher.bottcherSeries c c‖ ≤ 2 / ‖c‖ + 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3 := by
  have hcpos : 0 < ‖c‖ := by linarith
  set B : ℝ := 2 / ‖c‖ + 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3 with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hBhalf : B ≤ 1 / 2 := by
    rw [hBdef]
    have hEq : 2 / ‖c‖ + 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3
        = (2 * ‖c‖ ^ 2 + ‖c‖ + 1) / ‖c‖ ^ 3 := by
      have hc0 : (‖c‖ : ℝ) ≠ 0 := ne_of_gt hcpos
      field_simp
    rw [hEq, div_le_iff₀ (by positivity : (0 : ℝ) < ‖c‖ ^ 3)]
    nlinarith [hc, sq_nonneg (‖c‖), sq_nonneg (‖c‖ - 5)]
  have hterm : ∀ n : ℕ, ‖Work.Bottcher.bottcherTerm c n c‖
      ≤ (1 / 4 : ℝ) ^ (n + 1) * ((3 / 2) * B) := by
    intro n
    have hiter : ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[n] c‖ := norm_iterate_pMap_self_ge c hc n
    have hw1 : 1 ≤ ‖(Work.Bottcher.pMap c)^[n] c‖ := le_trans (by linarith) hiter
    have hBw : 2 / ‖(Work.Bottcher.pMap c)^[n] c‖
        + 1 / (‖(Work.Bottcher.pMap c)^[n] c‖) ^ 2
        + 1 / (‖(Work.Bottcher.pMap c)^[n] c‖) ^ 3 ≤ 1 / 2 :=
      le_trans (bound_antitone hcpos hiter) hBhalf
    have hlog := log_normFactor_bound c ((Work.Bottcher.pMap c)^[n] c) hiter hw1 hBw
    have hlogB : ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))‖
        ≤ (3 / 2) * B := by
      refine le_trans hlog ?_
      have hbound : 2 / ‖(Work.Bottcher.pMap c)^[n] c‖
          + 1 / (‖(Work.Bottcher.pMap c)^[n] c‖) ^ 2
          + 1 / (‖(Work.Bottcher.pMap c)^[n] c‖) ^ 3 ≤ B := by
        rw [hBdef]
        exact bound_antitone hcpos hiter
      exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    have hb : ‖Work.Bottcher.bottcherTerm c n c‖
        = (1 / 4 : ℝ) ^ (n + 1)
          * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))‖ := by
      rw [Work.Bottcher.bottcherTerm, norm_mul]
      congr 1
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    rw [hb]
    exact mul_le_mul_of_nonneg_left hlogB (by positivity)
  have hgsum : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * ((3 / 2) * B)) :=
    summable_quarterPow_succ.mul_right _
  have hf_norm : Summable (fun n : ℕ => ‖Work.Bottcher.bottcherTerm c n c‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgsum
  calc ‖Work.Bottcher.bottcherSeries c c‖
    _ ≤ ∑' n : ℕ, ‖Work.Bottcher.bottcherTerm c n c‖ := by
        rw [Work.Bottcher.bottcherSeries]
        exact norm_tsum_le_tsum_norm hf_norm
    _ ≤ ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) * ((3 / 2) * B) :=
        Summable.tsum_le_tsum hterm hf_norm hgsum
    _ = (1 / 3) * ((3 / 2) * B) := by rw [tsum_mul_right, tsum_quarterPow_succ]
    _ = B / 2 := by ring
    _ ≤ B := by linarith [hB0]
    _ = 2 / ‖c‖ + 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3 := by rw [hBdef]

/-! ## The limit at infinity -/

private lemma tendsto_bound_self :
    Tendsto (fun c : ℂ => 2 / ‖c‖ + 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3) (cocompact ℂ) (nhds 0) := by
  have hρ : Tendsto (fun c : ℂ => (‖c‖)⁻¹) (cocompact ℂ) (nhds 0) :=
    tendsto_norm_cocompact_atTop.inv_tendsto_atTop
  have hfun : (fun c : ℂ => 2 / ‖c‖ + 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3)
      = fun c : ℂ => 2 * (‖c‖)⁻¹ + ((‖c‖)⁻¹) ^ 2 + ((‖c‖)⁻¹) ^ 3 := by
    funext c
    rw [div_eq_mul_inv, one_div, one_div, inv_pow, inv_pow]
  rw [hfun]
  have h := ((hρ.const_mul 2).add (hρ.pow 2)).add (hρ.pow 3)
  simpa using h

private lemma tendsto_bottcherSeries_self :
    Tendsto (fun c : ℂ => Work.Bottcher.bottcherSeries c c) (cocompact ℂ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun c => norm_nonneg _)) ?_ tendsto_bound_self
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (5 : ℝ)] with c hc
  exact norm_bottcherSeries_self_le c hc

private lemma tendsto_bottcher_self_div :
    Tendsto (fun c : ℂ => Work.Bottcher.bottcher c c / c) (cocompact ℂ) (nhds 1) := by
  have hexp : Tendsto (fun c : ℂ => Complex.exp (Work.Bottcher.bottcherSeries c c))
      (cocompact ℂ) (nhds 1) := by
    have h := Complex.continuous_exp.continuousAt.tendsto.comp tendsto_bottcherSeries_self
    simpa [Function.comp_def] using h
  refine Tendsto.congr' ?_ hexp
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (5 : ℝ)] with c hc
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hc; norm_num at hc
  simp only [Work.Bottcher.bottcher]
  rw [mul_div_cancel_left₀ _ hc0]

theorem Phi_isBigO_atTop :
    Filter.Tendsto (fun c : ℂ => Work.Bottcher.Phi c / c) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  refine Tendsto.congr' ?_ tendsto_bottcher_self_div
  filter_upwards [Work.Bottcher.Green.eventually_not_mem_mandelbar] with c hc
  rw [Work.Bottcher.Phi_eq_bottcher hc]

end Work.Bottcher.Critical
