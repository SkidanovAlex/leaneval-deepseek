import Mathlib
import Submission.Work.BMF.mr_direct.badDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The arithmetic threshold of the bad-set stage

The bad-set stage of `Work.BMF.MRDirichletL2Direct` uses the scales

* `Q = badQ Y = exp(log Y / log log Y)`,
* `P = badP a Y = Q ^ a`, with `a ∈ (0, 1/2]` a fixed constant,

and it needs to know that, for every `θ ∈ (0,1)`, every resolution `K ≥ 3` and every
tolerance `ε > 0`, the *fixed* prefactor

`c (K+1)^3 (log(Q/P) + 1)^2 · (2 Q^{1/2}/H + 3 P^{-1/2})`

is below `ε` for all large `Y`, uniformly in the window length `H ≥ Y^θ` (and `H ≤ Y`).
This is the purely arithmetic lemma that discharges that bookkeeping; the analysis of the
bad set itself (the Buchstab/Ramaré decomposition, the large values lemmas) is separate.

The mathematical content is that `Q = exp(o(log Y))` is subpolynomial: for large `Y`

* `Q^{1/2}/H ≤ Q^{1/2}/Y^θ = exp(log Y/(2 log log Y) - θ log Y) ≤ Y^{-θ/2}`, and
* `P^{-1/2} = exp(- (a/2) log Y/log log Y) ≤ exp(-(a/4) √(log Y))`,

while `log(Q/P) + 1 = (1-a) log Y/log log Y + 1 ≤ 2 log Y`, so that

`(log(Q/P)+1)^2 · (2 Q^{1/2}/H + 3 P^{-1/2})
   ≤ 12 ((log Y)^2 e^{-θ(log Y)/2} + (log Y)^2 e^{-(a/4)√(log Y)})`,

and the right-hand side tends to `0` as `Y → ∞`.  Since the left-hand side is decreasing in
`H`, the bound at `H = Y^θ` dominates every admissible `H`, and choosing the threshold large
enough finishes the proof.

## Main results

* `tendsto_logsq_majorant` — the majorant tends to `0`;
* `bound_logsq_majorant` — the explicit bound at `H = Y^θ`;
* `expr_monoH` — monotonicity in `H`;
* `badGoodArith` — the arithmetic input of the bad-set stage.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Filter

noncomputable section

/-- The majorant
`12 * D * ((log Y)^2 * exp (-(θ/2) * log Y) + (log Y)^2 * exp (-(a/4) * sqrt (log Y)))`
of the bad-set prefactor tends to `0` as `Y → ∞`, for `θ > 0`, `a > 0` and any constant `D`.
Both summands are of the shape `(polynomial in log Y) · exp(-const · (log Y)^(1/2))`
(substituting `x = log Y`, resp. `x = sqrt (log Y)`). -/
theorem tendsto_logsq_majorant (θ a D : ℝ) (hθ : 0 < θ) (ha : 0 < a) :
    Filter.Tendsto
      (fun Y : ℝ => 12 * D * ((Real.log Y) ^ 2 * Real.exp (-(θ / 2) * Real.log Y)
        + (Real.log Y) ^ 2 * Real.exp (-(a / 4) * Real.sqrt (Real.log Y))))
      Filter.atTop (nhds 0) := by
  have hθ2 : 0 < θ / 2 := by linarith
  have ha4 : 0 < a / 4 := by linarith
  have h1 : Filter.Tendsto (fun Y : ℝ => (Real.log Y) ^ 2 * Real.exp (-(θ / 2) * Real.log Y))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (θ / 2) hθ2).comp
      Real.tendsto_log_atTop
    refine h.congr' ?_
    filter_upwards with Y
    show Real.log Y ^ ((2 : ℕ) : ℝ) * Real.exp (-(θ / 2) * Real.log Y)
      = Real.log Y ^ 2 * Real.exp (-(θ / 2) * Real.log Y)
    rw [Real.rpow_natCast]
  have h2 : Filter.Tendsto
      (fun Y : ℝ => (Real.log Y) ^ 2 * Real.exp (-(a / 4) * Real.sqrt (Real.log Y)))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 (a / 4) ha4).comp
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with Y hY
    have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
    have hsq : (Real.sqrt (Real.log Y)) ^ 4 = (Real.log Y) ^ 2 := by
      calc (Real.sqrt (Real.log Y)) ^ 4 = ((Real.sqrt (Real.log Y)) ^ 2) ^ 2 := by ring
        _ = (Real.log Y) ^ 2 := by rw [Real.sq_sqrt hlog]
    show (Real.sqrt (Real.log Y)) ^ ((4 : ℕ) : ℝ) * Real.exp (-(a / 4) * Real.sqrt (Real.log Y))
      = Real.log Y ^ 2 * Real.exp (-(a / 4) * Real.sqrt (Real.log Y))
    rw [Real.rpow_natCast, hsq]
  have hsum := h1.add h2
  have hfinal := hsum.const_mul (12 * D)
  simpa using hfinal

/-- The explicit bound at the endpoint `H = Y ^ θ`: for `Y ≥ exp (exp (1/θ) + 1)` the
bad-set prefactor is at most the majorant of `tendsto_logsq_majorant`.  All the estimates are
`Real.exp`-monotonicity plus `log s ≤ 2 √s`. -/
theorem bound_logsq_majorant (θ a c K : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ha : 0 < a)
    (ha1 : a ≤ 1) (hc : 0 ≤ c) (hK : -1 ≤ K) {Y : ℝ}
    (hY : Real.exp (Real.exp (1 / θ) + 1) ≤ Y) :
    c * (K + 1) ^ 3 * (Real.log (badQ Y / badP a Y) + 1) ^ 2 *
        (2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ + 3 * (badP a Y) ^ (-(1 / 2 : ℝ)))
      ≤ 12 * (c * (K + 1) ^ 3) *
        ((Real.log Y) ^ 2 * Real.exp (-(θ / 2) * Real.log Y)
          + (Real.log Y) ^ 2 * Real.exp (-(a / 4) * Real.sqrt (Real.log Y))) := by
  set s := Real.log Y with hs
  set v := Real.log s with hv
  set D := c * (K + 1) ^ 3 with hD
  have hDnn : 0 ≤ D := by rw [hD]; exact mul_nonneg hc (pow_nonneg (by linarith) 3)
  have hXpos : 0 < Real.exp (Real.exp (1 / θ) + 1) := Real.exp_pos _
  have hYpos : 0 < Y := lt_of_lt_of_le hXpos hY
  have hs_ge : Real.exp (1 / θ) + 1 ≤ s := by
    have h := Real.log_le_log hXpos hY
    rw [Real.log_exp] at h
    rw [← hs] at h
    exact h
  have hexp_le : Real.exp (1 / θ) ≤ s := by linarith
  have hs1 : 1 ≤ s := by linarith [Real.exp_pos (1 / θ)]
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs1
  have hv_ge : 1 / θ ≤ v := by
    have h := Real.log_le_log (Real.exp_pos (1 / θ)) hexp_le
    rw [Real.log_exp] at h
    rw [← hv] at h
    exact h
  have hv1 : 1 ≤ v := by
    have h1θ : 1 ≤ 1 / θ := by
      rw [one_le_div hθ₀]
      linarith
    linarith
  have hvpos : 0 < v := lt_of_lt_of_le one_pos hv1
  have hbadQ : badQ Y = Real.exp (s / v) := by
    show Real.exp (Real.log Y / Real.log (Real.log Y)) = Real.exp (s / v)
    rw [← hs, ← hv]
  have hbadP : badP a Y = Real.exp (a * (s / v)) := by
    rw [badP, hbadQ, Real.rpow_def_of_pos (Real.exp_pos (s / v)) a, Real.log_exp]
    congr 1
    ring
  have hbqpos : 0 < badQ Y := by rw [hbadQ]; exact Real.exp_pos _
  have hbppos : 0 < badP a Y := by rw [hbadP]; exact Real.exp_pos _
  have hlog : Real.log (badQ Y / badP a Y) = (1 - a) * (s / v) := by
    rw [Real.log_div (ne_of_gt hbqpos) (ne_of_gt hbppos), hbadQ, hbadP, Real.log_exp, Real.log_exp]
    ring
  have hsqrt : (badQ Y) ^ ((1 : ℝ) / 2) = Real.exp (s / (2 * v)) := by
    rw [hbadQ, Real.rpow_def_of_pos (Real.exp_pos (s / v)) (1 / 2), Real.log_exp]
    congr 1
    ring
  have hinv : (badP a Y) ^ (-(1 / 2 : ℝ)) = Real.exp (-(a * s / (2 * v))) := by
    rw [hbadP, Real.rpow_def_of_pos (Real.exp_pos (a * (s / v))) (-(1 / 2)), Real.log_exp]
    congr 1
    ring
  have hYθ : Y ^ θ = Real.exp (θ * s) := by
    rw [Real.rpow_def_of_pos hYpos θ, ← hs]
    congr 1
    ring
  have hR : ((1 - a) * (s / v) + 1) ^ 2 ≤ 4 * s ^ 2 := by
    have h1a : 0 ≤ 1 - a := by linarith
    have hw0 : 0 ≤ s / v := div_nonneg hspos.le hvpos.le
    have hx0 : 0 ≤ (1 - a) * (s / v) + 1 := by
      have := mul_nonneg h1a hw0
      linarith
    have hx_le : (1 - a) * (s / v) + 1 ≤ s + 1 := by
      have h2 : (1 - a) * (s / v) ≤ 1 * (s / v) :=
        mul_le_mul_of_nonneg_right (by linarith : 1 - a ≤ 1) hw0
      have h3 : s / v ≤ s := by
        rw [div_le_iff₀ hvpos]
        nlinarith [hs1, hv1, hspos]
      linarith
    have hss : s + 1 ≤ 2 * s := by linarith
    calc ((1 - a) * (s / v) + 1) ^ 2 ≤ (s + 1) ^ 2 := pow_le_pow_left₀ hx0 hx_le 2
      _ ≤ (2 * s) ^ 2 := pow_le_pow_left₀ (by linarith) hss 2
      _ = 4 * s ^ 2 := by ring
  have hT1 : 2 * Real.exp (s / (2 * v)) / Real.exp (θ * s) ≤ 2 * Real.exp (-(θ / 2) * s) := by
    have hA : 2 * Real.exp (s / (2 * v)) / Real.exp (θ * s)
        = 2 * Real.exp (s / (2 * v) - θ * s) := by
      rw [show 2 * Real.exp (s / (2 * v)) / Real.exp (θ * s)
          = 2 * (Real.exp (s / (2 * v)) / Real.exp (θ * s)) by ring, ← Real.exp_sub]
    rw [hA]
    have h1 : 1 ≤ θ * v := by
      have h := mul_le_mul_of_nonneg_left hv_ge hθ₀.le
      rwa [mul_one_div_cancel hθ₀.ne'] at h
    have h2 : s / (2 * v) ≤ θ * s / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * v)]
      nlinarith [h1, hspos]
    have hle : s / (2 * v) - θ * s ≤ -(θ / 2) * s := by linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by norm_num)
  have hv_le : v ≤ 2 * Real.sqrt s := by
    have h1 : Real.log (Real.sqrt s) = v / 2 := by
      rw [Real.log_sqrt hspos.le, ← hv]
    have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hspos)
    linarith [Real.sqrt_nonneg s]
  have hT2 : 3 * Real.exp (-(a * s / (2 * v))) ≤ 3 * Real.exp (-(a / 4) * Real.sqrt s) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
    apply Real.exp_le_exp.mpr
    have h1 : Real.sqrt s * v ≤ 2 * s := by
      calc Real.sqrt s * v ≤ Real.sqrt s * (2 * Real.sqrt s) :=
            mul_le_mul_of_nonneg_left hv_le (Real.sqrt_nonneg s)
        _ = 2 * (Real.sqrt s) ^ 2 := by ring
        _ = 2 * s := by rw [Real.sq_sqrt hspos.le]
    have hle : a / 4 * Real.sqrt s ≤ a * s / (2 * v) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * v)]
      have h3 : a / 2 * (Real.sqrt s * v) ≤ a / 2 * (2 * s) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      nlinarith [h3]
    linarith
  rw [hlog, hsqrt, hinv, hYθ]
  have hsum : 2 * Real.exp (s / (2 * v)) / Real.exp (θ * s) + 3 * Real.exp (-(a * s / (2 * v)))
      ≤ 2 * Real.exp (-(θ / 2) * s) + 3 * Real.exp (-(a / 4) * Real.sqrt s) :=
    add_le_add hT1 hT2
  have hstep1 : D * ((1 - a) * (s / v) + 1) ^ 2 *
        (2 * Real.exp (s / (2 * v)) / Real.exp (θ * s) + 3 * Real.exp (-(a * s / (2 * v))))
      ≤ D * (4 * s ^ 2) *
        (2 * Real.exp (-(θ / 2) * s) + 3 * Real.exp (-(a / 4) * Real.sqrt s)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hR hDnn) hsum (by positivity) (by positivity)
  have hstep2 : D * (4 * s ^ 2) *
        (2 * Real.exp (-(θ / 2) * s) + 3 * Real.exp (-(a / 4) * Real.sqrt s))
      ≤ 12 * D * (s ^ 2 * Real.exp (-(θ / 2) * s)
          + s ^ 2 * Real.exp (-(a / 4) * Real.sqrt s)) := by
    have h3 : D * (4 * s ^ 2) *
          (2 * Real.exp (-(θ / 2) * s) + 3 * Real.exp (-(a / 4) * Real.sqrt s))
        ≤ D * (4 * s ^ 2) *
          (3 * Real.exp (-(θ / 2) * s) + 3 * Real.exp (-(a / 4) * Real.sqrt s)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [(Real.exp_pos (-(θ / 2) * s)).le]
    have h4 : D * (4 * s ^ 2) *
          (3 * Real.exp (-(θ / 2) * s) + 3 * Real.exp (-(a / 4) * Real.sqrt s))
        = 12 * D * (s ^ 2 * Real.exp (-(θ / 2) * s)
            + s ^ 2 * Real.exp (-(a / 4) * Real.sqrt s)) := by
      ring
    rw [h4] at h3
    exact h3
  linarith [hstep1, hstep2]

/-- Monotonicity of the bad-set prefactor in the window length `H`: the first summand
`2 Q^{1/2}/H` decreases as `H` grows, so the endpoint `H = Y ^ θ` is the worst case. -/
theorem expr_monoH (θ a D Y H : ℝ) (hθ : 0 < θ) (hD : 0 ≤ D) (hY : 1 ≤ Y) (hH : Y ^ θ ≤ H) :
    D * (Real.log (badQ Y / badP a Y) + 1) ^ 2 *
        (2 * (badQ Y) ^ ((1 : ℝ) / 2) / H + 3 * (badP a Y) ^ (-(1 / 2 : ℝ)))
      ≤ D * (Real.log (badQ Y / badP a Y) + 1) ^ 2 *
        (2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ + 3 * (badP a Y) ^ (-(1 / 2 : ℝ))) := by
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY
  have hYθpos : 0 < Y ^ θ := Real.rpow_pos_of_pos hYpos θ
  have hbqpos : 0 < badQ Y := by rw [badQ]; exact Real.exp_pos _
  have hbq : 0 ≤ (badQ Y) ^ ((1 : ℝ) / 2) := (Real.rpow_pos_of_pos hbqpos _).le
  have hT1 : 2 * (badQ Y) ^ ((1 : ℝ) / 2) / H ≤ 2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ := by
    have h1 : H⁻¹ ≤ (Y ^ θ)⁻¹ := inv_anti₀ hYθpos hH
    calc 2 * (badQ Y) ^ ((1 : ℝ) / 2) / H = (2 * (badQ Y) ^ ((1 : ℝ) / 2)) * H⁻¹ := by ring
      _ ≤ (2 * (badQ Y) ^ ((1 : ℝ) / 2)) * (Y ^ θ)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hbq)
      _ = 2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ := by ring
  have hsum : 2 * (badQ Y) ^ ((1 : ℝ) / 2) / H + 3 * (badP a Y) ^ (-(1 / 2 : ℝ))
      ≤ 2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ + 3 * (badP a Y) ^ (-(1 / 2 : ℝ)) :=
    add_le_add hT1 le_rfl
  have hDR : 0 ≤ D * (Real.log (badQ Y / badP a Y) + 1) ^ 2 := mul_nonneg hD (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left hsum hDR

theorem badGoodArith (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (a ε c K : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hε : 0 < ε) (hc : 0 < c) (hK : 3 ≤ K) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ Y H : ℝ, X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y →
      c * (K + 1) ^ 3 * (Real.log (Work.BMF.mr_direct.badQ Y / Work.BMF.mr_direct.badP a Y) + 1) ^ 2 *
        (2 * (Work.BMF.mr_direct.badQ Y) ^ ((1 : ℝ) / 2) / H +
          3 * (Work.BMF.mr_direct.badP a Y) ^ (-(1 / 2 : ℝ))) ≤ ε := by
  have hDnn : 0 ≤ c * (K + 1) ^ 3 := mul_nonneg hc.le (pow_nonneg (by linarith) 3)
  -- The endpoint value `H = Y^θ` is eventually at most the majorant ...
  have hbnd : ∀ᶠ Y in Filter.atTop,
      c * (K + 1) ^ 3 * (Real.log (badQ Y / badP a Y) + 1) ^ 2 *
        (2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ + 3 * (badP a Y) ^ (-(1 / 2 : ℝ)))
      ≤ 12 * (c * (K + 1) ^ 3) *
        ((Real.log Y) ^ 2 * Real.exp (-(θ / 2) * Real.log Y)
          + (Real.log Y) ^ 2 * Real.exp (-(a / 4) * Real.sqrt (Real.log Y))) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp (1 / θ) + 1))] with Y hY
    exact bound_logsq_majorant θ a c K hθ₀ hθ₁ ha (by linarith) hc.le (by linarith) hY
  -- ... and the majorant tends to `0`.
  have hsmallG : ∀ᶠ Y in Filter.atTop,
      12 * (c * (K + 1) ^ 3) * ((Real.log Y) ^ 2 * Real.exp (-(θ / 2) * Real.log Y)
          + (Real.log Y) ^ 2 * Real.exp (-(a / 4) * Real.sqrt (Real.log Y))) < ε :=
    (tendsto_order.1 (tendsto_logsq_majorant θ a (c * (K + 1) ^ 3) hθ₀ ha)).2 ε hε
  have hsmall : ∀ᶠ Y in Filter.atTop,
      c * (K + 1) ^ 3 * (Real.log (badQ Y / badP a Y) + 1) ^ 2 *
        (2 * (badQ Y) ^ ((1 : ℝ) / 2) / Y ^ θ + 3 * (badP a Y) ^ (-(1 / 2 : ℝ))) < ε :=
    (hbnd.and hsmallG).mono (fun Y h => lt_of_le_of_lt h.1 h.2)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max 1 X₁, le_max_left _ _, ?_⟩
  intro Y H hY hH1 hH2
  have hYX₁ : X₁ ≤ Y := le_trans (le_max_right 1 X₁) hY
  have hY1 : 1 ≤ Y := le_trans (le_max_left 1 X₁) hY
  have key := hX₁ Y hYX₁
  have hmono := expr_monoH θ a (c * (K + 1) ^ 3) Y H hθ₀ hDnn hY1 hH1
  exact le_of_lt (lt_of_le_of_lt hmono key)

end

end Work.BMF.mr_direct
