import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Series.summable_bottcherTerm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Helper lemmas for `farInverse_sub_le_of_weak` -/

/-- Third-order Taylor remainder of `log` at `1`: for `‖u‖ ≤ 1/2`,
`‖log (1 + u) - u + u^2/2‖ ≤ ‖u‖^3`. -/
theorem norm_log_one_add_sub_self_add_sq_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - u + u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 := by
  have hlt : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have h1 := Complex.norm_log_sub_logTaylor_le 2 hlt
  have h2 : Complex.logTaylor (2 + 1) u = u - u ^ 2 / 2 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    ring
  have h4 : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have key : ‖Complex.log (1 + u) - Complex.logTaylor (2 + 1) u‖ ≤ ‖u‖ ^ 3 := by
    refine h1.trans ?_
    have h5 : ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (↑(2 : ℕ) + 1) ≤ ‖u‖ ^ 3 := by
      have h6 : ‖u‖ ^ (2 + 1) = ‖u‖ ^ 3 := by norm_num
      rw [h6, show (↑(2 : ℕ) + 1 : ℝ) = 3 by norm_num]
      calc ‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / 3 ≤ ‖u‖ ^ 3 * 2 / 3 := by gcongr
        _ ≤ ‖u‖ ^ 3 := by nlinarith [show (0:ℝ) ≤ ‖u‖ ^ 3 by positivity]
    exact h5
  have heq : Complex.log (1 + u) - u + u ^ 2 / 2
      = Complex.log (1 + u) - Complex.logTaylor (2 + 1) u := by rw [h2]; ring
  rw [heq]
  exact key

/-- The correction term `nfG c v = 2 c̄/v^2 + (c̄²+c)/v^4` is bounded by
`(2‖c‖‖v‖² + ‖c‖²+‖c‖)/‖v‖⁴`. -/
theorem norm_nfG_le_div (c v : ℂ) :
    ‖Work.Bottcher.Core.nfG c v‖
      ≤ (2 * ‖c‖ * ‖v‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) / ‖v‖ ^ 4 := by
  rw [Work.Bottcher.Core.nfG, norm_div, norm_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : ‖2 * conj c * v ^ 2‖ = 2 * ‖c‖ * ‖v‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_pow]; norm_num
  have h2 : ‖(conj c) ^ 2‖ = ‖c‖ ^ 2 := by rw [norm_pow, Complex.norm_conj]
  calc ‖2 * conj c * v ^ 2 + (conj c) ^ 2 + c‖
      ≤ ‖2 * conj c * v ^ 2 + (conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (‖2 * conj c * v ^ 2‖ + ‖(conj c) ^ 2‖) + ‖c‖ := by
        linarith [norm_add_le (2 * conj c * v ^ 2) ((conj c) ^ 2)]
    _ = 2 * ‖c‖ * ‖v‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by rw [h1, h2]

/-- `x ≤ x^4/2` for `x ≥ 3/2`. -/
theorem le_pow_four_div_two_of_three_halves {x : ℝ} (hx : 3 / 2 ≤ x) : x ≤ x ^ 4 / 2 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h3 : (3 / 2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  nlinarith [h3, h0, mul_nonneg (by linarith : (0:ℝ) ≤ x / 2) (by linarith : (0:ℝ) ≤ x^3 - 2)]

/-- In the region `‖z‖ ≥ (3/2)(1+‖c‖)` the quartic `pMap c` at least raises the
fourth power: `‖z‖⁴/2 ≤ ‖pMap c z‖`. -/
theorem pow_four_div_two_le_norm_pMap (c z : ℂ) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    ‖z‖ ^ 4 / 2 ≤ ‖Work.Bottcher.pMap c z‖ := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : (‖z‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ ≤ ‖Work.Bottcher.pMap c z‖ :=
    Work.Bottcher.Core.norm_pMap_ge c z (by
      refine max_le ?_ ?_
      · linarith
      · linarith)
  have h2 : ‖z‖ ^ 4 / 2 ≤ (‖z‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ := by
    nlinarith [sq_nonneg (‖z‖ ^ 2 - 2 * ‖c‖), sq_nonneg (‖z‖ - 3 / 2 * (1 + ‖c‖)),
      sq_nonneg ‖c‖, pow_nonneg hb 3, pow_nonneg hb 4]
  linarith

/-- In the region `‖z‖ ≥ (3/2)(1+‖c‖)` the `pMap c`-orbit stays in the region and is
at least `‖z‖⁴/2` from the first step onwards. -/
theorem pow_four_div_two_le_norm_pMap_iterate (c z : ℂ) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    ∀ n : ℕ, 1 ≤ n → ‖z‖ ^ 4 / 2 ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
  have hreg : ∀ n : ℕ, 3 / 2 * (1 + ‖c‖) ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h15 : (3 / 2 : ℝ) ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
        have : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
        nlinarith
      exact le_trans ih (le_trans (le_pow_four_div_two_of_three_halves h15)
        (pow_four_div_two_le_norm_pMap c _ ih))
  have key : ∀ m : ℕ, ‖z‖ ^ 4 / 2 ≤ ‖(Work.Bottcher.pMap c)^[m + 1] z‖ := by
    intro m
    induction m with
    | zero => simpa using pow_four_div_two_le_norm_pMap c z hz
    | succ m ih =>
      rw [show (m + 1) + 1 = m + 1 + 1 from rfl, Function.iterate_succ_apply']
      have h15 : (3 / 2 : ℝ) ≤ ‖(Work.Bottcher.pMap c)^[m + 1] z‖ := by
        have : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
        linarith [hreg (m + 1)]
      exact le_trans (le_trans ih (le_pow_four_div_two_of_three_halves h15))
        (pow_four_div_two_le_norm_pMap c _ (hreg (m + 1)))
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m

/-- In the region `‖z‖ ≥ (3/2)(1+‖c‖)` the `Tantibar c`-orbit escapes to infinity. -/
theorem tendsto_norm_Tantibar_iterate_of_ge (c z : ℂ) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    Filter.Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) Filter.atTop Filter.atTop := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hTz : Work.Bottcher.escapeRadius c ≤ ‖Tantibar c z‖ := by
    have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := Work.Bottcher.Core.norm_Tantibar_ge c z
    have h2 : Work.Bottcher.escapeRadius c ≤ ‖z‖ ^ 2 - ‖c‖ := by
      rw [Work.Bottcher.escapeRadius]
      nlinarith [sq_nonneg (‖z‖ - 3 / 2 * (1 + ‖c‖)), sq_nonneg ‖c‖]
    linarith
  have hgrow : ∀ m : ℕ, 2 ^ m * ‖Tantibar c z‖ ≤ ‖(Tantibar c)^[m + 1] z‖ := by
    intro m
    have h := (Work.Bottcher.Core.escapeRadius_le_norm_Tantibar_iterate c hTz m).2
    simpa [Function.iterate_succ_apply] using h
  have h2 : Filter.Tendsto (fun m : ℕ => 2 ^ m * ‖Tantibar c z‖) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      (lt_of_lt_of_le (by norm_num) (le_trans (Work.Bottcher.Core.two_le_escapeRadius c) hTz))
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact Filter.tendsto_atTop_mono' Filter.atTop (Filter.Eventually.of_forall hgrow) h2

/-- Summability of the Böttcher series in the region `‖z‖ ≥ (3/2)(1+‖c‖)`. -/
theorem summable_bottcherTerm_far (c z : ℂ) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    Summable (fun n : ℕ => Work.Bottcher.bottcherTerm c n z) :=
  Work.Bottcher.Series.summable_bottcherTerm c z (tendsto_norm_Tantibar_iterate_of_ge c z hz)

/-- Arithmetic inequality behind the fourth-order term of the Böttcher series on the
region `R ≥ (3/2)(1+b)`, `0 ≤ b ≤ 2`:
`(2bR² + b² + b)³ ≤ (12/5) b R⁸`. -/
theorem pow_three_le_twelve_fifths (b R : ℝ) (hb : 0 ≤ b) (hb2 : b ≤ 2)
    (hR : 3 / 2 * (1 + b) ≤ R) :
    (2 * b * R ^ 2 + b ^ 2 + b) ^ 3 ≤ (12 / 5) * b * R ^ 8 := by
  have hRpos : 0 < R := by linarith
  have hR2 : (9 / 4) * (1 + b) ^ 2 ≤ R ^ 2 := by nlinarith
  have hpoly : 40 * b ^ 2 * (9 * (1 + b) + 2) ^ 3 ≤ 19683 * (1 + b) ^ 5 := by
    have h1 : 0 ≤ 1 + b - 1 := by linarith
    have h2 : 0 ≤ 3 - (1 + b) := by linarith
    nlinarith [sq_nonneg (1 + b - 1), sq_nonneg (1 + b - 3), mul_nonneg h1 h2,
      mul_nonneg (mul_nonneg h1 h1) h2, mul_nonneg h1 (mul_nonneg h2 h2),
      sq_nonneg ((1 + b) ^ 2 - 4), sq_nonneg (1 + b - 2)]
  have step1 : 2 * R ^ 2 + (1 + b) ≤ 2 * R ^ 2 * (1 + 2 / (9 * (1 + b))) := by
    have h : (1 + b) ≤ 2 * R ^ 2 * (2 / (9 * (1 + b))) := by
      rw [show 2 * R ^ 2 * (2 / (9 * (1 + b))) = 4 * R ^ 2 / (9 * (1 + b)) from by ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hR2]
    linarith
  have step2 : 8 * b ^ 2 * (1 + 2 / (9 * (1 + b))) ^ 3 ≤ (12 / 5) * R ^ 2 := by
    have hA : 40 * b ^ 2 * (1 + 2 / (9 * (1 + b))) ^ 3 ≤ 27 * (1 + b) ^ 2 := by
      have he : (1 + 2 / (9 * (1 + b))) = (9 * (1 + b) + 2) / (9 * (1 + b)) := by field_simp
      rw [he, div_pow]
      rw [show 40 * b ^ 2 * ((9 * (1 + b) + 2) ^ 3 / ((9 * (1 + b)) ^ 3))
            = 40 * b ^ 2 * (9 * (1 + b) + 2) ^ 3 / ((9 * (1 + b)) ^ 3) from by ring]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ((9 * (1 + b)) ^ 3))]
      nlinarith [hpoly]
    have hB : (27 / 5) * (1 + b) ^ 2 ≤ (12 / 5) * R ^ 2 := by nlinarith [hR2]
    linarith
  calc (2 * b * R ^ 2 + b ^ 2 + b) ^ 3
      = (b * (2 * R ^ 2 + (1 + b))) ^ 3 := by ring
    _ = b ^ 3 * (2 * R ^ 2 + (1 + b)) ^ 3 := by ring
    _ ≤ b ^ 3 * (2 * R ^ 2 * (1 + 2 / (9 * (1 + b)))) ^ 3 := by
        gcongr
      _ = b * (8 * b ^ 2 * (1 + 2 / (9 * (1 + b))) ^ 3) * R ^ 6 := by ring
    _ ≤ b * ((12 / 5) * R ^ 2) * R ^ 6 := by
        gcongr
      _ = (12 / 5) * b * R ^ 8 := by ring

/-- On the far region, every `pMap c`-iterate from the first one on lies in a region
where the correction term `nfG c` has norm at most `1/2`. -/
theorem norm_nfG_le_half_of_far_iterate (c z : ℂ) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) (n : ℕ) :
    ‖Work.Bottcher.Core.nfG c ((Work.Bottcher.pMap c)^[n + 1] z)‖ ≤ 1 / 2 := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  set V : ℝ := ‖(Work.Bottcher.pMap c)^[n + 1] z‖ with hVdef
  have hVge : (81 / 32) * (1 + ‖c‖) ^ 4 ≤ V := by
    have hv := pow_four_div_two_le_norm_pMap_iterate c z hz (n + 1) (by omega)
    have h3 : (3 / 2 * (1 + ‖c‖)) ^ 4 ≤ ‖z‖ ^ 4 := pow_le_pow_left₀ (by positivity) hz 4
    have h4 : (81 / 32) * (1 + ‖c‖) ^ 4 = (3 / 2 * (1 + ‖c‖)) ^ 4 / 2 := by ring
    rw [hVdef, h4]
    linarith
  have hVpos : 0 < V := by
    have : (0:ℝ) < (81/32) * (1+‖c‖)^4 := by positivity
    linarith
  have hV2 : ((81 / 32) * (1 + ‖c‖) ^ 4) ^ 2 ≤ V ^ 2 :=
    pow_le_pow_left₀ (by positivity) hVge 2
  have hV4 : ((81 / 32) * (1 + ‖c‖) ^ 4) ^ 4 ≤ V ^ 4 :=
    pow_le_pow_left₀ (by positivity) hVge 4
  have hb17 : 17 * ‖c‖ ≤ (1 + ‖c‖) ^ 8 := by
    nlinarith [sq_nonneg ‖c‖, pow_nonneg hb 3, pow_nonneg hb 4, pow_nonneg hb 5,
      pow_nonneg hb 6, pow_nonneg hb 7]
  have hb10 : 10 * ‖c‖ ≤ (1 + ‖c‖) ^ 15 := by
    have hh : (1 + ‖c‖) ^ 8 ≤ (1 + ‖c‖) ^ 15 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith [hb17, hh]
  have h1 := norm_nfG_le_div c ((Work.Bottcher.pMap c)^[n + 1] z)
  rw [← hVdef] at h1
  have key : (2 * ‖c‖ * V ^ 2 + ‖c‖ ^ 2 + ‖c‖) / V ^ 4 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have ha : 8 * ‖c‖ ≤ V ^ 2 := by
      have h8 : 8 * ‖c‖ ≤ ((81 / 32) ^ 2) * (1 + ‖c‖) ^ 8 := by nlinarith [hb17]
      linarith [h8, hV2]
    have hbnd : 4 * ‖c‖ ≤ ((81 / 32) ^ 4) * (1 + ‖c‖) ^ 15 := by nlinarith [hb10]
    have e1 : 4 * ‖c‖ * V ^ 2 ≤ V ^ 4 / 2 := by
      have hm := mul_le_mul_of_nonneg_right ha (le_of_lt (pow_pos hVpos 2))
      nlinarith [hm, sq_nonneg V]
    have e2 : 2 * ‖c‖ ^ 2 + 2 * ‖c‖ ≤ V ^ 4 / 2 := by
      have hstep : 2 * ‖c‖ * (1 + ‖c‖) ≤ ((81 / 32) ^ 4) * (1 + ‖c‖) ^ 16 / 2 := by
        have h2 : 2 * ‖c‖ * (1 + ‖c‖) = (4 * ‖c‖) * ((1 + ‖c‖) / 2) := by ring
        rw [h2]
        have h3 : (4 * ‖c‖) * ((1 + ‖c‖) / 2)
            ≤ (((81 / 32) ^ 4) * (1 + ‖c‖) ^ 15) * ((1 + ‖c‖) / 2) :=
          mul_le_mul_of_nonneg_right hbnd (by linarith [norm_nonneg c])
        have h4 : (((81 / 32) ^ 4) * (1 + ‖c‖) ^ 15) * ((1 + ‖c‖) / 2)
            = ((81 / 32) ^ 4) * (1 + ‖c‖) ^ 16 / 2 := by ring
        linarith [h3, h4]
      have hstep2 : ((81 / 32) ^ 4) * (1 + ‖c‖) ^ 16 / 2 ≤ V ^ 4 / 2 := by
        nlinarith [hV4]
      calc 2 * ‖c‖ ^ 2 + 2 * ‖c‖ = 2 * ‖c‖ * (1 + ‖c‖) := by ring
        _ ≤ V ^ 4 / 2 := le_trans hstep hstep2
    linarith [e1, e2]
  linarith [h1, key]


end Work.Bottcher.Contraction
