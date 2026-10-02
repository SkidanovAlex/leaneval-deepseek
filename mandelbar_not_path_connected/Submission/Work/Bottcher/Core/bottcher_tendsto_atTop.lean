import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Core

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-!
# `φ_c(z)/z → 1` as `z → ∞` for the tricorn Böttcher coordinate

The Böttcher coordinate of the (anti-holomorphic) tricorn family
`T_c(z) = z̄² + c` is defined on the `CritDomain` by the product formula

`φ_c(z) = z ∏_n (p_c^n z / (p_c^n z)^4)^{4^{-(n+1)}}`,   `p_c = T_c ∘ T_c`,

i.e. `bottcher c z = z * exp (∑' n, 4^{-(n+1)} log (normFactor c (p_c^n z)))`.

Since `p_c` is a monic quartic, `normFactor c w = p_c w / w^4 → 1` as `w → ∞`, so
each factor is a small perturbation of `1`; the weights `4^{-(n+1)}` make the sum
uniformly small as soon as the whole `p_c`-orbit of `z` stays outside a large
disc.  Consequently

`φ_c(z)/z = exp (bottcherSeries c z) → exp 0 = 1` as `z → ∞`.

This file proves that limit.  Everything is elementary: a monic-growth estimate
for `p_c`, the estimate `‖log (1+u)‖ ≤ (3/2)‖u‖` for `‖u‖ ≤ 1/2`
(`Complex.norm_log_one_add_half_le_self`), and a geometric comparison for the
series.
-/

/-! ## A uniform radius -/

/-- A radius, depending only on the parameter `c`, with the following properties
(for all `w` with `‖w‖ ≥ normRadius c`):

* `p_c` satisfies its standard monic growth `‖w‖ ≤ ‖p_c w‖` (so that the whole
  `p_c`-orbit of such a `w` stays outside the radius);
* the Böttcher factor `normFactor c w = p_c w / w^4` is within distance `1/2`
  of `1`, so that `Complex.log (normFactor c w)` is controlled by
  `Complex.norm_log_one_add_half_le_self`. -/
noncomputable def normRadius (c : ℂ) : ℝ :=
  max 2 (max (8 * ‖c‖ + 1) (max (‖c‖ ^ 2 + ‖c‖ + 2) (2 * (‖c‖ ^ 2 + 3 * ‖c‖) + 1)))

theorem two_le_normRadius (c : ℂ) : (2 : ℝ) ≤ normRadius c := le_max_left _ _

theorem eight_le_normRadius (c : ℂ) : 8 * ‖c‖ + 1 ≤ normRadius c :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cnorm_le_normRadius (c : ℂ) : ‖c‖ ^ 2 + ‖c‖ + 2 ≤ normRadius c :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem two_mul_le_normRadius (c : ℂ) : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) + 1 ≤ normRadius c :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

/-! ## Monic growth of `p_c` -/

/-- For `‖w‖` large, the monic quartic `p_c(w) = w^4 + 2 c̄ w^2 + c̄² + c` grows
at least as fast as `‖w‖`. -/
theorem norm_le_norm_pMap (c : ℂ) {w : ℂ} (h2 : 2 ≤ ‖w‖) (h8 : 8 * ‖c‖ + 1 ≤ ‖w‖)
    (hx : ‖c‖ ^ 2 + ‖c‖ + 2 ≤ ‖w‖) : ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖ := by
  have hA : 0 ≤ ‖c‖ := norm_nonneg c
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hw1 : (1 : ℝ) ≤ ‖w‖ := by linarith
  have hsq8 : 8 * ‖c‖ ≤ ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg ‖w‖, mul_le_mul_of_nonneg_left hw1 hw0]
  have hsqx : ‖c‖ ^ 2 + ‖c‖ + 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg ‖w‖, mul_le_mul_of_nonneg_left hw1 hw0]
  have hgeom : ‖w‖ ≤ ‖w‖ ^ 4 - (2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) := by
    nlinarith [hsq8, hsqx, sq_nonneg (‖w‖ ^ 2), sq_nonneg ‖w‖, sq_nonneg (‖c‖)]
  have hexp : Work.Bottcher.pMap c w
      = w ^ 4 + (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c) := by
    simp only [Work.Bottcher.pMap_apply]; ring
  have hpert : ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by
    have h1' := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2) c
    have h2' := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2) ((starRingEnd ℂ c) ^ 2)
    have hrw : ‖2 * (starRingEnd ℂ c) * w ^ 2‖ + ‖(starRingEnd ℂ c) ^ 2‖
        = 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 := by
      simp only [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_ofNat]
    linarith
  rw [hexp]
  have hbound : ‖w ^ 4‖ - ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ ‖w ^ 4 + (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c)‖ := by
    have h := norm_sub_norm_le (w ^ 4)
      (-(2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c))
    rw [sub_neg_eq_add, norm_neg] at h
    exact h
  rw [norm_pow] at hbound
  linarith

/-! ## The Böttcher factor and its logarithm -/

/-- The Böttcher factor `normFactor c w = p_c w / w^4` is `1 + O(1/‖w‖²)`. -/
theorem norm_normFactor_sub_one_le_of_one_le (c w : ℂ) (hw : 1 ≤ ‖w‖) :
    ‖Work.Bottcher.normFactor c w - 1‖ ≤ (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 := by
  have hwpos : (0 : ℝ) < ‖w‖ := by linarith
  have hnum : ‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖
      ≤ 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by
    have h1 := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2) c
    have h2 := norm_add_le (2 * (starRingEnd ℂ c) * w ^ 2) ((starRingEnd ℂ c) ^ 2)
    have hrw : ‖2 * (starRingEnd ℂ c) * w ^ 2‖ + ‖(starRingEnd ℂ c) ^ 2‖
        = 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 := by
      simp only [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_ofNat]
    linarith
  have hwne : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwpos; exact lt_irrefl _ hwpos
  have hrew : Work.Bottcher.normFactor c w - 1
      = (2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c) / w ^ 4 := by
    simp only [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply]
    field_simp
    ring
  rw [hrew, norm_div, norm_pow]
  calc (‖2 * (starRingEnd ℂ c) * w ^ 2 + (starRingEnd ℂ c) ^ 2 + c‖) / ‖w‖ ^ 4
    _ ≤ (2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 4 := by gcongr
    _ = (2 * ‖c‖ + (‖c‖ ^ 2 + ‖c‖) / ‖w‖ ^ 2) / ‖w‖ ^ 2 := by field_simp; ring
    _ ≤ (2 * ‖c‖ + (‖c‖ ^ 2 + ‖c‖)) / ‖w‖ ^ 2 := by
          gcongr
          exact div_le_self (by positivity) (by nlinarith)
    _ = (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 := by ring

/-- Uniform control of `log (normFactor c w)` for `‖w‖ ≥ normRadius c`, via
`‖log (1+u)‖ ≤ (3/2)‖u‖` for `‖u‖ ≤ 1/2`. -/
theorem norm_log_normFactor_le_of_one_le (c w : ℂ) (h1 : 1 ≤ ‖w‖)
    (hD : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) + 1 ≤ ‖w‖) :
    ‖Complex.log (Work.Bottcher.normFactor c w)‖
      ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 := by
  have hz : ‖Work.Bottcher.normFactor c w - 1‖ ≤ (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 :=
    norm_normFactor_sub_one_le_of_one_le c w h1
  have hz2 : ‖Work.Bottcher.normFactor c w - 1‖ ≤ 1 / 2 := by
    refine le_trans hz ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖ ^ 2)]
    have : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) + 1 ≤ ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg w]
    linarith
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := Work.Bottcher.normFactor c w - 1) hz2
  have hsum : (1 : ℂ) + (Work.Bottcher.normFactor c w - 1) = Work.Bottcher.normFactor c w := by
    ring
  rw [hsum] at hlog
  calc ‖Complex.log (Work.Bottcher.normFactor c w)‖
      ≤ 3 / 2 * ‖Work.Bottcher.normFactor c w - 1‖ := hlog
    _ ≤ 3 / 2 * ((‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2) := by gcongr
    _ = (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖w‖ ^ 2 := by ring

/-! ## Uniformity along the whole orbit -/

/-- If `‖z‖ ≥ normRadius c`, then every `p_c`-iterate of `z` also has norm at
least `normRadius c`, and at least `‖z‖`. -/
theorem norm_iterate_pMap_ge_normRadius (c z : ℂ) (hz : normRadius c ≤ ‖z‖) (n : ℕ) :
    normRadius c ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ ∧ ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
  induction n with
  | zero => exact ⟨hz, le_refl ‖z‖⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := ih
      have hle := norm_le_norm_pMap c (le_trans (two_le_normRadius c) h1)
        (le_trans (eight_le_normRadius c) h1) (le_trans (cnorm_le_normRadius c) h1)
      exact ⟨le_trans h1 hle, le_trans h2 hle⟩

/-! ## The Böttcher series -/

/-- Termwise estimate plus a geometric comparison: the weighted sum of the
`log (normFactor c (p_c^n z))` is `O(1/‖z‖²)`. -/
theorem norm_tsum_bottcherTerm_le_normRadius (c z : ℂ) (hR : 0 < ‖z‖)
    (hge : ∀ n : ℕ, ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖)
    (hlog : ∀ n : ℕ, ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))‖
        ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖(Work.Bottcher.pMap c)^[n] z‖ ^ 2) :
    ‖∑' n : ℕ, Work.Bottcher.bottcherTerm c n z‖
      ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 := by
  set K : ℝ := (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hterm : ∀ n, ‖Work.Bottcher.bottcherTerm c n z‖ ≤ (1 / 4 : ℝ) ^ (n + 1) * K := by
    intro n
    have hw : ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := hge n
    have hle : (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖(Work.Bottcher.pMap c)^[n] z‖ ^ 2
        ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hw, norm_nonneg z])
    have hb : ‖Work.Bottcher.bottcherTerm c n z‖
        = (1 / 4 : ℝ) ^ (n + 1)
          * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))‖ := by
      rw [Work.Bottcher.bottcherTerm, norm_mul]
      congr 1
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    rw [hb, hKdef]
    calc (1 / 4 : ℝ) ^ (n + 1)
          * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))‖
      _ ≤ (1 / 4 : ℝ) ^ (n + 1)
            * ((3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖(Work.Bottcher.pMap c)^[n] z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hlog n) (by positivity)
      _ ≤ (1 / 4 : ℝ) ^ (n + 1) * ((3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
  have hgeo : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum1 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using hgeo.mul_right (1 / 4 : ℝ)
  have hgsum : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * K) := hsum1.mul_right K
  have hntermsum : Summable (fun n : ℕ => ‖Work.Bottcher.bottcherTerm c n z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgsum
  have hfirst : ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) = 1 / 3 := by
    have hfun : (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) = (fun n => (1 / 4 : ℝ) ^ n * (1 / 4)) := by
      funext n; rw [pow_succ]
    rw [hfun, hgeo.tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hKg : ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) * K = 1 / 3 * K := by
    rw [hsum1.tsum_mul_right, hfirst]
  calc ‖∑' n : ℕ, Work.Bottcher.bottcherTerm c n z‖
    _ ≤ ∑' n : ℕ, ‖Work.Bottcher.bottcherTerm c n z‖ := norm_tsum_le_tsum_norm hntermsum
    _ ≤ ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) * K := Summable.tsum_le_tsum hterm hntermsum hgsum
    _ = 1 / 3 * K := hKg
    _ ≤ K := by nlinarith [hK0]
    _ = (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 := hKdef

/-- The Böttcher series is `O(1/‖z‖²)` on `‖z‖ ≥ normRadius c`. -/
theorem norm_bottcherSeries_le (c z : ℂ) (hz : normRadius c ≤ ‖z‖) :
    ‖Work.Bottcher.bottcherSeries c z‖ ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2 := by
  have hR := norm_iterate_pMap_ge_normRadius c z hz
  have hge : ∀ n : ℕ, ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := fun n => (hR n).2
  have hlog : ∀ n : ℕ, ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z))‖
      ≤ (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖(Work.Bottcher.pMap c)^[n] z‖ ^ 2 := by
    intro n
    exact norm_log_normFactor_le_of_one_le c _
      (by linarith [two_le_normRadius c, (hR n).1])
      (by linarith [two_mul_le_normRadius c, (hR n).1])
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) (le_trans (two_le_normRadius c) hz)
  have := norm_tsum_bottcherTerm_le_normRadius c z hzpos hge hlog
  simpa only [Work.Bottcher.bottcherSeries] using this

/-! ## The limit at infinity -/

/-- The tail bound `(3/2)(‖c‖²+3‖c‖)/‖z‖²` tends to `0` as `z → ∞`. -/
theorem tendsto_bound (c : ℂ) :
    Filter.Tendsto (fun z : ℂ => (3 / 2) * (‖c‖ ^ 2 + 3 * ‖c‖) / ‖z‖ ^ 2)
      (Filter.cocompact ℂ) (nhds 0) := by
  have h2 : Filter.Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Filter.cocompact ℂ) Filter.atTop :=
    (Filter.tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_norm_cocompact_atTop
  have h3 : Filter.Tendsto (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (Filter.cocompact ℂ) (nhds 0) :=
    h2.inv_tendsto_atTop
  simpa [div_eq_mul_inv] using
    h3.const_mul ((3 / 2 : ℝ) * (‖c‖ ^ 2 + 3 * ‖c‖))

/-- The Böttcher series tends to `0` at infinity. -/
theorem tendsto_bottcherSeries (c : ℂ) :
    Filter.Tendsto (fun z : ℂ => Work.Bottcher.bottcherSeries c z)
      (Filter.cocompact ℂ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) ?_ (tendsto_bound c)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (normRadius c))] with z hz
  exact norm_bottcherSeries_le c z hz

/-- **The Böttcher coordinate is tangent to the identity at infinity.** -/
theorem bottcher_tendsto_atTop (c : ℂ) :
    Filter.Tendsto (fun z : ℂ => Work.Bottcher.bottcher c z / z) (Filter.cocompact ℂ)
      (nhds (1 : ℂ)) := by
  have hexp : Filter.Tendsto (fun z : ℂ => Complex.exp (Work.Bottcher.bottcherSeries c z))
      (Filter.cocompact ℂ) (nhds 1) := by
    have h := Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_bottcherSeries c)
    simpa [Complex.exp_zero, Function.comp_def] using h
  refine Filter.Tendsto.congr' ?_ hexp
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (normRadius c))] with z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz
    have : (2 : ℝ) ≤ normRadius c := two_le_normRadius c
    linarith
  simp only [Work.Bottcher.bottcher]
  rw [mul_div_cancel_left₀ _ hz0]

end Work.Bottcher.Core
