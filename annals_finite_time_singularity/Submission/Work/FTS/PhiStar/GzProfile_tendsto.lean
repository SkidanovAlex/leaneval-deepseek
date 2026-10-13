/-
# `GzProfile_tendsto` — the explicit radial profile decays at infinity

`GzProfile α = −Gsing α (Construction.Fstar α)` is the paper's explicit radial profile `G`
of §'The singular term' (the decaying solution of `GzOde α`), so `z ↦ GzProfile α z` tends to
`0` as `z → ∞`.  This file proves that limit for `0 < α ≤ 1/4` (in fact for `0 < α ≤ 5/2`).

## The route

Writing `GzProfile α = (GzProfile α − ThetaProfile) + ThetaProfile = Aprof α + ThetaProfile`
with `ThetaProfile z = 1/(2(1+z)) → 0`, everything reduces to the decay of the *flat* profile
`Aprof α = −Ḡ`, where `Ḡ` is the `Ḡ`-remainder of the singular part.  Two already-proved
identifications do all the analytic work:

* `Aprof_eqOn_negDk` : `Aprof α = −Dk (5/α) 0` on `(0,∞)`;
* `Gbar_eq_of_nonneg`/`Dk_zero` : `Dk (5/α) 0 z = −(1/2)·(z·At (5/α) 0 z)`, i.e.
  `Aprof α z = (1/2)·Pi (5/α) z` for `z > 0`, where `Pi N z = z·At N 0 z`.

So it suffices to show `Pi N z → 0` as `z → ∞` for `N ≥ 2`.  The only estimate needed is the
pointwise comparison (for `z ≥ 1`, `t ∈ [0,1]`)

`z² · t^N/(1+zt)² ≤ t^(N-2)`,     i.e.   `z·(t^N/(1+zt)²) ≤ t^(N-2)/z`,

which follows from `t^N = t^(N-2)·t²` and `(zt)² ≤ (1+zt)²`; integrating over `[0,1]` and
bounding `∫₀¹ t^(N-2) dt ≤ 1` gives `Pi N z ≤ 1/z` for `z ≥ 1`, whence the limit.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Aprof_wiln

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## The auxiliary model integral `At`/`Pi` -/

/-- **Pointwise comparison for the model integral.**  For `N ≥ 2`, `z ≥ 1` and `t ∈ [0,1]`,

`z² · t^N/(1+zt)² ≤ t^(N-2)`.

This is the integrand form of `(tz)² ≤ (1+tz)²` after writing `t^N = t^(N-2)·t²`. -/
theorem At_pointwise (N : ℝ) (hN : 2 ≤ N) {z t : ℝ} (hz : 1 ≤ z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    z ^ 2 * (t ^ N / (1 + z * t) ^ 2) ≤ t ^ (N - 2) := by
  have hz0 : 0 < z := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    rw [Real.zero_rpow (ne_of_gt hN0), zero_div, mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · have ht2 : t ^ N = t ^ (N - 2) * t ^ (2 : ℝ) := by
      rw [← Real.rpow_add h0 (N - 2) 2]
      congr 1
      ring
    have hkey : z ^ 2 * (t ^ N / (1 + z * t) ^ 2)
        = t ^ (N - 2) * ((z * t) ^ 2 / (1 + z * t) ^ 2) := by
      rw [ht2, Real.rpow_two, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hkey]
    refine mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt h0) _) ?_
    rw [div_le_one (by positivity)]
    nlinarith [mul_nonneg (le_of_lt hz0) (le_of_lt h0)]

/-- **The decay bound for `Pi`.**  For `N ≥ 2` and `z ≥ 1` one has `Pi N z ≤ 1/z`. -/
theorem Pi_le_inv (N : ℝ) (hN : 2 ≤ N) {z : ℝ} (hz : 1 ≤ z) :
    Work.FTS.H2.PhiStarE.Pi N z ≤ 1 / z := by
  have hz0 : 0 < z := by linarith
  have hN2 : (0 : ℝ) ≤ N - 2 := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hcont1 : ContinuousOn (fun t : ℝ => t ^ N / (1 + z * t) ^ 2) (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.div
      (Work.FTS.H2.PhiStarE.continuous_rpow_const_nonneg hN0).continuousOn
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact pow_ne_zero 2 (ne_of_gt (by linarith [mul_nonneg (le_of_lt hz0) ht.1]))
  have hint1 : IntervalIntegrable (fun t : ℝ => t ^ N / (1 + z * t) ^ 2) volume 0 1 :=
    hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => z * (t ^ N / (1 + z * t) ^ 2)) volume 0 1 :=
    hint1.const_mul z
  have hint3 : IntervalIntegrable (fun t : ℝ => t ^ (N - 2) / z) volume 0 1 :=
    ((Work.FTS.H2.PhiStarE.continuous_rpow_const_nonneg hN2).intervalIntegrable 0 1).div_const z
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      z * (t ^ N / (1 + z * t) ^ 2) ≤ t ^ (N - 2) / z := by
    intro t ht
    rw [le_div_iff₀ hz0]
    calc z * (t ^ N / (1 + z * t) ^ 2) * z
        = z ^ 2 * (t ^ N / (1 + z * t) ^ 2) := by ring
      _ ≤ t ^ (N - 2) := At_pointwise N hN hz ht
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint2 hint3 hpt
  have hAt : Work.FTS.H2.PhiStarE.At N 0 z
      = ∫ t in (0 : ℝ)..1, t ^ N / (1 + z * t) ^ 2 := by
    rw [Work.FTS.H2.PhiStarE.At_def]
    simp only [Nat.cast_zero, add_zero, zero_add]
  rw [Work.FTS.H2.PhiStarE.Pi_def, hAt, ← intervalIntegral.integral_const_mul]
  refine hmono.trans ?_
  rw [intervalIntegral.integral_div]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt hz0)
  calc (∫ t in (0 : ℝ)..1, t ^ (N - 2))
      ≤ ∫ t in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
          ((Work.FTS.H2.PhiStarE.continuous_rpow_const_nonneg hN2).intervalIntegrable 0 1)
          intervalIntegrable_const
          (fun t ht => Real.rpow_le_one ht.1 ht.2 hN2)
    _ = 1 := by simp

/-- `Pi N z ≥ 0` for `z ≥ 0` (`At N 0` is an integral of a nonnegative integrand). -/
theorem Pi_nonneg (N : ℝ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FTS.H2.PhiStarE.Pi N z := by
  rw [Work.FTS.H2.PhiStarE.Pi_def]
  refine mul_nonneg hz ?_
  rw [Work.FTS.H2.PhiStarE.At_def]
  refine intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1) fun t ht => ?_
  exact div_nonneg (Real.rpow_nonneg ht.1 _)
    (pow_nonneg (by linarith [mul_nonneg hz ht.1]) _)

/-- **`Pi N z → 0` as `z → ∞` for `N ≥ 2`** (in fact for any `N > 1`). -/
theorem tendsto_Pi_atTop (N : ℝ) (hN : 2 ≤ N) :
    Tendsto (Work.FTS.H2.PhiStarE.Pi N) atTop (𝓝 (0 : ℝ)) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact Pi_nonneg N hz
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have h := Pi_le_inv N hN hz
    rwa [one_div] at h

/-! ## The decay of `Aprof` and of the main theorem -/

/-- **The flat profile decays.**  `Aprof α = −Ḡ` equals `(1/2)·Pi (5/α)` on `(0,∞)` and
`5/α ≥ 2` for `0 < α ≤ 5/2`, so `Aprof α z → 0`. -/
theorem tendsto_Aprof {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Tendsto (Aprof α) atTop (𝓝 (0 : ℝ)) := by
  have hN : (2 : ℝ) ≤ 5 / α := by
    rw [le_div_iff₀ hα]
    linarith
  have hPi := tendsto_Pi_atTop (5 / α) hN
  have h2 : Tendsto (fun z => (1 / 2) * Work.FTS.H2.PhiStarE.Pi (5 / α) z) atTop (𝓝 (0 : ℝ)) := by
    have h := hPi.const_mul (1 / 2)
    simpa using h
  have hev : (fun z => (1 / 2) * Work.FTS.H2.PhiStarE.Pi (5 / α) z)
      =ᶠ[atTop] Aprof α := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [Aprof_eqOn_negDk hα hα1 (show z ∈ Set.Ioi 0 from hz)]
    simp only [Work.FTS.H2.PhiStarE.Dk_zero, Work.FTS.H2.PhiStarE.Pi_def]
    ring
  exact h2.congr' hev

/-- `ThetaProfile z = 1/(2(1+z)) → 0`. -/
theorem tendsto_ThetaProfile : Tendsto ThetaProfile atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun z : ℝ => 1 / (1 + z)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_zero, pow_one] using
      tendsto_pow_div_pow_atTop (k := 0) (m := 1) (by norm_num)
  have h2 : Tendsto (fun z : ℝ => (1 / 2) * (1 / (1 + z))) atTop (𝓝 (0 : ℝ)) := by
    have h := h.const_mul (1 / 2)
    simpa using h
  refine h2.congr' ?_
  filter_upwards with z
  rw [ThetaProfile, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- **The explicit radial profile `GzProfile α` decays at infinity**: `GzProfile α z → 0` as
`z → ∞`, for `0 < α ≤ 1/4`.

Since `GzProfile α = Aprof α + ThetaProfile` and both summands tend to `0`, the limit follows. -/
theorem GzProfile_tendsto {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (fun z => Work.FTS.PhiStar.GzProfile α z) Filter.atTop (nhds (0 : ℝ)) := by
  have hα1' : α ≤ 1 := by linarith
  have hsum := (tendsto_Aprof hα hα1').add tendsto_ThetaProfile
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with z
  simp only [Aprof]
  ring

end Work.FTS.PhiStar
