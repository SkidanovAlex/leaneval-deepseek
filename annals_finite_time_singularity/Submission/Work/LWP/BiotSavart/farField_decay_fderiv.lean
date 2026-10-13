/-
# `Work.LWP.BiotSavart.farField_decay_fderiv` — far-field decay of `D (biotSavart ω)`

For a vorticity `ω` bounded by `M` and supported in the closed ball of radius `R`, the derivative
of the Newtonian-potential Biot–Savart field decays like `‖x‖⁻³`:

  `‖fderiv ℝ (biotSavart ω) x‖ ≤ C · M · R³ / ‖x‖³`   whenever `2R ≤ ‖x‖`.

The proof has two branches.

* If `ω` is ae strongly measurable, then the integrand `y ↦ (‖x-y‖³)⁻¹ • (ω y × (x-y))` is
  integrable and `z ↦ biotSavart ω z` is Lipschitz on `ball x (‖x‖/4)` with constant
  `≈ 21973 · M R³/‖x‖³`: on that ball one has `‖x‖/4 ≤ ‖z - y‖ ≤ 7‖x‖/4` for `y` in the support,
  and the elementary kernel estimate `‖a/‖a‖³ - b/‖b‖³‖ ≤ 1030 ‖a-b‖/m³` gives, after integrating
  over the ball and using its volume `4πR³/3`, the stated decay.  A Lipschitz bound bounds
  `fderiv` at every differentiability point, and `fderiv` vanishes elsewhere.
* If `ω` is *not* ae strongly measurable, then `biotSavart ω` is (essentially) the zero function:
  the integrand is not ae strongly measurable at any point which has a *second* point nearby with
  ae strongly measurable integrand (two independent cross-product directions determine `ω`, see
  `crossMeasDichotomy`), so all integrals vanish and `fderiv` is `0`.

The auxiliary inputs `integrand_norm_le` (cross-product norm bound) and `volume_closedBall_real`
are proved in the companion files of this directory.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.integrand_norm_le
import Submission.Work.LWP.BiotSavart.volume_closedBall_real
import Submission.Work.LWP.BiotSavart.crossMeasDichotomy

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open FiniteTimeSingularity MeasureTheory Set Filter Topology
open scoped Matrix Topology

set_option autoImplicit false

namespace Work.LWP.BiotSavart

/-! ## Elementary estimates for the kernel `a ↦ a/‖a‖³` -/

/-- Elementary estimate for the difference of cubes: on `[m, 7m]` with `m > 0` the map
`t ↦ t³` is `3(7m)²`-Lipschitz. -/
theorem abs_pow_three_sub_le {s t m : ℝ} (hm : 0 < m) (hs : m ≤ s) (ht : m ≤ t)
    (hsC : s ≤ 7 * m) (htC : t ≤ 7 * m) :
    |t ^ 3 - s ^ 3| ≤ 3 * (7 * m) ^ 2 * |t - s| := by
  have hs0 : 0 ≤ s := le_trans (le_of_lt hm) hs
  have ht0 : 0 ≤ t := le_trans (le_of_lt hm) ht
  have h1 : t ^ 3 - s ^ 3 = (t - s) * (t ^ 2 + t * s + s ^ 2) := by ring
  have h2 : 0 ≤ t ^ 2 + t * s + s ^ 2 := by positivity
  have h3 : t ^ 2 + t * s + s ^ 2 ≤ 3 * (7 * m) ^ 2 := by nlinarith
  rw [h1, abs_mul, abs_of_nonneg h2]
  calc |t - s| * (t ^ 2 + t * s + s ^ 2)
      ≤ |t - s| * (3 * (7 * m) ^ 2) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = 3 * (7 * m) ^ 2 * |t - s| := by ring

/-- The map `t ↦ t⁻³` is Lipschitz on `[m, 7m]` with constant `147/m⁴`. -/
theorem abs_inv_cube_sub_le {s t m : ℝ} (hm : 0 < m) (hs : m ≤ s) (ht : m ≤ t)
    (hsC : s ≤ 7 * m) (htC : t ≤ 7 * m) :
    |(s ^ 3)⁻¹ - (t ^ 3)⁻¹| ≤ 147 / m ^ 4 * |s - t| := by
  have hs0 : 0 < s := lt_of_lt_of_le hm hs
  have ht0 : 0 < t := lt_of_lt_of_le hm ht
  have h1 : (s ^ 3)⁻¹ - (t ^ 3)⁻¹ = (t ^ 3 - s ^ 3) * ((s ^ 3)⁻¹ * (t ^ 3)⁻¹) := by
    have hm0 : m ≠ 0 := ne_of_gt hm
    rw [← mul_inv]
    field_simp
  have hsi : |(s ^ 3)⁻¹| ≤ (m ^ 3)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
    exact pow_le_pow_left₀ (le_of_lt hm) hs 3
  have hti : |(t ^ 3)⁻¹| ≤ (m ^ 3)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
    exact pow_le_pow_left₀ (le_of_lt hm) ht 3
  have hcube := abs_pow_three_sub_le hm hs ht hsC htC
  have hm3 : 0 ≤ (m ^ 3)⁻¹ := by positivity
  rw [h1, abs_mul, abs_mul]
  calc |t ^ 3 - s ^ 3| * (|(s ^ 3)⁻¹| * |(t ^ 3)⁻¹|)
      ≤ (3 * (7 * m) ^ 2 * |t - s|) * ((m ^ 3)⁻¹ * (m ^ 3)⁻¹) := by
        refine mul_le_mul hcube (mul_le_mul hsi hti (abs_nonneg _) hm3) (by positivity) ?_
        positivity
    _ = 3 * (7 * m) ^ 2 * ((m ^ 3)⁻¹ * (m ^ 3)⁻¹) * |t - s| := by ring
    _ = 147 / m ^ 4 * |s - t| := by
        rw [abs_sub_comm]
        have hcoef : 3 * (7 * m) ^ 2 * ((m ^ 3)⁻¹ * (m ^ 3)⁻¹) = 147 / m ^ 4 := by
          have hm0 : m ≠ 0 := ne_of_gt hm
          field_simp
          ring
        rw [hcoef]

/-- The elementary Lipschitz estimate for the Biot–Savart kernel `a ↦ a/‖a‖³` on the annulus
`m ≤ ‖·‖ ≤ 7m`: `‖a/‖a‖³ - b/‖b‖³‖ ≤ 1030 ‖a - b‖/m³`. -/
theorem norm_smul_inv_norm_cube_sub_le {a b : R3} {m : ℝ} (hm : 0 < m)
    (ha : m ≤ ‖a‖) (hb : m ≤ ‖b‖) (haC : ‖a‖ ≤ 7 * m) (hbC : ‖b‖ ≤ 7 * m) :
    ‖(‖a‖ ^ 3)⁻¹ • a - (‖b‖ ^ 3)⁻¹ • b‖ ≤ 1030 / m ^ 3 * ‖a - b‖ := by
  have hm3 : 0 < m ^ 3 := by positivity
  have hdecomp : (‖a‖ ^ 3)⁻¹ • a - (‖b‖ ^ 3)⁻¹ • b
      = (‖a‖ ^ 3)⁻¹ • (a - b) + ((‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹) • b := by
    rw [smul_sub, sub_smul]
    abel
  have hscal := abs_inv_cube_sub_le hm ha hb haC hbC
  have hnorm : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have ha_inv : (‖a‖ ^ 3)⁻¹ ≤ (m ^ 3)⁻¹ := by
    refine (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hm ha) 3)
      (pow_pos hm 3)).mpr ?_
    exact pow_le_pow_left₀ (le_of_lt hm) ha 3
  have hb_le : ‖b‖ ≤ 7 * m := hbC
  have hb_nonneg : 0 ≤ ‖b‖ := norm_nonneg b
  rw [hdecomp]
  calc ‖(‖a‖ ^ 3)⁻¹ • (a - b) + ((‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹) • b‖
      ≤ ‖(‖a‖ ^ 3)⁻¹ • (a - b)‖ + ‖((‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹) • b‖ := norm_add_le _ _
    _ = (‖a‖ ^ 3)⁻¹ * ‖a - b‖ + |(‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹| * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    _ ≤ (m ^ 3)⁻¹ * ‖a - b‖ + (147 / m ^ 4 * ‖a - b‖) * (7 * m) := by
        have h1 : (‖a‖ ^ 3)⁻¹ * ‖a - b‖ ≤ (m ^ 3)⁻¹ * ‖a - b‖ :=
          mul_le_mul_of_nonneg_right ha_inv (norm_nonneg _)
        have h2 : |(‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹| * ‖b‖ ≤ (147 / m ^ 4 * ‖a - b‖) * (7 * m) := by
          have h3 : |(‖a‖ ^ 3)⁻¹ - (‖b‖ ^ 3)⁻¹| ≤ 147 / m ^ 4 * ‖a - b‖ := by
            refine hscal.trans ?_
            exact mul_le_mul_of_nonneg_left hnorm (by positivity)
          exact mul_le_mul h3 hb_le hb_nonneg (by positivity)
        linarith
    _ ≤ 1030 / m ^ 3 * ‖a - b‖ := by
        have hc : 147 / m ^ 4 * (7 * m) = 1029 / m ^ 3 := by
          have hm0 : m ≠ 0 := ne_of_gt hm
          field_simp
          ring
        have hcomb : (m ^ 3)⁻¹ * ‖a - b‖ + (147 / m ^ 4 * ‖a - b‖) * (7 * m)
            = (1030 / m ^ 3) * ‖a - b‖ := by
          have hc' : (147 / m ^ 4 * ‖a - b‖) * (7 * m) = (1029 / m ^ 3) * ‖a - b‖ := by
            rw [mul_assoc, mul_comm ‖a - b‖ (7 * m), ← mul_assoc, hc]
          rw [show (m ^ 3)⁻¹ = 1 / m ^ 3 by ring, hc']
          ring
        rw [hcomb]

/-! ## The Biot–Savart integrand -/

/-- The integrand of the Newtonian-potential Biot–Savart operator,
`bsK ω x y = (‖x - y‖³)⁻¹ • (ω y × (x - y))`, so that `biotSavart ω x = (4π)⁻¹ • ∫ y, bsK ω x y`. -/
noncomputable def bsK (ω : R3 → R3) (x : R3) : R3 → R3 :=
  fun y => WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))

theorem biotSavart_apply (ω : R3 → R3) (x : R3) :
    biotSavart ω x = (4 * Real.pi)⁻¹ • ∫ y, bsK ω x y := rfl

theorem bsK_eq_zero {ω : R3 → R3} {x y : R3} (h : ω y = 0) : bsK ω x y = 0 := by
  simp [bsK, h]

/-- The pointwise size of the integrand: `‖((‖x-y‖³)⁻¹ • (ω y × (x-y)))‖ ≤ ‖ω y‖/‖x-y‖²`. -/
theorem norm_bsK_le (ω : R3 → R3) (x y : R3) :
    ‖bsK ω x y‖ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖ω y‖ * ‖x - y‖ := by
  rw [bsK, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  have h := norm_toLp_crossProduct_le (ω y) (x - y)
  calc (‖x - y‖ ^ 3)⁻¹ * ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖
      ≤ (‖x - y‖ ^ 3)⁻¹ * (‖ω y‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (by positivity))
    _ = (‖x - y‖ ^ 3)⁻¹ * ‖ω y‖ * ‖x - y‖ := by ring

/-! ## Measurability and integrability of the integrand -/

theorem aestronglyMeasurable_bsK {ω : R3 → R3} (hω : AEStronglyMeasurable ω volume) (x : R3) :
    AEStronglyMeasurable (bsK ω x) volume := by
  have h1 : AEStronglyMeasurable (fun y : R3 => crossProduct (ω y) (x - y)) volume := by
    have hp : AEStronglyMeasurable (fun y : R3 => ((ω y, x - y) : R3 × R3)) volume :=
      hω.prodMk ((continuous_const.sub continuous_id).aestronglyMeasurable)
    exact (by fun_prop : Continuous fun p : R3 × R3 => crossProduct p.1 p.2).comp_aestronglyMeasurable hp
  have h2 : AEStronglyMeasurable (fun y : R3 => (‖x - y‖ ^ (3 : ℕ))⁻¹) volume :=
    (Measurable.inv (by fun_prop : Measurable fun y : R3 => ‖x - y‖ ^ (3 : ℕ))).aestronglyMeasurable
  have h3 : AEStronglyMeasurable
      (fun y : R3 => (‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y)) volume := h2.smul h1
  exact (by fun_prop : Continuous fun (v : Fin 3 → ℝ) => WithLp.toLp 2 v).comp_aestronglyMeasurable h3

/-- `bsK ω x` is integrable whenever the support of `ω` lies in the closed ball of radius `R`
and `R < ‖x‖`: it is bounded by `M/(‖x‖-R)²` on a set of finite measure and vanishes outside. -/
theorem integrable_bsK {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M) (hω : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) {x : R3} (hx : R < ‖x‖) :
    Integrable (bsK ω x) volume := by
  have hfin : volume (Metric.closedBall (0 : R3) R) ≠ ⊤ :=
    (isCompact_closedBall 0 R).measure_lt_top.ne
  have hc : 0 < ‖x‖ - R := sub_pos.mpr hx
  set C : ℝ := M / (‖x‖ - R) ^ 2 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hg : Integrable ((Metric.closedBall (0 : R3) R).indicator (fun _ => C)) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const hfin (by simp)
  refine Integrable.mono' hg (aestronglyMeasurable_bsK hmeas x) ?_
  filter_upwards with y
  by_cases hy : ω y = 0
  · rw [bsK_eq_zero hy]
    simp only [norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hCnn) y
  · have hyR : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp y hy
    rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_eq_norm] using hyR)]
    have hd : ‖x‖ - R ≤ ‖x - y‖ := by
      have h := norm_sub_norm_le x y
      linarith
    have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hc hd
    have hd3 : (‖x - y‖ ^ 3)⁻¹ * ‖x - y‖ = (‖x - y‖ ^ 2)⁻¹ := by
      rw [show (‖x - y‖ ^ 3) = ‖x - y‖ ^ 2 * ‖x - y‖ by ring, mul_inv]
      field_simp
    have hstep : (‖x - y‖ ^ 3)⁻¹ * ‖ω y‖ * ‖x - y‖ ≤ M * (‖x - y‖ ^ 2)⁻¹ := by
      calc (‖x - y‖ ^ 3)⁻¹ * ‖ω y‖ * ‖x - y‖
          = ‖ω y‖ * ((‖x - y‖ ^ 3)⁻¹ * ‖x - y‖) := by ring
        _ = ‖ω y‖ * (‖x - y‖ ^ 2)⁻¹ := by rw [hd3]
        _ ≤ M * (‖x - y‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (hω y) (by positivity)
    refine (norm_bsK_le ω x y).trans (hstep.trans ?_)
    rw [hCdef, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith)) hM

/-! ## The pointwise Lipschitz estimate for the integrand -/

/-- On `ball x (‖x‖/4)` and on the support of `ω`, the integrand `bsK ω z y` is Lipschitz in `z`
with constant `1030·64·M/‖x‖³`. -/
theorem bsK_diff_le {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M) (hω : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) {x : R3} (hxR : 2 * R ≤ ‖x‖)
    {z z' : R3} (hz : z ∈ Metric.ball x (‖x‖ / 4)) (hz' : z' ∈ Metric.ball x (‖x‖ / 4))
    (y : R3) :
    ‖bsK ω z y - bsK ω z' y‖ ≤ (1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖ := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
  · exfalso
    have h : dist z x < ‖x‖ / 4 := hz
    have h4 : ‖x‖ / 4 = 0 := by nlinarith [hx0]
    linarith [dist_nonneg (x := z) (y := x)]
  · have hR2 : R ≤ ‖x‖ / 2 := by linarith
    by_cases hy : ω y = 0
    · rw [bsK_eq_zero hy, bsK_eq_zero hy, sub_zero, norm_zero]
      have h1 : 0 ≤ (1030 * 64) * M := by positivity
      have h2 : 0 ≤ (‖x‖ ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
      have h3 : 0 ≤ (1030 * 64) * M / ‖x‖ ^ 3 := by
        rw [div_eq_mul_inv]; exact mul_nonneg h1 h2
      exact mul_nonneg h3 (norm_nonneg _)
    · have hyR : ‖y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp y hy
      have hy2 : ‖y‖ ≤ ‖x‖ / 2 := le_trans hyR hR2
      have hzx : dist z x < ‖x‖ / 4 := hz
      have hz'x : dist z' x < ‖x‖ / 4 := hz'
      rw [dist_eq_norm] at hzx hz'x
      have hxy : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      have hzx' : ‖z - x‖ < ‖x‖ / 4 := by first | exact hzx | rwa [norm_sub_rev] at hzx
      have hz'x' : ‖z' - x‖ < ‖x‖ / 4 := by first | exact hz'x | rwa [norm_sub_rev] at hz'x
      have hlo : ‖x‖ / 4 ≤ ‖z - y‖ := by
        have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
          rw [show x - y = (x - z) + (z - y) by abel]
          simpa [norm_sub_rev] using norm_add_le (x - z) (z - y)
        have h3 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
        linarith
      have hlo' : ‖x‖ / 4 ≤ ‖z' - y‖ := by
        have h1 : ‖x - y‖ ≤ ‖z' - x‖ + ‖z' - y‖ := by
          rw [show x - y = (x - z') + (z' - y) by abel]
          simpa [norm_sub_rev] using norm_add_le (x - z') (z' - y)
        have h3 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
        linarith
      have hhi : ‖z - y‖ ≤ 7 * (‖x‖ / 4) := by
        have h2 : ‖z - y‖ ≤ ‖z - x‖ + ‖x - y‖ := by
          rw [show z - y = (z - x) + (x - y) by abel]
          exact norm_add_le _ _
        have h3 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        linarith
      have hhi' : ‖z' - y‖ ≤ 7 * (‖x‖ / 4) := by
        have h2 : ‖z' - y‖ ≤ ‖z' - x‖ + ‖x - y‖ := by
          rw [show z' - y = (z' - x) + (x - y) by abel]
          exact norm_add_le _ _
        have h3 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        linarith
      have hm : 0 < ‖x‖ / 4 := by positivity
      have hbd : ‖(‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y)‖
          ≤ 1030 / (‖x‖ / 4) ^ 3 * ‖z - z'‖ := by
        have h := norm_smul_inv_norm_cube_sub_le hm hlo hlo' hhi hhi'
        have heq : (z - y) - (z' - y) = z - z' := by abel
        rwa [heq] at h
      have hrew : bsK ω z y - bsK ω z' y
          = WithLp.toLp 2 (crossProduct (ω y)
              ((‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y))) := by
        simp only [bsK, WithLp.toLp_sub, map_sub, map_smul]
      calc ‖bsK ω z y - bsK ω z' y‖
          = ‖WithLp.toLp 2 (crossProduct (ω y)
              ((‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y)))‖ := by rw [hrew]
        _ ≤ ‖ω y‖ * ‖(‖z - y‖ ^ 3)⁻¹ • (z - y) - (‖z' - y‖ ^ 3)⁻¹ • (z' - y)‖ :=
            norm_toLp_crossProduct_le _ _
        _ ≤ M * (1030 / (‖x‖ / 4) ^ 3 * ‖z - z'‖) :=
            mul_le_mul (hω y) hbd (norm_nonneg _) hM
        _ = (1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖ := by
            have hxne : ‖x‖ ≠ 0 := ne_of_gt hx0
            field_simp
            ring

/-! ## The congr--- version of the measurability transfer -/

/-- Stripping the `toLp` wrapper and the (ae nonzero) scalar factor `(‖z - y‖³)⁻¹` from the
ae strong measurability of the Biot–Savart integrand. -/
theorem aestronglyMeasurable_cross_of_bsK {ω : R3 → R3} {z : R3}
    (hz : AEStronglyMeasurable (bsK ω z) volume) :
    AEStronglyMeasurable (fun y : R3 => crossProduct (ω y) (z - y)) volume := by
  have h1 : AEStronglyMeasurable
      (fun y : R3 => (‖z - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (z - y)) volume :=
    (by fun_prop : Continuous fun v : R3 => WithLp.ofLp v).comp_aestronglyMeasurable hz
  have h2 : AEStronglyMeasurable (fun y : R3 =>
      (‖z - y‖ ^ (3 : ℕ)) • ((‖z - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (z - y))) volume :=
    (((by fun_prop : Continuous fun y : R3 => ‖z - y‖ ^ (3 : ℕ))).aestronglyMeasurable).smul h1
  refine h2.congr ?_
  have hne : ∀ᵐ y ∂(volume : Measure R3), y ≠ z := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton z
  filter_upwards [hne] with y hy
  rw [smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hy)))),
    one_smul]

/-! ## Lipschitz decay of `biotSavart ω` in the far field -/

/-- On the ball of radius `‖x‖/4` around a far point `x` (`2R ≤ ‖x‖`), the Biot–Savart field of a
bounded, compactly supported, ae strongly measurable vorticity is Lipschitz with constant
`2^20 · M R³/‖x‖³`. -/
theorem biotSavart_lipschitzOn_far {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) {x : R3} (hxR : 2 * R ≤ ‖x‖) :
    LipschitzOnWith ((2 ^ 20 : ℝ) * M * R ^ 3 / ‖x‖ ^ 3).toNNReal (biotSavart ω)
      (Metric.ball x (‖x‖ / 4)) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro z hz z' hz'
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
  · exfalso
    have h : dist z x < ‖x‖ / 4 := hz
    have h4 : ‖x‖ / 4 = 0 := by nlinarith [hx0]
    linarith [dist_nonneg (x := z) (y := x)]
  · have hK : 0 ≤ (2 ^ 20 : ℝ) * M * R ^ 3 / ‖x‖ ^ 3 := by positivity
    rw [Real.coe_toNNReal _ hK]
    have hR2 : R ≤ ‖x‖ / 2 := by linarith
    -- the two points are outside the support
    have hsq : ∀ w ∈ Metric.ball x (‖x‖ / 4), R < ‖w‖ := by
      intro w hw
      have hwx : ‖w - x‖ < ‖x‖ / 4 := by simpa [dist_eq_norm] using hw
      have h1 : ‖x‖ ≤ ‖w - x‖ + ‖w‖ := by
        rw [show x = (x - w) + w by abel]
        simpa [norm_sub_rev] using norm_add_le (x - w) w
      linarith
    have hi_z : Integrable (bsK ω z) volume := integrable_bsK hM hω hsupp hmeas (hsq z hz)
    have hi_z' : Integrable (bsK ω z') volume := integrable_bsK hM hω hsupp hmeas (hsq z' hz')
    have hsub : (∫ y, bsK ω z y) - (∫ y, bsK ω z' y) = ∫ y, (bsK ω z y - bsK ω z' y) :=
      (integral_sub hi_z hi_z').symm
    have hF : biotSavart ω z - biotSavart ω z'
        = (4 * Real.pi)⁻¹ • ∫ y, (bsK ω z y - bsK ω z' y) := by
      rw [biotSavart_apply, biotSavart_apply, ← smul_sub, ← hsub]
    have hvanish : ∀ y ∉ Metric.closedBall (0 : R3) R, bsK ω z y - bsK ω z' y = 0 := by
      intro y hy
      have h0 : ω y = 0 := by
        by_contra h
        exact hy (hsupp y h)
      rw [bsK_eq_zero h0, bsK_eq_zero h0, sub_zero]
    have hset : ‖∫ y, (bsK ω z y - bsK ω z' y)‖
        = ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
    have hbound : ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖
        ≤ ((1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖)
            * (R ^ 3 * (Real.pi * 4 / 3)) := by
      have h1 : ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖
          ≤ ((1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖)
              * Measure.real volume (Metric.closedBall (0 : R3) R) := by
        apply norm_setIntegral_le_of_norm_le_const
        · rw [EuclideanSpace.volume_closedBall_fin_three]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
        · intro y _
          exact bsK_diff_le hM hω hsupp hxR hz hz' y
      rwa [volume_closedBall_real R hR] at h1
    have hcoef : (4 * Real.pi)⁻¹ * (1030 * 64) * (Real.pi * 4 / 3) ≤ (2 : ℝ) ^ 20 := by
      have h1 : (4 * Real.pi)⁻¹ * (Real.pi * 4) = 1 := by
        rw [mul_comm 4 Real.pi, inv_mul_cancel₀ (by positivity)]
      nlinarith [h1, Real.pi_pos]
    have hX : 0 ≤ M * R ^ 3 / ‖x‖ ^ 3 * ‖z - z'‖ := by
      have h1 : 0 ≤ M * R ^ 3 := by positivity
      exact mul_nonneg (div_nonneg h1 (by positivity)) (norm_nonneg _)
    calc ‖biotSavart ω z - biotSavart ω z'‖
        = (4 * Real.pi)⁻¹ * ‖∫ y, (bsK ω z y - bsK ω z' y)‖ := by
          rw [hF, norm_smul, Real.norm_of_nonneg (by positivity)]
      _ = (4 * Real.pi)⁻¹
            * ‖∫ y in Metric.closedBall (0 : R3) R, (bsK ω z y - bsK ω z' y)‖ := by rw [hset]
      _ ≤ (4 * Real.pi)⁻¹ * (((1030 * 64) * M / ‖x‖ ^ 3 * ‖z - z'‖)
            * (R ^ 3 * (Real.pi * 4 / 3))) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ((4 * Real.pi)⁻¹ * (1030 * 64) * (Real.pi * 4 / 3))
            * (M * R ^ 3 / ‖x‖ ^ 3 * ‖z - z'‖) := by ring
      _ ≤ (2 : ℝ) ^ 20 * (M * R ^ 3 / ‖x‖ ^ 3 * ‖z - z'‖) :=
          mul_le_mul_of_nonneg_right hcoef hX
      _ = ((2 ^ 20 : ℝ) * M * R ^ 3 / ‖x‖ ^ 3) * ‖z - z'‖ := by ring


/-- A function that vanishes off a single point has zero Fréchet derivative everywhere: off the
point it is locally zero, and at the point it is either discontinuous (hence not differentiable)
or identically zero. -/
theorem fderiv_eq_zero_of_eq_zero_off_single {F : R3 → R3} {p : R3}
    (h : ∀ z, z ≠ p → F z = 0) (x : R3) : fderiv ℝ F x = 0 := by
  by_cases hxp : x = p
  · have h' : ∀ z, z ≠ x → F z = 0 := by
      intro z hz
      exact h z (fun hzp => hz (by rw [hxp, hzp]))
    by_cases hd : DifferentiableAt ℝ F x
    · have hcont : ContinuousAt F x := hd.continuousAt
      have hev : F =ᶠ[𝓝[≠] x] 0 := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact h' z hz
      have hlim : Tendsto F (𝓝[≠] x) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm
          (tendsto_const_nhds : Tendsto (fun _ : R3 => (0 : R3)) (𝓝[≠] x) (𝓝 0))
      have hfx : F x = 0 :=
        tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hlim
      have hzero : F = fun _ => 0 := by
        funext z
        by_cases hz : z = x
        · rw [hz]; exact hfx
        · exact h' z hz
      rw [hzero]
      simp
    · exact fderiv_zero_of_not_differentiableAt hd
  · have hev : F =ᶠ[𝓝 x] (fun _ : R3 => 0) := by
      have hball : Metric.ball x (dist x p / 2) ∈ 𝓝 x :=
        Metric.ball_mem_nhds x (div_pos (dist_pos.mpr hxp) two_pos)
      filter_upwards [hball] with z hz
      refine h z ?_
      intro hzp
      have h1 : dist z x < dist x p / 2 := hz
      subst hzp
      rw [dist_comm] at h1
      linarith [dist_pos.mpr hxp]
    rw [hev.fderiv_eq]
    simp


/-! ## The main theorem -/

theorem farField_decay_fderiv {ω : R3 → R3} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (biotSavart ω) x‖ ≤ C * M * R ^ 3 / ‖x‖ ^ 3 := by
  by_cases hmeas : AEStronglyMeasurable ω volume
  · -- the measurable case: `biotSavart ω` is Lipschitz in the far field
    refine ⟨2 ^ 20, by norm_num, fun x hx => ?_⟩
    by_cases hd : DifferentiableAt ℝ (biotSavart ω) x
    · have hx0 : 0 < ‖x‖ := by linarith
      have hlip := biotSavart_lipschitzOn_far (le_of_lt hR) hM hω hsupp hmeas hx
      have hb := hd.hasFDerivAt.le_of_lipschitzOn
        (Metric.ball_mem_nhds x (by positivity)) hlip
      rw [Real.coe_toNNReal _ (by positivity)] at hb
      exact hb
    · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
      positivity
  · -- the non-measurable case: two independent cross-product directions determine `ω`, so there
    -- is at most one point at which the integrand is ae strongly measurable; hence `biotSavart ω`
    -- vanishes off a single point and its derivative vanishes everywhere
    refine ⟨1, one_pos, fun x hx => ?_⟩
    have hkey : ∀ z z' : R3, AEStronglyMeasurable (bsK ω z) volume →
        AEStronglyMeasurable (bsK ω z') volume → z = z' := by
      intro z z' hz hz'
      by_contra hne
      exact hmeas (crossMeasDichotomy hne
        (aestronglyMeasurable_cross_of_bsK hz) (aestronglyMeasurable_cross_of_bsK hz'))
    have hsingle : ∃ p : R3, ∀ z, z ≠ p → biotSavart ω z = 0 := by
      by_cases hM : ∃ p : R3, AEStronglyMeasurable (bsK ω p) volume
      · obtain ⟨p, hp⟩ := hM
        refine ⟨p, fun z hz => ?_⟩
        have hz' : ¬ AEStronglyMeasurable (bsK ω z) volume := fun h => hz (hkey z p h hp)
        rw [biotSavart_apply, integral_non_aestronglyMeasurable hz', smul_zero]
      · exact ⟨x, fun z _ => by
          rw [biotSavart_apply, integral_non_aestronglyMeasurable (fun h => hM ⟨z, h⟩),
            smul_zero]⟩
    rw [fderiv_eq_zero_of_eq_zero_off_single hsingle.choose_spec x, norm_zero]
    positivity

end Work.LWP.BiotSavart
