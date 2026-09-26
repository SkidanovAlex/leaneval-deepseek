/-
# The `K₊^{(24)}` five-term decomposition with abstract `τ`-atom bounds

This file adapts the funnel estimates of `Submission/Work/Asymptotics/K24F_sm_sum_bound.lean`
to the form used by the cusp-`±1` tiles: instead of taking the `τ`-atom bounds from the
funnel hypothesis `Funnel τ`, they are hypotheses (`TileAtoms24 τ D Dj`), and the exponential
bookkeeping `e^{-2π(t - Im τ)}` is replaced by the plain factor `‖qParamFun z‖ = e^{-2π Im z}`.

All statements are of the shapes
* `≤ C (1 + D) (scale τ)^N` for the `τ`-side quantities `Phiref`, `Q1`, `Uref`, `Th0`,
* `≤ C (1 + D) (scale τ)^N ‖q z‖^{k}` for `Φ - Φref` (`k = 1`) and `Φ - Φref - q Q1` (`k = 2`),
* `≤ C (1 + D) (1 + Dj) (scale τ)^2 ‖q z‖` for the five remainder groups `Sm i`.

The bodies are copied from `K24F_sm_sum_bound.lean`; the only changes are where the atom
bounds come from.
-/
import Mathlib
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.Tile.HalfDev24Defs

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace Tile

/-! ## Shape helpers -/

/-- `c · s · X ≤ c (1+D)(1+Dj) s² X` for `D, Dj, X, c ≥ 0`, `s ≥ 1`. -/
lemma shape_core {D Dj s X c m : ℝ} (hD : 0 ≤ D) (hDj : 0 ≤ Dj) (hs : 1 ≤ s)
    (hX : 0 ≤ X) (hc : 0 ≤ c) (hm : m ≤ (1 + D) * (1 + Dj)) (hm0 : 0 ≤ m) :
    c * m * s * X ≤ c * (1 + D) * (1 + Dj) * s ^ 2 * X := by
  have hs0 : 0 ≤ s := by linarith
  have h2 : s ≤ s ^ 2 := by nlinarith
  calc c * m * s * X = (c * m) * (s * X) := by ring
    _ ≤ (c * ((1 + D) * (1 + Dj))) * (s * X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hc) (mul_nonneg hs0 hX)
    _ ≤ (c * ((1 + D) * (1 + Dj))) * (s ^ 2 * X) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right h2 hX
    _ = c * (1 + D) * (1 + Dj) * s ^ 2 * X := by ring

/-- `c · s · X ≤ c (1+D)(1+Dj) s² X` for `D, Dj, X, c ≥ 0`, `s ≥ 1`. -/
lemma shape_le_one {D Dj s X c : ℝ} (hD : 0 ≤ D) (hDj : 0 ≤ Dj) (hs : 1 ≤ s)
    (hX : 0 ≤ X) (hc : 0 ≤ c) :
    c * s * X ≤ c * (1 + D) * (1 + Dj) * s ^ 2 * X := by
  have hm : (1:ℝ) ≤ (1 + D) * (1 + Dj) := by nlinarith
  simpa only [mul_one] using shape_core (m := 1) hD hDj hs hX hc hm (by norm_num)

/-- `c · D · s · X ≤ c (1+D)(1+Dj) s² X`. -/
lemma shape_le_D {D Dj s X c : ℝ} (hD : 0 ≤ D) (hDj : 0 ≤ Dj) (hs : 1 ≤ s)
    (hX : 0 ≤ X) (hc : 0 ≤ c) :
    c * D * s * X ≤ c * (1 + D) * (1 + Dj) * s ^ 2 * X := by
  have hm : D ≤ (1 + D) * (1 + Dj) := by nlinarith
  exact shape_core hD hDj hs hX hc hm hD

/-- `c · Dj · s · X ≤ c (1+D)(1+Dj) s² X`. -/
lemma shape_le_Dj {D Dj s X c : ℝ} (hD : 0 ≤ D) (hDj : 0 ≤ Dj) (hs : 1 ≤ s)
    (hX : 0 ≤ X) (hc : 0 ≤ c) :
    c * Dj * s * X ≤ c * (1 + D) * (1 + Dj) * s ^ 2 * X := by
  have hm : Dj ≤ (1 + D) * (1 + Dj) := by nlinarith
  exact shape_core hD hDj hs hX hc hm hDj

/-- `c · D · Dj · s · X ≤ c (1+D)(1+Dj) s² X`. -/
lemma shape_le_DDj {D Dj s X c : ℝ} (hD : 0 ≤ D) (hDj : 0 ≤ Dj) (hs : 1 ≤ s)
    (hX : 0 ≤ X) (hc : 0 ≤ c) :
    c * D * Dj * s * X ≤ c * (1 + D) * (1 + Dj) * s ^ 2 * X := by
  have hm : D * Dj ≤ (1 + D) * (1 + Dj) := by nlinarith
  simpa only [mul_assoc] using shape_core hD hDj hs hX hc hm (mul_nonneg hD hDj)

/-! ## The `τ`-side atoms -/


/-- `Φref` is `O((1+D) scale τ)`. -/
theorem phiref_le_atoms : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (D : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hD0 : 0 ≤ D) →
    (3 : ℝ) ≤ z.im → ‖K24F.Phiref τ z‖ ≤ C * (1 + D) * scale τ := by
  refine ⟨128112 + 1, by norm_num, fun τ z D hr0 hr2 hR0 hr1 hD0 hz => ?_⟩
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z (by linarith)
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  have h1S0sq : ‖1 - K24F.S0 z ^ 2‖ ≤ 10 := by
    have h := norm_sub_le (1:ℂ) (K24F.S0 z ^ 2)
    rw [norm_one] at h; linarith
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have hA : ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)‖ ≤ 120 * D * scale τ := by
    calc ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)‖
        = 6 * ‖K24F.r0 τ + K24F.r2 τ‖ * ‖1 - K24F.S0 z ^ 2‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
      _ ≤ 6 * (2 * (D * scale τ)) * 10 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hr02 (by norm_num)) h1S0sq
            (norm_nonneg _) (by positivity)
      _ = 120 * D * scale τ := by ring
  have hB : ‖(12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2‖ ≤ 108972 * D * scale τ := by
    rw [norm_mul]
    have hR : ‖12 * K24F.R0 τ - 12096 * K24F.r1 τ‖ ≤ 12108 * D * scale τ := by
      have h := norm_sub_le (12 * K24F.R0 τ) (12096 * K24F.r1 τ)
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at h
      nlinarith [h, hR0, hr1]
    calc ‖12 * K24F.R0 τ - 12096 * K24F.r1 τ‖ * ‖K24F.S0 z ^ 2‖
        ≤ (12108 * D * scale τ) * 9 := mul_le_mul hR hS0sq (norm_nonneg _) (by positivity)
      _ = 108972 * D * scale τ := by ring
  have hC : ‖-12 * K24F.R0 τ + 8640 * K24F.r1 τ‖ ≤ 8652 * D * scale τ := by
    have h := norm_add_le (-((12 : ℂ) * K24F.R0 τ)) (8640 * K24F.r1 τ)
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at h
    have heq : -12 * K24F.R0 τ + 8640 * K24F.r1 τ
        = -((12 : ℂ) * K24F.R0 τ) + 8640 * K24F.r1 τ := by ring
    rw [heq]
    nlinarith [h, hR0, hr1]
  have hDl : ‖3456 * K24F.r1 τ * K24F.S0 z‖ ≤ 10368 * D * scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 3456 * ‖K24F.r1 τ‖ * ‖K24F.S0 z‖ ≤ 3456 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 10368 * D * scale τ := by ring
  rw [K24Fsm.phiref_jfree]
  calc ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)
        + (12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2
        + (-12 * K24F.R0 τ + 8640 * K24F.r1 τ) + 3456 * K24F.r1 τ * K24F.S0 z‖
      ≤ ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)‖
        + ‖(12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2‖
        + ‖-12 * K24F.R0 τ + 8640 * K24F.r1 τ‖ + ‖3456 * K24F.r1 τ * K24F.S0 z‖ := K24Fsm.norm_sum4_le
    _ ≤ 120 * D * scale τ + 108972 * D * scale τ + 8652 * D * scale τ + 10368 * D * scale τ := by
        linarith
    _ = 128112 * D * scale τ := by ring
    _ ≤ (128112 * D + 1) * scale τ := by nlinarith [hs0]
    _ ≤ (128112 + 1) * (1 + D) * scale τ := by nlinarith [hs0, hD0]

/-- `Q1` is `O((1+D) scale τ)`. -/
theorem q1_le_atoms : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (D : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hD0 : 0 ≤ D) →
    (3 : ℝ) ≤ z.im → ‖K24F.Q1 τ z‖ ≤ C * (1 + D) * scale τ := by
  refine ⟨11621376 + 1, by norm_num, fun τ z D hr0 hr2 hR0 hr1 hD0 hz => ?_⟩
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z (by linarith)
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have h1 : ‖(1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)‖ ≤ 4608 * D * scale τ := by
    rw [norm_mul]
    have hA : ‖(1440 : ℂ) + 288 * K24F.S0 z‖ ≤ 2304 := by
      have h := norm_add_le (1440 : ℂ) (288 * K24F.S0 z)
      rw [norm_mul] at h
      have hc1 : ‖(1440 : ℂ)‖ = 1440 := by norm_num
      have hc2 : ‖(288 : ℂ)‖ = 288 := by norm_num
      rw [hc1, hc2] at h
      linarith
    calc ‖(1440 : ℂ) + 288 * K24F.S0 z‖ * ‖K24F.r0 τ + K24F.r2 τ‖
        ≤ 2304 * (2 * (D * scale τ)) := mul_le_mul hA hr02 (norm_nonneg _) (by norm_num)
      _ = 4608 * D * scale τ := by ring
  have h2 : ‖-2880 * K24F.R0 τ‖ ≤ 2880 * D * scale τ := by
    rw [(show (-2880 : ℂ) * K24F.R0 τ = -((2880 : ℂ) * K24F.R0 τ) by ring), norm_neg, norm_mul]
    have hc : ‖(2880 : ℂ)‖ = 2880 := by norm_num
    rw [hc]
    linarith
  have h3 : ‖2073600 * K24F.r1 τ‖ ≤ 2073600 * D * scale τ := by
    rw [norm_mul]
    have hc : ‖(2073600 : ℂ)‖ = 2073600 := by norm_num
    rw [hc]
    linarith
  have h4 : ‖-576 * K24F.R0 τ * K24F.S0 z‖ ≤ 1728 * D * scale τ := by
    rw [(show (-576 : ℂ) * K24F.R0 τ * K24F.S0 z = -(((576 : ℂ) * K24F.R0 τ) * K24F.S0 z)
        by ring), norm_neg, norm_mul, norm_mul]
    have hc : ‖(576 : ℂ)‖ = 576 := by norm_num
    rw [hc]
    calc 576 * ‖K24F.R0 τ‖ * ‖K24F.S0 z‖ ≤ 576 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR0 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 1728 * D * scale τ := by ring
  have h5 : ‖580608 * K24F.r1 τ * K24F.S0 z‖ ≤ 1741824 * D * scale τ := by
    rw [norm_mul, norm_mul]
    have hc : ‖(580608 : ℂ)‖ = 580608 := by norm_num
    rw [hc]
    calc 580608 * ‖K24F.r1 τ‖ * ‖K24F.S0 z‖ ≤ 580608 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 1741824 * D * scale τ := by ring
  have h6 : ‖-(82944 * K24F.r1 τ)‖ ≤ 82944 * D * scale τ := by
    rw [norm_neg, norm_mul]
    have hc : ‖(82944 : ℂ)‖ = 82944 := by norm_num
    rw [hc]
    linarith
  have h7 : ‖-(2571264 * K24F.r1 τ * K24F.S0 z)‖ ≤ 7713792 * D * scale τ := by
    rw [norm_neg, norm_mul, norm_mul]
    have hc : ‖(2571264 : ℂ)‖ = 2571264 := by norm_num
    rw [hc]
    calc 2571264 * ‖K24F.r1 τ‖ * ‖K24F.S0 z‖ ≤ 2571264 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 7713792 * D * scale τ := by ring
  rw [K24Fsm.q1_jfree]
  have heq : (1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)
      + (-2880 * K24F.R0 τ + 2073600 * K24F.r1 τ - 576 * K24F.R0 τ * K24F.S0 z
          + 580608 * K24F.r1 τ * K24F.S0 z)
      - 82944 * K24F.r1 τ - 2571264 * K24F.r1 τ * K24F.S0 z
      = (1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)
        + (-2880 * K24F.R0 τ) + (2073600 * K24F.r1 τ) + (-576 * K24F.R0 τ * K24F.S0 z)
        + (580608 * K24F.r1 τ * K24F.S0 z) + (-(82944 * K24F.r1 τ))
        + (-(2571264 * K24F.r1 τ * K24F.S0 z)) := by ring
  rw [heq]
  calc ‖(1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ) + (-2880 * K24F.R0 τ)
        + (2073600 * K24F.r1 τ) + (-576 * K24F.R0 τ * K24F.S0 z)
        + (580608 * K24F.r1 τ * K24F.S0 z) + (-(82944 * K24F.r1 τ))
        + (-(2571264 * K24F.r1 τ * K24F.S0 z))‖
      ≤ ‖(1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)‖ + ‖-2880 * K24F.R0 τ‖
        + ‖2073600 * K24F.r1 τ‖ + ‖-576 * K24F.R0 τ * K24F.S0 z‖
        + ‖580608 * K24F.r1 τ * K24F.S0 z‖ + ‖-(82944 * K24F.r1 τ)‖
        + ‖-(2571264 * K24F.r1 τ * K24F.S0 z)‖ := K24Fsm.norm_sum7_le
    _ ≤ 4608 * D * scale τ + 2880 * D * scale τ + 2073600 * D * scale τ + 1728 * D * scale τ
        + 1741824 * D * scale τ + 82944 * D * scale τ + 7713792 * D * scale τ := by
        linarith
    _ = 11621376 * D * scale τ := by ring
    _ ≤ (11621376 * D + 1) * scale τ := by nlinarith [hs0]
    _ ≤ (11621376 + 1) * (1 + D) * scale τ := by nlinarith [hs0, hD0]

/-- `Uref` is `O((1+D) scale τ)`. -/
theorem uref_le_atoms : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (D : ℝ),
    (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hD0 : 0 ≤ D) → (1 : ℝ) ≤ z.im → ‖K24F.Uref τ z‖ ≤ C * (1 + D) * scale τ := by
  refine ⟨17280 + 1, by norm_num, fun τ z D hr0 hr2 hD0 hz => ?_⟩
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  rw [K24F.Uref]
  have h1 : ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ ≤ 15552 * D * scale τ := by
    have hA : ‖(1728 : ℂ) * K24F.r0 τ‖ ≤ 1728 * (D * scale τ) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hr0 (by norm_num)
    calc ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖
        ≤ (1728 * (D * scale τ)) * 9 := K24Fsm.norm_mul_le_mul hA hS0sq
      _ = 15552 * D * scale τ := by ring
  have h2 : ‖(1728 : ℂ) * K24F.r2 τ‖ ≤ 1728 * D * scale τ := by
    rw [norm_mul, Complex.norm_ofNat]
    nlinarith [hr2]
  calc ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + 1728 * K24F.r2 τ‖
      ≤ ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ + ‖(1728 : ℂ) * K24F.r2 τ‖ := norm_add_le _ _
    _ ≤ 15552 * D * scale τ + 1728 * D * scale τ := by linarith
    _ = 17280 * D * scale τ := by ring
    _ ≤ (17280 * D + 1) * scale τ := by nlinarith [hs0]
    _ ≤ (17280 + 1) * (1 + D) * scale τ := by nlinarith [hs0, hD0]

/-! ## Further shape helpers -/

/-- `1 ≤ 1 + x` for `x ≥ 0`. -/
lemma one_le_one_add (x : ℝ) (hx : 0 ≤ x) : (1 : ℝ) ≤ 1 + x := by linarith

/-- `x ≤ 1 + x` for `x ≥ 0`. -/
lemma le_one_add (x : ℝ) (hx : 0 ≤ x) : x ≤ 1 + x := by linarith

/-- `s ≤ s²` for `s ≥ 1`. -/
lemma le_sq_pow {s : ℝ} (hs : 1 ≤ s) : s ≤ s ^ 2 := by
  have hs0 : 0 ≤ s := by linarith
  nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ s - 1)]

/-- Multiplying an inequality by a common nonneg factor `s * X` (associativity handled). -/
lemma mul_le_mul_of_nonneg_two {a b s X : ℝ} (h : a ≤ b) (hs : 0 ≤ s) (hX : 0 ≤ X) :
    a * s * X ≤ b * s * X := by
  have h0 : 0 ≤ s * X := mul_nonneg hs hX
  calc a * s * X = a * (s * X) := by ring
    _ ≤ b * (s * X) := mul_le_mul_of_nonneg_right h h0
    _ = b * s * X := by ring

/-- Multiplying an inequality by the common factor `(1+D)(1+Dj) s² X`. -/
lemma mul_le_mul_of_nonneg_shape {a b D Dj s X : ℝ} (h : a ≤ b) (hD : 0 ≤ D) (hDj : 0 ≤ Dj)
    (hs : 0 ≤ s) (hX : 0 ≤ X) :
    a * (1 + D) * (1 + Dj) * s ^ 2 * X ≤ b * (1 + D) * (1 + Dj) * s ^ 2 * X := by
  have h0 : 0 ≤ (1 + D) * (1 + Dj) * s ^ 2 * X := by positivity
  calc a * (1 + D) * (1 + Dj) * s ^ 2 * X
      = a * ((1 + D) * (1 + Dj) * s ^ 2 * X) := by ring
    _ ≤ b * ((1 + D) * (1 + Dj) * s ^ 2 * X) := mul_le_mul_of_nonneg_right h h0
    _ = b * (1 + D) * (1 + Dj) * s ^ 2 * X := by ring

/-! ## `Th0` -/

/-- `Th0` is `O((1+D) scale τ)`. -/
theorem th0_le_atoms : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (D : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hD0 : 0 ≤ D) →
    (3 : ℝ) ≤ z.im → ‖K24F.Th0 τ z‖ ≤ C * (1 + D) * scale τ := by
  obtain ⟨CQ, hCQp, hCQ⟩ := q1_le_atoms
  obtain ⟨CP, hCPp, hCP⟩ := phiref_le_atoms
  obtain ⟨CU, hCUp, hCU⟩ := uref_le_atoms
  refine ⟨CQ + 24 * CP + CU + 10368 + 1, by positivity,
    fun τ z D hr0 hr2 hR0 hr1 hD0 hz => ?_⟩
  have hQ := hCQ τ z D hr0 hr2 hR0 hr1 hD0 hz
  have hP := hCP τ z D hr0 hr2 hR0 hr1 hD0 hz
  have hU := hCU τ z D hr0 hr2 hD0 (by linarith : (1:ℝ) ≤ z.im)
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z (by linarith)
  have hR : ‖3456 * K24F.R0 τ * K24F.S0 z‖ ≤ 10368 * D * scale τ := by
    have hA : ‖(3456 : ℂ) * K24F.R0 τ‖ ≤ 3456 * (D * scale τ) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hR0 (by norm_num)
    calc ‖(3456 : ℂ) * K24F.R0 τ * K24F.S0 z‖ ≤ (3456 * (D * scale τ)) * 3 :=
          K24Fsm.norm_mul_le_mul hA hS0
      _ = 10368 * D * scale τ := by ring
  have h24 : ‖(24 : ℂ) * K24F.Phiref τ z‖ ≤ 24 * (CP * (1 + D) * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hP (by norm_num)
  have hmain : ‖K24F.Q1 τ z + 24 * K24F.Phiref τ z - K24F.Uref τ z
        + 3456 * K24F.R0 τ * K24F.S0 z‖
      ≤ CQ * (1 + D) * scale τ + 24 * (CP * (1 + D) * scale τ)
        + CU * (1 + D) * scale τ + 10368 * D * scale τ := by
    have h1 := norm_add_le (K24F.Q1 τ z + 24 * K24F.Phiref τ z - K24F.Uref τ z)
      (3456 * K24F.R0 τ * K24F.S0 z)
    have h3 := norm_sub_le (K24F.Q1 τ z + 24 * K24F.Phiref τ z) (K24F.Uref τ z)
    have h4 := norm_add_le (K24F.Q1 τ z) ((24 : ℂ) * K24F.Phiref τ z)
    linarith
  rw [K24F.Th0]
  calc ‖K24F.Q1 τ z + 24 * K24F.Phiref τ z - K24F.Uref τ z + 3456 * K24F.R0 τ * K24F.S0 z‖
      ≤ CQ * (1 + D) * scale τ + 24 * (CP * (1 + D) * scale τ)
        + CU * (1 + D) * scale τ + 10368 * D * scale τ := hmain
    _ = ((CQ + 24 * CP + CU) * (1 + D) + 10368 * D) * scale τ := by ring
    _ ≤ (CQ + 24 * CP + CU + 10368 + 1) * (1 + D) * scale τ := by
        have hcoef : (CQ + 24 * CP + CU) * (1 + D) + 10368 * D
            ≤ (CQ + 24 * CP + CU + 10368 + 1) * (1 + D) := by
          nlinarith [hD0]
        exact mul_le_mul_of_nonneg_right hcoef hs0

/-! ## `Φ - Φref` and `Φ - Φref - q Q⁽¹⁾` -/

/-- `Φ - Φref = O((1+D) scale τ · q)`. -/
theorem phi_sub_phiref_le_atoms : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (D : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hD0 : 0 ≤ D) →
    (3 : ℝ) ≤ z.im →
    ‖K24F.Phi τ z - K24F.Phiref τ z‖ ≤ C * (1 + D) * scale τ * ‖qParamFun z‖ := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨A * 24240 + 1, by positivity, fun τ z D hr0 hr2 hR0 hr1 hD0 hz => ?_⟩
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hE4ne : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have hdev1 : ‖(E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2)‖ ≤ 2 * A * ‖qParamFun z‖ := by
    have h := norm_sub_le (E4Fun z - 1) (E2S z ^ 2 - Small.S0c z ^ 2)
    linarith
  have hdev2 : ‖12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1)‖
      ≤ 24 * A * ‖qParamFun z‖ := by
    have h := norm_sub_le ((12:ℂ) * (E2S z ^ 2 - Small.S0c z ^ 2)) ((12:ℂ) * (E4Fun z - 1))
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have hdev3 : ‖8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2)‖
      ≤ 20736 * A * ‖qParamFun z‖ := by
    have h := norm_sub_le ((8640:ℂ) * (E4Fun z - 1)) ((12096:ℂ) * (E2S z ^ 2 - Small.S0c z ^ 2))
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have h6r : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)‖ ≤ 6 * (2 * (D * scale τ)) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr02 (by norm_num)
  have hS1 : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))‖
      ≤ (6 * (2 * (D * scale τ))) * (2 * A * ‖qParamFun z‖) :=
    K24Fsm.norm_mul_le_mul h6r hdev1
  have hS2 : ‖K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))‖
      ≤ (D * scale τ) * (24 * A * ‖qParamFun z‖) := K24Fsm.norm_mul_le_mul hR0 hdev2
  have hS3 : ‖K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))‖
      ≤ (D * scale τ) * (20736 * A * ‖qParamFun z‖) := K24Fsm.norm_mul_le_mul hr1 hdev3
  have h3456 : ‖(3456:ℂ) * K24F.r1 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr1 (by norm_num)
  have hS4 : ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
      ≤ (3456 * (D * scale τ)) * (A * ‖qParamFun z‖) := K24Fsm.norm_mul_le_mul h3456 hdF
  have hsum : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))
      + K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))
      + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
      ≤ ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
            * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))‖
        + ‖K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))‖
        + ‖K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))‖
        + ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖ :=
    K24Fsm.norm_sum4_le
  have key : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))
      + K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))
      + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
      ≤ D * A * 24240 * scale τ * ‖qParamFun z‖ := by
    calc ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
          * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))
        + K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))
        + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))
        + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
        ≤ (6 * (2 * (D * scale τ))) * (2 * A * ‖qParamFun z‖)
          + (D * scale τ) * (24 * A * ‖qParamFun z‖)
          + (D * scale τ) * (20736 * A * ‖qParamFun z‖)
          + (3456 * (D * scale τ)) * (A * ‖qParamFun z‖) := by
          linarith [hsum, hS1, hS2, hS3, hS4]
      _ = D * A * 24240 * scale τ * ‖qParamFun z‖ := by ring
  have hgoal : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - K24F.S0 z ^ 2))
      + K24F.R0 τ * (12 * (E2S z ^ 2 - K24F.S0 z ^ 2) - 12 * (E4Fun z - 1))
      + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2))
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - K24F.S0 z)‖
      ≤ D * A * 24240 * scale τ * ‖qParamFun z‖ := by
    rw [K24Fsm.S0_eq_S0c]
    exact key
  rw [K24F.Phi_sub_Phiref_expanded τ z hE4ne]
  refine le_trans hgoal ?_
  have hcoef : D * A * 24240 ≤ (A * 24240 + 1) * (1 + D) := by nlinarith [hD0, hAp]
  exact mul_le_mul_of_nonneg_two hcoef hs0 hq0

/-- `Φ - Φref - q Q⁽¹⁾ = O((1+D) scale τ · q²)`. -/
theorem phi_sub_phiref_sub_le_atoms : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (D : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hD0 : 0 ≤ D) →
    (3 : ℝ) ≤ z.im →
    ‖K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z‖
      ≤ C * (1 + D) * scale τ * ‖qParamFun z‖ ^ 2 := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  obtain ⟨CB, hCBp, hCB⟩ := b2_le
  refine ⟨(A + CB) * 12120 + 1, by positivity, fun τ z D hr0 hr2 hR0 hr1 hD0 hz => ?_⟩
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hE4ne : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have hB2 := hCB z hz
  have hdev1 : ‖(E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z‖
      ≤ (A + CB) * ‖qParamFun z‖ ^ 2 := by
    have h := norm_sub_le (E4Fun z - 1 - 240 * qParamFun z) (K24F.B2 z)
    linarith
  have hdev2 : ‖12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z)‖
      ≤ 12 * (A + CB) * ‖qParamFun z‖ ^ 2 := by
    have h := norm_sub_le ((12:ℂ) * K24F.B2 z) ((12:ℂ) * (E4Fun z - 1 - 240 * qParamFun z))
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have hdev3 : ‖8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z‖
      ≤ (8640 * A + 12096 * CB) * ‖qParamFun z‖ ^ 2 := by
    have h := norm_sub_le ((8640:ℂ) * (E4Fun z - 1 - 240 * qParamFun z)) ((12096:ℂ) * K24F.B2 z)
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have hdev4 : ‖E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
        + 744 * qParamFun z * Small.S0c z‖ ≤ A * ‖qParamFun z‖ ^ 2 := hdG2
  have h6r : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)‖ ≤ 6 * (2 * (D * scale τ)) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr02 (by norm_num)
  have hS1 : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)‖
      ≤ (6 * (2 * (D * scale τ))) * ((A + CB) * ‖qParamFun z‖ ^ 2) :=
    K24Fsm.norm_mul_le_mul h6r hdev1
  have hS2 : ‖K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))‖
      ≤ (D * scale τ) * (12 * (A + CB) * ‖qParamFun z‖ ^ 2) :=
    K24Fsm.norm_mul_le_mul hR0 hdev2
  have hS3 : ‖K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)‖
      ≤ (D * scale τ) * ((8640 * A + 12096 * CB) * ‖qParamFun z‖ ^ 2) :=
    K24Fsm.norm_mul_le_mul hr1 hdev3
  have h3456 : ‖(3456:ℂ) * K24F.r1 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr1 (by norm_num)
  have hS4 : ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
        + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ (3456 * (D * scale τ)) * (A * ‖qParamFun z‖ ^ 2) := K24Fsm.norm_mul_le_mul h3456 hdev4
  have hsum : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
          + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
            * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)‖
        + ‖K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))‖
        + ‖K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)‖
        + ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
            + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖ := K24Fsm.norm_sum4_le
  have key : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
          + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ D * (A + CB) * 12120 * scale τ * ‖qParamFun z‖ ^ 2 := by
    calc ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
          * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
        + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
        + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
        + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
            + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
        ≤ (6 * (2 * (D * scale τ))) * ((A + CB) * ‖qParamFun z‖ ^ 2)
          + (D * scale τ) * (12 * (A + CB) * ‖qParamFun z‖ ^ 2)
          + (D * scale τ) * ((8640 * A + 12096 * CB) * ‖qParamFun z‖ ^ 2)
          + (3456 * (D * scale τ)) * (A * ‖qParamFun z‖ ^ 2) := by
          linarith [hsum, hS1, hS2, hS3, hS4]
      _ = D * (A + CB) * 12120 * scale τ * ‖qParamFun z‖ ^ 2 := by ring
  have hgoal : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - K24F.S0 z
          + 24 * qParamFun z + 744 * qParamFun z * K24F.S0 z)‖
      ≤ D * (A + CB) * 12120 * scale τ * ‖qParamFun z‖ ^ 2 := by
    rw [K24Fsm.S0_eq_S0c]
    exact key
  rw [K24F.Phi_sub_Phiref_sub_expanded τ z hE4ne]
  refine le_trans hgoal ?_
  have hcoef : D * (A + CB) * 12120 ≤ ((A + CB) * 12120 + 1) * (1 + D) := by
    nlinarith [hD0, hAp, hCBp]
  exact mul_le_mul_of_nonneg_two hcoef hs0 (by positivity : (0:ℝ) ≤ ‖qParamFun z‖ ^ 2)
/-! ## The five remainder groups -/

/-- `Sm1` is `O((1+D)(1+Dj) (scale τ)² q)`. -/
theorem sm1_le_atoms : ∃ K : ℝ, 0 < K ∧ ∀ (τ z : ℍ) (D Dj : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hj : ‖jInvariantFun τ‖ ≤ Dj * scale τ) →
    (hD0 : 0 ≤ D) → (hDj : 0 ≤ Dj) → (3 : ℝ) ≤ z.im →
    ‖K24F.Sm1 τ z‖ ≤ K * (1 + D) * (1 + Dj) * (scale τ) ^ 2 * ‖qParamFun z‖ := by
  obtain ⟨CΦ, hCΦp, hCΦ⟩ := phi_sub_phiref_le_atoms
  obtain ⟨CΦ2, hCΦ2p, hCΦ2⟩ := phi_sub_phiref_sub_le_atoms
  obtain ⟨CQ, hCQp, hCQ⟩ := q1_le_atoms
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨CΦ + (27 / 8) * CQ * A + (27 / 8) * CΦ2 * A + 1, by positivity,
    fun τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hs0 : (0 : ℝ) < scale τ := scale_pos τ
  have hsle : (0 : ℝ) ≤ scale τ := hs0.le
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hE4c : ‖E4Fun z ^ 3‖ ≤ 27 / 8 := by
    rw [norm_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) hE4up 3
    have h3 : ((3 : ℝ) / 2) ^ 3 = 27 / 8 := by norm_num
    linarith
  have hT1 : ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)‖
      ≤ CΦ * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h := K24Fsm.norm_mul_le_mul hj (hCΦ τ z D hr0 hr2 hR0 hr1 hD0 hz)
    refine le_trans h ?_
    calc (Dj * scale τ) * (CΦ * (1 + D) * scale τ * ‖qParamFun z‖)
        = (CΦ * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * Dj := by ring
      _ ≤ (CΦ * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * (1 + Dj) :=
          mul_le_mul_of_nonneg_left (le_one_add Dj hDj) (by positivity)
      _ = CΦ * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  have hT2 : ‖E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)‖
      ≤ (27 / 8) * CQ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h1 := K24Fsm.norm_mul_le_mul hE4c (hCQ τ z D hr0 hr2 hR0 hr1 hD0 hz)
    have h := K24Fsm.norm_mul_le_mul h1 hdqd
    refine le_trans h ?_
    calc ((27 / 8) * (CQ * (1 + D) * scale τ)) * (A * ‖qParamFun z‖)
        = ((27 / 8) * CQ * A * (1 + D) * ‖qParamFun z‖) * scale τ := by ring
      _ ≤ ((27 / 8) * CQ * A * (1 + D) * ‖qParamFun z‖) * scale τ ^ 2 :=
          mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
      _ = (27 / 8) * CQ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
      _ ≤ (27 / 8) * CQ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc (27 / 8) * CQ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖
              = ((27 / 8) * CQ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * 1 := by ring
            _ ≤ ((27 / 8) * CQ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * (1 + Dj) :=
                mul_le_mul_of_nonneg_left (one_le_one_add Dj hDj) (by positivity)
            _ = (27 / 8) * CQ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  have hT3 : ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹‖
      ≤ (27 / 8) * CΦ2 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h1 : ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)‖
        ≤ (27 / 8) * (CΦ2 * (1 + D) * scale τ * ‖qParamFun z‖ ^ 2) :=
      K24Fsm.norm_mul_le_mul hE4c (hCΦ2 τ z D hr0 hr2 hR0 hr1 hD0 hz)
    have h := K24Fsm.norm_mul_le_mul h1 hdinv
    refine le_trans h ?_
    calc ((27 / 8) * (CΦ2 * (1 + D) * scale τ * ‖qParamFun z‖ ^ 2)) * (A * ‖qParamFun z‖⁻¹)
        = (27 / 8) * CΦ2 * A * (1 + D) * scale τ
            * (‖qParamFun z‖ ^ 2 * ‖qParamFun z‖⁻¹) := by ring
      _ = (27 / 8) * CΦ2 * A * (1 + D) * scale τ * ‖qParamFun z‖ := by
          rw [K24Fsm.qsq_mul_qinv]
      _ ≤ (27 / 8) * CΦ2 * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc (27 / 8) * CΦ2 * A * (1 + D) * scale τ * ‖qParamFun z‖
              = ((27 / 8) * CΦ2 * A * (1 + D) * ‖qParamFun z‖) * scale τ := by ring
            _ ≤ ((27 / 8) * CΦ2 * A * (1 + D) * ‖qParamFun z‖) * scale τ ^ 2 :=
                mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
            _ = (27 / 8) * CΦ2 * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
      _ ≤ (27 / 8) * CΦ2 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc (27 / 8) * CΦ2 * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖
              = ((27 / 8) * CΦ2 * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * 1 := by ring
            _ ≤ ((27 / 8) * CΦ2 * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * (1 + Dj) :=
                mul_le_mul_of_nonneg_left (one_le_one_add Dj hDj) (by positivity)
            _ = (27 / 8) * CΦ2 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  rw [K24F.Sm1]
  rw [show E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        / DeltaFun z
      = E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹ by ring]
  have hsub1 := norm_sub_le (jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)
      - E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1))
      (E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹)
  have hsub2 := norm_sub_le (jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z))
      (E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1))
  calc ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)
        - E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)
        - E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
          * (DeltaFun z)⁻¹‖
      ≤ CΦ * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖
        + (27 / 8) * CQ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖
        + (27 / 8) * CΦ2 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
        linarith [hsub1, hsub2, hT1, hT2, hT3]
    _ = (CΦ + (27 / 8) * CQ * A + (27 / 8) * CΦ2 * A) * (1 + D) * (1 + Dj)
          * scale τ ^ 2 * ‖qParamFun z‖ := by ring
    _ ≤ (CΦ + (27 / 8) * CQ * A + (27 / 8) * CΦ2 * A + 1) * (1 + D) * (1 + Dj)
          * scale τ ^ 2 * ‖qParamFun z‖ :=
        mul_le_mul_of_nonneg_shape (by linarith) hD0 hDj hsle hq0

/-- `Sm2` is `O((1+D)(1+Dj) (scale τ)² q)`. -/
theorem sm2_le_atoms : ∃ K : ℝ, 0 < K ∧ ∀ (τ z : ℍ) (D Dj : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hj : ‖jInvariantFun τ‖ ≤ Dj * scale τ) →
    (hD0 : 0 ≤ D) → (hDj : 0 ≤ Dj) → (3 : ℝ) ≤ z.im →
    ‖K24F.Sm2 τ z‖ ≤ K * (1 + D) * (1 + Dj) * (scale τ) ^ 2 * ‖qParamFun z‖ := by
  obtain ⟨CΦ, hCΦp, hCΦ⟩ := phiref_le_atoms
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨CΦ * A + (27 / 8) * CΦ * A + 1, by positivity,
    fun τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hs0 : (0 : ℝ) < scale τ := scale_pos τ
  have hsle : (0 : ℝ) ≤ scale τ := hs0.le
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hE4c : ‖E4Fun z ^ 3‖ ≤ 27 / 8 := by
    rw [norm_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) hE4up 3
    have h3 : ((3 : ℝ) / 2) ^ 3 = 27 / 8 := by norm_num
    linarith
  have hd1 : ‖K24F.d1 z‖ ≤ A * ‖qParamFun z‖ := hd1c
  have hT1 : ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)‖
      ≤ CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h1 : ‖jInvariantFun τ * K24F.Phiref τ z‖
        ≤ (Dj * scale τ) * (CΦ * (1 + D) * scale τ) :=
      K24Fsm.norm_mul_le_mul hj (hCΦ τ z D hr0 hr2 hR0 hr1 hD0 hz)
    have h := K24Fsm.norm_mul_le_mul h1 hdqd2
    refine le_trans h ?_
    calc ((Dj * scale τ) * (CΦ * (1 + D) * scale τ)) * (A * ‖qParamFun z‖)
        = (CΦ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * Dj := by ring
      _ ≤ (CΦ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * (1 + Dj) :=
          mul_le_mul_of_nonneg_left (le_one_add Dj hDj) (by positivity)
      _ = CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  have hT2 : ‖E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
      ≤ (27 / 8) * CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h1 : ‖E4Fun z ^ 3 * K24F.Phiref τ z‖ ≤ (27 / 8) * (CΦ * (1 + D) * scale τ) :=
      K24Fsm.norm_mul_le_mul hE4c (hCΦ τ z D hr0 hr2 hR0 hr1 hD0 hz)
    have h := K24Fsm.norm_mul_le_mul h1 hd1
    refine le_trans h ?_
    calc ((27 / 8) * (CΦ * (1 + D) * scale τ)) * (A * ‖qParamFun z‖)
        = ((27 / 8) * CΦ * A * (1 + D) * ‖qParamFun z‖) * scale τ := by ring
      _ ≤ ((27 / 8) * CΦ * A * (1 + D) * ‖qParamFun z‖) * scale τ ^ 2 :=
          mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
      _ = (27 / 8) * CΦ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
      _ ≤ (27 / 8) * CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc (27 / 8) * CΦ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖
              = ((27 / 8) * CΦ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * 1 := by ring
            _ ≤ ((27 / 8) * CΦ * A * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * (1 + Dj) :=
                mul_le_mul_of_nonneg_left (one_le_one_add Dj hDj) (by positivity)
            _ = (27 / 8) * CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  rw [K24F.Sm2]
  have hsub := norm_sub_le (jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z))
    (E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z)
  calc ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)
        - E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
      ≤ CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖
        + (27 / 8) * CΦ * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
        linarith [hsub, hT1, hT2]
    _ = (CΦ * A + (27 / 8) * CΦ * A) * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
        ring
    _ ≤ (CΦ * A + (27 / 8) * CΦ * A + 1) * (1 + D) * (1 + Dj) * scale τ ^ 2
          * ‖qParamFun z‖ :=
        mul_le_mul_of_nonneg_shape (by linarith) hD0 hDj hsle hq0

/-- `Sm3` is `O((1+D)(1+Dj) (scale τ)² q)`. -/
theorem sm3_le_atoms : ∃ K : ℝ, 0 < K ∧ ∀ (τ z : ℍ) (D Dj : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hj : ‖jInvariantFun τ‖ ≤ Dj * scale τ) →
    (hD0 : 0 ≤ D) → (hDj : 0 ≤ Dj) → (3 : ℝ) ≤ z.im →
    ‖K24F.Sm3 τ z‖ ≤ K * (1 + D) * (1 + Dj) * (scale τ) ^ 2 * ‖qParamFun z‖ := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨13824 * A + 1, by positivity,
    fun τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hs0 : (0 : ℝ) < scale τ := scale_pos τ
  have hsle : (0 : ℝ) ≤ scale τ := hs0.le
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz1
  have hdF' : ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z‖ ≤ A * ‖qParamFun z‖ := hdF
  have hbr : ‖K24F.S0 z * (E4Fun z ^ 3 - 1)
        - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)‖ ≤ 4 * A * ‖qParamFun z‖ := by
    have h1 : ‖K24F.S0 z * (E4Fun z ^ 3 - 1)‖ ≤ 3 * (A * ‖qParamFun z‖) :=
      K24Fsm.norm_mul_le_mul hS0 hdE4c
    have hsub := norm_sub_le (K24F.S0 z * (E4Fun z ^ 3 - 1))
      (E6Fun z * E2S z / E4Fun z - K24F.S0 z)
    linarith
  have h3456 : ‖(3456 : ℂ) * K24F.R0 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hR0 (by norm_num)
  have hmain : ‖(3456 : ℂ) * K24F.R0 τ * (K24F.S0 z * (E4Fun z ^ 3 - 1)
        - (E6Fun z * E2S z / E4Fun z - K24F.S0 z))‖
      ≤ 13824 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h := K24Fsm.norm_mul_le_mul h3456 hbr
    refine le_trans h ?_
    have hDle : D ≤ (1 + D) * (1 + Dj) := by
      nlinarith [hD0, hDj, mul_nonneg hD0 hDj]
    calc (3456 * (D * scale τ)) * (4 * A * ‖qParamFun z‖)
        = ((13824 * A * ‖qParamFun z‖) * D) * scale τ := by ring
      _ ≤ ((13824 * A * ‖qParamFun z‖) * ((1 + D) * (1 + Dj))) * scale τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDle (by positivity)) hsle
      _ = 13824 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 13824 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc 13824 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖
              = (13824 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ := by ring
            _ ≤ (13824 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ ^ 2 :=
                mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
            _ = 13824 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  rw [K24F.Sm3_bracket]
  refine le_trans hmain ?_
  exact mul_le_mul_of_nonneg_shape (by linarith) hD0 hDj hsle hq0

/-- `Sm4` is `O((1+D)(1+Dj) (scale τ)² q)`. -/
theorem sm4_le_atoms : ∃ K : ℝ, 0 < K ∧ ∀ (τ z : ℍ) (D Dj : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hj : ‖jInvariantFun τ‖ ≤ Dj * scale τ) →
    (hD0 : 0 ≤ D) → (hDj : 0 ≤ Dj) → (3 : ℝ) ≤ z.im →
    ‖K24F.Sm4 τ z‖ ≤ K * (1 + D) * (1 + Dj) * (scale τ) ^ 2 * ‖qParamFun z‖ := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨20736 * A + 1, by positivity,
    fun τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hs0 : (0 : ℝ) < scale τ := scale_pos τ
  have hsle : (0 : ℝ) ≤ scale τ := hs0.le
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz1
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  have h1E4c : ‖1 - E4Fun z ^ 3‖ ≤ A * ‖qParamFun z‖ := by
    rw [show 1 - E4Fun z ^ 3 = -(E4Fun z ^ 3 - 1) by ring, norm_neg]
    exact hdE4c
  have h1728r0 : ‖(1728 : ℂ) * K24F.r0 τ‖ ≤ 1728 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr0 (by norm_num)
  have h1728r2 : ‖(1728 : ℂ) * K24F.r2 τ‖ ≤ 1728 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr2 (by norm_num)
  have hDle : D ≤ (1 + D) * (1 + Dj) := by nlinarith [hD0, hDj, mul_nonneg hD0 hDj]
  have hT1 : ‖(1728 : ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
      ≤ 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h := K24Fsm.norm_mul_le_mul h1728r0 hdSq
    refine le_trans h ?_
    calc (1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
        = ((1728 * A * ‖qParamFun z‖) * D) * scale τ := by ring
      _ ≤ ((1728 * A * ‖qParamFun z‖) * ((1 + D) * (1 + Dj))) * scale τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDle (by positivity)) hsle
      _ = 1728 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc 1728 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖
              = (1728 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ := by ring
            _ ≤ (1728 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ ^ 2 :=
                mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
            _ = 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  have hT2 : ‖(1728 : ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
      ≤ 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h := K24Fsm.norm_mul_le_mul h1728r2 hdE4
    refine le_trans h ?_
    calc (1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
        = ((1728 * A * ‖qParamFun z‖) * D) * scale τ := by ring
      _ ≤ ((1728 * A * ‖qParamFun z‖) * ((1 + D) * (1 + Dj))) * scale τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDle (by positivity)) hsle
      _ = 1728 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc 1728 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖
              = (1728 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ := by ring
            _ ≤ (1728 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ ^ 2 :=
                mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
            _ = 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  have hinner : ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728 : ℂ) * K24F.r2 τ‖
      ≤ 1728 * (D * scale τ) * 9 + 1728 * (D * scale τ) := by
    have h1 : ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ ≤ (1728 * (D * scale τ)) * 9 :=
      K24Fsm.norm_mul_le_mul h1728r0 hS0sq
    have hadd := norm_add_le ((1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2) ((1728 : ℂ) * K24F.r2 τ)
    linarith
  have hT3 : ‖((1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728 : ℂ) * K24F.r2 τ)
        * (1 - E4Fun z ^ 3)‖
      ≤ 17280 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
    have h := K24Fsm.norm_mul_le_mul hinner h1E4c
    refine le_trans h ?_
    calc (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
        = ((17280 * A * ‖qParamFun z‖) * D) * scale τ := by ring
      _ ≤ ((17280 * A * ‖qParamFun z‖) * ((1 + D) * (1 + Dj))) * scale τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDle (by positivity)) hsle
      _ = 17280 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 17280 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
          calc 17280 * A * (1 + D) * (1 + Dj) * scale τ * ‖qParamFun z‖
              = (17280 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ := by ring
            _ ≤ (17280 * A * (1 + D) * (1 + Dj) * ‖qParamFun z‖) * scale τ ^ 2 :=
                mul_le_mul_of_nonneg_left (le_sq_pow hs1) (by positivity)
            _ = 17280 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
  rw [K24F.Sm4_split]
  have hsum := K24Fsm.norm_sum3_le
    (a := (1728 : ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2))
    (b := (1728 : ℂ) * K24F.r2 τ * (E4Fun z - 1))
    (c := ((1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728 : ℂ) * K24F.r2 τ)
      * (1 - E4Fun z ^ 3))
  calc ‖(1728 : ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)
        + (1728 : ℂ) * K24F.r2 τ * (E4Fun z - 1)
        + ((1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728 : ℂ) * K24F.r2 τ)
          * (1 - E4Fun z ^ 3)‖
      ≤ 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖
        + 1728 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖
        + 17280 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by
        linarith [hsum, hT1, hT2, hT3]
    _ = 20736 * A * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
    _ ≤ (20736 * A + 1) * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ :=
        mul_le_mul_of_nonneg_shape (by linarith) hD0 hDj hsle hq0

/-- `Sm5` is `O((1+D)(1+Dj) (scale τ)² q)`. -/
theorem sm5_le_atoms : ∃ K : ℝ, 0 < K ∧ ∀ (τ z : ℍ) (D Dj : ℝ), (hr0 : ‖K24F.r0 τ‖ ≤ D * scale τ) → (hr2 : ‖K24F.r2 τ‖ ≤ D * scale τ) →
    (hR0 : ‖K24F.R0 τ‖ ≤ D * scale τ) → (hr1 : ‖K24F.r1 τ‖ ≤ D * scale τ) →
    (hj : ‖jInvariantFun τ‖ ≤ Dj * scale τ) →
    (hD0 : 0 ≤ D) → (hDj : 0 ≤ Dj) → (3 : ℝ) ≤ z.im →
    ‖K24F.Sm5 τ z‖ ≤ K * (1 + D) * (1 + Dj) * (scale τ) ^ 2 * ‖qParamFun z‖ := by
  obtain ⟨CΘ, hCΘp, hCΘ⟩ := th0_le_atoms
  refine ⟨2 * CΘ + 1, by positivity,
    fun τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have hs0 : (0 : ℝ) < scale τ := scale_pos τ
  have hsle : (0 : ℝ) ≤ scale τ := hs0.le
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hDz : ‖DeltaFun z‖ ≤ 2 * ‖qParamFun z‖ := by
    have h := DeltaFun_upper_sharp z hz1
    rwa [← norm_qParamFun z] at h
  have hprod : ‖DeltaFun z * jInvariantFun τ‖ ≤ 2 * Dj * scale τ * ‖qParamFun z‖ := by
    have h := K24Fsm.norm_mul_le_mul hDz hj
    calc ‖DeltaFun z * jInvariantFun τ‖ ≤ (2 * ‖qParamFun z‖) * (Dj * scale τ) := h
      _ = 2 * Dj * scale τ * ‖qParamFun z‖ := by ring
  rw [K24F.Sm5]
  rw [show -(DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z
      = -((DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z) by ring, norm_neg]
  have h := K24Fsm.norm_mul_le_mul hprod (hCΘ τ z D hr0 hr2 hR0 hr1 hD0 hz)
  refine le_trans h ?_
  calc (2 * Dj * scale τ * ‖qParamFun z‖) * (CΘ * (1 + D) * scale τ)
      = (2 * CΘ * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * Dj := by ring
    _ ≤ (2 * CΘ * (1 + D) * scale τ ^ 2 * ‖qParamFun z‖) * (1 + Dj) :=
        mul_le_mul_of_nonneg_left (le_one_add Dj hDj) (by positivity)
    _ = 2 * CΘ * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ := by ring
    _ ≤ (2 * CΘ + 1) * (1 + D) * (1 + Dj) * scale τ ^ 2 * ‖qParamFun z‖ :=
        mul_le_mul_of_nonneg_shape (by linarith) hD0 hDj hsle hq0

/-- **The five remainder groups of the `K₊^{(24)}` cusp expansion, with abstract `τ`-atom
bounds.** -/
theorem sm_sum_le_atoms :
    ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧
      ∀ (τ z : ℍ) (D Dj : ℝ), 0 ≤ D → 0 ≤ Dj → TileAtoms24 τ D Dj → (3 : ℝ) ≤ z.im →
        ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z + K24F.Sm5 τ z‖
          ≤ K * (1 + D) * (1 + Dj) * (scale τ) ^ N * ‖qParamFun z‖ := by
  obtain ⟨K1, hK1p, hK1⟩ := sm1_le_atoms
  obtain ⟨K2, hK2p, hK2⟩ := sm2_le_atoms
  obtain ⟨K3, hK3p, hK3⟩ := sm3_le_atoms
  obtain ⟨K4, hK4p, hK4⟩ := sm4_le_atoms
  obtain ⟨K5, hK5p, hK5⟩ := sm5_le_atoms
  refine ⟨K1 + K2 + K3 + K4 + K5 + 1, 2, by positivity, by norm_num, ?_⟩
  intro τ z D Dj hD0 hDj hA hz
  obtain ⟨hr0, hr1, hr2, hR0, hj⟩ := hA
  have h1 := hK1 τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz
  have h2 := hK2 τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz
  have h3 := hK3 τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz
  have h4 := hK4 τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz
  have h5 := hK5 τ z D Dj hr0 hr2 hR0 hr1 hj hD0 hDj hz
  have hsum := K24Fsm.norm_sum5_le (a := K24F.Sm1 τ z) (b := K24F.Sm2 τ z)
    (c := K24F.Sm3 τ z) (d := K24F.Sm4 τ z) (e := K24F.Sm5 τ z)
  rw [Real.rpow_two]
  calc ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z + K24F.Sm5 τ z‖
      ≤ (K1 + K2 + K3 + K4 + K5) * (1 + D) * (1 + Dj) * (scale τ) ^ 2
          * ‖qParamFun z‖ := by
        linarith [hsum, h1, h2, h3, h4, h5]
    _ ≤ (K1 + K2 + K3 + K4 + K5 + 1) * (1 + D) * (1 + Dj) * (scale τ) ^ 2
          * ‖qParamFun z‖ :=
        mul_le_mul_of_nonneg_shape (by linarith) hD0 hDj (scale_pos τ).le (norm_nonneg _)

end Tile

end

end Work.Asymptotics
