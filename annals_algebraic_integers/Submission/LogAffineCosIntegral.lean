import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The classical integral `∫₀^π log(A + B·cos t) dt`

Sub-lemma for the balayage identity (A2′) of the arithmeticity development:

    ∫ t in 0..π, log(A + B·cos t) dt = π·log((A + √(A²−B²))/2)     (0 < B < A)

(The integrand is positive since `A + B·cos t ≥ A − B > 0`, so no `|·|`.)

## Proof strategy

The proof is built on the classical Jensen identity, as provided by mathlib:

    circleAverage_log_norm_sub_const₀ : circleAverage (log ‖· − a‖) 0 1 = 0   (‖a‖ < 1)

1. For `0 < s < 1` the identity `‖e^{iθ} + s‖² = 1 + 2s·cos θ + s²` (a plain
   `normSq` computation) turns Jensen's identity into
   `∫ θ in 0..(2π), log (1 + 2s·cos θ + s²) = 0`.
2. Since `cos (2π − θ) = cos θ`, the integrand is symmetric on the two halves,
   so `∫ θ in 0..π, log (1 + 2s·cos θ + s²) = 0`.
3. With `m = A + √(A²−B²)`, `k = m/2 > 0`, `s = B/m ∈ (0,1)` one has the exact
   factorization `A + B·cos t = k·(1 + 2s·cos t + s²)` (the identity reduces to
   `m² = 2Am − B²`, which is `(√(A²−B²))² = A² − B²` after expansion).
4. Take logs (all factors positive) and integrate over `t ∈ 0..π`; step 2 kills
   the remaining term, leaving `π·log k = π·log((A + √(A²−B²))/2)`.
-/

noncomputable section

open MeasureTheory
open scoped Real
open intervalIntegral

namespace Submission.LogAffineCosIntegral

/-- `‖e^{i·θ} + s‖² = 1 + 2·s·cos θ + s²`, as a real `normSq` identity. -/
lemma normSq_circleMap_add_ofReal (s θ : ℝ) :
    Complex.normSq (circleMap 0 1 θ + (s : ℂ)) = 1 + 2 * s * Real.cos θ + s ^ 2 := by
  rw [Complex.normSq_apply]
  have hre : (circleMap 0 1 θ + (s : ℂ)).re = Real.cos θ + s := by
    simp [circleMap_zero_re]
  have him : (circleMap 0 1 θ + (s : ℂ)).im = Real.sin θ := by
    simp [circleMap_zero_im]
  rw [hre, him]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `log (1 + 2·s·cos θ + s²) = 2·log ‖e^{i·θ} + s‖`. -/
lemma log_norm_two_mul_circleMap_add_ofReal (s θ : ℝ) :
    Real.log (1 + 2 * s * Real.cos θ + s ^ 2) =
      2 * Real.log ‖circleMap 0 1 θ + (s : ℂ)‖ := by
  calc
    Real.log (1 + 2 * s * Real.cos θ + s ^ 2)
        = Real.log (Complex.normSq (circleMap 0 1 θ + (s : ℂ))) := by
            rw [normSq_circleMap_add_ofReal]
    _ = Real.log (‖circleMap 0 1 θ + (s : ℂ)‖ ^ 2) := by
            rw [Complex.normSq_eq_norm_sq]
    _ = 2 * Real.log ‖circleMap 0 1 θ + (s : ℂ)‖ := by rw [Real.log_pow]; norm_num

/-- Jensen's identity, in real form: `∫₀^{2π} log(1 + 2·s·cos θ + s²) = 0` for `0 < s < 1`. -/
lemma full_circle_log (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log (1 + 2 * s * Real.cos θ + s ^ 2)) = 0 := by
  have hnorm : ‖(-(s : ℂ) : ℂ)‖ < 1 := by
    calc
      ‖(-(s : ℂ) : ℂ)‖ = ‖(s : ℂ)‖ := by rw [norm_neg]
      _ = |s| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = s := abs_of_pos hs0
      _ < 1 := hs1
  have hJ := circleAverage_log_norm_sub_const₀ (a := (-(s : ℂ) : ℂ)) hnorm
  let L : ℝ → ℝ := fun θ : ℝ => Real.log ‖circleMap 0 1 θ + (s : ℂ)‖
  have hJint : (∫ θ in (0 : ℝ)..(2 * Real.pi), L θ) = 0 := by
    have hJ' : (2 * π)⁻¹ • (∫ θ in (0 : ℝ)..(2 * Real.pi), L θ) = 0 := by
      simpa [Real.circleAverage_def, L, sub_neg_eq_add] using hJ
    have hJ'' : (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), L θ) = 0 := by
      simpa [smul_eq_mul] using hJ'
    exact (mul_eq_zero.mp hJ'').resolve_left (by positivity)
  have hpoint : (fun θ : ℝ => Real.log (1 + 2 * s * Real.cos θ + s ^ 2)) = fun θ => 2 * L θ := by
    funext θ
    rw [log_norm_two_mul_circleMap_add_ofReal]
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log (1 + 2 * s * Real.cos θ + s ^ 2))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), 2 * L θ := by rw [hpoint]
    _ = 2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), L θ) := by rw [intervalIntegral.integral_const_mul]
    _ = 0 := by rw [hJint]; ring

/-- Lower bound `1 + 2·s·cos θ + s² ≥ (1 − s)² > 0` for `0 < s < 1`. -/
lemma one_add_two_mul_s_mul_cos_pos (s θ : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < 1 + 2 * s * Real.cos θ + s ^ 2 := by
  have hcosb : -(2 * s) ≤ 2 * s * Real.cos θ := by
    have hs2 : 0 ≤ 2 * s := by positivity
    have := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hs2
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg] using this
  have hge : 0 < 1 - 2 * s + s ^ 2 := by
    have hsp : 0 < (1 - s) ^ 2 := sq_pos_of_pos (sub_pos.mpr hs1)
    nlinarith
  nlinarith

/-- `log (1 + 2·s·cos θ + s²)` is continuous for `0 < s < 1`. -/
lemma continuous_log_one_add_two_mul_s_mul_cos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Continuous (fun θ : ℝ => Real.log (1 + 2 * s * Real.cos θ + s ^ 2)) := by
  apply Continuous.log
  · fun_prop
  · intro θ
    exact ne_of_gt (one_add_two_mul_s_mul_cos_pos s θ hs0 hs1)

/-- The integrand of the auxiliary Jensen identity is interval integrable. -/
lemma intervalIntegrable_log_sq_cos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log (1 + 2 * s * Real.cos θ + s ^ 2)) volume a b := by
  exact (continuous_log_one_add_two_mul_s_mul_cos s hs0 hs1).intervalIntegrable a b

/-- Half-circle Jensen identity:
`∫₀^π log(1 + 2·s·cos θ + s²) = 0` for `0 < s < 1`. -/
lemma half_circle_log (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.log (1 + 2 * s * Real.cos θ + s ^ 2)) = 0 := by
  let g : ℝ → ℝ := fun θ => Real.log (1 + 2 * s * Real.cos θ + s ^ 2)
  have hgint (a b : ℝ) : IntervalIntegrable g volume a b := by
    simpa [g] using intervalIntegrable_log_sq_cos s hs0 hs1 a b
  have hfull : (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ) = 0 := by
    simpa [g] using (full_circle_log s hs0 hs1)
  have hsplit : (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ)
      = (∫ θ in (0 : ℝ)..Real.pi, g θ) + (∫ θ in Real.pi..(2 * Real.pi), g θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgint 0 Real.pi) (hgint Real.pi (2*Real.pi))]
  have hsub : (∫ θ in (0 : ℝ)..Real.pi, g (2 * Real.pi - θ))
      = ∫ θ in Real.pi..(2 * Real.pi), g θ := by
    rw [intervalIntegral.integral_comp_sub_left (f := g) (d := 2 * Real.pi)]
    rw [show 2 * Real.pi - Real.pi = Real.pi by ring]
    rw [show 2 * Real.pi - 0 = 2 * Real.pi by ring]
  have hsym : (∫ θ in Real.pi..(2 * Real.pi), g θ) = (∫ θ in (0 : ℝ)..Real.pi, g θ) := by
    calc
      (∫ θ in Real.pi..(2 * Real.pi), g θ) = ∫ θ in (0 : ℝ)..Real.pi, g (2 * Real.pi - θ) := hsub.symm
      _ = (∫ θ in (0 : ℝ)..Real.pi, g θ) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [g]
              rw [Real.cos_two_pi_sub]
  have hboth : (∫ θ in (0 : ℝ)..Real.pi, g θ) + (∫ θ in (0 : ℝ)..Real.pi, g θ) = 0 := by
    calc
      (∫ θ in (0 : ℝ)..Real.pi, g θ) + (∫ θ in (0 : ℝ)..Real.pi, g θ)
          = (∫ θ in (0 : ℝ)..Real.pi, g θ) + (∫ θ in Real.pi..(2 * Real.pi), g θ) := by rw [hsym]
      _ = (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ) := hsplit.symm
      _ = 0 := hfull
  linarith

/-- `∫ t in 0..π, log(A + B·cos t) dt = π·log((A + √(A²−B²))/2)` for `0 < B < A`. -/
lemma integral_log_affine_cos {A B : ℝ} (hB : 0 < B) (hBA : B < A) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log (A + B * Real.cos t)) =
      Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) := by
  let m : ℝ := A + Real.sqrt (A ^ 2 - B ^ 2)
  let k : ℝ := m / 2
  let s : ℝ := B / m
  have hA : 0 < A := lt_trans hB hBA
  have hpos : 0 < A ^ 2 - B ^ 2 := by
    have h1 : 0 < A - B := sub_pos.mpr hBA
    have h2 : 0 < A + B := add_pos hA hB
    have : (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
    rw [← this]
    exact mul_pos h1 h2
  have hmpos : 0 < m := by
    have hsq : 0 ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_nonneg _
    dsimp [m]
    nlinarith
  have hmgtB : B < m := by
    have hsq : 0 ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_nonneg _
    dsimp [m]
    nlinarith
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hmm : m ^ 2 = 2 * A * m - B ^ 2 := by
    have hs : (Real.sqrt (A ^ 2 - B ^ 2)) ^ 2 = A ^ 2 - B ^ 2 := Real.sq_sqrt (le_of_lt hpos)
    dsimp [m]
    nlinarith
  have hs0 : 0 < s := by
    dsimp [s]
    exact div_pos hB hmpos
  have hs1 : s < 1 := by
    dsimp [s]
    exact (div_lt_one hmpos).2 hmgtB
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hfac (t : ℝ) : A + B * Real.cos t = k * (1 + 2 * s * Real.cos t + s ^ 2) := by
    dsimp [k, s]
    field_simp [hmne]
    nlinarith [hmm]
  have hlogfac (t : ℝ) :
      Real.log (A + B * Real.cos t) =
        Real.log k + Real.log (1 + 2 * s * Real.cos t + s ^ 2) := by
    rw [hfac t]
    rw [Real.log_mul (ne_of_gt hkpos) (ne_of_gt (one_add_two_mul_s_mul_cos_pos s t hs0 hs1))]
  have hconv : (∫ t in (0 : ℝ)..Real.pi, Real.log (A + B * Real.cos t)) =
      (∫ t in (0 : ℝ)..Real.pi,
        (Real.log k + Real.log (1 + 2 * s * Real.cos t + s ^ 2))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hlogfac t
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log (A + B * Real.cos t))
        = (∫ t in (0 : ℝ)..Real.pi,
            (Real.log k + Real.log (1 + 2 * s * Real.cos t + s ^ 2))) := hconv
    _ = (∫ t in (0 : ℝ)..Real.pi, Real.log k)
        + (∫ t in (0 : ℝ)..Real.pi, Real.log (1 + 2 * s * Real.cos t + s ^ 2)) := by
          rw [intervalIntegral.integral_add
              (intervalIntegrable_const (a := (0 : ℝ)) (b := Real.pi) (μ := volume) (c := Real.log k))
              (intervalIntegrable_log_sq_cos s hs0 hs1 0 Real.pi)]
    _ = Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) := by
          rw [half_circle_log s hs0 hs1]
          rw [intervalIntegral.integral_const]
          dsimp [k, m]
          simp

end Submission.LogAffineCosIntegral
