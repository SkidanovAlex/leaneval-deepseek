import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open intervalIntegral
open scoped BigOperators

namespace Commons.Analysis.Real

/-! Auxiliary facts for the vertical log-weight integral bound used in the
Lagarias criterion.  The main point is the crude bound

`∫_{-T}^{T} (log (|t|+3)+1)^3 / sqrt (β² + t²)  ≤  8 (log (T+3)+1)^3 (log (T/β)+1)`

obtained by bounding the cubic log-weight by its value at `T`, and then
splitting `1 / sqrt (β² + t²)` into the middle region `|t| ≤ β`
(bounded by `1/β`, contributing `2`) and the two tails
(bounded by `1/|t|`, contributing `2 log (T/β)`). -/

/-- `recipSqrt β t = 1 / sqrt (β ^ 2 + t ^ 2)`. -/
private def recipSqrt (β : ℝ) : ℝ → ℝ := fun t => (Real.sqrt (β ^ 2 + t ^ 2))⁻¹

private lemma recipSqrt_pos {β t : ℝ} (hβ0 : 0 < β) : 0 < recipSqrt β t := by
  dsimp [recipSqrt]
  exact inv_pos.mpr (by
    have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ0
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    exact Real.sqrt_pos.mpr (by nlinarith))

private lemma continuous_recipSqrt {β : ℝ} (hβ0 : 0 < β) : Continuous (recipSqrt β) := by
  have hc : Continuous fun t : ℝ => Real.sqrt (β ^ 2 + t ^ 2) := by fun_prop
  have h0 : ∀ t : ℝ, Real.sqrt (β ^ 2 + t ^ 2) ≠ 0 := by
    intro t
    have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ0
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    exact (Real.sqrt_pos.mpr (by nlinarith)).ne'
  change Continuous fun t : ℝ => (Real.sqrt (β ^ 2 + t ^ 2))⁻¹
  exact Continuous.inv₀ hc h0

private lemma sqrt_sq_add_ge_self {β t : ℝ} (hβ0 : 0 < β) (htβ : β ≤ t) :
    t ≤ Real.sqrt (β ^ 2 + t ^ 2) := by
  have htpos : 0 < t := lt_of_lt_of_le hβ0 htβ
  have ht2le : t ^ 2 ≤ β ^ 2 + t ^ 2 := by nlinarith [sq_nonneg β]
  have hs0 := Real.sqrt_le_sqrt ht2le
  have hsqrt : Real.sqrt (t ^ 2) = t := by rw [Real.sqrt_sq_eq_abs t, abs_of_pos htpos]
  rwa [hsqrt] at hs0

private lemma recipSqrt_le_inv_on_pos {β t : ℝ} (hβ0 : 0 < β) (htβ : β ≤ t) :
    recipSqrt β t ≤ t⁻¹ := by
  have htpos : 0 < t := lt_of_lt_of_le hβ0 htβ
  have hs := sqrt_sq_add_ge_self hβ0 htβ
  have hsp : 0 < Real.sqrt (β ^ 2 + t ^ 2) := by
    have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ0
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    exact Real.sqrt_pos.mpr (by nlinarith)
  dsimp [recipSqrt]
  exact (inv_le_inv₀ hsp htpos).2 hs

private lemma recipSqrt_le_inv_beta {β t : ℝ} (hβ0 : 0 < β) : recipSqrt β t ≤ β⁻¹ := by
  have hs : β ≤ Real.sqrt (β ^ 2 + t ^ 2) := by
    have hb2le : β ^ 2 ≤ β ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
    have hs0 := Real.sqrt_le_sqrt hb2le
    have hsqrtβ : Real.sqrt (β ^ 2) = β := by rw [Real.sqrt_sq_eq_abs β, abs_of_pos hβ0]
    rwa [hsqrtβ] at hs0
  have hsp : 0 < Real.sqrt (β ^ 2 + t ^ 2) := by
    have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ0
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    exact Real.sqrt_pos.mpr (by nlinarith)
  dsimp [recipSqrt]
  exact (inv_le_inv₀ hsp hβ0).2 hs

/-- On `|t| ≤ T` the cubic log-weight is bounded by its value at `T`. -/
private lemma weight_le_weight_top {T t : ℝ} (ht : |t| ≤ T) :
    (Real.log (|t| + 3) + 1) ^ 3 ≤ (Real.log (T + 3) + 1) ^ 3 := by
  have hT0 : 0 ≤ T := by linarith [abs_nonneg t]
  have hT3ge1 : (1 : ℝ) ≤ T + 3 := by nlinarith
  have hle1 : |t| + 3 ≤ T + 3 := by nlinarith
  have hpos1 : 0 < |t| + 3 := by nlinarith [abs_nonneg t]
  have hlog : Real.log (|t| + 3) ≤ Real.log (T + 3) := Real.log_le_log hpos1 hle1
  have hnon : 0 ≤ Real.log (|t| + 3) + 1 := by
    have h0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by nlinarith [abs_nonneg t])
    linarith
  exact pow_le_pow_left₀ hnon (by linarith) 3

/-- The positive tail: `∫_β^T 1/sqrt(β²+t²) ≤ log (T/β)`. -/
private lemma recipSqrt_int_pos_le_log {β T : ℝ} (hβ0 : 0 < β) (hβT : β ≤ T) :
    (∫ t in β..T, recipSqrt β t) ≤ Real.log (T / β) := by
  have hTpos : 0 < T := lt_of_lt_of_le hβ0 hβT
  have hcF : Continuous (recipSqrt β) := continuous_recipSqrt hβ0
  have hpt : ∀ t ∈ Set.Icc β T, recipSqrt β t ≤ t⁻¹ := by
    intro t ht
    exact recipSqrt_le_inv_on_pos hβ0 ht.1
  have hgcontOn : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc β T) := by
    apply continuousOn_inv₀.mono
    intro x hx
    show x ≠ 0
    intro hz
    have h0not : (0 : ℝ) ∉ Set.uIcc β T := Set.notMem_uIcc_of_lt hβ0 hTpos
    exact h0not (by simpa [hz] using hx)
  have hgii : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume β T :=
    hgcontOn.intervalIntegrable
  have hle := intervalIntegral.integral_mono_on hβT (hcF.intervalIntegrable β T) hgii hpt
  calc
    (∫ t in β..T, recipSqrt β t) ≤ ∫ t in β..T, t⁻¹ := hle
    _ = Real.log (T / β) := by
      simpa using (integral_inv_of_pos hβ0 hTpos)

/-- By evenness, the negative tail equals the positive one. -/
private lemma recipSqrt_int_neg_eq_pos {β T : ℝ} :
    (∫ t in -T..-β, recipSqrt β t) = ∫ t in β..T, recipSqrt β t := by
  have heven : ∀ x : ℝ, recipSqrt β (-x) = recipSqrt β x := by
    intro x
    dsimp [recipSqrt]
    have hsq : β ^ 2 + (-x) ^ 2 = β ^ 2 + x ^ 2 := by ring
    rw [hsq]
  have h := integral_comp_neg (f := recipSqrt β) (a := β) (b := T)
  calc
    (∫ t in -T..-β, recipSqrt β t) = ∫ x in β..T, recipSqrt β (-x) := h.symm
    _ = ∫ x in β..T, recipSqrt β x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact heven x

/-- The middle region: `∫_{-β}^{β} 1/sqrt(β²+t²) ≤ 2`. -/
private lemma recipSqrt_int_mid_le_two {β : ℝ} (hβ0 : 0 < β) :
    (∫ t in -β..β, recipSqrt β t) ≤ 2 := by
  have hcF : Continuous (recipSqrt β) := continuous_recipSqrt hβ0
  have hpt : ∀ t ∈ Set.Icc (-β) β, recipSqrt β t ≤ β⁻¹ := by
    intro t ht
    exact recipSqrt_le_inv_beta hβ0
  have hle := intervalIntegral.integral_mono_on (by linarith)
    (hcF.intervalIntegrable (-β) β) (intervalIntegrable_const (μ := MeasureTheory.volume) (c := β⁻¹)) hpt
  calc
    (∫ t in -β..β, recipSqrt β t) ≤ ∫ _ in -β..β, β⁻¹ := hle
    _ = 2 := by
      rw [integral_const]
      dsimp
      field_simp [hβ0.ne']
      ring

/-- Crude global bound for `∫_{-T}^{T} 1/sqrt(β²+t²)`. -/
private lemma recipSqrt_int_le {β T : ℝ} (hβ0 : 0 < β) (hβT : β ≤ T) :
    (∫ t in -T..T, recipSqrt β t) ≤ 2 + 2 * Real.log (T / β) := by
  have hT0 : 0 ≤ T := le_of_lt (lt_of_lt_of_le hβ0 hβT)
  have hcF : Continuous (recipSqrt β) := continuous_recipSqrt hβ0
  have hs1 : (∫ t in -T..-β, recipSqrt β t) + (∫ t in -β..β, recipSqrt β t) =
      ∫ t in -T..β, recipSqrt β t := by
    exact intervalIntegral.integral_add_adjacent_intervals (f := recipSqrt β)
      (hcF.intervalIntegrable (-T) (-β)) (hcF.intervalIntegrable (-β) β)
  have hs2 : (∫ t in -T..β, recipSqrt β t) + (∫ t in β..T, recipSqrt β t) =
      ∫ t in -T..T, recipSqrt β t := by
    exact intervalIntegral.integral_add_adjacent_intervals (f := recipSqrt β)
      (hcF.intervalIntegrable (-T) β) (hcF.intervalIntegrable β T)
  have hneg : (∫ t in -T..-β, recipSqrt β t) ≤ Real.log (T / β) := by
    rw [recipSqrt_int_neg_eq_pos]
    exact recipSqrt_int_pos_le_log hβ0 hβT
  have hmid : (∫ t in -β..β, recipSqrt β t) ≤ 2 := recipSqrt_int_mid_le_two hβ0
  have hpos : (∫ t in β..T, recipSqrt β t) ≤ Real.log (T / β) :=
    recipSqrt_int_pos_le_log hβ0 hβT
  nlinarith [hneg, hmid, hpos,
    (show (∫ t in -T..-β, recipSqrt β t) + (∫ t in -β..β, recipSqrt β t)
        + (∫ t in β..T, recipSqrt β t) = ∫ t in -T..T, recipSqrt β t by
      rw [hs1, hs2])]

theorem verticalLogWeight_integral_le {β T : ℝ} (hβ0 : 0 < β) (hβT : β ≤ T) (hT : 2 ≤ T) :
    (∫ (t : ℝ) in -T..T, ((Real.log (|t| + 3) + 1) ^ 3) / Real.sqrt (β ^ 2 + t ^ 2))
      ≤ 8 * (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / β) + 1) := by
  let W : ℝ := (Real.log (T + 3) + 1) ^ 3
  have hT0 : 0 ≤ T := by linarith
  have hT3 : 1 ≤ T + 3 := by nlinarith
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg hT3
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact pow_nonneg (by linarith) 3
  have hL0 : 0 ≤ Real.log (T / β) := by
    exact Real.log_nonneg ((one_le_div hβ0).2 hβT)
  -- pointwise weight bound on the whole interval
  have hwt : ∀ t ∈ Set.Icc (-T) T,
      ((Real.log (|t| + 3) + 1) ^ 3) / Real.sqrt (β ^ 2 + t ^ 2)
        ≤ W / Real.sqrt (β ^ 2 + t ^ 2) := by
    intro t ht
    have habs : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    exact div_le_div_of_nonneg_right (by
      dsimp [W]
      exact weight_le_weight_top habs) (Real.sqrt_nonneg _)
  -- continuity of both integrands
  have hcontSqrt : Continuous fun t : ℝ => Real.sqrt (β ^ 2 + t ^ 2) := by fun_prop
  have hsqrt0 : ∀ t : ℝ, Real.sqrt (β ^ 2 + t ^ 2) ≠ 0 := by
    intro t
    have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ0
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    exact (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have hcontW : Continuous (fun t : ℝ => W / Real.sqrt (β ^ 2 + t ^ 2)) :=
    Continuous.div₀ continuous_const hcontSqrt hsqrt0
  have hcontWeight : Continuous (fun t : ℝ =>
      ((Real.log (|t| + 3) + 1) ^ 3) / Real.sqrt (β ^ 2 + t ^ 2)) := by
    have hlogcont : Continuous (fun t : ℝ => (Real.log (|t| + 3) + 1) ^ 3) := by
      have h1 : Continuous (fun t : ℝ => |t| + 3) := by fun_prop
      have h1ne : ∀ t : ℝ, |t| + 3 ≠ 0 := by
        intro t
        nlinarith [abs_nonneg t]
      have h2 : Continuous (fun t : ℝ => Real.log (|t| + 3)) := h1.log h1ne
      have h3 : Continuous (fun t : ℝ => Real.log (|t| + 3) + 1) := h2.add continuous_const
      exact h3.pow 3
    exact Continuous.div₀ hlogcont hcontSqrt hsqrt0
  have hImono : (∫ t in -T..T,
      ((Real.log (|t| + 3) + 1) ^ 3) / Real.sqrt (β ^ 2 + t ^ 2))
        ≤ ∫ t in -T..T, W / Real.sqrt (β ^ 2 + t ^ 2) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact hcontWeight.intervalIntegrable (-T) T
    · exact hcontW.intervalIntegrable (-T) T
    · exact hwt
  -- pull the constant W out
  have hpull : (∫ t in -T..T, W / Real.sqrt (β ^ 2 + t ^ 2))
      = W * (∫ t in -T..T, recipSqrt β t) := by
    calc
      (∫ t in -T..T, W / Real.sqrt (β ^ 2 + t ^ 2))
          = ∫ t in -T..T, W * ((Real.sqrt (β ^ 2 + t ^ 2))⁻¹) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
      _ = W * (∫ t in -T..T, (Real.sqrt (β ^ 2 + t ^ 2))⁻¹) := by
        exact intervalIntegral.integral_const_mul W (fun t => (Real.sqrt (β ^ 2 + t ^ 2))⁻¹)
      _ = W * (∫ t in -T..T, recipSqrt β t) := by
        congr 1
  have hFle : (∫ t in -T..T, recipSqrt β t) ≤ 2 + 2 * Real.log (T / β) :=
    recipSqrt_int_le hβ0 hβT
  have hWmul : W * (∫ t in -T..T, recipSqrt β t) ≤ W * (2 + 2 * Real.log (T / β)) :=
    mul_le_mul_of_nonneg_left hFle hW0
  have hnum : 2 + 2 * Real.log (T / β) ≤ 8 * (1 + Real.log (T / β)) := by
    nlinarith
  have hWnum : W * (2 + 2 * Real.log (T / β)) ≤ W * (8 * (1 + Real.log (T / β))) :=
    mul_le_mul_of_nonneg_left hnum hW0
  calc
    (∫ (t : ℝ) in -T..T, ((Real.log (|t| + 3) + 1) ^ 3) / Real.sqrt (β ^ 2 + t ^ 2))
        ≤ ∫ t in -T..T, W / Real.sqrt (β ^ 2 + t ^ 2) := hImono
    _ = W * (∫ t in -T..T, recipSqrt β t) := hpull
    _ ≤ W * (2 + 2 * Real.log (T / β)) := hWmul
    _ ≤ W * (8 * (1 + Real.log (T / β))) := hWnum
    _ = 8 * W * (1 + Real.log (T / β)) := by ring
    _ = 8 * (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / β) + 1) := by
      dsimp [W]
      ring

end Commons.Analysis.Real