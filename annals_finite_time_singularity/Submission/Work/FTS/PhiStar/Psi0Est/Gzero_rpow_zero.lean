import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real
open MeasureTheory Set Filter

/-! ## Auxiliary pointwise facts about `Γ̄` near `0`

`G₀(θ) = −∫_0^θ sin t cos²t Γ̄(t) dt` (`Gzero_eq_neg`), so a two-sided power bound for `G₀`
at `θ = 0` follows pointwise from a bound on the integrand.  The integrand is
`|sin t cos²t Γ̄(t)| ≤ |sin t| cos²t (|Γ(t)|/c + (5/4)|sin 2t|)`, and the only non-elementary
ingredient is the estimate `|Γ(t)| = |(sin t cos²t)^{α/3}| ≤ |t|^{α/3}`, which must hold for
`t < 0` as well: there `Real.rpow` of the negative base `sin t cos²t` is
`exp(log|t|·(α/3))·cos((α/3)π)`, whose modulus is `≤ |t|^{α/3}`. -/

/-- The modulus of `Real.rpow x y` for a *negative* base `x` is at most `(-x)^y`:
`x^y = exp(log x · y) cos(yπ)` and `log x = log (-x)` (`Real.log_neg_eq_log`), so
`|x^y| ≤ exp(log(-x)·y) = (-x)^y`. -/
lemma abs_rpow_le_rpow_neg {x y : ℝ} (hx : x < 0) : |x ^ y| ≤ (-x) ^ y := by
  rw [Real.rpow_def_of_neg hx, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have h1 : Real.exp (Real.log x * y) = (-x) ^ y := by
    rw [Real.rpow_def_of_pos (neg_pos.mpr hx), Real.log_neg_eq_log]
  rw [h1]
  exact mul_le_of_le_one_right (le_of_lt (Real.rpow_pos_of_pos (neg_pos.mpr hx) y))
    (Real.abs_cos_le_one _)

/-- `|Γ(θ)| = |(sin θ cos²θ)^{α/3}| ≤ |θ|^{α/3}` — two-sided, i.e. also for `θ < 0` where the
base `sin θ cos²θ` is negative. -/
lemma abs_Gam_le_abs_rpow (α : ℝ) (hα : 0 ≤ α) (t : ℝ) :
    |Work.Spaces.Gam α t| ≤ |t| ^ (α / 3) := by
  rw [Work.Spaces.Gam]
  set b : ℝ := Real.sin t * Real.cos t ^ 2 with hb
  have hle : |b| ≤ |t| := by
    have h1 : |b| = |Real.sin t| * Real.cos t ^ 2 := by
      rw [hb, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.cos t ^ 2)]
    rw [h1]
    calc |Real.sin t| * Real.cos t ^ 2 ≤ |Real.sin t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_sq_le_one t) (abs_nonneg _)
      _ = |Real.sin t| := mul_one _
      _ ≤ |t| := Real.abs_sin_le_abs
  rcases lt_or_ge b 0 with hb0 | hb0
  · have h1 : |b ^ (α/3)| ≤ (-b) ^ (α/3) := abs_rpow_le_rpow_neg hb0
    have h2 : (-b) ≤ |t| := by rw [← abs_of_neg hb0]; exact hle
    have h3 : (-b) ^ (α/3) ≤ |t| ^ (α/3) :=
      Real.rpow_le_rpow (le_of_lt (neg_pos.mpr hb0)) h2 (by linarith : (0:ℝ) ≤ α/3)
    linarith
  · have hle' : b ≤ |t| := by rwa [abs_of_nonneg hb0] at hle
    have h1 : |b ^ (α/3)| = b ^ (α/3) := abs_of_nonneg (Real.rpow_nonneg hb0 _)
    rw [h1]
    exact Real.rpow_le_rpow hb0 hle' (by linarith : (0:ℝ) ≤ α/3)

/-- **The pointwise two-sided bound**: for `|t| ≤ 1/2`,
`|sin t cos²t Γ̄(t)| ≤ 13 |t|^{1+α/3}`.

Indeed `|Γ̄(t)| ≤ |Γ(t)|/c + (5/4)|sin 2t| ≤ 10|t|^{α/3} + (5/2)|t|` (using `1/c ≤ 10` and
`|sin 2t| ≤ 2|t|`), hence `|sin t cos²t Γ̄(t)| ≤ |t|(10|t|^{α/3} + (5/2)|t|)
= 10|t|^{1+α/3} + (5/2)|t|²` and `|t|² ≤ |t|^{1+α/3}` because `α/3 ≤ 1` and `|t| ≤ 1`. -/
lemma abs_sin_cos_sq_GamBar_le_rpow (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/4) {t : ℝ}
    (ht : |t| ≤ 1/2) :
    |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| ≤ 13 * |t| ^ (1 + α / 3) := by
  have hα0 : 0 ≤ α := le_of_lt hα
  have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc10 : 1 / Work.Spaces.c α ≤ 10 := by rw [div_le_iff₀ hcpos]; linarith
  have hΓ : |Work.Spaces.Gam α t| ≤ |t| ^ (α / 3) := abs_Gam_le_abs_rpow α hα0 t
  have h1 : |Work.Spaces.Gam α t / Work.Spaces.c α| ≤ 10 * |t| ^ (α / 3) := by
    rw [abs_div, abs_of_pos hcpos, div_eq_mul_one_div]
    calc |Work.Spaces.Gam α t| * (1 / Work.Spaces.c α) ≤ |t| ^ (α/3) * 10 :=
          mul_le_mul hΓ hc10 (by positivity) (by positivity)
      _ = 10 * |t| ^ (α/3) := by ring
  have hsin2 : |Real.sin (2 * t)| ≤ 2 * |t| := by
    have h := Real.abs_sin_le_abs (x := 2 * t)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
    linarith
  have hGb : |Work.FTS.VocabO.GamBar α t| ≤ 10 * |t| ^ (α/3) + (5/2) * |t| := by
    rw [Work.FTS.VocabO.GamBar]
    have hsplit : |Work.Spaces.Gam α t / Work.Spaces.c α - 5/4 * Real.sin (2*t)|
        ≤ |Work.Spaces.Gam α t / Work.Spaces.c α| + |(5:ℝ)/4 * Real.sin (2*t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.Spaces.Gam α t / Work.Spaces.c α) (-(5/4 * Real.sin (2*t)))
    have h2 : |(5:ℝ)/4 * Real.sin (2*t)| ≤ (5/2) * |t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5/4)]
      linarith
    linarith
  rw [abs_mul]
  have hbase : |Real.sin t * Real.cos t ^ 2| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.cos t ^ 2)]
    calc |Real.sin t| * Real.cos t ^ 2 ≤ |Real.sin t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_sq_le_one t) (abs_nonneg _)
      _ = |Real.sin t| := mul_one _
      _ ≤ |t| := Real.abs_sin_le_abs
  have hmul1 : |t| * |t| ^ (α/3) = |t| ^ (1 + α/3) := by
    rw [Real.rpow_add' (abs_nonneg t) (by positivity : (1:ℝ) + α/3 ≠ 0), Real.rpow_one]
  have hsq : |t| * |t| ≤ |t| ^ (1 + α/3) := by
    rcases eq_or_lt_of_le (abs_nonneg t) with h | h
    · rw [← h, mul_zero, Real.zero_rpow (by positivity : (1:ℝ) + α/3 ≠ 0)]
    · conv_lhs => rw [← Real.rpow_one |t|, ← Real.rpow_add' (le_of_lt h) (by norm_num : (1:ℝ)+1 ≠ 0)]
      exact Real.rpow_le_rpow_of_exponent_ge h (by linarith [ht]) (by linarith)
  calc |Real.sin t * Real.cos t ^ 2| * |Work.FTS.VocabO.GamBar α t|
      ≤ |t| * (10 * |t|^(α/3) + (5/2) * |t|) := mul_le_mul hbase hGb (abs_nonneg _) (abs_nonneg _)
    _ = 10 * (|t| * |t|^(α/3)) + (5/2) * (|t| * |t|) := by ring
    _ ≤ 10 * |t|^(1+α/3) + (5/2) * |t|^(1+α/3) := by linarith [hmul1, hsq]
    _ = (25/2) * |t|^(1+α/3) := by ring
    _ ≤ 13 * |t|^(1+α/3) := by
        have hpos : 0 ≤ |t| ^ (1 + α/3) := Real.rpow_nonneg (abs_nonneg t) _
        linarith

/-- The source integrand `sin t cos²t Γ̄(t)` is continuous on the closed interval `[-1,1]`
(hence in particular on the *negative* range `[-1/2,0]`, which is all we need).  Continuity of
`Γ(t) = (sin t cos²t)^{α/3}` off the positive range uses `ContinuousOn.rpow_const`, whose side
condition `x ≠ 0 ∨ 0 ≤ p` holds because `p = α/3 ≥ 0`. -/
lemma continuousOn_sin_cos_sq_GamBar_Icc (α : ℝ) (hα : 0 ≤ α) :
    ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      (Set.Icc (-1) 1) := by
  have hGam : ContinuousOn (fun t : ℝ => Work.Spaces.Gam α t) (Set.Icc (-1:ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (α / 3)) (Set.Icc (-1:ℝ) 1)
    exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).rpow_const
      (fun t _ => Or.inr (by linarith))
  have hGb : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.GamBar α t) (Set.Icc (-1:ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (α / 3) / Work.Spaces.c α
      - (5 / 4) * Real.sin (2 * t)) (Set.Icc (-1:ℝ) 1)
    exact (hGam.div_const _).sub (by fun_prop)
  exact (by fun_prop : ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
    (Set.Icc (-1:ℝ) 1)).mul hGb

/-- **Two-sided form of `Gzero_eq_neg`**: for `|θ| ≤ 1/2`,
`G₀(θ) = −∫_0^θ sin t cos²t Γ̄(t) dt`.

For `θ ≥ 0` this is `Gzero_eq_neg`.  For `θ < 0` use the additivity of the interval integral
through `0`: `∫_θ^{π/2} = ∫_θ^0 + ∫_0^{π/2}`, and `∫_0^{π/2} sin t cos²t Γ̄(t) dt = G₀(0) = 0`
(the moment condition `Gzero_zero`), while `∫_θ^0 = −∫_0^θ`. -/
lemma Gzero_eq_neg_of_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/4) {θ : ℝ}
    (hθ : |θ| ≤ 1/2) :
    Work.FTS.PhiStar.Gzero α θ
      = -∫ t in 0..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
  have hθ1 : θ ≤ 1/2 := (abs_le.mp hθ).2
  have hθm : -(1/2) ≤ θ := (abs_le.mp hθ).1
  rcases lt_or_ge θ 0 with hθneg | hθnn
  · have hcont : ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) (Set.Icc (-(1/2)) 0) :=
      (continuousOn_sin_cos_sq_GamBar_Icc α (le_of_lt hα)).mono (by
        intro t ht
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hsub : Set.uIcc θ 0 ⊆ Set.Icc (-(1/2)) 0 := by
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hθneg)] at ht
      exact ⟨le_trans hθm ht.1, ht.2⟩
    have hint1 : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume θ 0 := (hcont.mono hsub).intervalIntegrable
    have hint2 : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume 0 (π / 2) :=
      intervalIntegrable_GamBar α (le_of_lt hα) le_rfl le_rfl (by linarith [Real.pi_pos])
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hzero : ∫ t in 0..(π / 2), Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t = 0 := by
      have h := Gzero_zero α hα hα1
      simpa only [Work.FTS.PhiStar.Gzero] using h
    have hG : Work.FTS.PhiStar.Gzero α θ = ∫ t in θ..0, Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t := by
      rw [Work.FTS.PhiStar.Gzero, ← hadd, hzero, add_zero]
    rw [hG, intervalIntegral.integral_symm (f := fun t => Real.sin t * Real.cos t ^ 2 *
      Work.FTS.VocabO.GamBar α t) 0 θ]
  · exact Gzero_eq_neg α hα hα1 θ
      ⟨hθnn, by have := Real.pi_gt_three; linarith⟩

/-- Two-sided power bound for `G₀` near the left endpoint of `Iθ`: `|G₀(θ)| ≤ C|θ|^{2+α/3}`
for `|θ| ≤ 1/2`.

This is the quantitative form of `G₀(θ) = -∫_0^θ sin t cos²t Γ̄(t) dt` (`Gzero_eq_neg`, with
`Gzero α 0 = 0` the moment condition `Gzero_zero`): the integrand is
`|sin t cos²t Γ̄(t)| ≤ |t|(|t|^{α/3}/c + (5/2)|t|) ≤ C|t|^{1+α/3}` for `|t| ≤ 1/2`, using
`|sin t| ≤ |t|`, `|cos t| ≤ 1`, `|Γ(t)| = |(sin t cos²t)^{α/3}| ≤ |t|^{α/3}` (for `t < 0` as
well: `Real.rpow` of a negative base is `exp(log|x|·y)·cos(yπ)`, whose modulus is
`≤ |x|^y`) and `1/c ≤ 10` (`Spaces.c_bounds`); integrating gives `C|θ|^{2+α/3}`, since
`|θ|³ ≤ C'|θ|^{2+α/3}` for `|θ| ≤ 1/2`.  The estimate improves the existing
`Gzero_abs_le_sq` (`|G₀ θ| ≤ 7θ²` for `θ ∈ [0,1]`, one-sided) by the factor `|θ|^{α/3}`, and
it is two-sided (for `θ < 0` use the additivity of the interval integral through `0`). -/
theorem Gzero_rpow_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, |θ| ≤ 1 / 2 →
      |Work.FTS.PhiStar.Gzero α θ| ≤ C * |θ| ^ (2 + α / 3) := by
  refine ⟨20, by norm_num, fun θ hθ => ?_⟩
  have hp : (0:ℝ) ≤ 1 + α/3 := by linarith
  have hθ1 : θ ≤ 1/2 := (abs_le.mp hθ).2
  have hθm : -(1/2) ≤ θ := (abs_le.mp hθ).1
  have hpt : ∀ t : ℝ, |t| ≤ 1/2 → |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|
      ≤ 13 * |t| ^ (1 + α/3) := fun t ht => abs_sin_cos_sq_GamBar_le_rpow α hα hα1 ht
  rcases lt_or_ge θ 0 with hθneg | hθnn
  · -- `θ < 0`: integrate the two-sided pointwise bound from `θ` to `0`
    have hsub : Set.uIcc θ 0 ⊆ Set.Icc (-1) 1 := by
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hθneg)] at ht
      exact ⟨by linarith [ht.1, hθm], by linarith [ht.2]⟩
    have hintf : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume θ 0 :=
      ((continuousOn_sin_cos_sq_GamBar_Icc α (le_of_lt hα)).mono hsub).intervalIntegrable
    have hintg : IntervalIntegrable (fun t : ℝ => 13 * |t| ^ (1 + α/3)) volume θ 0 := by
      have hcon : Continuous fun t : ℝ => 13 * |t| ^ (1 + α/3) :=
        continuous_const.mul ((Real.continuous_rpow_const hp).comp continuous_abs)
      exact hcon.intervalIntegrable _ _
    have hintc : IntervalIntegrable (fun _ : ℝ => 13 * |θ| ^ (1 + α/3)) volume θ 0 :=
      continuous_const.intervalIntegrable _ _
    have hGl : Work.FTS.PhiStar.Gzero α θ = ∫ t in θ..0, Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t := by
      rw [Gzero_eq_neg_of_abs_le α hα hα1 hθ, ← intervalIntegral.integral_symm
        (f := fun t => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) 0 θ]
    calc |Work.FTS.PhiStar.Gzero α θ|
        = |∫ t in θ..0, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| := by
          rw [hGl]
      _ ≤ ∫ t in θ..0, |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| :=
          intervalIntegral.abs_integral_le_integral_abs (le_of_lt hθneg)
      _ ≤ ∫ t in θ..0, 13 * |t| ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on (le_of_lt hθneg) hintf.abs hintg
            (fun t ht => ?_)
          have habs : |t| ≤ |θ| := by
            rw [abs_of_neg hθneg]
            exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2, hθneg]⟩
          exact hpt t (by linarith [habs, hθ])
      _ ≤ ∫ t in θ..0, 13 * |θ| ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on (le_of_lt hθneg) hintg hintc
            (fun t ht => ?_)
          have habs : |t| ≤ |θ| := by
            rw [abs_of_neg hθneg]
            exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2, hθneg]⟩
          have h := Real.rpow_le_rpow (abs_nonneg t) habs hp
          linarith
      _ = 13 * |θ| ^ (1 + α/3) * |θ| := by
          rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_neg hθneg]; ring
      _ = 13 * |θ| ^ (2 + α/3) := by
          rw [show (2:ℝ) + α/3 = 1 + (1 + α/3) by ring,
            Real.rpow_add' (abs_nonneg θ) (by positivity : (1:ℝ) + (1 + α/3) ≠ 0),
            Real.rpow_one]
          ring
      _ ≤ 20 * |θ| ^ (2 + α/3) := by
          have : (0:ℝ) ≤ |θ| ^ (2 + α/3) := Real.rpow_nonneg (abs_nonneg θ) _
          linarith
  · -- `θ ≥ 0`: `Gzero_eq_neg` plus the one-sided pointwise bound
    have hsub : Set.uIcc 0 θ ⊆ Set.Icc (-1) 1 := by
      intro t ht
      rw [Set.uIcc_of_le hθnn] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hθ1]⟩
    have hintf : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume 0 θ :=
      ((continuousOn_sin_cos_sq_GamBar_Icc α (le_of_lt hα)).mono hsub).intervalIntegrable
    have hintg : IntervalIntegrable (fun t : ℝ => 13 * t ^ (1 + α/3)) volume 0 θ :=
      (continuous_const.mul (Real.continuous_rpow_const hp)).intervalIntegrable _ _
    have hintc : IntervalIntegrable (fun _ : ℝ => 13 * θ ^ (1 + α/3)) volume 0 θ :=
      continuous_const.intervalIntegrable _ _
    calc |Work.FTS.PhiStar.Gzero α θ|
        = |∫ t in 0..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| := by
          rw [Gzero_eq_neg_of_abs_le α hα hα1 hθ, abs_neg]
      _ ≤ ∫ t in 0..θ, |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| :=
          intervalIntegral.abs_integral_le_integral_abs hθnn
      _ ≤ ∫ t in 0..θ, 13 * t ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on hθnn hintf.abs hintg (fun t ht => ?_)
          have ht' : |t| ≤ 1/2 := by rw [abs_of_nonneg ht.1]; linarith [ht.2, hθ1]
          have h := hpt t ht'
          rwa [abs_of_nonneg ht.1] at h
      _ ≤ ∫ t in 0..θ, 13 * θ ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on hθnn hintg hintc (fun t ht => ?_)
          have h := Real.rpow_le_rpow ht.1 ht.2 hp
          linarith
      _ = 13 * θ ^ (1 + α/3) * θ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ = 13 * |θ| ^ (2 + α/3) := by
          rw [abs_of_nonneg hθnn, show (2:ℝ) + α/3 = 1 + (1 + α/3) by ring,
            Real.rpow_add' hθnn (by positivity : (1:ℝ) + (1 + α/3) ≠ 0), Real.rpow_one]
          ring
      _ ≤ 20 * |θ| ^ (2 + α/3) := by
          have : (0:ℝ) ≤ |θ| ^ (2 + α/3) := Real.rpow_nonneg (abs_nonneg θ) _
          linarith

end Work.FTS.PhiStar.Psi0Est
