import Submission.PotentialDefs
import Submission.EquilibriumMeasure
import Submission.LogAffineCosIntegral
import Submission.EquilibriumPotentialIcc
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Equilibrium potential bound at real points (A1, real case)

For `c < d` and every REAL `x`, the equilibrium potential satisfies

    logPotential (equilibrium c d) (x : ℂ) ≤ logCap c d = −log((d−c)/4)

with equality when `x ∈ [c,d]` (that equality is A1′,
`EquilibriumPotentialIcc.equilibrium_potential_on_Icc`, already proved).

For `x` outside the interval the value is computed exactly.  For example with
`x > d`: writing `x(t) = (c+d)/2 + (d−c)/2·cos t` we have `x − x(t) > 0`, and
by `Submission.LogAffineCosIntegral.integral_log_affine_cos` with
`A = x − (c+d)/2`, `B = (d−c)/2`:

    U(x) = (1/π)∫₀^π −log(x − x(t)) dt
         = −log((x − (c+d)/2 + √((x−(c+d)/2)² − ((d−c)/2)²))/2) .

The argument `(A + √(A²−B²))/2` is ≥ `(d−c)/4` (minimal at `A = B`, i.e.
`x = d`), so `U(x) ≤ −log((d−c)/4) = logCap c d`.  The case `x < c` is
symmetric (`|x − x(t)| = x(t) − x`, `A = (c+d)/2 − x`).
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.EquilibriumPotentialBoundReal

open Submission.PotentialDefs
open Submission.Equilibrium
open Submission.LogAffineCosIntegral
open Submission.EquilibriumPotentialIcc

/-! ## Reduction of the potential at a real point to an interval integral -/

/-- `U^{μ_eq}(x) = −π⁻¹·∫₀^π log|x − (mid + half·cos t)| dt` for real `x`. -/
private lemma logPotential_eq_neg {c d x : ℝ} :
    logPotential (equilibrium c d) (x : ℂ) =
      -((Real.pi)⁻¹ * (∫ t in (0 : ℝ)..Real.pi,
        Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|)) := by
  unfold logPotential equilibrium
  have h1 : (∫ t : ℝ, -Real.log ‖(x : ℂ) - (t : ℂ)‖ ∂Measure.map (chart c d) uniform01) =
      (∫ u : ℝ, -Real.log ‖(x : ℂ) - (chart c d u : ℂ)‖ ∂uniform01) := by
    exact MeasureTheory.integral_map (φ := chart c d) (μ := uniform01)
      (f := fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖)
      (chart_measurable c d).aemeasurable
      (by
        have hmeas : Measurable fun t : ℝ => -Real.log ‖(x : ℂ) - (t : ℂ)‖ := by
          fun_prop
        exact hmeas.aestronglyMeasurable)
  rw [h1]
  have hfun : (fun u : ℝ => -Real.log ‖(x : ℂ) - (chart c d u : ℂ)‖) =
      fun u : ℝ => -Real.log |x - chart c d u| := by
    funext u
    exact log_norm_sub_ofReal x (chart c d u)
  rw [hfun]
  rw [uniform01_integral]
  let M : ℝ → ℝ := fun t => -Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|
  have hMpi : (fun u : ℝ => -Real.log |x - chart c d u|) = fun u : ℝ => M (Real.pi * u) := by
    funext u
    dsimp [M]
    unfold chart
    rfl
  rw [hMpi]
  calc
    (∫ u in (0 : ℝ)..1, M (Real.pi * u))
        = (Real.pi)⁻¹ • (∫ t in Real.pi * (0 : ℝ)..Real.pi * (1 : ℝ), M t) := by
            exact intervalIntegral.integral_comp_mul_left (f := M) (c := Real.pi)
              (a := (0 : ℝ)) (b := (1 : ℝ)) (by positivity : (Real.pi : ℝ) ≠ 0)
    _ = (Real.pi)⁻¹ * (∫ t in (0 : ℝ)..Real.pi, M t) := by
            rw [smul_eq_mul, mul_zero, mul_one]
    _ = -((Real.pi)⁻¹ * (∫ t in (0 : ℝ)..Real.pi,
          Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|)) := by
          have hneg : (∫ t in (0 : ℝ)..Real.pi, M t) =
              -((∫ t in (0 : ℝ)..Real.pi,
                  Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|)) := by
            dsimp [M]
            rw [intervalIntegral.integral_neg]
          rw [hneg]
          ring

/-! ## The integral `∫₀^π log(A − B·cos t) dt` (reflection of the affine identity) -/

/-- `∫₀^π log(A − B·cos t) dt = π·log((A + √(A²−B²))/2)` for `0 < B < A`. -/
private lemma intervalIntegral_log_sub_cos {A B : ℝ} (hB : 0 < B) (hBA : B < A) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log (A - B * Real.cos t)) =
      Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) := by
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log (A - B * Real.cos t))
        = (∫ t in (Real.pi - Real.pi)..(Real.pi - 0), Real.log (A - B * Real.cos t)) := by
            rw [show Real.pi - Real.pi = (0 : ℝ) by ring,
              show Real.pi - (0 : ℝ) = Real.pi by ring]
    _ = (∫ t in (0 : ℝ)..Real.pi, Real.log (A - B * Real.cos (Real.pi - t))) := by
            rw [intervalIntegral.integral_comp_sub_left
              (f := fun t : ℝ => Real.log (A - B * Real.cos t)) (d := Real.pi)]
    _ = (∫ t in (0 : ℝ)..Real.pi, Real.log (A + B * Real.cos t)) := by
            apply intervalIntegral.integral_congr
            intro t ht
            change Real.log (A - B * Real.cos (Real.pi - t)) =
              Real.log (A + B * Real.cos t)
            rw [Real.cos_pi_sub]
            congr 1
            ring
    _ = Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - B ^ 2)) / 2) :=
            integral_log_affine_cos hB hBA

/-! ## Exact values outside the interval -/

/-- For `x > d`: `∫₀^π log|x − (mid + half·cos t)| = π·log((x−mid+√((x−mid)²−half²))/2)`. -/
private lemma intervalIntegral_log_abs_cos_gt {c d x : ℝ} (hcd : c < d) (hdx : d < x) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|) =
      Real.pi * Real.log ((x - (c + d) / 2 +
        Real.sqrt ((x - (c + d) / 2) ^ 2 - ((d - c) / 2) ^ 2)) / 2) := by
  let m : ℝ := (c + d) / 2
  let r : ℝ := (d - c) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hcd) (by norm_num)
  have hAr : r < x - m := by
    dsimp [m, r]
    linarith
  have hpt : (fun t : ℝ => Real.log |x - (m + r * Real.cos t)|) =
      fun t : ℝ => Real.log ((x - m) - r * Real.cos t) := by
    funext t
    have harg : x - (m + r * Real.cos t) = (x - m) - r * Real.cos t := by ring
    rw [harg, Real.log_abs]
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|)
        = (∫ t in (0 : ℝ)..Real.pi, Real.log |x - (m + r * Real.cos t)|) := by rfl
    _ = (∫ t in (0 : ℝ)..Real.pi, Real.log ((x - m) - r * Real.cos t)) := by
            rw [hpt]
    _ = Real.pi * Real.log ((x - m + Real.sqrt ((x - m) ^ 2 - r ^ 2)) / 2) := by
            exact intervalIntegral_log_sub_cos (A := x - m) (B := r) hr hAr
    _ = Real.pi * Real.log ((x - (c + d) / 2 +
          Real.sqrt ((x - (c + d) / 2) ^ 2 - ((d - c) / 2) ^ 2)) / 2) := by
            dsimp [m, r]

/-- For `x < c`: `∫₀^π log|x − (mid + half·cos t)| = π·log((mid−x+√((mid−x)²−half²))/2)`. -/
private lemma intervalIntegral_log_abs_cos_lt {c d x : ℝ} (hcd : c < d) (hxc : x < c) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|) =
      Real.pi * Real.log (((c + d) / 2 - x +
        Real.sqrt (((c + d) / 2 - x) ^ 2 - ((d - c) / 2) ^ 2)) / 2) := by
  let m : ℝ := (c + d) / 2
  let r : ℝ := (d - c) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hcd) (by norm_num)
  have hAr : r < m - x := by
    dsimp [m, r]
    linarith
  have hpt : (fun t : ℝ => Real.log |x - (m + r * Real.cos t)|) =
      fun t : ℝ => Real.log ((m - x) + r * Real.cos t) := by
    funext t
    rw [abs_sub_comm]
    have harg : (m + r * Real.cos t) - x = (m - x) + r * Real.cos t := by ring
    rw [harg, Real.log_abs]
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|)
        = (∫ t in (0 : ℝ)..Real.pi, Real.log |x - (m + r * Real.cos t)|) := by rfl
    _ = (∫ t in (0 : ℝ)..Real.pi, Real.log ((m - x) + r * Real.cos t)) := by
            rw [hpt]
    _ = Real.pi * Real.log ((m - x + Real.sqrt ((m - x) ^ 2 - r ^ 2)) / 2) := by
            exact integral_log_affine_cos hr hAr
    _ = Real.pi * Real.log (((c + d) / 2 - x +
          Real.sqrt (((c + d) / 2 - x) ^ 2 - ((d - c) / 2) ^ 2)) / 2) := by
            dsimp [m, r]

/-! ## The elementary bound on the log-argument -/

/-- `−log((A+√(A²−r²))/2) ≤ −log(r/2)` for `0 < r ≤ A`. -/
private lemma neg_log_arg_le {A r : ℝ} (hr : 0 < r) (hAr : r ≤ A) :
    -Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2) ≤ -Real.log (r / 2) := by
  have hsq : 0 ≤ Real.sqrt (A ^ 2 - r ^ 2) := Real.sqrt_nonneg _
  have hbound : r / 2 ≤ (A + Real.sqrt (A ^ 2 - r ^ 2)) / 2 := by
    calc
      r / 2 ≤ A / 2 := div_le_div_of_nonneg_right hAr (by norm_num)
      _ ≤ (A + Real.sqrt (A ^ 2 - r ^ 2)) / 2 :=
            div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hlog := Real.log_le_log (div_pos hr (by norm_num)) hbound
  linarith

/-! ## The bound in each outer case -/

/-- The bound for `x < c`. -/
private lemma bound_lt {c d x : ℝ} (hcd : c < d) (hxc : x < c) :
    logPotential (equilibrium c d) (x : ℂ) ≤ logCap c d := by
  rw [logPotential_eq_neg]
  rw [intervalIntegral_log_abs_cos_lt hcd hxc]
  let A : ℝ := (c + d) / 2 - x
  let r : ℝ := (d - c) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hcd) (by norm_num)
  have hAr : r ≤ A := by
    dsimp [A, r]
    linarith
  change -((Real.pi)⁻¹ * (Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2)))
    ≤ logCap c d
  have hpi : (Real.pi)⁻¹ * (Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2)) =
      Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ (Real.pi_ne_zero), one_mul]
  rw [hpi]
  have hlog := neg_log_arg_le hr hAr
  have hcap : -Real.log (r / 2) = logCap c d := by
    unfold logCap
    have hEq : r / 2 = (d - c) / 4 := by dsimp [r]; ring
    rw [hEq]
  exact le_trans hlog (le_of_eq hcap)

/-- The bound for `x > d`. -/
private lemma bound_gt {c d x : ℝ} (hcd : c < d) (hdx : d < x) :
    logPotential (equilibrium c d) (x : ℂ) ≤ logCap c d := by
  rw [logPotential_eq_neg]
  rw [intervalIntegral_log_abs_cos_gt hcd hdx]
  let A : ℝ := x - (c + d) / 2
  let r : ℝ := (d - c) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hcd) (by norm_num)
  have hAr : r ≤ A := by
    dsimp [A, r]
    linarith
  change -((Real.pi)⁻¹ * (Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2)))
    ≤ logCap c d
  have hpi : (Real.pi)⁻¹ * (Real.pi * Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2)) =
      Real.log ((A + Real.sqrt (A ^ 2 - r ^ 2)) / 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ (Real.pi_ne_zero), one_mul]
  rw [hpi]
  have hlog := neg_log_arg_le hr hAr
  have hcap : -Real.log (r / 2) = logCap c d := by
    unfold logCap
    have hEq : r / 2 = (d - c) / 4 := by dsimp [r]; ring
    rw [hEq]
  exact le_trans hlog (le_of_eq hcap)

/-- The equilibrium potential of `[c,d]` at a real point is at most `logCap c d`. -/
theorem equilibrium_potential_bound_real {c d x : ℝ} (hcd : c < d) :
    logPotential (equilibrium c d) (x : ℂ) ≤ logCap c d := by
  by_cases hx : x ∈ Set.Icc c d
  · exact le_of_eq (equilibrium_potential_on_Icc hcd hx)
  · have hlt : x < c ∨ d < x := by
      by_cases h1 : x < c
      · exact Or.inl h1
      · right
        have hclx : c ≤ x := le_of_not_gt h1
        have hxnd : ¬ x ≤ d := by
          intro hxd
          exact hx ⟨hclx, hxd⟩
        exact lt_of_not_ge hxnd
    rcases hlt with hxc | hdx
    · exact bound_lt hcd hxc
    · exact bound_gt hcd hdx

end Submission.EquilibriumPotentialBoundReal
