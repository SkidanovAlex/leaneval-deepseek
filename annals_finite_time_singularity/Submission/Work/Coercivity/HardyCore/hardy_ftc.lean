/-
# The Hardy integration-by-parts identity `hardy_ftc`

For a continuously differentiable function `g` on `(0,∞)` with derivative `g'`, for which
the "boundary term" `z ↦ g z ^ 2 / z` tends to `0` at `0⁺` and at `+∞`, and for which
`g ^ 2 / z ^ 2` and `g' ^ 2` are integrable on `(0,∞)`, one has

  `∫_0^∞ g(z)² / z² dz = ∫_0^∞ 2 g(z) g'(z) / z dz`.

This is the classical Hardy integration by parts: writing `φ z = g z ^ 2 / z`,
`φ' z = 2 g z g' z / z - g z ^ 2 / z ^ 2` on `(0,∞)`, and `φ → 0` at both ends, so
`∫_0^∞ φ' = 0` (`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`), which rearranges to
the identity.

The integrability of the right-hand side `2 g g' / z` is derived from the two given
integrability hypotheses by the elementary pointwise bound `2 |g/z| |g'| ≤ (g/z)² + g'²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity.HardyCore

open MeasureTheory Set Filter
open scoped Topology

theorem hardy_ftc (g g' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' z) z)
    (h0 : Filter.Tendsto (fun z => g z ^ 2 / z) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0))
    (htop : Filter.Tendsto (fun z => g z ^ 2 / z) Filter.atTop (nhds 0))
    (hA : MeasureTheory.IntegrableOn (fun z => g z ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ)))
    (hB : MeasureTheory.IntegrableOn (fun z => g' z ^ 2) (Set.Ioi (0 : ℝ))) :
    ∫ z in Set.Ioi (0 : ℝ), g z ^ 2 / z ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), 2 * (g z * g' z) / z := by
  -- ## The derivative of `φ z = g z ^ 2 / z` on `(0,∞)`.
  have hphi : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => g z ^ 2 / z) (2 * (g z * g' z) / z - g z ^ 2 / z ^ 2) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1 : HasDerivAt (fun z => g z ^ 2) (2 * g z * g' z) z := by
      have h := (hderiv z hz).pow 2
      have hd : (↑2 * g z ^ (2 - 1) * g' z) = 2 * g z * g' z := by norm_num
      exact h.congr_deriv hd
    have h2 : HasDerivAt (fun z : ℝ => z) 1 z := hasDerivAt_id z
    exact (h1.div h2 hz0).congr_deriv (by field_simp)
  -- ## `2 g g' / z` is a.e. strongly measurable on `(0,∞)`.
  -- On `(0,∞)` it equals `deriv φ + f₂`, a sum of a measurable function (`deriv φ`) and an
  -- a.e. measurable one (`f₂`, from `hA`).
  have hf1_meas : AEStronglyMeasurable (fun z => 2 * (g z * g' z) / z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEStronglyMeasurable (deriv (fun z => g z ^ 2 / z))
        (volume.restrict (Set.Ioi (0 : ℝ))) := (measurable_deriv _).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z => g z ^ 2 / z ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) := hA.aestronglyMeasurable
    refine (h1.add h2).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hd := (hphi z hz).deriv
    show deriv (fun z => g z ^ 2 / z) z + g z ^ 2 / z ^ 2 = 2 * (g z * g' z) / z
    rw [hd]; ring
  -- ## Integrability of the right-hand side, by `2|a b| ≤ a² + b²`.
  have hf1_int : MeasureTheory.IntegrableOn (fun z => 2 * (g z * g' z) / z)
      (Set.Ioi (0 : ℝ)) := by
    refine (hA.add hB).mono' hf1_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : 0 < z := hz
    change ‖2 * (g z * g' z) / z‖ ≤ g z ^ 2 / z ^ 2 + g' z ^ 2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hz0, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hx : 2 * (|g z| * |g' z|) / z = 2 * (|g z| / z) * |g' z| := by field_simp
    rw [hx]
    have h2 : (|g z| / z) ^ 2 = g z ^ 2 / z ^ 2 := by rw [div_pow, sq_abs]
    have h3 : (|g' z|) ^ 2 = g' z ^ 2 := sq_abs (g' z)
    nlinarith [sq_nonneg (|g z| / z - |g' z|)]
  -- ## Integrability of `φ'` on `(0,∞)`.
  have hf'_int : MeasureTheory.IntegrableOn
      (fun z => 2 * (g z * g' z) / z - g z ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ)) :=
    hf1_int.sub hA
  -- ## Continuity of `φ` on `[0,∞)` at `0`, from the one-sided limit `h0`.
  have hcont : ContinuousWithinAt (fun z => g z ^ 2 / z) (Set.Ici (0 : ℝ)) 0 := by
    have hpure : Tendsto (fun z => g z ^ 2 / z) (𝓝[{(0 : ℝ)}] 0) (𝓝 (g 0 ^ 2 / 0)) := by
      rw [nhdsWithin_singleton]; exact tendsto_pure_nhds _ 0
    have hgt : Tendsto (fun z => g z ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 (g 0 ^ 2 / 0)) := by
      simpa only [div_zero] using h0
    have h3 := hgt.sup hpure
    rw [nhdsGT_sup_nhdsWithin_singleton] at h3
    exact h3
  -- ## The fundamental theorem of calculus on `(0,∞)`: `∫_0^∞ φ' = 0`.
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := (0 : ℝ))
    (f := fun z => g z ^ 2 / z) (f' := fun z => 2 * (g z * g' z) / z - g z ^ 2 / z ^ 2)
    hcont hphi hf'_int htop
  simp only [div_zero, sub_zero] at hftc
  -- ## Split the integral and conclude.
  rw [MeasureTheory.integral_sub hf1_int hA] at hftc
  linarith

end Work.Coercivity.HardyCore
