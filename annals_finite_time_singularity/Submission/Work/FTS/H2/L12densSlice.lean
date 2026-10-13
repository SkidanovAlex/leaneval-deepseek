import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.Coercivity.K_facts
import Submission.Work.Coercivity.integral_Itheta_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set

namespace Work.FTS.H2

/-- The `L₁₂` density of the elliptic section is the fundamental-model density for the
angular weight `K = 3 sin θ cos²θ`: the two definitions differ only by `Ktheta_eq_K`, and
`Work.Spaces.Iθ` is definitionally `Icc 0 (π/2)`. -/
theorem L12dens_eq_FM_K (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12dens f z = Work.FM.L12dens Work.Spaces.K f z := by
  simp only [Work.Elliptic.L12dens, Work.FM.L12dens, Work.Elliptic.Ktheta_eq_K,
    Work.Spaces.Iθ]

/-- The angular slice `θ ↦ f z θ` of a `SmoothNbhd` function is continuous on the compact
`Iθ`, hence its square is integrable there. -/
theorem slice_sq_integrableOn {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  -- The slice map `θ ↦ (z,θ)` sends `Iθ` into the open neighbourhood `U` of `SmoothNbhd`.
  have ht : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hz], by
      simp only [Set.mem_Ioo]
      exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have hcont : ContinuousOn (fun θ : ℝ => f z θ) Work.Spaces.Iθ :=
    hsm.continuousOn.comp (f := fun θ : ℝ => (z, θ)) (g := Function.uncurry f)
      ((continuous_const.prodMk continuous_id).continuousOn) ht
  have hsq : ContinuousOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := hcont.pow 2
  exact hsq.integrableOn_compact (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)

/-- Elementary square-root algebra: if `x² ≤ 3 X / z²` with `X ≥ 0` and `z > 0`, then
`|x| ≤ √3 · √X / z`. -/
theorem abs_le_sqrt_three_mul_sqrt_div {x X z : ℝ} (hz : 0 < z) (hX : 0 ≤ X)
    (h : x ^ 2 ≤ 3 * X / z ^ 2) : |x| ≤ Real.sqrt 3 * Real.sqrt X / z := by
  calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ Real.sqrt (3 * X / z ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt 3 * Real.sqrt X / z := by
        rw [Real.sqrt_div (by positivity) (z ^ 2), Real.sqrt_mul (by norm_num) X,
          Real.sqrt_sq hz.le]

/-- The angular Cauchy–Schwarz bound for the `L₁₂` density on a single radial slice: for `f`
smooth on an open neighbourhood of the closed quadrant and `z > 0`,
`|L₁₂dens(f)(z)| ≤ √3 · √(∫_θ f(z,θ)²) / z`.

This is `Work.Coercivity.L12dens_sq_slice` — for `z > 0`,
`(L₁₂^K(f)(z))² ≤ 3 (∫_θ f(z,θ)²)/z²` for the weight `K = 3 sin θ cos²θ` with `∫_θ K = 1`
(`Work.Coercivity.integral_Itheta_K`, `Work.Coercivity.K_facts`) — after identifying
`Work.Elliptic.L12dens f = Work.FM.L12dens Work.Spaces.K f` (they differ only by
`Work.Elliptic.Ktheta_eq_K`, and `Work.Spaces.Iθ` is definitionally `Icc 0 (π/2)`), together
with `√(a²) = |a|` and `√(3X/z²) = √3 √X / z` for `z > 0` (`Real.sqrt_div`, `Real.sqrt_mul`).
The slice integrability hypothesis of `L12dens_sq_slice` is supplied by `SmoothNbhd f`
(the angular slice `θ ↦ f z θ` is continuous on the compact `Iθ`, see
`ContinuousOn.integrableOn_compact`). -/
theorem L12densSlice (f : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.L12dens f z|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z := by
  have hsl := slice_sq_integrableOn hsm hz
  have hsq := Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hz hsl
  have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      fun θ _ => by positivity
  rw [L12dens_eq_FM_K f z]
  exact abs_le_sqrt_three_mul_sqrt_div hz hX hsq

end Work.FTS.H2
