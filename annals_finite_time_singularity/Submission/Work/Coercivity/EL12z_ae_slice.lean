import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter

/-- If `(z,θ) ↦ (f z θ · w z)²` is integrable on `Iz ×ˢ Iθ`, then for almost every
`z ∈ (0,∞)` the `θ`-slice `θ ↦ f z θ` is square integrable on `Iθ`.

This is Fubini/Tonelli for the slice integral, together with the fact that the radial
weight `w z = (1+z)²/z²` is non-zero for every `z > 0` (so that the factor `w z` can be
divided out). -/
theorem EL12z_ae_slice (f : ℝ → ℝ → ℝ)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ := by
  set g : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2) with hg
  -- `Iz ×ˢ Iθ` carries the product of the two restricted measures
  have hInt : MeasureTheory.Integrable g
      ((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hfw
  -- Fubini: almost every `z`-slice is integrable
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.Integrable (fun θ => g (z, θ))
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
    hInt.prod_right_ae
  -- `(0,∞)` and `Iz = [0,∞)` differ by the null point `0`
  have hmono : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ≤
      (MeasureTheory.volume.restrict Spaces.Iz) :=
    MeasureTheory.Measure.restrict_mono_set volume
      (by intro x hx; exact le_of_lt (Set.mem_Ioi.mp hx))
  have hs : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.Integrable (fun θ => g (z, θ))
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
    MeasureTheory.ae_mono hmono hslice
  filter_upwards [hs,
    MeasureTheory.ae_restrict_mem
      (show MeasurableSet (Set.Ioi (0 : ℝ)) from isOpen_Ioi.measurableSet)] with z hzsl hzpos
  have hzpos' : (0 : ℝ) < z := hzpos
  -- the radial weight does not vanish on `(0,∞)`
  have hzw : Spaces.w z ≠ 0 := by
    have h1 : (1 + z) ≠ 0 := by linarith
    have h2 : z ≠ 0 := ne_of_gt hzpos'
    simp only [Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2)
  -- divide the slice integrand by `(w z)²`, which is legitimate as `w z ≠ 0`
  have h2 : MeasureTheory.Integrable
      (fun θ => ((Spaces.w z) ^ 2)⁻¹ * g (z, θ))
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
    hzsl.const_mul _
  refine h2.congr ?_
  filter_upwards with θ
  simp only [hg, Function.uncurry_apply_pair]
  rw [mul_pow, inv_mul_eq_div]
  field_simp

end Work.Coercivity
