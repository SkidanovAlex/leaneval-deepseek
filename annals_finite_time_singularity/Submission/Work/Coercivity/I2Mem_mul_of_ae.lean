import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.H1IPAddDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The elementary AM–GM bound `|a·b| ≤ (a²+b²)/2`, used to dominate the product of two
`L²`-functions by the sum of their squares. -/
private theorem abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  linarith

/-- A product of two `L²`-functions (in the iterated sense of `Spaces.L2Mem`) whose
*slices* are `AEStronglyMeasurable` and whose *joint* version is `AEStronglyMeasurable`
has an honest iterated integral (`I2Mem`).

Pointwise the product is dominated by `(X²+Y²)/2` (AM–GM), so each angular slice is
integrable (`hsl` provides the required measurability), and for each `z ∈ Iz` the slice
integral obeys
`‖∫_θ X z θ Y z θ‖ ≤ ∫_θ |X z θ Y z θ| ≤ ∫_θ (X z θ² + Y z θ²)/2 = (A z + B z)/2`,
where `A z = ∫_θ X z θ²` and `B z = ∫_θ Y z θ²` are the two integrable functions supplied
by `hX.2`, `hY.2`.  The measurability of `z ↦ ∫_θ X z θ Y z θ` is read off from the joint
`AEStronglyMeasurable` hypothesis `hjt`; `Integrable.mono'` then gives the outer
integrability. -/
theorem I2Mem_mul_of_ae (X Y : ℝ → ℝ → ℝ)
    (hX : Spaces.L2Mem X) (hY : Spaces.L2Mem Y)
    (hsl : ∀ z ∈ Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => X z θ * Y z θ)
      (MeasureTheory.volume.restrict Spaces.Iθ))
    (hjt : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2 * Y p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))) :
    I2Mem (fun z θ => X z θ * Y z θ) := by
  have hAM := abs_mul_le_half_sq_add_sq
  -- Every angular slice of the product is integrable.
  have hslice : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => X z θ * Y z θ) Spaces.Iθ := by
    intro z hz
    have hdom : IntegrableOn (fun θ => ((X z θ) ^ 2 + (Y z θ) ^ 2) / 2) Spaces.Iθ :=
      ((hX.1 z hz).add (hY.1 z hz)).div_const 2
    refine Integrable.mono' hdom (hsl z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_eq_abs]
    exact hAM _ _
  refine ⟨hslice, ?_⟩
  -- Measurability of the outer function, from the joint `AEStronglyMeasurable` hypothesis.
  have hFmeas : AEStronglyMeasurable (fun z => ∫ θ in Spaces.Iθ, X z θ * Y z θ)
      (MeasureTheory.volume.restrict Spaces.Iz) := by
    have h := hjt.integral_prod_right' (ν := MeasureTheory.volume.restrict Spaces.Iθ)
    simpa using h
  -- The dominating function `(A z + B z)/2` is integrable.
  have hgint : Integrable
      (fun z => ((∫ θ in Spaces.Iθ, (X z θ) ^ 2) + (∫ θ in Spaces.Iθ, (Y z θ) ^ 2)) / 2)
      (MeasureTheory.volume.restrict Spaces.Iz) := (hX.2.add hY.2).div_const 2
  refine hgint.mono' hFmeas ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iz from measurableSet_Ici)]
    with z hz
  have hXz := hX.1 z hz
  have hYz := hY.1 z hz
  have hdom : IntegrableOn (fun θ => ((X z θ) ^ 2 + (Y z θ) ^ 2) / 2) Spaces.Iθ :=
    (hXz.add hYz).div_const 2
  calc ‖∫ θ in Spaces.Iθ, X z θ * Y z θ‖
      ≤ ∫ θ in Spaces.Iθ, ‖X z θ * Y z θ‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ θ in Spaces.Iθ, |X z θ * Y z θ| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ θ in Spaces.Iθ, ((X z θ) ^ 2 + (Y z θ) ^ 2) / 2 := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Eventually.of_forall fun θ => abs_nonneg _
        · exact hdom
        · filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)]
            with θ hθ
          exact hAM _ _
    _ = ((∫ θ in Spaces.Iθ, (X z θ) ^ 2) + (∫ θ in Spaces.Iθ, (Y z θ) ^ 2)) / 2 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add hXz hYz]

end Work.Coercivity

