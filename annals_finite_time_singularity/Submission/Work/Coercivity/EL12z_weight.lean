import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter

/-- The plain `1/z²` piece of the weighted `L²` energy `Ef`:

`∫_{z>0} (∫_θ f(z,θ)² dθ)/z² ≤ ∫∫_{[0,∞)×[0,π/2]} (f(z,θ) w(z))² dθ dz`.

The point is simply that `1/z² ≤ w(z)²` on `(0,∞)`, where `w(z) = (1+z)²/z²`;
the hypothesis `hfw` (joint integrability of `(f w)²`) is used through Fubini to
make the right-hand side available as an integrable majorant. -/
theorem EL12z_weight (f : ℝ → ℝ → ℝ)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ) :
    ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2 ≤ Ef f := by
  -- abbreviations for the two slice integrals
  set G : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (f z θ) ^ 2 with hGdef
  set H : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2 with hHdef
  set g : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2) with hgdef
  -- joint integrability of `(z,θ) ↦ (f z θ w z)²` on the product `Iz ×ˢ Iθ`
  have hInt : MeasureTheory.Integrable g
      ((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hfw
  -- Fubini: the `θ`-slice integrals form an integrable function of `z`
  have hH_int : MeasureTheory.Integrable H (MeasureTheory.volume.restrict Spaces.Iz) := by
    have h := hInt.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hgdef, Function.uncurry_apply_pair, hHdef]
  -- the slice integrals of `(f w)²` are the pointwise product `w² · G`
  have hHeq : H =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => (Spaces.w z) ^ 2 * G z) := by
    filter_upwards with z
    simp only [hHdef, hGdef]
    calc ∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2
        = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * (f z θ) ^ 2 := by
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun θ => ?_)
          ring
      _ = (Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2 :=
          MeasureTheory.integral_const_mul _ _
  -- `(0,∞) ⊆ Iz = [0,∞)`, so integrability descends to the smaller measure
  have hle : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      ≤ MeasureTheory.volume.restrict Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set volume
      (fun x hx => le_of_lt (Set.mem_Ioi.mp hx))
  have hH_int' : MeasureTheory.Integrable H
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hH_int.mono_measure hle
  have hGint : MeasureTheory.Integrable (fun z => (Spaces.w z) ^ 2 * G z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hH_int'.congr hHeq
  -- `G z ≥ 0`
  have hG_nonneg : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ G z := by
    intro z _
    simp only [hGdef]
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- the pointwise comparison `1/z² ≤ w(z)²` on `(0,∞)`
  have hineq_all : ∀ z ∈ Set.Ioi (0 : ℝ), (z ^ 2)⁻¹ ≤ (Spaces.w z) ^ 2 := by
    intro z hz
    have hzpos : 0 < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    rw [Spaces.w]
    field_simp
    nlinarith [sq_nonneg z]
  -- main comparison, with `w² · G` as integrable majorant
  have hmain : ∫ z in Set.Ioi (0 : ℝ), G z / z ^ 2
      ≤ ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hGint ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet (Set.Ioi (0 : ℝ)) from isOpen_Ioi.measurableSet)] with z hz
      exact div_nonneg (hG_nonneg z hz) (sq_nonneg z)
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet (Set.Ioi (0 : ℝ)) from isOpen_Ioi.measurableSet)] with z hz
      have hGz := hG_nonneg z hz
      rw [div_eq_mul_inv]
      calc G z * (z ^ 2)⁻¹ ≤ G z * (Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_left (hineq_all z hz) hGz
        _ = (Spaces.w z) ^ 2 * G z := by ring
  -- identify the majorant integral with `Ef f`
  have hEq : ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z = Ef f := by
    have h6a : ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z
        = ∫ z in Set.Ioi (0 : ℝ), H z :=
      MeasureTheory.integral_congr_ae hHeq.symm
    have h6b : ∫ z in Set.Ioi (0 : ℝ), H z = ∫ z in Spaces.Iz, H z := by
      rw [Spaces.Iz]
      exact MeasureTheory.integral_Ici_eq_integral_Ioi.symm
    have h6c : ∫ z in Spaces.Iz, H z = Ef f := by
      simp only [Ef, Spaces.L2Sq, hHdef]
    rw [h6a, h6b, h6c]
  calc ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), G z / z ^ 2 := by simp only [hGdef]
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z := hmain
    _ = Ef f := hEq

end Work.Coercivity
