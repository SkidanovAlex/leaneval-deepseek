import Mathlib.Analysis.SpecialFunctions.PolarCoord

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Work.FTS.FireFix.Clauses

/-- **The two-dimensional polar change of variables for a radial density.**

For an a.e.-measurable `H : ℝ → ℝ≥0∞`, the integral of `H (‖v‖)` over the plane `ℝ × ℝ`
equals `2π ∫_0^∞ r H r dr`: the area element in polar coordinates is `r dr dθ` and the angular
measure of a full turn is `2π`.

The proof rewrites `∫⁻ v, H ‖v‖` with Mathlib's polar-coordinate change of variables
(`lintegral_comp_polarCoord_symm`, an open partial homeomorphism with Jacobian `p.1`), reduces
the integrand to `ENNReal.ofReal p.1 * H p.1` in the sector `0 < p.1`, and then applies Tonelli
to the rectangle `(0,∞) × (-π,π)`. -/
theorem xfer_plane_radial {H : ℝ → ENNReal} (hH : AEMeasurable H MeasureTheory.volume) :
    ∫⁻ v : ℝ × ℝ, H (Real.sqrt (v.1 ^ 2 + v.2 ^ 2))
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * H r := by
  -- a.e.-measurability of the radial integrand, on the restricted ray
  have hgaem : AEMeasurable (fun r : ℝ => ENNReal.ofReal r * H r)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ENNReal.measurable_ofReal.aemeasurable.mul (hH.mono_measure restrict_le_self)
  -- pointwise identity in the polar sector `(0,∞) × (-π,π)`
  have hpt : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • H (Real.sqrt (((polarCoord.symm : ℝ × ℝ → ℝ × ℝ) p).1 ^ 2 + ((polarCoord.symm : ℝ × ℝ → ℝ × ℝ) p).2 ^ 2))
        = ENNReal.ofReal p.1 * H p.1 := by
    intro p hp
    have hp1 : 0 < p.1 := (Set.mem_prod.mp hp).1
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have h1 : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2
          = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      rw [h1, Real.cos_sq_add_sin_sq, mul_one]
    have hsqrt : Real.sqrt (((polarCoord.symm : ℝ × ℝ → ℝ × ℝ) p).1 ^ 2 + ((polarCoord.symm : ℝ × ℝ → ℝ × ℝ) p).2 ^ 2) = p.1 := by
      rw [polarCoord_symm_apply]
      change Real.sqrt ((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) = p.1
      rw [hsq, Real.sqrt_sq (le_of_lt hp1)]
    rw [smul_eq_mul, hsqrt]
  -- the sector is the target of the polar map
  have hst : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) = polarCoord.target := by
    rw [polarCoord_target]
  -- a.e.-measurability of the planar integrand for Tonelli
  have hae : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * H p.1)
      ((volume.prod volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) := by
    rw [← prod_restrict]
    exact hgaem.comp_fst
  -- the angular measure of a full turn
  have hvol : volume (Set.Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
    have h2 : Real.pi - -Real.pi = 2 * Real.pi := by ring
    rw [Real.volume_Ioo, h2]
  calc ∫⁻ v : ℝ × ℝ, H (Real.sqrt (v.1 ^ 2 + v.2 ^ 2))
      = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 •
            H (Real.sqrt (((polarCoord.symm : ℝ × ℝ → ℝ × ℝ) p).1 ^ 2 + ((polarCoord.symm : ℝ × ℝ → ℝ × ℝ) p).2 ^ 2)) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * H p.1 := by
        rw [← hst]
        exact setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * H r := by
        have hstep : ∫⁻ z in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
              ENNReal.ofReal z.1 * H z.1 ∂(volume : Measure (ℝ × ℝ))
            = ∫⁻ r in Set.Ioi (0 : ℝ),
                ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal r * H r ∂volume ∂volume :=
          setLIntegral_prod _ hae
        rw [hstep]
        have hinner : ∀ r : ℝ,
            ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal r * H r ∂volume
              = (ENNReal.ofReal r * H r) * volume (Set.Ioo (-Real.pi) Real.pi) :=
          fun r => setLIntegral_const _ _
        simp_rw [hinner, hvol]
        rw [lintegral_mul_const'' _ hgaem, mul_comm]

end Work.FTS.FireFix.Clauses
