import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.Finiteness.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Polar transfer on the right half-plane

`Work.FTS.FireFix.Clauses.xfer_halfline_polar` is the two-dimensional polar change of
variables for the right half-plane `{x > 0}` (in the *unnormalised* form in which the
jacobian `ρ` is absorbed into the angular weight):

`∫⁻_{(x,y), x > 0} x · K x y  =  ∫⁻_{(ρ,θ), ρ > 0, |θ| < π/2} ρ² cos θ · K (ρ cos θ) (ρ sin θ)`.

It is the polar counterpart of `xfer_plane_radial`/`xfer_scaling_rpow` (the radial transfers),
and is what turns a half-line integral of a radial profile into the analogous integral in the
angular variable of the physical firing construction.

The proof writes the left-hand side as the image of `(0,∞) × (-π/2, π/2)` under the polar
parametrisation `polarCoord.symm (ρ, θ) = (ρ cos θ, ρ sin θ)` (Mathlib's
`Real.polarCoord`), which is a diffeomorphism of that strip onto the right half-plane, and
applies `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` whose jacobian
determinant is `ρ`.  No measurability of `K` is needed: the change-of-variables formula in
`lintegral` form holds for arbitrary `ℝ≥0∞`-valued integrands.
-/

namespace Work.FTS.FireFix.Clauses

open MeasureTheory Set ENNReal

/-- The polar parametrisation `(ρ, θ) ↦ (ρ cos θ, ρ sin θ)` maps the strip
`(0,∞) × (-π/2, π/2)` bijectively onto the right half-plane `{x > 0}`. -/
private lemma polar_symm_image_strip :
    polarCoord.symm '' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
      = Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [polarCoord_symm_apply]
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
    exact mul_pos hp.1 (Real.cos_pos_of_mem_Ioo hp.2)
  · rintro ⟨x, y⟩ hx
    have hx' : 0 < x := hx.1
    have hz0 : (⟨x, y⟩ : ℂ) ≠ 0 := by
      intro h
      have h1 : (⟨x, y⟩ : ℂ).re = (0 : ℂ).re := congrArg Complex.re h
      rw [show (⟨x, y⟩ : ℂ).re = x from rfl] at h1
      simp at h1
      linarith
    refine ⟨(‖(⟨x, y⟩ : ℂ)‖, (⟨x, y⟩ : ℂ).arg), ⟨?_, ?_⟩, ?_⟩
    · exact norm_pos_iff.2 hz0
    · have h : |(⟨x, y⟩ : ℂ).arg| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.2
          (Or.inl (by rw [show (⟨x, y⟩ : ℂ).re = x from rfl]; exact hx'))
      exact abs_lt.1 h
    · rw [polarCoord_symm_apply, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]

theorem xfer_halfline_polar {K : ℝ → ℝ → ENNReal}
    (hK : AEMeasurable (fun p : ℝ × ℝ => K p.1 p.2) MeasureTheory.volume) :
    ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal p.1 * K p.1 p.2
      = ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
          ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * K (q.1 * Real.cos q.2) (q.1 * Real.sin q.2) := by
  have hs : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ polarCoord.target := by
    intro p hp
    rw [show polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl]
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨hp.1, ⟨by linarith [Real.pi_pos, hp.2.1], by linarith [Real.pi_pos, hp.2.2]⟩⟩
  rw [← polar_symm_image_strip]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    (Set.InjOn.mono hsub polarCoord.symm.injOn)]
  refine setLIntegral_congr_fun hs (fun q hq => ?_)
  rw [Set.mem_prod] at hq
  have hq1 : 0 < q.1 := hq.1
  have h2 : ENNReal.ofReal q.1 * ENNReal.ofReal (q.1 * Real.cos q.2)
      = ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) := by
    rw [← ENNReal.ofReal_mul (le_of_lt hq1)]
    congr 1
    ring
  simp only [polarCoord_symm_apply, det_fderivPolarCoordSymm]
  rw [abs_of_pos hq1, ← h2]
  ring

end Work.FTS.FireFix.Clauses
