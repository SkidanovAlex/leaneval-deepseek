import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set

/-- Fubini–Tonelli step underlying `marginal`: for a function which is jointly integrable on
`ℝ × Iθ` after multiplication of the second variable by `w`, the integral over the second
variable may be computed in either order, and the outer iterated integral is integrable.

The point is that `w θ` is a constant as far as the inner (`s`-)integration is concerned, so
`∫ s, G s θ * w θ = (∫ s, G s θ) * w θ` for *every* `θ`, and then the two iterated integrals
are the two iterated integrals of a single integrable function on the product, hence equal by
Fubini. -/
private theorem marginal_aux (G : ℝ → ℝ → ℝ) (w : ℝ → ℝ)
    (hJ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => G p.1 p.2 * w p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => (∫ s in Set.univ, G s θ) * w θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, (∫ s in Set.univ, G s θ) * w θ)
        = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, G p.1 p.2 * w p.2 := by
  -- Regard the integrand as a function on the product, with `s` the first variable.
  have hprod : MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2 * w p.2)
      ((MeasureTheory.volume.restrict (Set.univ : Set ℝ)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Measure.prod_restrict]
    exact hJ
  -- Fubini, symmetric form: the product integral is the iterated integral with the
  -- second variable outermost.
  have hsymm := MeasureTheory.integral_prod_symm (fun p : ℝ × ℝ => G p.1 p.2 * w p.2) hprod
  constructor
  · -- Integrability of the outer iterated integral.
    have hInt : MeasureTheory.Integrable
        (fun θ => ∫ s, G s θ * w θ ∂(MeasureTheory.volume.restrict (Set.univ : Set ℝ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hprod.integral_prod_right
    rw [show (fun θ => (∫ s in Set.univ, G s θ) * w θ)
        = fun θ => ∫ s, G s θ * w θ ∂(MeasureTheory.volume.restrict (Set.univ : Set ℝ)) from by
      funext θ
      rw [integral_mul_const]]
    exact hInt
  · -- The two iterated integrals agree.
    rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, hsymm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    rw [integral_mul_const]

theorem marginal (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hJ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => (∫ s in Set.univ,
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    ∧ (∫ θ in Work.Spaces.Iθ, (∫ s in Set.univ, (Work.Spaces.pz u s θ - b * u s θ) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE θ)
        = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 := by
  exact marginal_aux (fun s θ => (Work.Spaces.pz u s θ - b * u s θ) ^ 2)
    Work.FTS.EllSol.FlatFT.wE hJ

end Work.FTS.EllSol.ShiftFT.Aux2
