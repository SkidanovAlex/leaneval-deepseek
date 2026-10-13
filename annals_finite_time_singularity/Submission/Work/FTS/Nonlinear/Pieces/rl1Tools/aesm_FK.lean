/-
# `aesm_FK` — a.e. strong measurability of the angular moment `FK g`

The statement: if the datum `g` is a.e. strongly measurable for the product measure
`QdMeas = volume ↾ (0,∞) ⊗ volume ↾ Iθ`, then so is the `z`-only function
`z ↦ FK g z = ∫_θ K(θ) g(z,θ) dθ`, viewed (via `Function.uncurry`) as a function on
`ℝ × ℝ`.

The proof is the measurability-of-parametric-Bochner-integrals argument:

* `p ↦ K p.2` is (strongly) measurable, so the joint integrand
  `p ↦ Function.uncurry g p * K p.2` is a.e. strongly measurable for `QdMeas`;
* `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` then says the parametric
  integral `z ↦ ∫_θ (that integrand) (z,θ) ∂(volume ↾ Iθ)` is a.e. strongly measurable
  for `volume ↾ (0,∞)` — no integrability is needed, since a Bochner integral of a
  non-integrable function is `0` and the statement concerns only measurability;
* finally `AEStronglyMeasurable.comp_fst` pushes the conclusion along the projection
  `Prod.fst`, which is quasi-measure-preserving for the product measure (the angular
  factor `volume ↾ Iθ` is finite, hence s-finite).

Nothing is used about `K` beyond its measurability, nor about `Iθ` beyond the
s-finiteness of its restricted measure.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.QuadMeasAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

theorem aesm_FK {g : ℝ → ℝ → ℝ}
    (hg : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK g z))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
  -- the angular weight `θ ↦ K θ` is measurable, hence a.e. strongly measurable
  have hK : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
    have : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      simp only [Work.Spaces.K]
      fun_prop
    exact this.aestronglyMeasurable
  -- the joint integrand `(z,θ) ↦ g z θ * K θ` is a.e. strongly measurable
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Function.uncurry g p * Work.Spaces.K p.2)
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := hg.mul hK
  -- measurability of the parametric Bochner integral in `z`
  have hz : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, Function.uncurry g (z, θ) * Work.Spaces.K θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hprod.integral_prod_right'
  -- push along `Prod.fst` (quasi-measure-preserving: the angular factor is finite)
  have hmain := hz.comp_fst (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  show MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Construction.FK g p.1)
    ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
  exact hmain

end Work.FTS.Nonlinear.Pieces.rl1Tools
