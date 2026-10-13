/-
# `QuadMeasAux` — a.e. strong measurability of functions continuous on the open quadrant

The measurability statement `Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas` is about the product
measure `volume` on `(0,∞)` times `volume` on `Iθ = [0,π/2]`.  This file provides the two
elementary bridges between that measure and the open quadrant `Qd = (0,∞) × (0,π/2)`:

* `QdMeas`, the product measure of the statement;
* `qd_ae`, the a.e. equality `(0,∞) × Iθ =ᵐ Qd` (the difference is contained in the two lines
  `θ = 0`, `θ = π/2`, of measure zero);
* `aesm_of_contOn_Qd`: a function continuous on the open quadrant is a.e. strongly measurable;
* `aesm_of_smoothQuad`: a function in `Work.FTS.LocData.SmoothQuad` (that is, `C^∞` on the
  open strip `(-1,∞) × (0,π/2)`) is a.e. strongly measurable for `QdMeas`.

The proof is the same argument as `Work.Spaces.aesm_of_continuousOn_Qd`, with `Iz = [0,∞)`
replaced by the half line `Ioi 0` and `Iθ` by the open interval `(0,π/2)`: the product measure
of the restrictions is the restriction of the planar measure to the product, and the two
products agree up to a null set.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-- The product measure of the statement: `volume` restricted to `(0,∞)`, times `volume`
restricted to `Iθ = [0,π/2]`. -/
abbrev QdMeas : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The open quadrant `(0,∞) × (0,π/2)` of the interior estimates. -/
abbrev Qd2 : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

/-- `(0,∞) × Iθ` and the open quadrant agree outside the two angular boundary lines, a null
set. -/
theorem qd_ae : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
    =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Qd2 :=
  MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _)
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm

/-- A function continuous on the open quadrant is a.e. strongly measurable for the product
measure `QdMeas`. -/
theorem aesm_of_contOn_Qd {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) Qd2) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas := by
  have hUm : MeasurableSet Qd2 := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Qd2) :=
    hf.aestronglyMeasurable hUm
  rw [QdMeas, MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set qd_ae]
  exact hmain

/-- `SmoothQuad` (that is `C^∞` on the open strip `(-1,∞) × (0,π/2)`) implies a.e. strong
measurability for `QdMeas`. -/
theorem aesm_of_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas :=
  aesm_of_contOn_Qd (h.continuousOn.mono fun p hp =>
    ⟨show (-1 : ℝ) < p.1 by linarith [show (0 : ℝ) < p.1 from hp.1], hp.2⟩)

end Work.FTS.Nonlinear.Pieces.rl1Tools
