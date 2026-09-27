import Mathlib
import Submission.Work.EKLC6Core.AtomInfoSetup

/-!
# `EKLC6Core.ShapeAvgDefs` — the leafwise shape average

`shapeAvg t S U ν g x` is the `ν x`-average of `g` over the `U`-shape `Wsh t S U x` of the
pull-back atom of `x` (the conditioning σ-algebra is `betaAlg t S = comap (aDiag t ·) S.m`).

The main consumer is `Work.EKLC6Core.lintegral_shapeAvg_eq`:

    ∫⁻ x, shapeAvg t S U ν g x ∂μ = ∫⁻ x, g x ∂μ,

i.e. the shape average is the conditional expectation of `g` w.r.t. the pull-back plaque
algebra, hence measure preserving on `μ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The leafwise average of `g` over the `U`-shape of the pull-back atom:
`(ν x)`-average of `u ↦ g (u • x)` over `Wsh t S U x`. -/
def shapeAvg (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (U : Subgroup SL3)
    (ν : X3 → Measure SL3) (g : X3 → ENNReal) : X3 → ENNReal :=
  fun x => (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x)) / (ν x (Wsh t S U x))

@[simp] theorem shapeAvg_def (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (U : Subgroup SL3)
    (ν : X3 → Measure SL3) (g : X3 → ENNReal) (x : X3) :
    shapeAvg t S U ν g x =
      (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) := rfl

/-- Pointwise monotonicity of the shape average. -/
theorem shapeAvg_mono {t : Fin 3 → ℝ} {S : Work.EKLRelCross.MSAlg} {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {g g' : X3 → ENNReal} (h : ∀ x, g x ≤ g' x) (x : X3) :
    shapeAvg t S U ν g x ≤ shapeAvg t S U ν g' x := by
  simp only [shapeAvg_def]
  exact ENNReal.div_le_div_right
    (MeasureTheory.lintegral_mono (f := fun u : SL3 => g (u • x))
      (g := fun u : SL3 => g' (u • x)) fun u => h (u • x)) _

/-- Pointwise congruence of the shape average. -/
theorem shapeAvg_congr {t : Fin 3 → ℝ} {S : Work.EKLRelCross.MSAlg} {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {g g' : X3 → ENNReal} (h : ∀ x, g x = g' x) :
    shapeAvg t S U ν g = shapeAvg t S U ν g' := by
  funext x
  simp only [shapeAvg_def]
  rw [lintegral_congr fun u => h (u • x)]

end Work.EKLC6Core

end
