import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.windowedMul_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.BSKinetic.IterKernelAux

open MeasureTheory

/-- The moving window is `bsWin ℓ u = χ_ℓ(· − ℓu)`, definitionally. -/
lemma bsWin_eq_chiScale_comp_subRight (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.bsWin ℓ u
      = Submission.BoseGases.chiScale ℓ ∘ ⇑(Homeomorph.subRight (ℓ • u)) := rfl

/-- The moving window `bsWin ℓ u = χ_ℓ(· − ℓu)` is continuous (as a function of `x`). -/
lemma continuous_bsWin (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Continuous (Work.BSKinetic.bsWin ℓ u) := by
  rw [bsWin_eq_chiScale_comp_subRight]
  exact (Submission.BoseGases.chiScale_continuous ℓ).comp
    (Homeomorph.subRight (ℓ • u)).continuous

/-- The moving window `bsWin ℓ u = χ_ℓ(· − ℓu)` has compact support. -/
lemma hasCompactSupport_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    HasCompactSupport (Work.BSKinetic.bsWin ℓ u) := by
  rw [bsWin_eq_chiScale_comp_subRight]
  exact (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph _

/-- The windowed product `x ↦ bsWin ℓ u x * ψ x` of the moving window with a continuous
function `ψ` is integrable: `bsWin ℓ u` is continuous with compact support. -/
lemma bsWin_mul_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsWin ℓ u x * ψ x) :=
  Work.BSKinetic.integrable_mul_of_hasCompactSupport
    (continuous_bsWin ℓ u) hψ.continuous (hasCompactSupport_bsWin hℓ u)

end Work.BSKinetic.IterKernelAux
