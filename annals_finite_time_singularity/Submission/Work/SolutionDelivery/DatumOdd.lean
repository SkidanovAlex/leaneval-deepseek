/-
# `Work.SolutionDelivery.DatumOdd` — the parity of the datum from the `Cyl` dictionary

The field `ConstructedSolution.ω₀_odd` (the oddness of the datum `u₀ = BS ω₀`) is, in the
construction, a consequence of the **`Cyl` parity dictionary** rather than an extra assumption:
the cut-off vorticity of the self-similar solution is an axisymmetric field without swirl with the
axial reflection parity `IsOddVorticity` (`ω ∘ reflZ = - flipZ ∘ ω`), and

* `Work.LWP.biotSavart_reflZ` (with the proved `Work.LWP.biotSavartReflection_holds`) gives the
  reflection invariance `BS ω (reflZ x) = flipZ (BS ω x)`;
* `Work.Cyl.isOdd_of_reflZ_invariant` upgrades reflection invariance + axisymmetry to the full
  `FiniteTimeSingularity.IsOdd`.

The one piece of the dictionary *not* available in the workspace is the **rotation equivariance of
the Biot–Savart integral** — that the Biot–Savart field of an axisymmetric no-swirl vorticity is
axisymmetric no-swirl (a linear-isometry change of variables in the Boole integral).  The lemma
below takes it as an explicit hypothesis, so a caller holding it gets `ω₀_odd` for free.
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.SolutionDelivery.Datum
import Submission.Work.Cyl.isOdd_of_reflZ_invariant
import Submission.Work.LWP.BiotSavart

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The `Cyl` parity dictionary for the Biot–Savart field.**  An axisymmetric no-swirl
Biot–Savart field of a vorticity of parity class `IsOddVorticity` is odd. -/
theorem isOdd_biotSavart_of_axiNoSwirl {ω : R3 → R3}
    (hω : Work.LWP.IsOddVorticity ω) (hax : Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart ω)) :
    IsOdd (Work.LWP.biotSavart ω) :=
  Work.Cyl.isOdd_of_reflZ_invariant _ hax
    (fun x => Work.LWP.biotSavart_reflZ Work.LWP.biotSavartReflection_holds hω x)

/-- **The `ω₀_odd` field of the constructed solution from the `Cyl` dictionary.** -/
theorem datum_odd_of_axiNoSwirl {α : NNReal} (C : ConstructedSolution α)
    (hω₀ : Work.LWP.IsOddVorticity C.ω₀)
    (hax : Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart C.ω₀)) :
    IsOdd (Work.LWP.biotSavart C.ω₀) :=
  isOdd_biotSavart_of_axiNoSwirl hω₀ hax

end Work.SolutionDelivery
