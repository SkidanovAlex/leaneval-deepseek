/-
Copyright: subproject `Submission/Work/FatouParabolic2/` of `mandelbar_not_path_connected`.

# `QuarterParabolicIsFixed` from the simple case of Fatou's input

The ledger statement `Work.LANDCL.QuarterParabolicIsFixed` (every parabolic point of
`T_{1/4}` is fixed) is proved in `Submission/Work/FatouParabolic/Quarter.lean` from
`Work.LANDCL.ParabolicCycleInOmegaLimit (1/4)` and the unconditional real dynamics
`(T_{1/4})^[n] (1/4) → 1/2`.  Here the parabolic-cycle input is re-derived in the two forms of
`Submission/Work/FatouParabolic2/parabolicCycleInOmegaLimit_of_simple.lean`.
-/
import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_simple
import Submission.Work.FatouParabolic.Quarter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- **`QuarterParabolicIsFixed` from the simple case of the input**, under the hypothesis that
every parabolic point of `T_{1/4}` is simple for its holomorphic return map. -/
theorem quarterParabolicIsFixed_of_simple (hFatou : FatouParabolicInput_simple)
    (hsimple : ParabolicCyclesSimple (1 / 4 : ℂ)) : Work.LANDCL.QuarterParabolicIsFixed :=
  Work.FatouParabolic.quarterParabolicIsFixed_of
    (parabolicCycleInOmegaLimit_of_simple hFatou (1 / 4) hsimple)
    Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit

/-- **`QuarterParabolicIsFixed` from the degenerate case of the input only.** -/
theorem quarterParabolicIsFixed_of_degenerate (hDeg : FatouParabolicInput_degenerate) :
    Work.LANDCL.QuarterParabolicIsFixed :=
  Work.FatouParabolic.quarterParabolicIsFixed_of
    (parabolicCycleInOmegaLimit_of_degenerate hDeg (1 / 4))
    Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit

/-- **`QuarterParabolicIsFixed` from the simple case of the input, in the weakest "simplicity"
form**: for every parabolic point of `T_{1/4}` one exhibits a period at which the holomorphic
return map is simple. -/
theorem quarterParabolicIsFixed_of_exists_simple (hFatou : FatouParabolicInput_simple)
    (h : ∀ z : ℂ, (∃ m : ℕ, Work.Landing.IsParabolic (1 / 4 : ℂ) m z) →
      ∃ m : ℕ, Work.Landing.IsParabolic (1 / 4 : ℂ) m z ∧
        iteratedDeriv 2 ((Work.Landing.Tsq (1 / 4 : ℂ))^[m]) z ≠ 0) :
    Work.LANDCL.QuarterParabolicIsFixed :=
  Work.FatouParabolic.quarterParabolicIsFixed_of
    (parabolicCycleInOmegaLimit_of_exists_simple hFatou (1 / 4) h)
    Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit


end

end Work.FatouParabolic2
