import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.BoxTauGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxFrameDefs` — the q-frame integrand and the mean-free slot fibre

This module only collects the two abbreviations used by the frame-bound layer
(`Work.BoseFixB1.boxFramePGen` and its supporting lemmas):

* `frameIntegrand volA Ac χ Ψ q x` — the q-diagonal *frame* integrand of the two genuine
  windowed modes `boxWinModeReGen`/`boxWinModeImGen` at `q`:
  `(a(Re_q)Ψ x)² + (a(Im_q)Ψ x)²`, i.e. the `q`-integrand of `boxWinModePGen`.
* `slotFibre volA Ac i Ψ x z` — the mean-free fibre of `Ψ` in the slot `i`, i.e.
  `boxQInd volA Ac i Ψ` evaluated at the configuration in which the `i`-th coordinate is set
  to `z` (`= 1_{Ac}(z)·(Ψ(x[i↦z]) − ⨍_{Ac}Ψ(x[i↦·]))`).

Nothing here is proved; the module exists so that the lemmas about these objects can be
stated in a common vocabulary.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

/-- The `q`-frame integrand: the sum of the `P`-contents of the two genuine windowed modes
at the momentum `q`, evaluated at the configuration `x`. -/
noncomputable def frameIntegrand (volA : ℝ) (Ac : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (Ψ : X N → ℝ)
    (q : EuclideanSpace ℝ (Fin 3)) (x : X N) : ℝ :=
  (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
    + (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ q) Ψ x) ^ 2

/-- The mean-free fibre of `Ψ` in the slot `i`: the FS-faithful box projection `Q_{Ac,i}`
evaluated at the configuration in which the `i`-th coordinate is set to `z`. -/
noncomputable def slotFibre (volA : ℝ) (Ac : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ}
    (i : Fin N) (Ψ : X N → ℝ) (x : X N) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z)

/-- The symmetric (`SFinite`) instance for the restricted box measure, recorded here so that
every module of this layer sees the same instance. -/
example {N : ℕ} {a : ℝ} :
    SFinite ((volume : Measure (X N)).restrict (abox N a)) := inferInstance

end Work.BoseFixB1
