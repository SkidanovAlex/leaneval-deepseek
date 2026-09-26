import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.isCoveringMap_psiMapToRange

/-!
# The parametrisation is a covering map onto its range

Hypotheses (i) and (ii) (periodicity and injectivity modulo `2π`) say exactly that the
parametrisation `psiMap psi : ℝ × ℝ → R3` factors as the quotient map
`ℝ² → ℝ²/2πℤ²` followed by an injective map; the latter is a continuous bijection from a
compact space onto the Hausdorff space `range psi`, hence a homeomorphism.  Consequently
`psiMapToRange psi` — the parametrisation viewed as a map onto its range — is a covering map
(the quotient map composed with a homeomorphism).

This is the input for the path lifting theorems of `Work.TorusCover.Lifting`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

/-- **The parametrisation is a covering map onto its range.** -/
theorem TorusParam.isCoveringMap_psiMapToRange (P : TorusParam) :
    IsCoveringMap (psiMapToRange P.psi) :=
  _root_.Work.TorusCover.isCoveringMap_psiMapToRange P.psi P.contDiff.continuous
    P.periodic_fst P.periodic_snd P.inj_mod

end

end Work.TorusCover
