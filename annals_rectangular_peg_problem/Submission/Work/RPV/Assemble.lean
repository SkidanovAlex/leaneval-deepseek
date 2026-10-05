import Submission.Work.RPV.Glue
import Submission.Work.RPV.theorem_1_of_main

/-!
# Rectangular peg: assembled wiring (`Work.RPV`)

This is the final assembly (route design §4.6, bottom line): the four geometric node theorems

* `Work.RPV.CoreNode` (CORE),
* `Work.RPV.CurveIsotopyNode` (B1),
* `Work.RPV.LagFamilyNode` (B5),
* `Work.RPV.LagIsotopyNode` (A3),

together with the proved G1 reduction `Work.RPV.theorem_1_of_main`, yield the challenge
statement.  Concretely, once the four node theorems are available as definitions
`hC : Work.RPV.CoreNode`, `hB1 : Work.RPV.CurveIsotopyNode`, `hB5 : Work.RPV.LagFamilyNode`,
`hA3 : Work.RPV.LagIsotopyNode`, the challenge is

```
Work.RPV.theorem_1_of_geometric_nodes hC hB1 hB5 hA3 γ z w θ hγ
```

and `Submission.lean`'s `theorem_1` can be defined by `exact` of that term (the hypothesis
`IsSmoothJordan` is definitionally `IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ`, see the check below).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-- The challenge statement from the four geometric nodes. -/
theorem theorem_1_of_geometric_nodes (hC : CoreNode) (hB1 : CurveIsotopyNode)
    (hB5 : LagFamilyNode) (hA3 : LagIsotopyNode) :
    ∀ (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle), IsSmoothJordan γ →
      ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
        Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
        ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ :=
  theorem_1_of_nodes theorem_1_of_main hC hB1 hB5 hA3

/-- Check: the assembled wiring gives the challenge's conclusion under the challenge's own
hypothesis `IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ`. -/
example (hC : CoreNode) (hB1 : CurveIsotopyNode) (hB5 : LagFamilyNode) (hA3 : LagIsotopyNode)
    (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ) :
    ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
      Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
      ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ :=
  theorem_1_of_geometric_nodes hC hB1 hB5 hA3 γ z w θ hγ

end Work.RPV
