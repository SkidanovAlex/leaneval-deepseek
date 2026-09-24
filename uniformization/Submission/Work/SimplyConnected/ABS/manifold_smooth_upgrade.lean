import Mathlib
import Submission.Work.Analysis.RiemannSurface.chart_transition_analytic

/-!
# A complex one-manifold is smooth of every order

The chart transitions of a complex one-manifold are *holomorphic* whenever the manifold structure is
`C^1` (`Submission.Work.Analysis.RiemannSurface.analyticAt_transition`), hence `C^∞`.  This file
records the resulting upgrade

* `Work.SimplyConnected.ABS.isManifold_self_model_infty` :
  `IsManifold (modelWithCornersSelf ℂ ℂ) ∞ X`, and
* `Work.SimplyConnected.ABS.isManifold_self_model_real_infty` :
  `IsManifold (modelWithCornersSelf ℝ ℂ) ∞ X`,

from the hypothesis `IsManifold (modelWithCornersSelf ℂ ℂ) 1 X` of the target.

The real-model form is the one that a smooth partition of unity needs
(`SmoothPartitionOfUnity.exists_isSubordinate` asks for `IsManifold I ⊤ M` for a *real* model
`I : ModelWithCorners ℝ E H`); it is what the gluing rung (B3) of the divisor chapter consumes.
-/

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Chart transitions are `C^∞` on their source. -/
theorem contDiffOn_transition (c₀ c₁ : OpenPartialHomeomorph X ℂ) (hc₀ : c₀ ∈ atlas ℂ X)
    (hc₁ : c₁ ∈ atlas ℂ X) :
    ContDiffOn ℂ ⊤ ((c₁.symm ≫ₕ c₀ : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      ((c₁.symm ≫ₕ c₀ : OpenPartialHomeomorph ℂ ℂ)).source :=
  AnalyticOnNhd.contDiffOn_of_completeSpace
    (fun w hw => Work.Analysis.RiemannSurface.analyticAt_transition hc₀ hc₁ hw)

/-- **The complex manifold structure is smooth of every order.** -/
theorem isManifold_self_model_infty : IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ X := by
  haveI : HasGroupoid X (contDiffGroupoid ⊤ (modelWithCornersSelf ℂ ℂ)) :=
    hasGroupoid_of_pregroupoid _ (fun {e e'} he he' => by
      simpa only [contDiffPregroupoid,
        show ((modelWithCornersSelf ℂ ℂ : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ) = id from rfl,
        show (((modelWithCornersSelf ℂ ℂ : ModelWithCorners ℂ ℂ ℂ).symm : ℂ → ℂ)) = id from rfl,
        Function.comp_apply, Set.preimage_id, Set.range_id, Set.univ_inter,
        Function.id_comp, Function.comp_id, Set.inter_univ]
        using contDiffOn_transition e' e he' he)
  exact IsManifold.mk' (modelWithCornersSelf ℂ ℂ) ⊤ X

/-- **The real-model smooth structure**: the same transitions are `C^∞` over `ℝ`, which is the form a
smooth partition of unity consumes (`SmoothPartitionOfUnity.exists_isSubordinate`). -/
theorem isManifold_self_model_real_infty :
    IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X := by
  haveI : HasGroupoid X (contDiffGroupoid ⊤ (modelWithCornersSelf ℝ ℂ)) :=
    hasGroupoid_of_pregroupoid _ (fun {e e'} he he' => by
      simpa only [contDiffPregroupoid,
        show ((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ) : ℂ → ℂ) = id from rfl,
        show (((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ).symm : ℂ → ℂ)) = id from rfl,
        Function.comp_apply, Set.preimage_id, Set.range_id, Set.univ_inter,
        Function.id_comp, Function.comp_id, Set.inter_univ]
        using (contDiffOn_transition e' e he' he).restrict_scalars ℝ)
  exact IsManifold.mk' (modelWithCornersSelf ℝ ℂ) ⊤ X

/- **Note.**

*Not* stated here: the groupoid bookkeeping is being proved at
`Work.Analysis.RiemannSurface.isManifold_self_model_infty`
(`Submission/Work/Analysis/RiemannSurface/isManifold_self_model_infty.lean`), which imports this file
for `contDiffOn_transition` above.  (It is deliberately *not* declared here as well: a duplicate
`sorry`'d declaration in the import closure would let any proof of it fall back on `sorryAx`.)

The same argument gives the *real*-model form `IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X`, which is
what smooth partitions of unity ask for; the transitions are holomorphic, hence `C^∞` over `ℝ`. -/
end Work.SimplyConnected.ABS
