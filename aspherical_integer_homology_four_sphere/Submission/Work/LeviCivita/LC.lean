/-
# `Work.LC`: the names of the lead blueprint's contract for area LC

The lead blueprint (`Submission/Work/NOTES_LEAD_aspherical_blueprint.md`, section
`### LC LeviCivita/`) writes the interface of this area in a namespace `Work.LC`.  The area itself
lives in `Work.LeviCivita` (the namespace dictated by the directory `Submission/Work/LeviCivita/`);
this file re-exports the four contract items (plus the Koszul identity) under `Work.LC`, so that
code written against the blueprint compiles unchanged.

    Work.LC.lcConn                        -- = Work.LeviCivita.lcConn
    Work.LC.lcConn_torsion                -- lcConn.torsion = 0
    Work.LC.lcConn_compat                 -- IsMetricCompatible lcConn  (challenge's predicate)
    Work.LC.lcConn_contMDiff              -- ContMDiffCovariantDerivative lcConn ∞  (instance)
    Work.LC.chartGram_chrB_eq_koszul      -- the Koszul identity in charts
-/
import Submission.Work.LeviCivita.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.LC

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- The Levi-Civita connection (alias of `Work.LeviCivita.lcConn`). -/
abbrev lcConn : CovariantDerivative I E (TangentSpace I (M := M)) :=
  Work.LeviCivita.lcConn

theorem lcConn_torsion : (lcConn (I := I) (M := M)).torsion = 0 :=
  Work.LeviCivita.lcConn_torsion

theorem lcConn_compat :
    LeanEval.Geometry.SphereTheorem.IsMetricCompatible (lcConn (I := I) (M := M)) :=
  Work.LeviCivita.lcConn_compat

section Boundaryless

variable [I.Boundaryless]

/-- Smoothness of the Levi-Civita connection (instance).  Note the hypothesis `[I.Boundaryless]`,
which is needed because the proof differentiates in chart coordinates; the intended application
`I = 𝓘(ℝ,E4)` is boundaryless. -/
theorem lcConn_contMDiff :
    CovariantDerivative.ContMDiffCovariantDerivative (lcConn (I := I) (M := M)) ∞ :=
  Work.LeviCivita.contMDiffCovariantDerivative_lcConn

attribute [instance] lcConn_contMDiff

theorem chartGram_chrB_eq_koszul
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (a b c : E) :
    Submission.ChartConnection.chartGram (I := I) x₀ p
        (Submission.ChartCurv.chrB cov x₀ p a b) c =
      (1/2) * (Work.Curvature.chartDg (I := I) x₀ p b a c
        + Work.Curvature.chartDg (I := I) x₀ p a b c
        - Work.Curvature.chartDg (I := I) x₀ p c a b) :=
  Work.LeviCivita.chartGram_chrB_eq_koszul (I := I) hmet htor x₀ p hp a b c

end Boundaryless

end

end Work.LC
