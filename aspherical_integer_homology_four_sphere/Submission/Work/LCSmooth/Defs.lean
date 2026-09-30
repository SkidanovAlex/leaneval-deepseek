/-
# Area `LCSmooth`: smoothness of the Levi-Civita connection, in the framework of the project

This is the interface file of the area `Submission/Work/LCSmooth/`.  Its subject is the one
regularity statement that the *final assembly* of the challenge theorem consumes and that the
areas `LeviCivita/`, `Curvature/`, `CartanHadamard/` and `Final/` state in their own vocabularies:

    CovariantDerivative.ContMDiffCovariantDerivative (lcConn) smoothGrade

(the `cov_smooth` field of `Work.Final.FinalInputs`), together with the bundled form of the same
fact, `Work.Final.ChartedRiemConn`.

## The mathematics

The Levi-Civita connection `Work.LeviCivita.lcConn` is Mathlib's abstract Koszul construction
`CovariantDerivative.leviCivitaConnection`; its torsion-freeness and metric compatibility are
Mathlib theorems, but *smoothness* is Mathlib's "future PR": the definition of `lcConn` is
implicit (it is the unique connection satisfying the Koszul identity pointwise), so there is no
formula to differentiate directly.  The route used in this project (area `LeviCivita`,
`Submission/Work/LeviCivita/Smooth.lean` and `Main.lean`) is:

* the Koszul formula in charts, `Work.LeviCivita.chartGram_chrB_eq_koszul`, exhibits the chart
  Christoffel symbol of `lcConn` as `½ (∂g + ∂g − ∂g)` contracted with `g⁻¹`; since the chart
  metric `chartGram` is the metric restricted to the chart, hence `C^∞`, all coefficients are
  `C^∞` — this is where the smoothness of the metric of the project's chart models is used, and
  why `[I.Boundaryless]` (the model of the project, `I4 = 𝓘(ℝ,E4)`, is boundaryless) is needed:
  `(extChartAt I x₀).symm` is differentiable only on its target;
* equivalently (and this is the proof actually implemented) the *intrinsic* Koszul formula
  `Work.LeviCivita.lcConn_apply_inner` writes `⟪∇_X σ, Z⟫` as a sum of directional derivatives
  of smooth functions and Lie brackets of smooth fields, so `x ↦ ⟪lcConn σ x (X x), Z x⟫` is `C^∞`
  (`Work.LeviCivita.contMDiffAt_lcConn_pairing`); raising this pairing with the inverse chart
  metric — smooth as the inverse of a smooth positive-definite family of Riesz maps
  (`Work.LeviCivita.contMDiffAt_chartGramCLM_inverse`) — gives the coordinate representative of
  `lcConn σ`, whose smoothness is the `contMDiff` field.

The theorem is therefore *proved* in `LeviCivita/`, but that area's entry point did not export it
under the name the final assembly asked for: `Work.LeviCivita.lcConn_contMDiff` did not exist
(`Work.LeviCivita.contMDiffCovariantDerivative_lcConn` and `Work.LC.lcConn_contMDiff` did).  This
area gives the missing name and, more importantly, the *instance-shaped* interface: from here on,

    import Submission.Work.LCSmooth.All
    inferInstance   -- ContMDiffCovariantDerivative (Work.Final.mhatCov (rt := rt)) smoothGrade

fires by typeclass inference, with no hypothesis to thread by hand.

## What a caller gets

* `Work.LCSmooth.smoothGrade` — the grade `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, with
  `Work.LCSmooth.smoothGrade_eq_final : smoothGrade = Work.Final.smoothGrade` and
  `Work.LCSmooth.smoothGrade_eq_infty : smoothGrade = (∞ : ℕ∞ω)`;
* `Work.LCSmooth.lcConn_contMDiff` — the theorem in the *generic* framework variable block
  (any boundaryless model `I`, any `M`), and the registered instance
  `Work.LCSmooth.instContMDiffCovariantDerivativeLcConn`;
* `Work.LCSmooth.chartedRiemConn` — the Levi-Civita connection of a `Work.Final.ChartedRiem`
  manifold bundled as a `Work.Final.ChartedRiemConn` (the smooth, torsion-free,
  metric-compatible connection of the framework), registered as an instance
  `Work.LCSmooth.instChartedRiemConn`;
* `Work.LCSmooth.cov_smooth`, `Work.LCSmooth.mhatCov_contMDiff` — the field type at the assembled
  space `M̂` (`Submission/Work/LCSmooth/Mhat.lean`);
* the assemblers of the challenge theorem from the still-owed data
  (`Work.LCSmooth.finalInputsOfCurvLe`, `…OfModels`, `…OfSecNonpos`) and the end-to-end composition
  with `Work.Final.aspherical_integer_homology_four_sphere`
  (`Work.LCSmooth.aspherical_integer_homology_four_sphere_of_data`), in
  `Submission/Work/LCSmooth/Field.lean`.

Everything here is axiom-clean (see `Submission/Work/LCSmooth/Axioms.lean`): the area only *names*
and *registers* the regularity of `lcConn` proved in `LeviCivita/`, and composes it with the
delivered final chain.
-/
import Submission.Work.Final.Framework
import Submission.Work.Final.Basic
import Submission.Work.Final.Mhat
import Submission.Work.Final.Homology
import Submission.Work.Final.Cover
import Submission.Work.Final.MhatCover
import Submission.Work.Final.Main
import Submission.Work.Final.mvRightX_zero_surjective
import Submission.Work.Final.secNonpos_of_chartModels
import Submission.Work.Final.curvLe_of_models
import Submission.Work.Final.CurvField
import Submission.Work.LeviCivita.Main
import Submission.Work.LeviCivita.ChartMetric
import Submission.Work.LeviCivita.FrameField
import Submission.Work.LeviCivita.Koszul
import Submission.Work.LeviCivita.Smooth
import Submission.Work.LeviCivita.isInvertible_of_posDef
import Submission.Work.LeviCivita.contDiffAt_chartGramCLM
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Work.LeviCivita.contMDiffAt_chartGramCLM_inverse
import Submission.Work.LeviCivita.contMDiffAt_lcConn_pairing
import Submission.Work.LeviCivita.chartDg_eq_chartGram_chrB
import Submission.Work.LeviCivita.chartLCcoords_eventuallyEq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open CategoryTheory

namespace Work.LCSmooth

noncomputable section

/-- **The smoothness grade `∞` of the project**: `((⊤ : ℕ∞) : WithTop ℕ∞)`.

It is *definitionally* `Work.Final.smoothGrade` (`smoothGrade_eq_final`), and *definitionally* the
`∞` of the `ContDiff` notation for `ℕ∞ω = WithTop ℕ∞` (`smoothGrade_eq_infty`), but it is not
`⊤ : ℕ∞ω`, which is analytic regularity (`ω`) and *not* what this area produces. -/
abbrev smoothGrade : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `Work.LCSmooth.smoothGrade` is `Work.Final.smoothGrade` (definitionally). -/
theorem smoothGrade_eq_final : smoothGrade = Work.Final.smoothGrade := rfl

/-- `Work.LCSmooth.smoothGrade` is the `∞` of the `ContDiff` notation (`ℕ∞ω = WithTop ℕ∞`). -/
theorem smoothGrade_eq_infty : smoothGrade = (∞ : ℕ∞ω) := rfl

section Framework

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

section Boundaryless

variable [I.Boundaryless]

/-- **The Levi-Civita connection is a smooth covariant derivative** (framework form): for a
manifold `M` in the project's Riemannian variable block over a boundaryless model `I`, the
connection `Work.LeviCivita.lcConn` is of class `C^∞`.

This is the general form of the field `Work.Final.FinalInputs.cov_smooth`; the proof is the one of
area `LeviCivita` (`Work.LeviCivita.contMDiffCovariantDerivative_lcConn`), which computes the
connection in charts from the Koszul formula and the smoothness of the chart metric and of its
inverse. -/
theorem lcConn_contMDiff :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.LeviCivita.lcConn (I := I) (M := M)) smoothGrade :=
  Work.LeviCivita.contMDiffCovariantDerivative_lcConn

/-- The instance form of `Work.LCSmooth.lcConn_contMDiff`: after importing this module, the
smoothness of the Levi-Civita connection is found by `inferInstance`. -/
instance instContMDiffCovariantDerivativeLcConn :
    CovariantDerivative.ContMDiffCovariantDerivative
      (Work.LeviCivita.lcConn (I := I) (M := M)) smoothGrade :=
  lcConn_contMDiff

/-- The class predicate `ContMDiffCovariantDerivative` unwound: for every `C^∞` section `σ` of the
tangent bundle, the section `x ↦ ⟨x, lcConn σ x⟩` of `Hom(TM, TM)` is `C^∞`.

This is the *statement* that the instance `ContMDiffCovariantDerivative lcConn smoothGrade`
instantiates (see `Work.LCSmooth.lcConn_contMDiffOn_homSection` for the `ContMDiffOn` form). -/
theorem lcConn_contMDiff_homSection {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I I.tangent ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M ↦ (⟨x, Work.LeviCivita.lcConn (I := I) (M := M) σ x⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x))) :=
  contMDiffOn_univ.mp fun x _ =>
    Work.LeviCivita.contMDiffWithinAt_lcConn_homSection (I := I) hσ x

end Boundaryless

end Framework

section ChartedRiem

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M]
  [Work.Final.ChartedRiem M]

/-- **The canonical connection of the project's framework**: on a charted Riemannian manifold
(`Work.Final.ChartedRiem`), the Levi-Civita connection, bundled as a
`Work.Final.ChartedRiemConn` — i.e. smooth (`instContMDiffCovariantDerivativeLcConn`), compatible
with the metric (`Work.LeviCivita.lcConn_compat`) and torsion-free
(`Work.LeviCivita.lcConn_torsion`).

This removes the `letI` plumbing that consumers of `Work.Final.secNonpos_of_chartModels` and
`Work.Final.curvLe_of_models` had to write by hand: with this module imported,
`inferInstance : Work.Final.ChartedRiemConn M` is available as soon as `[Work.Final.ChartedRiem M]`
is. -/
noncomputable def chartedRiemConn : Work.Final.ChartedRiemConn M where
  cov := Work.LeviCivita.lcConn (I := Work.Space.I4) (M := M)
  smooth := Work.LCSmooth.instContMDiffCovariantDerivativeLcConn
    (I := Work.Space.I4) (M := M)
  compat := Work.LeviCivita.lcConn_compat (I := Work.Space.I4) (M := M)
  torsion := Work.LeviCivita.lcConn_torsion (I := Work.Space.I4) (M := M)

/-- The instance form of `Work.LCSmooth.chartedRiemConn`. -/
instance instChartedRiemConn : Work.Final.ChartedRiemConn M :=
  chartedRiemConn

/-- The connected component of `Work.LCSmooth.chartedRiemConn` is the Levi-Civita connection. -/
@[simp]
theorem chartedRiemConn_cov :
    (chartedRiemConn (M := M)).cov
      = Work.LeviCivita.lcConn (I := Work.Space.I4) (M := M) := rfl

end ChartedRiem

end

end Work.LCSmooth
