import Mathlib
import Submission.Work.OddBound.IndexDirichlet
import Submission.Work.OddBound.IndexPair
import Submission.Work.OddBound.Minimax
import Submission.Work.OddBound.strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair
import Submission.Work.OddBound.longHomotopy.long_homotopy_lower_bound
import Submission.Work.OddBound.klingenbergOdd.klingenberg_length_bound_odd_of_minimaxInput_and_boundary
import Submission.Work.OddBound.assembly.MinimaxExtraction

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The odd-dimensional Klingenberg length bound from the minimax extraction

This module is the end of the chain of the `OddBound` chapter: it consumes the **long homotopy
lemma** — now a *theorem* (`Work.OddBound.longHomotopy.long_homotopy_lower_bound`) — and leaves a
single classical input, the **minimax extraction** `Work.OddBound.MinimaxExtraction K` (the minimax
principle on the based loop space `Ω_p M`: Palais–Smale Condition C plus the minimax principle, with
Gromoll–Meyer for the degenerate Morse lemma).

* `Work.OddBound.minimaxInput_of_extraction_and_lhl`: `MinimaxInput K` from `MinimaxExtraction K`
  alone (the long homotopy lemma supplies the value bound).
* `Work.OddBound.klingenberg_length_bound_odd_strict_of_extraction`: the **strictly**
  quarter-pinched length bound `K/4 + ε ≤ sec ≤ K` from `MinimaxExtraction K`.  This is the form
  `Submission/Klingenberg.lean` consumes.
* `Work.OddBound.klingenberg_length_bound_odd_of_extraction_and_boundary`: the **literal**
  (weakly pinched) statement `K/4 ≤ sec ≤ K`, `K < 4`, odd dimension, from `MinimaxExtraction K`
  plus the Cheeger–Gromoll boundary input (no closed unit-speed geodesic of length exactly `2π/√K`
  with at most one negative Dirichlet direction).  In the weakly pinched case the minimax geodesic
  can have length exactly `2π/√K`, where the Dirichlet index computation gives only `≤ 0`; the
  boundary analysis of Cheeger–Gromoll 1980 is what rules that case out, and it is *not* needed by
  the challenge (whose pinching is strict), see `refs/NOTES.md` §6.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **`MinimaxInput` from the minimax extraction alone.**  The long homotopy lemma
(`Work.OddBound.longHomotopy.long_homotopy_lower_bound`) is a theorem, so the only remaining input of
`MinimaxInput` is the minimax extraction. -/
theorem minimaxInput_of_extraction_and_lhl
    [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hext : MinimaxExtraction (I := I) (cov := cov) hmet htor K) :
    MinimaxInput (I := I) (cov := cov) hmet htor K :=
  minimaxInput_of_extraction (I := I) (cov := cov) hmet htor hext
    (fun {p γ L} hL hγsm hgeo hne hper h0 =>
      Work.OddBound.longHomotopy.long_homotopy_lower_bound (I := I) (cov := cov) hmet htor hK
        hcurv hL hγsm hgeo hne hper h0)

/-- **The strict quarter-pinched Klingenberg length bound from the minimax extraction.** -/
theorem klingenberg_length_bound_odd_strict_of_extraction
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 + ε ≤ inner ℝ (curvVec cov p u v v) u)
    (hext : MinimaxExtraction (I := I) (cov := cov) hmet htor K) :
    ∀ {p : M} {T : ℝ} {γ : ℝ → M},
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T :=
  klingenberg_length_bound_odd_strict_of_minimaxInput (I := I) (cov := cov) hmet htor hDim hK hε hcurv hpinch
    (minimaxInput_of_extraction_and_lhl (I := I) (cov := cov) hmet htor hK hcurv hext)

/-- **The literal (weakly pinched) Klingenberg length bound from the minimax extraction plus the
Cheeger–Gromoll boundary input.** -/
theorem klingenberg_length_bound_odd_of_extraction_and_boundary
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u)
    (hext : MinimaxExtraction (I := I) (cov := cov) hmet htor K)
    (hboundary : ∀ (c : ℝ → M) (T : ℝ), c T = c 0 →
      ContMDiff 𝓘(ℝ) I ∞ c →
      (∀ t : ℝ, IsGeodesicAt (I := I) cov c t) →
      (∀ t : ℝ, curveVelocity (I := I) c t ≠ 0) →
      (∀ t ∈ Icc (0 : ℝ) T, curveSpeed (I := I) c t = 1) →
      T = 2 * Real.pi / Real.sqrt K →
      ¬ DirichletIndexLeOne (I := I) (cov := cov) c T) :
    ∀ {p : M} {T : ℝ} {γ : ℝ → M},
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T :=
  Work.OddBound.klingenbergOdd.klingenberg_length_bound_odd_of_minimaxInput_and_boundary
    (I := I) (cov := cov) hmet htor hDim hK hK4 hcurv hpinch
    (minimaxInput_of_extraction_and_lhl (I := I) (cov := cov) hmet htor hK hcurv hext) hboundary

/-! ## 5. The unconditional forms: `MinimaxExtraction` is a theorem -/

/-- **`MinimaxInput` is now unconditional**: the loop-space minimax
(`Work.OddBound.minimaxExtraction`) is proved, and the long homotopy lemma
(`Work.OddBound.longHomotopy.long_homotopy_lower_bound`) supplies its value bound. -/
theorem minimaxInput_of_lhl
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K) :
    MinimaxInput (I := I) (cov := cov) hmet htor K :=
  minimaxInput_of_extraction (I := I) (cov := cov) hmet htor
    (Work.OddBound.minimaxExtraction (I := I) (cov := cov) hmet htor)
    (fun {p γ L} hL hγsm hgeo hne hper h0 =>
      Work.OddBound.longHomotopy.long_homotopy_lower_bound (I := I) (cov := cov) hmet htor
        hK hcurv hL hγsm hgeo hne hper h0)

/-- **The literal (weakly pinched) Klingenberg length bound from the Cheeger--Gromoll boundary
input** — now with `MinimaxExtraction` discharged. -/
theorem klingenberg_length_bound_odd_of_boundary
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u)
    (hboundary : ∀ (c : ℝ → M) (T : ℝ), c T = c 0 →
      ContMDiff 𝓘(ℝ) I ∞ c →
      (∀ t : ℝ, IsGeodesicAt (I := I) cov c t) →
      (∀ t : ℝ, curveVelocity (I := I) c t ≠ 0) →
      (∀ t ∈ Icc (0 : ℝ) T, curveSpeed (I := I) c t = 1) →
      T = 2 * Real.pi / Real.sqrt K →
      ¬ Work.OddBound.DirichletIndexLeOne (I := I) (cov := cov) c T) :
    ∀ {p : M} {T : ℝ} {γ : ℝ → M},
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T :=
  Work.OddBound.klingenbergOdd.klingenberg_length_bound_odd_of_minimaxInput_and_boundary
    (I := I) (cov := cov) hmet htor hDim hK hK4 hcurv hpinch
    (minimaxInput_of_lhl (I := I) (cov := cov) hmet htor hK hcurv) hboundary

end

end Work.OddBound
