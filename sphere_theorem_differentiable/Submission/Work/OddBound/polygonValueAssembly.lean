import Mathlib
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygonValue.Basic
import Submission.Work.OddBound.pvCrux.polygonSides
import Submission.Work.OddBound.polygonValue.balancedBrokenLoop
import Submission.Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The value bound, assembled from the side family and the balancing step

`Work.OddBound.polygonValueBoundFromParts` is the value bound
`Work.OddBound.polygonValueBound`, proved from the decomposition
`Work.OddBound.polygonValue.polygonSides` (the side-curve family) +
`Work.OddBound.polygonValue.balancedBrokenLoop` (concatenation and arclength balancing) +
`Work.OddBound.polygonValue.piecewiseLongHomotopy` (Klingenberg's long homotopy estimate for
piecewise `C¹` families).  Its statement is identical to that of the value bound, so it can be used
as the body of `Work.OddBound.polygonValueBound` directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound

theorem polygonValueBoundFromParts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {L : ℝ} (hL : 0 < L) (hLlt : L < 2 * Real.pi / Real.sqrt K) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hper : ∀ t : ℝ, γ (t + L) = γ t) (hγ0 : γ 0 = p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρlt : ρ < Real.pi / Real.sqrt K)
    (hρinj : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x ρ)
    {N : ℕ} (hN : 3 ≤ N) (hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ))
    {w : ℝ → Fin (N - 1) → M} (hwcont : Continuous w)
    (hw0 : w 0 = fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N))
    (hw1 : ∀ i : Fin (N - 1), w 1 i = p) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1, 2 * Real.pi ^ 2 / K ≤ Work.OddBound.gonEnergy (I := I) p (w τ) := by
  by_contra hcon
  push_neg at hcon
  have hE : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Work.OddBound.gonEnergy (I := I) p (w τ) < 2 * Real.pi ^ 2 / K :=
    fun τ hτ => hcon τ hτ
  obtain ⟨hside0, S, hScont, hSsm, hS0, hS1, hSlen, hS0slice, hS1slice⟩ :=
    Work.OddBound.pvCrux.polygonSides (I := I) (cov := cov) hmet htor hK hcurv hL hLlt hγsm
      hgeo hne hunit hper hγ0 hρ hρlt hρinj hN hbig hwcont hw0 hw1 hE
  obtain ⟨c, hcont, hcper, hcbase, hc0, hc1, hpiece, hlen⟩ :=
    Work.OddBound.polygonValue.balancedBrokenLoop (I := I) hK hL hLlt hper (by omega) hw0 hw1
      hE hside0 hScont hSsm hS0 hS1 hSlen hS0slice hS1slice
  exact Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise (I := I) (cov := cov) hmet htor hK hcurv
    hL hγsm hgeo hne hper hγ0 (c := c) hcont hcper hcbase hc0 hc1 hpiece hlen

end Work.OddBound
