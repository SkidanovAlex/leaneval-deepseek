import Mathlib
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.design.PolygonValueBound
import Submission.Work.OddBound.polygonValue.Basic
import Submission.Work.OddBound.pvCrux.polygonSides
import Submission.Work.OddBound.polygonValue.balancedBrokenLoop
import Submission.Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise
import Submission.Work.OddBound.polygonValueAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-- **The value bound of the odd-dimensional Klingenberg minimax** (polygon model): for a compact
Riemannian manifold with `sec ≤ K`, `0 < K`, a closed unit-speed geodesic `γ` of period `L` with
`L < 2π/√K`, a uniform injectivity radius `ρ < π/√K`, `N ≥ 3` with `4π²/(Kρ²) < N`, and a
continuous family of based `N`-gons `w` from the polygon inscribed in `γ` (at `τ = 0`) to the
constant polygon at `p` (at `τ = 1`), some slice has polygon energy `≥ 2π²/K`.

Proof: assume the contrary, so every slice has energy `< 2π²/K` and hence every side is shorter than
`ρ` (`Work.OddBound.gonSideLen_lt_of_energy_lt`); the sides carry unique minimising geodesics, whose
jointly continuous family is `Work.OddBound.polygonValue.polygonSides`, which
`Work.OddBound.polygonValue.balancedBrokenLoop` concatenates and reparametrises proportionally to
arclength, giving a continuous family of based loops from `γ (L ·)` to the constant loop whose two
halves are both shorter than `π/√K`.  That contradicts Klingenberg's long homotopy estimate
`Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise`. -/
theorem polygonValueBound
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
    ∃ τ ∈ Set.Icc (0 : ℝ) 1, 2 * Real.pi ^ 2 / K ≤ Work.OddBound.gonEnergy (I := I) p (w τ) :=
  Work.OddBound.polygonValueBoundFromParts (I := I) (cov := cov) hmet htor hK hcurv hL hLlt hγsm
    hgeo hne hunit hper hγ0 hρ hρlt hρinj hN hbig hwcont hw0 hw1

end Work.OddBound
