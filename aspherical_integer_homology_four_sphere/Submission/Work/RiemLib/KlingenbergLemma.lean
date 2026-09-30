import Submission.Work.RiemLib.CutStep3
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.CutTime
import Submission.Work.RiemLib.LensSync
import Submission.Work.RiemLib.GExpTwoSided
import Submission.Work.RiemLib.GExpRayIdent
import Submission.Work.RiemLib.GExpVelocity
import Submission.Work.RiemLib.LensLoop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The logical skeleton of Klingenberg's lemma

Klingenberg's lemma expresses the injectivity radius at `p` in terms of the conjugate radius and the
length of the shortest closed geodesic loop through `p`:

  `inj(p) = min { conj(p), ½ ℓ(p) }`   (Cheeger–Ebin, Lemma 5.6).

The project already has the *easy* half (`inj(p) ≤ ½ ℓ(p)`, i.e. a closed geodesic loop of length `T`
bounds the injectivity radius by `T/2`): that is `Submission.LensLoop.two_mul_le_of_isGeodesicAt_loop`.

This file formalises the **logical skeleton of the hard half** and thereby isolates the two classical
inputs that are still missing from the library (see `Submission/Roadmap.lean` §81.6):

* `hloc_sphere`: `GExp p` is locally injective at every vector of norm `m = inj(p)` (`LocallyInjectiveAtGExp`),
  equivalently C¹-smoothness of `v ↦ GExp p v` beyond the injectivity radius (the "fold", §73.4/§80.4);
* the **Klingenberg–Xu input**: two distinct minimal vectors of norm `m` with the same image give a
  *closed geodesic loop* through `p` of length `≤ 2m` (Klingenberg 1959/1961; Xu, arXiv:1401.5549,
  Theorem B: the two minimal geodesics to the closest cut point are the two halves of a whole geodesic).

The conclusion is the transference step that Klingenberg's estimate needs:
**every closed geodesic loop through `p` has length `≥ ℓ` implies `ℓ ≤ 2 inj(p)`**, i.e.
`½ ℓ(p) ≤ inj(p)`.  Combined with Rauch (`conj(p) ≥ π/√K`) and the lower bound for the length of the
shortest closed geodesic, this is what turns the closed-geodesic estimate into the injectivity radius
estimate, and hence into the diameter estimate `(K2)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.CutStep2
open Submission.CutStep3

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.KlingenbergLemma

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A closed geodesic loop at `p` of length `T`**: a unit-speed `C^∞` geodesic `γ : ℝ → M` with
`γ 0 = p = γ T` and with **matching velocities at the two ends** (`γ̇(T) = γ̇(0)`), i.e. `γ` descends
to a genuine closed geodesic on the circle `ℝ/Tℤ` — not merely a geodesic arc whose endpoints
coincide.  (The distinction matters: a geodesic arc with coinciding endpoints but *non*-matching
velocities, e.g. the "extremal lens" loop `t ↦ GExp p ((1 - t/ν) • u)` of `Submission.LensLoop`, is a
closed geodesic only when the ray is periodic.) -/
def IsClosedGeodesicLoopAt (hmet : IsMetricCompatible cov) (p : M) (T : ℝ) (γ : ℝ → M) : Prop :=
  0 < T ∧ γ 0 = p ∧ γ T = p ∧ ContMDiffOn 𝓘(ℝ) I ∞ γ univ ∧
    (∀ t : ℝ, IsGeodesicAt cov γ t) ∧ (∀ t : ℝ, ‖curveVelocity (I := I) γ t‖ = 1) ∧
    curveVelocity (I := I) γ T = curveVelocity (I := I) γ 0

/-- **Klingenberg's lemma, the transference step.**  Let `m = inj(p)` (the exponential map at `p` is
injective on the ball of radius `m` and on no larger ball), suppose that `GExp p` is locally
injective at every vector of norm `m` (`hloc_sphere`), and suppose the **Klingenberg–Xu input**:
two distinct minimal vectors of norm `m` with the same image produce a closed geodesic loop through
`p` of length `≤ 2m`.  If every closed geodesic loop through `p` has length `≥ ℓ`, then `ℓ ≤ 2m`.

In other words `½ ℓ(p) ≤ inj(p)` — the half of the structure theorem
`inj(p) = min{conj(p), ½ℓ(p)}` that transfers a lower bound for the lengths of closed geodesics to a
lower bound for the injectivity radius.

**CAUTION (roadmap §90).**  The hypothesis `hloc` is *false* in general at a maximal injectivity
radius: on `Sⁿ` with `m = π` all vectors of norm `π` map to the antipode, so `GExp p` is not locally
injective at them.  Hence this statement cannot be applied in the case `m ≥ π/√K` (that case is
handled by the diameter bound, `KlingenbergCore.diameter_gt_half_pi_of_klingenberg`).  The corrected,
`hloc`-free forms are
`KlingenbergTransfer.le_two_mul_of_isClosedGeodesicLoop_lower_of_lt` (the same conclusion, with
`m < π/√K` and a curvature bound `sec ≤ K` in place of `hloc`) and
`KlingenbergTransfer.pi_div_sqrt_le_of_isClosedGeodesicLoop_lower` (the assembled pointwise bound
`π/√K ≤ inj(p)`).  Prefer those. -/
theorem le_two_mul_of_isClosedGeodesicLoop_lower
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m ℓ : ℝ} (hm : 0 < m)
    (hinj : InjAtLeast hmet p m) (hmax : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hloc : ∀ w : TangentSpace I p, ‖w‖ = m → LocallyInjectiveAtGExp (I := I) hmet p w)
    (hXu : ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
      ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧ IsClosedGeodesicLoopAt hmet p T γ)
    (hℓ : ∀ (T : ℝ) (γ : ℝ → M), IsClosedGeodesicLoopAt hmet p T γ → ℓ ≤ T) :
    ℓ ≤ 2 * m := by
  rcases exists_two_minimising_or_not_locallyInjective (cov := cov) hmet htor (p := p) (m := m)
    hinj hmax with ⟨u, v, huv, hG, hu, hv, -⟩ | ⟨w, hw, hwloc⟩
  · rcases hXu u v huv hu hv hG with ⟨T, γ, hT, hloop⟩
    exact le_trans (hℓ T γ hloop) hT
  · exact absurd (hloc w hw) hwloc

end

end Submission.KlingenbergLemma
