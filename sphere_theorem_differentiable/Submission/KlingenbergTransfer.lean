import Submission.RayConj
import Submission.KlingenbergLemma
import Submission.InjDiam

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.RauchK
open Submission.CutStep3

namespace Submission.KlingenbergTransfer

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

/-- **Klingenberg's lemma, the transference step, in its correct (`hloc`-free) form.**

Let `m` be the injectivity radius of `p` (`InjAtLeast hmet p m` and maximal), suppose
**`m < π/√K`** for a curvature bound `sec ≤ K` (`0 < K`), and suppose the **Klingenberg–Xu input**:
two distinct vectors of norm `m` with the same image produce a closed geodesic loop through `p` of
length `≤ 2m`.  If every closed geodesic loop through `p` has length `≥ ℓ`, then `ℓ ≤ 2m`.

This is `KlingenbergLemma.le_two_mul_of_isClosedGeodesicLoop_lower` with the hypothesis

> `hloc : ∀ w, ‖w‖ = m → LocallyInjectiveAtGExp hmet p w`

**removed**.  That hypothesis is *false* in general at a maximal injectivity radius: on `Sⁿ` with
`m = π` every vector of norm `π` maps to the antipode, so `GExp p` is not locally injective there;
the case `m ≥ π/√K` has to be handled by the diameter bound (see
`KlingenbergCore.diameter_gt_half_pi_of_klingenberg`).  Below `π/√K` local injectivity is a
*theorem* (`RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt`, from Rauch's conjugate-radius
bound), and it is exactly what rules out the second alternative of the cut-point dichotomy
(`CutStep3.exists_two_minimising_or_not_locallyInjective`). -/
theorem le_two_mul_of_isClosedGeodesicLoop_lower_of_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    {p : M} {m ℓ : ℝ} (hm : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinj : InjAtLeast hmet p m) (hmax : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hXu : ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
      ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧
        Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ)
    (hℓ : ∀ (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ → ℓ ≤ T) :
    ℓ ≤ 2 * m := by
  rcases Submission.CutStep3.exists_two_minimising_or_not_locallyInjective (cov := cov) hmet htor
    (p := p) (m := m) hinj hmax with ⟨u, v, huv, hG, hu, hv, -⟩ | ⟨w, hw, hwloc⟩
  · rcases hXu u v huv hu hv hG with ⟨T, γ, hT, hloop⟩
    exact le_trans (hℓ T γ hloop) hT
  · have hw0 : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hw
      linarith
    exact absurd (Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov)
      hmet htor hK hKpos hw0 (by rw [hw]; exact hmπ)) hwloc

/-- **The pointwise Klingenberg estimate.**  Let `m` be the maximal injectivity radius of `p` and
suppose that (i) the **Klingenberg–Xu step** holds at `p` (two distinct vectors of norm `m` with the
same image give a closed geodesic loop through `p` of length `≤ 2m`) and (ii) every closed geodesic
loop through `p` has length `≥ 2π/√K` (the deep Klingenberg theorem, in the form needed here).  Then

`π/√K ≤ inj(p)`.

This is the "structure theorem" `inj(p) = min{conj(p), ½ ℓ(p)}` evaluated at the conjugate radius:
if `m < π/√K` the cut-point step produces the two vectors of `hXu`, whose loop has length `≤ 2m` but
also `≥ 2π/√K` — a contradiction; so `π/√K ≤ m`.  It is the pointwise form of the argument used in
`KlingenbergCore.diameter_gt_half_pi_of_klingenberg`. -/
theorem pi_div_sqrt_le_of_isClosedGeodesicLoop_lower
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    {p : M} {m : ℝ} (hm : 0 < m)
    (hinj : InjAtLeast hmet p m) (hmax : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hXu : ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
      ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧
        Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ)
    (hdeep : ∀ (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T) :
    Real.pi / Real.sqrt K ≤ m := by
  by_cases hcase : Real.pi / Real.sqrt K ≤ m
  · exact hcase
  · push_neg at hcase
    rcases Submission.CutStep3.exists_two_minimising_or_not_locallyInjective (cov := cov) hmet htor
      (p := p) (m := m) hinj hmax with ⟨u, v, huv, hG, hu, hv, -⟩ | ⟨w, hw, hwloc⟩
    · rcases hXu u v huv hu hv hG with ⟨T, γ, hT, hloop⟩
      have h1 := hdeep T γ hloop
      have h2 : 2 * Real.pi / Real.sqrt K ≤ 2 * m := le_trans h1 hT
      rw [mul_div_assoc] at h2
      linarith
    · have hw0 : w ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hw
        linarith
      exact absurd (Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov)
        hmet htor hK hKpos hw0 (by rw [hw]; exact hcase)) hwloc

end

end Submission.KlingenbergTransfer
