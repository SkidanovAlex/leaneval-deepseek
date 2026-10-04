import Submission.XuStep
import Submission.KlingenbergStep
import Submission.RayConj
import Submission.InjDiam
import Submission.InjBall
import Submission.Shorten
import Submission.RauchK
import Submission.KlingenbergLemma
import Submission.KlingenbergTransfer
import Submission.InjSup

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
open Submission.GExpRay2
open Submission.GlobalExp
open Submission.InjRadius
open Submission.InjRadiusCut
open Submission.RauchK

namespace Submission.KlingenbergCore

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

/-- **The whole Klingenberg estimate reduces to two classical inputs.**  Let `M` be a compact
Riemannian manifold with `sec ≤ K` for some `0 < K < 4`, and assume

* **the Klingenberg–Xu step** (`hXu`): at any point `p` whose *maximal* injectivity radius
  `m` satisfies `m < π/√K`, two distinct minimising vectors of norm `m` with the same image produce a
  **closed geodesic loop through `p` of length `≤ 2m`**.  This is the classical Klingenberg lemma
  (`KlingenbergLemma.le_two_mul_of_isClosedGeodesicLoop_lower` isolates it; the cut-point step
  producing the two vectors is `RayConj.exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt`, and
  `Shorten.exists_shorter_loop_of_lt` is the shortening half of it);
* **the deep Klingenberg theorem** (`hdeep`): every closed geodesic loop has length `≥ 2π/√K`, for
  `sec ∈ [K/4,K]` and `M` simply connected (Klingenberg 1961; this is the free-loop-space
  Morse-theoretic input).

Then `M` has diameter exceeding `π/2`.  *Proof.*  Fix `p` and let `m` be the maximal radius with
`InjAtLeast p m`.  If `π/√K ≤ m` we are done (the cut point of `p` is at distance `≥ m > π/2`).  If
`m < π/√K`, then the cut-point step produces `u ≠ v` of norm `m` with the same image, `hXu` turns
them into a closed geodesic loop of length `T ≤ 2m`, and `hdeep` gives `2π/√K ≤ T ≤ 2m`, i.e.
`π/√K ≤ m`: a contradiction.  So `InjAtLeast p (π/√K)` and Klingenberg's estimate gives the result.

This makes explicit that **the remaining gap of `Klingenberg.KlingenbergBound` is exactly
`hXu` + `hdeep`** (the `hloc`/"fold" input of `KlingenbergLemma` is *not* needed: the case `m ≥ π/√K`
is handled by the diameter bound, and below `π/√K` local injectivity is `RayConj`'s theorem). -/
theorem diameter_gt_half_pi_of_klingenberg (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : CurvLe cov K)
    (hXu : ∀ (p : M) {m : ℝ}, 0 < m → InjAtLeast hmet p m →
      (∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) → m < Real.pi / Real.sqrt K →
      ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
        GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
        ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧
          Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ)
    (hdeep : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q := by
  classical
  obtain ⟨p⟩ : Nonempty M := inferInstance
  -- the two classical facts that pin down the maximal injectivity radius
  obtain ⟨ρ, hρpos, hInjAll⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  obtain ⟨R, hR0, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor p
  obtain ⟨m, hinj, hmax⟩ := Submission.InjRadius.exists_injAtLeast_max (I := I) (cov := cov) hmet
    ⟨ρ, hInjAll p⟩
    ⟨R + 2, Submission.InjSup.not_injAtLeast_of_lt_diam (I := I) (cov := cov) hmet htor
      (x := p) (D := R) (s := R + 1) (by linarith) (by linarith) hR (by linarith)⟩
  have hmpos : 0 < m := by
    by_contra hcon
    push_neg at hcon
    exact hmax ρ (by linarith) (hInjAll p)
  -- the pointwise Klingenberg estimate, from the transfer lemma `KlingenbergTransfer`
  have hcase : Real.pi / Real.sqrt K ≤ m := by
    by_contra hcon
    push_neg at hcon
    refine absurd (Submission.KlingenbergTransfer.pi_div_sqrt_le_of_isClosedGeodesicLoop_lower
      (cov := cov) hmet htor hcurv hK hmpos hinj hmax ?_ (hdeep p)) (not_le.mpr hcon)
    intro u v huv hu hv hG
    exact hXu p hmpos hinj hmax hcon u v huv hu hv hG
  have hπ2 : Real.pi / 2 < Real.pi / Real.sqrt K := by
    have hspos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    have hs2 : Real.sqrt K < 2 := by
      have h := Real.sqrt_lt_sqrt hK.le hK4
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h4] at h
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hspos]
    nlinarith [Real.pi_pos]
  obtain ⟨q, hq⟩ := Submission.KlingenbergStep.exists_edist_gt_half_pi_of_injAtLeast (cov := cov)
    hmet htor hπ2 (injAtLeast_mono (I := I) hmet hinj hcase)
  exact ⟨p, q, hq⟩

end

end Submission.KlingenbergCore
