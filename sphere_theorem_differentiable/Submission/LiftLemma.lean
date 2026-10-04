import Submission.XuMain
import Submission.EDist
import Submission.SegmentDomain
import Submission.Commons.Topology.Manifold.riemannianEDist_le_half_pathELength

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp
open Submission.InjRadius

/-!
# The continuous minimal lift under the exponential map

**Klingenberg's lifting argument** (Roadmap §113.2, §124.3) needs, for a closed curve `c` which stays
inside the injectivity ball of its base point `p`, the *continuous* lift `s ↦ V s` with
`GExp p (V s) = c s` and `‖V s‖ = d(p, c s)` — i.e. the lift by *minimising* vectors.

Two of the three ingredients are already in the project:

* **existence and uniqueness** of the minimising vector:
  `Submission.SegmentDomain.exists_unique_segmentDomain_vec` (from `HopfRinow` + `InjAtLeast`);
* **continuity of the inverse of `GExp p` on the segment domain**:
  `Submission.XuMain.exists_pos_edist_lt_imp_norm_sub_lt`.

This module assembles them: the lift of a *continuous* curve is continuous.

The third ingredient — the bound `d(c 0, c s) ≤ ½ L(c)` which produces the hypothesis `hlt` for a
closed curve `c` whose length is `< 2 inj(p)` — is *not* in this module (it is a statement about
`Manifold.pathELength` and the Riemannian distance).
-/

namespace Submission.LiftLemma

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

/-- **THE CONTINUOUS MINIMAL LIFT.**  Let `p ∈ M` have injectivity radius at least `ρ`, and let
`c : ℝ → M` be a continuous closed curve with `c 0 = p` all of whose points are at Riemannian
distance `< ρ` from `p`.  Then there is a **continuous** lift `V : ℝ → T_pM` of `c` by
*minimising* vectors: `V s` lies in the segment domain, `GExp p (V s) = c s`, and it is the unique
vector with these properties. -/
theorem exists_continuous_lift (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {ρ : ℝ} (hinj : InjAtLeast hmet p ρ)
    {c : ℝ → M} (hc : ContinuousOn c (Icc (0 : ℝ) 1))
    (hlt : ∀ s ∈ Icc (0 : ℝ) 1, Manifold.riemannianEDist I p (c s) < ENNReal.ofReal ρ) :
    ∃ V : ℝ → TangentSpace I p, ContinuousOn V (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        V s ∈ Submission.SegmentDomain.segmentDomain hmet p ∧
          GExp (cov := cov) hmet p (V s) = c s := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- the lift, defined by choice of the (unique) minimising vector
  let V : ℝ → TangentSpace I p := fun s =>
    if h : Manifold.riemannianEDist I p (c s) < ENNReal.ofReal ρ then
      Classical.choose (Submission.SegmentDomain.exists_unique_segmentDomain_vec (cov := cov)
        hmet htor hinj h)
    else 0
  have hVspec : ∀ s ∈ Icc (0 : ℝ) 1,
      V s ∈ Submission.SegmentDomain.segmentDomain hmet p ∧
        GExp (cov := cov) hmet p (V s) = c s := by
    intro s hs
    have h : Manifold.riemannianEDist I p (c s) < ENNReal.ofReal ρ := hlt s hs
    have hspec := (Submission.SegmentDomain.exists_unique_segmentDomain_vec (cov := cov)
      hmet htor hinj h).choose_spec
    have hVs : V s = Classical.choose (Submission.SegmentDomain.exists_unique_segmentDomain_vec
      (cov := cov) hmet htor hinj h) := by
      change (dite (Manifold.riemannianEDist I p (c s) < ENNReal.ofReal ρ)
        (fun h => Classical.choose (Submission.SegmentDomain.exists_unique_segmentDomain_vec
          (cov := cov) hmet htor hinj h)) (fun _ => 0)) = _
      rw [dif_pos h]
    rw [hVs]
    exact hspec.1
  refine ⟨V, ?_, hVspec⟩
  -- the continuity: the uniqueness and the continuity of `GExp p` on the segment domain
  intro s₀ hs₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδspec⟩ := Submission.XuMain.exists_pos_edist_lt_imp_norm_sub_lt (cov := cov)
    hmet htor (hVspec s₀ hs₀).1 hε
  have hev : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] s₀,
      Manifold.riemannianEDist I (c s₀) (c s) < ENNReal.ofReal δ :=
    (hc.continuousWithinAt hs₀).eventually
      (Submission.EDist.eventually_riemannianEDist_lt (I := I) (c s₀)
        (ENNReal.ofReal_pos.mpr hδpos))
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ', hδ'pos, fun s hs hs' => ?_⟩
  have h1 : Manifold.riemannianEDist I (c s₀) (c s) < ENNReal.ofReal δ :=
    hδ'sub ⟨by rw [Metric.mem_ball]; exact hs', hs⟩
  have hkey : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (V s₀))
      (GExp (cov := cov) hmet p (V s)) < ENNReal.ofReal δ := by
    rw [(hVspec s₀ hs₀).2, (hVspec s hs).2]
    exact h1
  have hfin := hδspec (V s) (hVspec s hs).1 hkey
  simpa [dist_eq_norm] using hfin

/-- **The half-length bound.**  Every point of a closed `C¹` curve is at Riemannian distance at
most half the length of the curve from the base point.  (Proved in the commons as
`Commons.Topology.Manifold.riemannianEDist_le_half_pathELength`; this is the wrapper used by the
lifting argument.) -/
theorem riemannianEDist_le_half_pathELength {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1)) (hloop : γ 1 = γ 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Manifold.riemannianEDist I (γ 0) (γ s) ≤ Manifold.pathELength I γ 0 1 / 2 :=
  Commons.Topology.Manifold.riemannianEDist_le_half_pathELength (I := I) hγ hloop hs

end

end Submission.LiftLemma
