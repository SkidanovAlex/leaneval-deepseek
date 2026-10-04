import Submission.Work.CurvBound.exists_uniform_curvature_bound
import Submission.Work.EvenBound.EvenBound
import Submission.Work.OddBound.klingenbergOddPointwise
import Submission.MetricScale
import Submission.Klingenberg
import Submission.Work.Final.DimOne

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The final assembly of `KlingenbergBound`

`Submission.Klingenberg.KlingenbergBound cov` — the single classical input of the topological sphere
theorem — is proved here from the two parity halves of Klingenberg's diameter estimate, which are
theorems in this workspace:

* `Work.EvenBound.diameter_gt_half_pi_even` (Synge's argument, via the even-dimensional Klingenberg
  length bound), and
* `Work.OddBound.diameter_gt_half_pi_odd_of_lt` (the loop-space minimax, via the odd-dimensional
  Klingenberg length bound).

The passage from the pointwise *strict* pinching `1 ≤ sec < 4` of `KlingenbergBound` to the uniform
pinching `K/4 ≤ sec ≤ K` with `0 < K < 4` required by those theorems is
`Work.CurvBound.exists_uniform_curvature_bound`.

The statement of `KlingenbergBound` is *instance-free* (the metric is a parameter `g`, and the
hypotheses are spelled out through `g.inner`), so the assembled proof introduces the corresponding
`RiemannianBundle` instance locally (`letI`) and converts the hypotheses to the `inner ℝ` form — a
definitional identity, `Submission.MetricScale.inner_eq_g`.

In the odd case the length bound needs `3 ≤ Module.finrank ℝ E`; with `Odd (finrank)` and
`Nontrivial E` this reduces to excluding `finrank = 1`, which is
`Work.Final.false_of_finrank_one` (`Submission/Work/Final/DimOne.lean`).

## Main results

* `Work.Final.klingenbergBound_proved_of_hdim` — the estimate under the extra hypothesis
  `2 ≤ Module.finrank ℝ E`;
* `Work.Final.klingenbergBound_proved` — **the estimate, `sorry`-free, with no dimension
  hypothesis beyond `Nontrivial E`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.CurvatureVec

namespace Work.Final

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- A unit vector of a real inner product space has `⟪u, u⟫ = 1`. -/
lemma inner_self_eq_one_of_norm_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u : V} (h : ‖u‖ = 1) : inner ℝ u u = 1 := by
  rw [real_inner_self_eq_norm_sq, h]
  norm_num

/-- Conversely, `⟪u, u⟫ = 1` forces `‖u‖ = 1`. -/
lemma norm_eq_one_of_inner_self_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u : V} (h : inner ℝ u u = 1) : ‖u‖ = 1 := by
  have h2 : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h
  rw [← Real.sqrt_sq (norm_nonneg u), h2, Real.sqrt_one]

/-- **Klingenberg's diameter estimate, assuming `2 ≤ finrank ℝ E`.**  This is
`Submission.Klingenberg.KlingenbergBound` with the extra hypothesis that the manifold have
dimension at least two (which the sphere theorem always provides, and which is exactly what the
odd-dimensional length bound needs). -/
theorem klingenbergBound_proved_of_hdim
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞] :
    Submission.Klingenberg.KlingenbergBound (I := I) (M := M) cov := by
  intro g hsmooth hmetf htor hge hlt4
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g⟩
  letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := hsmooth
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  haveI hmetI : IsMetricCompatible cov :=
    (Submission.MetricScale.isMetricCompatibleFor_iff (I := I) (cov := cov)).mpr hmetf
  -- the ambient fibre metric is `g`, definitionally
  have hinner : ∀ (x : M) (v w : TangentSpace I x), inner ℝ v w = g.inner x v w :=
    fun x v w => Submission.MetricScale.inner_eq_g x v w
  -- convert the pointwise curvature hypotheses from the `g.inner` to the `inner ℝ`/norm form
  have hge' : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      (1 : ℝ) ≤ inner ℝ (curvVec cov p u v v) u := by
    intro p u v hu hv huv
    have hu' : g.inner p u u = 1 := by
      rw [← hinner p u u]; exact inner_self_eq_one_of_norm_eq_one hu
    have hv' : g.inner p v v = 1 := by
      rw [← hinner p v v]; exact inner_self_eq_one_of_norm_eq_one hv
    have huv' : g.inner p u v = 0 := by rw [← hinner p u v]; exact huv
    have h := hge p u v hu' hv' huv'
    simpa only [hinner p (curvVec cov p u v v) u] using h
  have hlt4' : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      inner ℝ (curvVec cov p u v v) u < (4 : ℝ) := by
    intro p u v hu hv huv
    have hu' : g.inner p u u = 1 := by
      rw [← hinner p u u]; exact inner_self_eq_one_of_norm_eq_one hu
    have hv' : g.inner p v v = 1 := by
      rw [← hinner p v v]; exact inner_self_eq_one_of_norm_eq_one hv
    have huv' : g.inner p u v = 0 := by rw [← hinner p u v]; exact huv
    have h := hlt4 p u v hu' hv' huv'
    simpa only [hinner p (curvVec cov p u v v) u] using h
  -- the uniform pinching `K/4 ≤ sec ≤ K`, `0 < K < 4`
  obtain ⟨K, hKpos, hK4, hcurv, hpinch⟩ :=
    Work.CurvBound.exists_uniform_curvature_bound (I := I) (cov := cov) hmetI htor hge' hlt4'
  rcases Nat.even_or_odd (Module.finrank ℝ E) with hev | hodd
  · exact Work.EvenBound.diameter_gt_half_pi_even (I := I) (cov := cov) hmetI htor hev hKpos hK4
      hcurv hpinch
  · refine Work.OddBound.diameter_gt_half_pi_odd_of_lt (I := I) (cov := cov) hmetI htor ?_ hKpos
      hK4 hcurv ?_
    · obtain ⟨k, hk⟩ := hodd
      omega
    · intro p u v hu hv huv
      have h1 := hge' p u v hu hv huv
      have h2 : K / 4 < 1 := by
        rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
        exact hK4
      linarith

/-- **Klingenberg's diameter estimate** — `Submission.Klingenberg.KlingenbergBound cov` — proved,
with no dimension hypothesis beyond `Nontrivial E`.

In dimension `≥ 2` this is `klingenbergBound_proved_of_hdim`; in dimension `1` the curvature
hypotheses are vacuous and the statement is discharged by the non-existence of a compact, connected,
simply connected, boundaryless one-dimensional manifold (`Work.Final.false_of_finrank_one`). -/
theorem klingenbergBound_proved
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞] :
    Submission.Klingenberg.KlingenbergBound (I := I) (M := M) cov := by
  by_cases hdim : 2 ≤ Module.finrank ℝ E
  · exact klingenbergBound_proved_of_hdim (I := I) (M := M) hdim cov
  · intro g hsmooth hmetf htor hge hlt4
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g⟩
    letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := hsmooth
    haveI hmetI : IsMetricCompatible cov :=
      (Submission.MetricScale.isMetricCompatibleFor_iff (I := I) (cov := cov)).mpr hmetf
    have h1 : Module.finrank ℝ E ≤ 1 := by omega
    have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos_iff.mpr (inferInstance : Nontrivial E)
    have hfreq : Module.finrank ℝ E = 1 := by omega
    exact (Work.Final.false_of_finrank_one (I := I) (M := M) hmetI htor hfreq).elim

end

end Work.Final
