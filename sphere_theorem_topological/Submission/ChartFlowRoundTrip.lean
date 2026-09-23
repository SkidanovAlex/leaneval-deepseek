import Submission.GExpFlow
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz_of_mem_Ioo
import Submission.Commons.Analysis.ODE.flow_semigroup_of_locallyLipschitz

/-!
# The chart geodesic flow is reversible: the round trip returns to the initial phase

`Submission.GExpFlow.ChartFlowData` provides a family `α` of solutions of the chart spray equation
on the interval `|t| ≤ ρ`, with *uniqueness* (`huniq`).  This file proves that the flow can be run
backwards:

> `chartFlowData_roundTrip`: for `p ∈ D.O`, `|t| ≤ D.ρ` and `D.α p t ∈ D.O`,
> `D.α (D.α p t) (-t) = p`.

The proof is the standard one: the two curves `s ↦ D.α (D.α p t) s` and `s ↦ D.α p (t + s)` solve
the same first order ODE `y' = chartSpray y` and agree at `s = 0`, so by the general uniqueness
theorem for locally Lipschitz ODEs
(`Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz` and its right-endpoint variant) they
agree on the whole interval between `0` and `-t`; evaluating at `s = -t` and using `D.h0` gives the
claim.

**Consequence** (`chartFlowData_injective_timeMap`): the time-`t` map `p ↦ D.α p t` is **injective**
on `D.O` (for `|t| ≤ D.ρ`, restricted to the phases whose image remains in `D.O`).  Together with the
joint smoothness `ChartFlowData.hjoint` — which makes `p ↦ D.α p t` smooth with smooth inverse (the
time-`(-t)` map) — this exhibits the chart flow as a **local diffeomorphism of the state space**,
the ingredient needed to iterate the flow along a ray.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.RauchGen
open Submission.GExpFlow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ChartFlowRoundTrip

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- The chart spray is locally Lipschitz at the phases of the flow. -/
theorem chartSpray_locallyLipschitzAt (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {p : E × E} (hp : p ∈ D.O) {t : ℝ} (ht : |t| ≤ D.ρ) :
    ∃ K : NNReal, ∃ U ∈ 𝓝 (D.α p t), LipschitzOnWith K (chartSpray (cov := cov) z₀) U := by
  have hmem : D.α p t ∈ (extChartAt I z₀).target ×ˢ (univ : Set E) :=
    ⟨D.htgt p hp t ht, mem_univ _⟩
  have hopen : IsOpen ((extChartAt I z₀).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target z₀).prod isOpen_univ
  have hcd : ContDiffAt ℝ 1 (chartSpray (cov := cov) z₀) (D.α p t) :=
    ((contDiffOn_chartSpray (cov := cov) z₀).contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
  exact hcd.exists_lipschitzOnWith

/-- **The chart flow round trip.**  Running the flow for the time `t` and then for the time `-t`
gives back the initial phase. -/
theorem chartFlowData_roundTrip (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {p : E × E} {t : ℝ} (hp : p ∈ D.O) (hpt : D.α p t ∈ D.O) (ht : |t| ≤ D.ρ) :
    D.α (D.α p t) (-t) = p := by
  have htlo : -D.ρ ≤ t := (abs_le.mp ht).1
  have hthi : t ≤ D.ρ := (abs_le.mp ht).2
  have h0' : (fun r : ℝ => D.α (D.α p t) r) 0 = (fun r : ℝ => D.α p (t + r)) 0 := by
    simp only [add_zero]
    exact D.h0 (D.α p t) hpt
  have hrend : D.α p (t + -t) = p := by
    rw [add_neg_cancel, D.h0 p hp]
  rcases le_total 0 (-t) with hle | hle
  · -- `t ≤ 0`: compare on `[0, -t]`
    have hu : ∀ r ∈ Icc (0:ℝ) (-t),
        HasDerivAt (fun r : ℝ => D.α (D.α p t) r)
          (chartSpray (cov := cov) z₀ (D.α (D.α p t) r)) r := by
      intro r hr
      rw [Set.mem_Icc] at hr
      refine D.hode (D.α p t) hpt r ?_
      rw [abs_le]
      exact ⟨by linarith [hr.1], by linarith [hr.2, hthi]⟩
    have hv : ∀ r ∈ Icc (0:ℝ) (-t),
        HasDerivAt (fun r : ℝ => D.α p (t + r))
          (chartSpray (cov := cov) z₀ (D.α p (t + r))) r := by
      intro r hr
      rw [Set.mem_Icc] at hr
      have hmem : |t + r| ≤ D.ρ := by
        rw [abs_le]
        exact ⟨by linarith [hr.1, htlo], by linarith [hr.2]⟩
      have h := D.hode p hp (t + r) hmem
      have h2 : HasDerivAt (fun r : ℝ => t + r) 1 r := by
        simpa using (hasDerivAt_id r).const_add t
      have h3 := HasDerivAt.scomp r h h2
      simpa only [Function.comp_def, one_smul] using h3
    have hloc : ∀ r ∈ Icc (0:ℝ) (-t),
        ∃ K : NNReal, ∃ U ∈ 𝓝 ((fun r : ℝ => D.α (D.α p t) r) r),
          LipschitzOnWith K (chartSpray (cov := cov) z₀) U := by
      intro r hr
      rw [Set.mem_Icc] at hr
      refine chartSpray_locallyLipschitzAt (cov := cov) D hpt ?_
      rw [abs_le]
      exact ⟨by linarith [hr.1], by linarith [hr.2, hthi]⟩
    have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz
      (f := chartSpray (cov := cov) z₀) (a := 0) (b := -t) hle hu hv hloc h0'
    have h_at : D.α (D.α p t) (-t) = D.α p (t + -t) := hEq ⟨hle, le_refl (-t)⟩
    rw [hrend] at h_at
    exact h_at
  · -- `0 ≤ t`: compare on `[-t, 0]` (agreement at the right endpoint `0`)
    have hab : -t ≤ 0 := hle
    have hu : ∀ r ∈ Icc (-t) (0:ℝ),
        HasDerivAt (fun r : ℝ => D.α (D.α p t) r)
          (chartSpray (cov := cov) z₀ (D.α (D.α p t) r)) r := by
      intro r hr
      rw [Set.mem_Icc] at hr
      refine D.hode (D.α p t) hpt r ?_
      rw [abs_le]
      exact ⟨by linarith [hr.1, htlo], by linarith [hr.2]⟩
    have hv : ∀ r ∈ Icc (-t) (0:ℝ),
        HasDerivAt (fun r : ℝ => D.α p (t + r))
          (chartSpray (cov := cov) z₀ (D.α p (t + r))) r := by
      intro r hr
      rw [Set.mem_Icc] at hr
      have hmem : |t + r| ≤ D.ρ := by
        rw [abs_le]
        exact ⟨by linarith [hr.1], by linarith [hr.2, hthi]⟩
      have h := D.hode p hp (t + r) hmem
      have h2 : HasDerivAt (fun r : ℝ => t + r) 1 r := by
        simpa using (hasDerivAt_id r).const_add t
      have h3 := HasDerivAt.scomp r h h2
      simpa only [Function.comp_def, one_smul] using h3
    have hloc : ∀ r ∈ Icc (-t) (0:ℝ),
        ∃ K : NNReal, ∃ U ∈ 𝓝 ((fun r : ℝ => D.α (D.α p t) r) r),
          LipschitzOnWith K (chartSpray (cov := cov) z₀) U := by
      intro r hr
      rw [Set.mem_Icc] at hr
      refine chartSpray_locallyLipschitzAt (cov := cov) D hpt ?_
      rw [abs_le]
      exact ⟨by linarith [hr.1, htlo], by linarith [hr.2]⟩
    have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz_right
      (f := chartSpray (cov := cov) z₀) (a := -t) (b := 0) hab hu hv hloc h0'
    have h_at : D.α (D.α p t) (-t) = D.α p (t + -t) := hEq ⟨le_refl (-t), hab⟩
    rw [hrend] at h_at
    exact h_at

/-- **The chart geodesic flow is a (local) flow**: running it for the time `s` and then for the
time `t` is the same as running it for the time `s + t`.  This is
`Commons.Analysis.ODE.flow_semigroup_of_locallyLipschitz` for the chart spray. -/
theorem chartFlowData_semigroup (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {p : E × E}
    {s t : ℝ} (hp : p ∈ D.O) (hps : D.α p s ∈ D.O)
    (hs : |s| ≤ D.ρ) (ht : |t| ≤ D.ρ) (hst : |s + t| ≤ D.ρ) :
    D.α (D.α p s) t = D.α p (s + t) :=
  Commons.Analysis.ODE.flow_semigroup_of_locallyLipschitz (f := chartSpray (cov := cov) z₀)
    D.hρ D.h0 D.hode (fun q hq r hr => chartSpray_locallyLipschitzAt (cov := cov) D hq hr)
    hp hps hs ht hst

/-- **The chart flow is injective in the initial phase at every fixed time.** -/
theorem chartFlowData_flowMap_injective (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {t : ℝ} (ht : |t| ≤ D.ρ) :
    ∀ p ∈ D.O, ∀ q ∈ D.O, D.α p t ∈ D.O → D.α q t ∈ D.O → D.α p t = D.α q t → p = q := by
  intro p hp q hq hpt hqt heq
  have h1 := chartFlowData_roundTrip (cov := cov) (I := I) D hp hpt ht
  have h2 := chartFlowData_roundTrip (cov := cov) (I := I) D hq hqt ht
  rw [← h1, ← h2, heq]

/-- **The chart flow map is a bijection onto its image.**  Every phase `q` whose backward image
`D.α q (-t)` still lies in `D.O` is the forward image of that backward image. -/
theorem chartFlowData_flowMap_surjective_on_image (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {t : ℝ} (ht : |t| ≤ D.ρ) {q : E × E} (hq : q ∈ D.O) (hqt : D.α q (-t) ∈ D.O) :
    D.α (D.α q (-t)) t = q := by
  have ht' : |-t| ≤ D.ρ := by simpa using ht
  have h := chartFlowData_roundTrip (cov := cov) (I := I) D hq hqt ht'
  simpa using h

end

end Submission.ChartFlowRoundTrip
