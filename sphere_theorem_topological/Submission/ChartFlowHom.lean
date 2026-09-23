import Submission.GExpFlow

/-!
# Homogeneity of the chart geodesic flow

`Submission.GExpFlow.ChartFlowData` provides, for a compact piece `Z` of the chart at `z₀`, a time
`ρ > 0`, an open set `O` of initial phases and a family `α` solving the chart geodesic spray
equation for `|t| ≤ ρ`, with uniqueness (`ChartFlowData.huniq`).

The chart spray is **quadratic in the velocity** (`Geodesic.chartGeodesicVectorField_smul`), so the
flow is homogeneous:

> `D.α (q, c • v) t = ((D.α (q, v) (c * t)).1, c • (D.α (q, v) (c * t)).2)`   for `|c| ≤ 1`.

The hypothesis `|c| ≤ 1` is what makes the rescaled curve `s ↦ ((α (q,v) (c s)).1, c • (α (q,v) (c s)).2)`
exist for all `|s| ≤ ρ` (the flow is only available for `|t| ≤ ρ`).

This is the "normalisation" that a continuation along a ray needs: the coordinate velocity of a
geodesic grows from box to box, and re-reading the phase with a smaller velocity and a longer flow
time is exactly what avoids leaving the flow domain.
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

namespace Submission.ChartFlowHom

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- **Homogeneity of the chart geodesic flow.** -/
theorem chartFlowData_homogeneous (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {q v : E} {c t : ℝ} (hc : |c| ≤ 1)
    (hcv : (q, c • v) ∈ D.O) (hv : (q, v) ∈ D.O) (ht : |t| ≤ D.ρ) :
    D.α (q, c • v) t = ((D.α (q, v) (c * t)).1, c • (D.α (q, v) (c * t)).2) := by
  classical
  have hle : ∀ s : ℝ, |s| ≤ D.ρ → |c * s| ≤ D.ρ := by
    intro s hs
    rw [abs_mul]
    calc |c| * |s| ≤ 1 * D.ρ := mul_le_mul hc hs (abs_nonneg s) (by norm_num)
      _ = D.ρ := one_mul _
  have hfst : ∀ s : ℝ, |s| ≤ D.ρ →
      HasDerivAt (fun u : ℝ => (D.α (q, v) (c * u)).1) (c • (D.α (q, v) (c * s)).2) s := by
    intro s hs
    have h1 : HasDerivAt (fun u : ℝ => (D.α (q, v) u).1) ((D.α (q, v) (c * s)).2) (c * s) :=
      (D.hode (q, v) hv (c * s) (hle s hs)).fst
    have h2 : HasDerivAt (fun u : ℝ => c * u) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    have h3 := HasDerivAt.scomp s h1 h2
    simpa only [Function.comp_def] using h3
  have hsnd : ∀ s : ℝ, |s| ≤ D.ρ →
      HasDerivAt (fun u : ℝ => c • (D.α (q, v) (c * u)).2)
        (chartGeodesicVectorField (cov := cov) z₀
          ((D.α (q, v) (c * s)).1, c • (D.α (q, v) (c * s)).2)) s := by
    intro s hs
    have hs' := hle s hs
    have htgt : (D.α (q, v) (c * s)).1 ∈ (extChartAt I z₀).target :=
      D.htgt (q, v) hv (c * s) hs'
    have h1 : HasDerivAt (fun u : ℝ => (D.α (q, v) u).2)
        (chartGeodesicVectorField (cov := cov) z₀ (D.α (q, v) (c * s))) (c * s) :=
      (D.hode (q, v) hv (c * s) hs').snd
    have h2 : HasDerivAt (fun u : ℝ => c * u) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    have h3 := HasDerivAt.scomp s h1 h2
    have h3' : HasDerivAt (fun u : ℝ => (D.α (q, v) (c * u)).2)
        (c • chartGeodesicVectorField (cov := cov) z₀ (D.α (q, v) (c * s))) s := by
      simpa only [Function.comp_def] using h3
    have h4 : HasDerivAt (fun u : ℝ => c • (D.α (q, v) (c * u)).2)
        (c • (c • chartGeodesicVectorField (cov := cov) z₀ (D.α (q, v) (c * s)))) s := by
      have h := h3'.const_smul c
      rw [show (c • fun u : ℝ => (D.α (q, v) (c * u)).2)
          = (fun u : ℝ => c • (D.α (q, v) (c * u)).2) from rfl] at h
      exact h
    have hX : c • (c • chartGeodesicVectorField (cov := cov) z₀ (D.α (q, v) (c * s)))
        = chartGeodesicVectorField (cov := cov) z₀
            ((D.α (q, v) (c * s)).1, c • (D.α (q, v) (c * s)).2) := by
      rw [smul_smul, ← pow_two, ← chartGeodesicVectorField_smul cov z₀ c
        (D.α (q, v) (c * s)) htgt]
    rw [hX] at h4
    exact h4
  have hode : ∀ s : ℝ, |s| ≤ D.ρ →
      HasDerivAt (fun u : ℝ => ((D.α (q, v) (c * u)).1, c • (D.α (q, v) (c * u)).2))
        (chartSpray (cov := cov) z₀
          ((D.α (q, v) (c * s)).1, c • (D.α (q, v) (c * s)).2)) s := by
    intro s hs
    have h := (hfst s hs).prodMk (hsnd s hs)
    rw [chartSpray_apply]
    exact h
  have h0 : (fun u : ℝ => ((D.α (q, v) (c * u)).1, c • (D.α (q, v) (c * u)).2)) 0
      = (q, c • v) := by
    simp only [mul_zero, D.h0 (q, v) hv]
  have hres := D.huniq (q, c • v) hcv
    (fun u : ℝ => ((D.α (q, v) (c * u)).1, c • (D.α (q, v) (c * u)).2)) hode h0 t ht
  exact hres.symm

end

end Submission.ChartFlowHom
