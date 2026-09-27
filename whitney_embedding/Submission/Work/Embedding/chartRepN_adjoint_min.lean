import Mathlib
import Submission.Work.Embedding.exists_unique_closest_point

/-!
# First-order optimality for the closest point in chart coordinates

Let `e : M → ℝ^N` be smooth and let `e q` be a closest point to `y` in the image of `e`
(`∀ z, dist y (e q) ≤ dist y (e z)`).  Then the squared distance
`u ↦ ‖y - chartRepN e p u‖ ^ 2`, expressed in the chart at `p`, has a local minimum at the
chart coordinates `u = (chartAt p) q`.  Its Fréchet derivative therefore vanishes there, and the
chain rule identifies that derivative with `-2 * inner ℝ (y - e q) (D ·)`, where
`D = fderiv ℝ (chartRepN e p) u`.  This gives the first-order necessary condition

`(fderiv ℝ (chartRepN e p) u).adjoint (y - e q) = 0`

for the closest point.  This is the linear-algebraic step behind the nearest-point projection
(the `Work.Embedding.exists_smooth_retraction` project).
-/

namespace Work.Embedding

open scoped Manifold ContDiff
open Topology Metric

theorem chartRepN_adjoint_min {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    {p q : M} (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {y : EuclideanSpace ℝ (Fin N)}
    (hmin : ∀ z : M, dist y (e q) ≤ dist y (e z)) :
    (fderiv ℝ (Work.Embedding.chartRepN e p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) q)).adjoint
      (y - e q) = 0 := by
  set u : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) p) q with hudef
  have hu : u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hq
  have hchart_u : Work.Embedding.chartRepN e p u = e q := Work.Embedding.chartRepN_chart e p q hq
  set D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    fderiv ℝ (Work.Embedding.chartRepN e p) u with hD
  -- the squared distance in chart coordinates has a local minimum at `u`
  have hloc : IsLocalMin
      (fun v : EuclideanSpace ℝ (Fin n) => ‖y - Work.Embedding.chartRepN e p v‖ ^ 2) u := by
    show ∀ᶠ v in 𝓝 u,
      ‖y - Work.Embedding.chartRepN e p u‖ ^ 2 ≤ ‖y - Work.Embedding.chartRepN e p v‖ ^ 2
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.mem_nhds hu] with v hv
    have hvs : (chartAt (EuclideanSpace ℝ (Fin n)) p).symm v ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
      (chartAt (EuclideanSpace ℝ (Fin n)) p).map_target hv
    rw [hchart_u, ← (chartAt (EuclideanSpace ℝ (Fin n)) p).right_inv hv,
      Work.Embedding.chartRepN_chart e p _ hvs, ← dist_eq_norm, ← dist_eq_norm]
    exact pow_le_pow_left₀ dist_nonneg (hmin _) 2
  -- differentiability of the chart representation at `u`
  have hdiff : DifferentiableAt ℝ (Work.Embedding.chartRepN e p) u :=
    (Work.Embedding.contDiffAt_chartRepN e he p hu).differentiableAt (by simp)
  have hbase : HasFDerivAt (Work.Embedding.chartRepN e p) D u := by
    simpa only [← hD] using hdiff.hasFDerivAt
  have hconstsub : HasFDerivAt (fun v => y - Work.Embedding.chartRepN e p v) (-D) u :=
    hbase.const_sub y
  -- chain rule: the derivative of the squared distance
  have hf_deriv : HasFDerivAt
      (fun v : EuclideanSpace ℝ (Fin n) => ‖y - Work.Embedding.chartRepN e p v‖ ^ 2)
      ((2 : ℕ) • ((innerSL ℝ (y - e q)) ∘SL (-D))) u := by
    simpa only [hchart_u] using hconstsub.norm_sq
  -- first-order condition: the derivative vanishes at the local minimum
  have hL0 : ((2 : ℕ) • ((innerSL ℝ (y - e q)) ∘SL (-D))) = 0 := by
    rw [← hf_deriv.fderiv]
    exact IsLocalMin.fderiv_eq_zero hloc
  -- hence `y - e q` is orthogonal to the range of `D`
  have hinner : ∀ v : EuclideanSpace ℝ (Fin n), inner ℝ (y - e q) (D v) = 0 := by
    intro v
    have hv : ((2 : ℕ) • ((innerSL ℝ (y - e q)) ∘SL (-D))) v = 0 := by rw [hL0]; simp
    have hval : ((2 : ℕ) • ((innerSL ℝ (y - e q)) ∘SL (-D))) v =
        -2 * inner ℝ (y - e q) (D v) := by
      simp [innerSL_apply_apply, inner_sub_left]
      ring
    linarith [hv, hval]
  have hfin : inner ℝ (D.adjoint (y - e q)) (D.adjoint (y - e q)) = 0 := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hinner _
  exact inner_self_eq_zero.mp hfin

end Work.Embedding
