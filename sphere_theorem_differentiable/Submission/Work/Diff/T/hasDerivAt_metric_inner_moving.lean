import Mathlib
import Submission.Work.Diff.T.lc_deps
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Work.Diff.T.bilin_apply_isLittleO

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- Product rule for a moving point against the `t`-dependent metric: if `F` is differentiable at
`t₀`, then `t ↦ (G t).inner x (F t) z` has derivative `dtMet G t₀ x (F t₀) z + (G t₀).inner x A z`.

Suggested route: split `F t = F t₀ + (F t - F t₀)`; the first part is `metric_family_deriv`
(imported).  For the second, write `F t - F t₀ = (t - t₀) • A + Δ t` with
`Δ t = F t - F t₀ - (t-t₀) • A`, so the second part is the sum of the differentiable
`t ↦ (t - t₀) * (G t).inner x A z` (derivative `(G t₀).inner x A z`) and the `o(t - t₀)` term
`t ↦ (G t).inner x (Δ t) z`.  For the latter, introduce the Riemannian bundle instance
`letI : RiemannianBundle _ := ⟨(G t₀).toRiemannianMetric⟩` inside the proof, take a
`(G t₀)`-orthonormal basis `b`, expand `Δ t = ∑ j, (G t₀).inner x (b j) (Δ t) • b j`, and use
`HasDerivAt.isLittleO` for `hF` together with the boundedness of `t ↦ (G t).inner x (b j) z` near
`t₀` (continuity, from `metric_family_deriv`). -/
theorem hasDerivAt_metric_inner_moving
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) {x : M} {F : ℝ → TangentSpace I x} {A : TangentSpace I x}
    (hF : HasDerivAt F A t₀) (z : TangentSpace I x) :
    HasDerivAt (fun t ↦ (G t).inner x (F t) z)
      (dtMet G t₀ x (F t₀) z + (G t₀).inner x A z) t₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  classical
  -- the metric pairing with fixed vectors is differentiable, by `metric_family_deriv`
  have hD : ∀ u v : TangentSpace I x,
      HasDerivAt (fun t ↦ (G t).inner x u v) (dtMet G t₀ x u v) t₀ :=
    fun u v ↦ metric_family_deriv hJopen hJs ht₀ x u v
  -- the second-order remainder `Δ t = F t - F t₀ - (t - t₀) • A`
  set Δ : ℝ → TangentSpace I x := fun t ↦ F t - F t₀ - (t - t₀) • A with hΔdef
  have hΔ : Δ =o[𝓝 t₀] (fun t ↦ t - t₀) := by
    rw [hΔdef]; exact hF.isLittleO
  -- splitting the moving point
  have hkey : ∀ t : ℝ, (G t).inner x (F t) z
      = (G t).inner x (F t₀) z
        + ((t - t₀) * ((G t).inner x A z) + (G t).inner x (Δ t) z) := by
    intro t
    have hdecomp : F t = F t₀ + (t - t₀) • A + (F t - F t₀ - (t - t₀) • A) := by abel
    rw [hdecomp, hΔdef]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
    abel
  have h0 : HasDerivAt (fun t ↦ (G t).inner x (F t₀) z) (dtMet G t₀ x (F t₀) z) t₀ := hD _ _
  -- the linear-in-`t` part
  have h1 : HasDerivAt (fun t : ℝ ↦ (t - t₀) * ((G t).inner x A z)) ((G t₀).inner x A z) t₀ := by
    have hd : HasDerivAt (fun t : ℝ ↦ t - t₀) 1 t₀ := by
      simpa using (hasDerivAt_id t₀).sub_const t₀
    have hm : HasDerivAt ((fun t : ℝ ↦ t - t₀) * (fun t ↦ (G t).inner x A z))
        (1 * ((G t₀).inner x A z) + (t₀ - t₀) * (dtMet G t₀ x A z)) t₀ := hd.mul (hD A z)
    have hm2 := hm.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext t; rfl))
    have hder : 1 * ((G t₀).inner x A z) + (t₀ - t₀) * (dtMet G t₀ x A z)
        = (G t₀).inner x A z := by ring
    exact hm2.congr_deriv hder
  -- the `o(t - t₀)` part
  have h2 : HasDerivAt (fun t ↦ (G t).inner x (Δ t) z) 0 t₀ := by
    refine HasDerivAt.of_isLittleO ?_
    have hcore : (fun t ↦ (G t).inner x (Δ t) z) =o[𝓝 t₀] (fun t ↦ t - t₀) :=
      bilin_apply_isLittleO (V := TangentSpace I x) (b := Module.finBasis ℝ E)
        (B := fun t ↦ (G t).inner x) hΔ (fun w ↦ (hD w z).continuousAt)
    simpa [hΔdef] using hcore
  have hsum := h0.add (h1.add h2)
  have hev : (fun t ↦ (G t).inner x (F t) z) =ᶠ[𝓝 t₀]
      ((fun t ↦ (G t).inner x (F t₀) z)
        + ((fun t ↦ (t - t₀) * ((G t).inner x A z)) + fun t ↦ (G t).inner x (Δ t) z)) :=
    Filter.EventuallyEq.of_eq (by funext t; exact hkey t)
  have hgoal := hsum.congr_of_eventuallyEq hev
  refine hgoal.congr_deriv ?_
  rw [add_zero]

end Work.Diff.T
