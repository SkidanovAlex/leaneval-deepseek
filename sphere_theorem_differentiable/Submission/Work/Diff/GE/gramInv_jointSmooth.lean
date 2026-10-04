import Mathlib
import Submission.Work.Diff.GE.rmPDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- Joint smoothness of the inverse Gram matrix of the coordinate frame.

`GramInv G x₀ t y = (GramM G x₀ t y)⁻¹` with `GramM G x₀ t y i j = mComp G x₀ i j t y =
(G t).inner y (cFrame x₀ i y) (cFrame x₀ j y)`.  For a jointly `C^∞` family of metrics `G` and
`t₀ ∈ J`, each entry of the inverse Gram matrix is jointly `C^∞` near `(t₀, x₀)`.
`Work.Diff.EXT.JointSmoothAt I M Ψ t x` is
`ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞ Ψ (t, x)`.

Usable route: `Work.Diff.EXT.contMDiffAt_metric_pairing` gives joint smoothness of
`(t,y) ↦ mComp G x₀ i j t y` (`cFrame x₀ i` is `SmoothFieldAt` at `x₀` by
`Work.Diff.EXT.smoothFieldAt_cFrame`), `contMDiffAt_pi_space` assembles the matrix-valued version
`Mx`, and `Work.Diff.EXT.contMDiffAt_matrix_inv` gives the inverse once
`(Matrix.of (Mx (t₀,x₀))).det ≠ 0`; the latter holds because the Gram matrix of a basis for a
positive definite form is invertible (e.g. `Work.Diff.GE.CGramInv.gramBil_nondegenerate` with
`@LinearMap.BilinForm.nondegenerate_iff_det_ne_zero` and `Work.Diff.GE.CGramInv.GramM_eq_toMatrix`).
Entry-wise smoothness of the inverse then follows by evaluating at `(k,m)`. -/
theorem gramInv_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (x₀ : M) (k m : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.GramInv (I := I) G x₀ p.1 p.2 k m) t₀ x₀ := by
  classical
  -- The coordinate frame vectors are `C^∞` sections at the chart centre `x₀`.
  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.SmoothFieldAt I M (Work.Diff.GE.cFrame (I := I) x₀ i) x₀ := by
    intro i
    have h := Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀
      (Work.Diff.GE.cBasis (E := E) i) (mem_chart_source H x₀)
    simpa only [Work.Diff.EXT.SmoothFieldAt, Work.Diff.GE.cFrame,
      Submission.Geodesic.frameSection_eq_frameVector, Submission.Geodesic.frameVector] using h
  -- Each entry of the Gram matrix is jointly smooth.
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) t₀ x₀ := by
    intro i j
    have h := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) (G := G)
      hJ hG ht₀ (hframe i) (hframe j)
    simpa only [Work.Diff.GE.GramM, Work.Diff.GE.mComp] using h
  -- Assembled into the matrix-valued (Pi-type) version.
  have hMx : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => fun i j => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) t₀ x₀ := by
    show ContMDiffAt _ _ _ (fun p : ℝ × M => fun i j =>
      Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) _
    rw [contMDiffAt_pi_space]
    intro i
    rw [contMDiffAt_pi_space]
    exact hentry i
  -- The Gram matrix of the coordinate basis for a positive definite form is invertible.
  have hdet : (Matrix.of (fun i j => Work.Diff.GE.GramM (I := I) G x₀ t₀ x₀ i j)).det ≠ 0 := by
    have hnd : (Work.Diff.GE.CGramInv.gramBil (I := I) G x₀ x₀ t₀).Nondegenerate :=
      Work.Diff.GE.CGramInv.gramBil_nondegenerate (I := I) G x₀ (mem_chart_source H x₀) t₀
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (Work.Diff.GE.cBasis (E := E))).mp hnd
    rwa [← Work.Diff.GE.CGramInv.GramM_eq_toMatrix (I := I) G x₀ x₀ t₀] at h
  -- The inverse family is jointly smooth ...
  have hinv := Work.Diff.EXT.contMDiffAt_matrix_inv (I := I) (M := M)
    (n := Module.finrank ℝ E)
    (Mx := fun p : ℝ × M => fun i j => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) hMx hdet
  -- ... and so is each of its entries.
  have hg : ContDiffAt ℝ ∞
      (fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => A k m)
      ((fun p : ℝ × M => fun i j =>
        ((Matrix.of (fun i j => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j))⁻¹) i j)
        (t₀, x₀)) := by
    fun_prop
  exact hg.comp_contMDiffAt hinv

end Work.Diff.GE
