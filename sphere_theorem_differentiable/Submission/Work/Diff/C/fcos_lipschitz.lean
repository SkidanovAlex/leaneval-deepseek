import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.HopfRinow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The Riemannian distance function `x ↦ d(q,x)` is 1-Lipschitz: the triangle inequality
for `Manifold.riemannianEDist`, transported to `ℝ` via `ENNReal.toReal`. -/
theorem rdist_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M] [PathConnectedSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (q x y : M) :
    |rdist (I := I) (M := M) q y - rdist (I := I) (M := M) q x| ≤ rdist (I := I) (M := M) x y := by
  have hfin : ∀ a b : M, Manifold.riemannianEDist I a b ≠ ⊤ := fun a b =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor a b).ne
  have hqx : (Manifold.riemannianEDist I q x) ≠ ⊤ := hfin q x
  have hxy : (Manifold.riemannianEDist I x y) ≠ ⊤ := hfin x y
  have hqy : (Manifold.riemannianEDist I q y) ≠ ⊤ := hfin q y
  have hyx : (Manifold.riemannianEDist I y x) ≠ ⊤ := hfin y x
  have h1 : rdist (I := I) (M := M) q y ≤ rdist (I := I) q x + rdist (I := I) x y := by
    simp only [rdist]
    calc (Manifold.riemannianEDist I q y).toReal
        ≤ (Manifold.riemannianEDist I q x + Manifold.riemannianEDist I x y).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqx, hxy⟩)
            (Manifold.riemannianEDist_triangle (I := I))
      _ = (Manifold.riemannianEDist I q x).toReal + (Manifold.riemannianEDist I x y).toReal :=
          ENNReal.toReal_add hqx hxy
  have h2 : rdist (I := I) (M := M) q x ≤ rdist (I := I) q y + rdist (I := I) x y := by
    simp only [rdist]
    calc (Manifold.riemannianEDist I q x).toReal
        ≤ (Manifold.riemannianEDist I q y + Manifold.riemannianEDist I y x).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqy, hyx⟩)
            (Manifold.riemannianEDist_triangle (I := I))
      _ = (Manifold.riemannianEDist I q y).toReal + (Manifold.riemannianEDist I y x).toReal :=
          ENNReal.toReal_add hqy hyx
      _ = (Manifold.riemannianEDist I q y).toReal + (Manifold.riemannianEDist I x y).toReal := by
          rw [Manifold.riemannianEDist_comm (I := I) (x := y) (y := x)]
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- `fcos q = cos ∘ d(q,·)` is 1-Lipschitz for the Riemannian distance. -/
theorem fcos_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M] [PathConnectedSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (q x y : M) :
    |fcos (I := I) (M := M) q y - fcos (I := I) (M := M) q x| ≤ rdist (I := I) (M := M) x y := by
  have h := rdist_lipschitz (I := I) (M := M) (cov := cov) hmet htor q x y
  have hcos := Real.abs_cos_sub_cos_le (rdist (I := I) (M := M) q y) (rdist (I := I) (M := M) q x)
  simp only [fcos]
  exact le_trans hcos h

end Work.Diff.C
