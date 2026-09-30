import Mathlib
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LeviCivita

open scoped Manifold ContDiff Bundle Topology in
theorem contMDiffAt_mvfderiv_section
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {f : M → ℝ} {Y : Π x : M, TangentSpace I x} {x₀ : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hY : ContMDiff I I.tangent ∞ (T% Y)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x : M ↦ mvfderiv I f x (Y x)) x₀ := by
  exact (Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
    (F := ℝ) (I := I) (f := f) (X := Y) hf hY).contMDiffAt

end Work.LeviCivita
