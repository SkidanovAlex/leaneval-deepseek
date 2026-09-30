import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.VectorBundle.CovariantDerivative

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField Bundle

/-- If a covariant derivative on the tangent bundle is smooth, then `∇_Y Z` (the section
`fun y => cov Z y (Y y)`) is a smooth vector field whenever `Z` and `Y` are smooth.
This is the regularity needed to differentiate metric-compatibility identities a second
time (e.g. to prove skew-adjointness of the Riemann curvature operator). -/
theorem contMDiff_cov_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {Z Y : Π x : M, TangentSpace I x}
    (hZ : CMDiff ∞ (T% Z)) (hY : CMDiff ∞ (T% Y)) :
    CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) := by
  -- `ContMDiffCovariantDerivative` requires its sections to be `C^{k+1}` (here `C^∞`)
  -- with the smoothness read in the product model `I.prod 𝓘(ℝ, E)` of the tangent bundle.
  -- This is the same statement as `hZ` (whose codomain model is `I.tangent = I.prod 𝓘(ℝ, E)`).
  have hZ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ + 1) (T% Z) Set.univ := by
    change ContMDiffOn I I.tangent (∞ + 1) (T% Z) Set.univ
    rw [contMDiffOn_univ]
    simpa using hZ
  -- Smoothness of the connection gives that the map `y ↦ ⟨y, cov Z y⟩` is a smooth
  -- section of the hom bundle `Hom(TM, TM)`.
  have hcovZ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => (⟨x, cov Z x⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) Set.univ := by
    simpa [CovariantDerivative.toFun] using (hcov.contMDiff.contMDiff (σ := Z) hZ')
  have hcovZ' : CMDiff ∞ (fun m : M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) m (cov Z m)) := by
    rw [← contMDiffOn_univ]
    simpa using hcovZ
  -- A smooth hom-bundle section applied to a smooth vector field is a smooth vector field.
  exact ContMDiff.clm_bundle_apply (F₁ := E) (F₂ := E) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (b := (id : M → M)) (ϕ := fun m => cov Z m) (v := Y) hcovZ' hY

end Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
