import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.Tangent

open scoped _root_.Manifold _root_.ContDiff
open Set

/-- **Smooth dependence of a frame on its coordinates.**  For a point `x₀` of a `C^∞` manifold,
the map `(q, v) ↦ v` read in the tangent-bundle trivialisation at `x₀`,
`z ↦ ⟨z.1, (trivializationAt E (TangentSpace I) x₀).symmL ℝ z.1 z.2⟩`, is `C^∞` on
`(chartAt H x₀).source ×ˢ univ`. -/
theorem contMDiffOn_trivializationAt_symmL_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : M × E => (⟨z.1,
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ z.1 z.2⟩ : TangentBundle I M))
      ((chartAt H x₀).source ×ˢ univ) := by
  -- The inverse of the tangent-bundle trivialisation at `x₀` is a `C^∞` map on its target, which
  -- is precisely `(chartAt H x₀).source ×ˢ univ`.
  have h : ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : M × E =>
        ((trivializationAt E (TangentSpace I) x₀).toOpenPartialHomeomorph.symm z :
          TangentBundle I M))
      (trivializationAt E (TangentSpace I) x₀).target :=
    (trivializationAt E (TangentSpace I) x₀).contMDiffOn_symm (n := ∞) (IB := I)
  -- On the base set, the junk-free linear inverse `symmL` agrees with the trivialisation's
  -- inverse, and the two functions have the same underlying total-space element.
  refine h.congr (fun z hz => ?_)
  have hb : z.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hz.1
  rw [Bundle.Trivialization.symmL_apply _ hb]
  exact Bundle.Trivialization.mk_symm _ hb z.2

end Commons.Geometry.Manifold.Tangent
