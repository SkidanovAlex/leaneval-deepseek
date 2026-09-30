import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.LocalDiffeomorph

open scoped _root_.Manifold _root_.ContDiff
open Filter
open scoped Topology

/-- `IsLocalDiffeomorphAt` depends only on the germ of the function at the point. -/
theorem isLocalDiffeomorphAt_congr_of_eventuallyEq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {f g : M → N} {x : M} {n : ℕ∞ω}
    (hf : IsLocalDiffeomorphAt I I' n f x) (h : f =ᶠ[𝓝 x] g) :
    IsLocalDiffeomorphAt I I' n g x := by
  obtain ⟨Φ, hx, heq⟩ := hf
  let S : Set M := {y | f y = g y}
  let U : Set M := Φ.source ∩ interior S
  have hUopen : IsOpen U := Φ.open_source.inter isOpen_interior
  have hxU : x ∈ U := ⟨hx, mem_interior_iff_mem_nhds.mpr h⟩
  have hUsub : U ⊆ Φ.source := Set.inter_subset_left
  have hUS : U ⊆ S := fun _ hy => interior_subset hy.2
  refine ⟨?_, ?_⟩
  · refine
      { toPartialEquiv :=
          { toFun := ⇑Φ
            invFun := Φ.invFun
            source := U
            target := ⇑Φ '' U
            map_source' := fun _ hy => ⟨_, hy, rfl⟩
            map_target' := ?_
            left_inv' := fun _ hy => Φ.left_inv' hy.1
            right_inv' := ?_ }
        open_source := hUopen
        open_target := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hUopen Set.inter_subset_left
        contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
        contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono ?_ }
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨Φ.map_target' (Φ.map_source' hz.1), by rw [Φ.left_inv' hz.1]; exact hz.2⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact Φ.right_inv' (Φ.map_source' hz.1)
    · rintro _ ⟨z, hz, rfl⟩
      exact Φ.map_source' hz.1
  · exact ⟨hxU, fun y hy => (hUS hy).symm.trans (heq hy.1)⟩

end Commons.Geometry.Manifold.LocalDiffeomorph