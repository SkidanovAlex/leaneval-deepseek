import Mathlib

/-! Germ-invariance of `IsLocalDiffeomorphAt`. -/

open Filter Set Function

namespace Work.OneDim

theorem local_diffeo_congr {𝕜 E F H₁ H₂ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H₁] [TopologicalSpace H₂]
    {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N]
    {n : WithTop ℕ∞} {f g : M → N} {x : M}
    (hfg : f =ᶠ[nhds x] g) (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨Φ, hxΦ, hEq⟩ := hf
  rw [eventuallyEq_iff_exists_mem] at hfg
  obtain ⟨U, hU, hUeq⟩ := hfg
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  set W : Set M := V ∩ Φ.source with hWdef
  have hWopen : IsOpen W := hVopen.inter Φ.open_source
  have hxW : x ∈ W := ⟨hxV, hxΦ⟩
  have hWsub : W ⊆ Φ.source := inter_subset_right
  have hWsubV : W ⊆ V := inter_subset_left
  set T : Set N := Φ.target ∩ Φ.invFun ⁻¹' W with hTdef
  have hTopen : IsOpen T := by
    have h := (Φ.toOpenPartialHomeomorph.restrOpen W hWopen).open_target
    simpa [hTdef, hWdef] using h
  have key : ∀ y ∈ W, g y = Φ.toFun y := by
    intro y hy
    rw [← hUeq (hVU (hWsubV hy)), hEq (hWsub hy)]
  refine ⟨{ toPartialEquiv :=
              { toFun := g, invFun := Φ.invFun, source := W, target := T,
                map_source' := ?_, map_target' := ?_, left_inv' := ?_, right_inv' := ?_ },
            open_source := hWopen, open_target := hTopen,
            contMDiffOn_toFun := ?_, contMDiffOn_invFun := ?_ }, hxW, ?_⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · rw [key y hy]; exact Φ.map_source (hWsub hy)
    · rw [mem_preimage, key y hy, Φ.toPartialEquiv.left_inv' (hWsub hy)]
      exact hy
  · intro y hy
    exact hy.2
  · intro y hy
    rw [key y hy]
    exact Φ.toPartialEquiv.left_inv' (hWsub hy)
  · intro y hy
    have : Φ.invFun y ∈ W := hy.2
    rw [key (Φ.invFun y) this]; exact Φ.right_inv hy.1
  · refine Φ.contMDiffOn_toFun.mono hWsub |>.congr ?_
    intro y hy
    exact key y hy
  · exact Φ.contMDiffOn_invFun.mono inter_subset_left
  · intro y hy
    change g y = (show M → N from fun z => g z) y
    rfl

end Work.OneDim
