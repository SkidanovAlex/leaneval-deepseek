import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map
import Submission.Work.ORCoherence.Tensor.balanced_map_surjective

namespace Work.ORCoherence.Tensor

open scoped TensorProduct

open Work.ORCoherence

/-- If `g : M →ₗ[R] M'` vanishes on a finite set `T` whose `Balanced.tmul f 1`-images
span `Balanced f M` over `S`, then `Balanced f (LinearMap.range g)` is a subsingleton:
the surjection `Balanced f M ↠ Balanced f (range g)` induced by the corestriction of `g`
sends every generator `Balanced.tmul f 1 m` (`m ∈ T`) to `0`. -/
theorem balanced_subsingleton_range_of_span {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (g : M →ₗ[R] M') (T : Finset M)
    (hspan : Submodule.span S (Balanced.tmul f 1 '' (T : Set M)) = ⊤)
    (h0 : ∀ m ∈ T, g m = 0) : Subsingleton (Balanced f (LinearMap.range g)) := by
  let g' : M →ₗ[R] LinearMap.range g :=
    g.codRestrict (LinearMap.range g) (fun m => g.mem_range_self m)
  have hg' : Function.Surjective g' := by
    intro y
    obtain ⟨m, hm⟩ := y.2
    exact ⟨m, Subtype.ext hm⟩
  have hsurj : Function.Surjective (Balanced.map f g') :=
    balanced_map_surjective f g' hg'
  have hgen : ∀ m ∈ T, Balanced.map f g' (Balanced.tmul f 1 m) = 0 := by
    intro m hm
    rw [Balanced.map_tmul]
    have hgm : g' m = 0 := by
      apply Subtype.ext
      rw [LinearMap.codRestrict_apply]
      simp [h0 m hm]
    rw [hgm, Balanced.tmul_zero]
  have hzero : ∀ y : Balanced f (LinearMap.range g), y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ Submodule.span S (Balanced.tmul f 1 '' (T : Set M)) := by
      rw [hspan]; exact Submodule.mem_top
    have hmap : Balanced.map f g' x ∈
        (Submodule.map (Balanced.map f g')) (Submodule.span S (Balanced.tmul f 1 '' (T : Set M))) :=
      ⟨x, hx, rfl⟩
    have hle : (Submodule.map (Balanced.map f g'))
        (Submodule.span S (Balanced.tmul f 1 '' (T : Set M))) ≤ ⊥ := by
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨m, hm, rfl⟩ := hy
      rw [hgen m hm]
      exact Submodule.zero_mem ⊥
    have hmem := hle hmap
    rwa [Submodule.mem_bot] at hmem
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end Work.ORCoherence.Tensor
