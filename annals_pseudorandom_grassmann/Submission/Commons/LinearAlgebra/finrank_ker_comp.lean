import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra

open Module

/-- **Dimension of the kernel of a composite linear map.**

For `f : V →ₗ[K] W` and `g : W →ₗ[K] U` with `V` finite dimensional,

`finrank (ker (g ∘ f)) = finrank (ker f) + finrank (ker g ⊓ range f)`.

This is rank–nullity applied to the restriction `f' := f ∘ (ker (g ∘ f)).subtype`:
its kernel is `ker f` (identified through the inclusion `ker f ≤ ker (g ∘ f)`) and its
range is `ker g ⊓ range f` (an element of `ker (g ∘ f)` maps into `ker g ∩ range f`, and
conversely an element of `ker g ∩ range f` is the image of a preimage lying in
`ker (g ∘ f)`). -/
theorem finrank_ker_comp {K : Type*} [Field K] {V W U : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [FiniteDimensional K V] (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    Module.finrank K ↥(LinearMap.ker (g.comp f)) =
      Module.finrank K ↥(LinearMap.ker f) +
        Module.finrank K ↥(LinearMap.ker g ⊓ LinearMap.range f) := by
  classical
  set S : Submodule K V := LinearMap.ker (g.comp f) with hS
  have hker_le : LinearMap.ker f ≤ S := by
    rw [hS]
    exact LinearMap.ker_le_ker_comp f g
  let f' : S →ₗ[K] W := f.comp S.subtype
  have hkerf' : LinearMap.ker f' = Submodule.comap S.subtype (LinearMap.ker f) := by
    change LinearMap.ker (f.comp S.subtype) = Submodule.comap S.subtype (LinearMap.ker f)
    rw [LinearMap.ker_comp]
  have h1 : Module.finrank K ↥(LinearMap.ker f') = Module.finrank K ↥(LinearMap.ker f) := by
    rw [hkerf']
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hker_le)
  have hmap : LinearMap.range f' = Submodule.map f S := by
    change LinearMap.range (f.comp S.subtype) = Submodule.map f S
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrange : LinearMap.range f' = LinearMap.ker g ⊓ LinearMap.range f := by
    rw [hmap]
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hxS, rfl⟩ := hy
      refine ⟨?_, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩
      rw [hS] at hxS
      simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hxS
    · rintro y ⟨hyg, hyr⟩
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hyr
      refine Submodule.mem_map.mpr ⟨x, ?_, rfl⟩
      rw [hS]
      show (g.comp f) x = 0
      simpa [LinearMap.comp_apply] using hyg
  have h2 : Module.finrank K ↥(LinearMap.range f') =
      Module.finrank K ↥(LinearMap.ker g ⊓ LinearMap.range f) := by
    rw [hrange]
  have hrn := LinearMap.finrank_range_add_finrank_ker f'
  rw [h1, h2] at hrn
  -- `set` already replaced the target occurrence by `S`
  omega

end Commons.LinearAlgebra